// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The sequential `stamp-verified` lanes' half of Lean's inductive replay.
//!
//! Those lanes replay a module's inductive blocks from its shard through the
//! kernel's own admission (`add_inductive_core`), so the environment the rest
//! of the module is checked against holds the REGENERATED constructors and
//! recursors. But the shard carries only each member's TYPE, never a
//! recursor's rules, and each member was stamped `KernelVerified` when its
//! type matched. Measured 2026-09-24 (`replay_forged/ReplayForgedRule`): the
//! recursor `FRR.rec` stored with the rule for `FRR.a` in place of the rule
//! for `FRR.b` was stamped `KernelVerified` with its block, while `leanchecker`
//! reports `Invalid recursor FRR.rec`.
//!
//! [`refuse_forged_family_members`] reads the members as the `.olean` stores
//! them and requires each to equal the one the kernel generated
//! (`Environment::lean_replay_compare_stored_member`, Lean's
//! `checkPostponedConstructors` / `checkPostponedRecursors`). Every member of
//! a block with a difference is refused and loses its stamp; the caller then
//! demotes every constant of the run that uses one.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use clean_kernel::env::StoredFamilyMember;
use clean_kernel::{Environment, Name};

use crate::verify::incremental::IncrementalVerifyReport;

/// The block (its first type) a stored member belongs to.
fn stored_block_heads(stored: &clean_olean::StoredFamilyMembers) -> BTreeMap<Name, Name> {
    let mut head_of: BTreeMap<Name, Name> = BTreeMap::new();
    for ind in &stored.inductives {
        let head = ind
            .all_names
            .first()
            .cloned()
            .unwrap_or_else(|| ind.name.clone());
        head_of.insert(ind.name.clone(), head);
    }
    let types: Vec<(Name, Name)> = head_of
        .iter()
        .map(|(t, h)| (t.clone(), h.clone()))
        .collect();
    for cv in &stored.constructors {
        if let Some(head) = head_of.get(&cv.inductive_name).cloned() {
            head_of.insert(cv.name.clone(), head);
        }
    }
    for rv in &stored.recursors {
        let rendered = rv.name.to_string();
        let owner = types.iter().find(|(ty, _)| {
            let prefix = format!("{ty}.rec");
            rendered == prefix
                || rendered
                    .strip_prefix(&prefix)
                    .and_then(|rest| rest.strip_prefix('_'))
                    .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
        });
        if let Some((_, head)) = owner {
            head_of.insert(rv.name.clone(), head.clone());
        }
    }
    head_of
}

/// Compare every inductive-family member `olean` stores with the one `env`
/// holds (the kernel's regeneration), refuse every member of a block with a
/// difference — and every stored member that belongs to no stored block, or
/// did not convert — and move each out of `report`'s `KernelVerified` names
/// into its failures. Returns how many were refused.
///
/// # Errors
/// The `.olean` could not be parsed; the caller refuses the module instead.
pub(super) fn refuse_forged_family_members(
    report: &mut IncrementalVerifyReport,
    env: &Environment,
    olean: &Path,
) -> Result<usize, String> {
    // The module's authoritative part (R113, `clean_olean::read_artifact`): a
    // module-system artifact's private families are in its `.olean.private`
    // alone, which the `.olean` this read before never showed.
    let module = crate::lean4::olean::olean_bridge::parse_dep_module_types_only(olean)
        .map_err(|e| e.to_string())?;
    let stored = clean_olean::stored_family_members(&module);
    let head_of = stored_block_heads(&stored);

    let mut findings: BTreeMap<Name, String> = BTreeMap::new();
    let mut orphans: Vec<(String, String)> = stored.unconvertible.clone();
    let members = stored
        .inductives
        .iter()
        .map(|v| (&v.name, StoredFamilyMember::Inductive(v)))
        .chain(
            stored
                .constructors
                .iter()
                .map(|v| (&v.name, StoredFamilyMember::Constructor(v))),
        )
        .chain(
            stored
                .recursors
                .iter()
                .map(|v| (&v.name, StoredFamilyMember::Recursor(v))),
        );
    for (name, member) in members {
        let Some(head) = head_of.get(name) else {
            orphans.push((
                name.to_string(),
                format!(
                    "replay order: `{name}` belongs to no inductive block this module declares, \
                     so Lean's replay never generates it (No such constructor/recursor)"
                ),
            ));
            continue;
        };
        if let Err(mismatch) = env.lean_replay_compare_stored_member(member) {
            findings
                .entry(head.clone())
                .or_insert_with(|| mismatch.to_string());
        }
    }

    let mut refused: BTreeMap<String, String> = orphans.into_iter().collect();
    for (member, head) in &head_of {
        if let Some(why) = findings.get(head) {
            refused
                .entry(member.to_string())
                .or_insert_with(|| format!("replay order: `{member}`: {why}"));
        }
    }
    let before = report.kernel_verified_names.len();
    report
        .kernel_verified_names
        .retain(|n| !refused.contains_key(n));
    let unstamped = before - report.kernel_verified_names.len();
    report.kernel_verified = report.kernel_verified.saturating_sub(unstamped);
    let already_failed: BTreeSet<String> = report.failures.iter().map(|(n, _)| n.clone()).collect();
    let mut newly_failed = 0usize;
    for (name, why) in &refused {
        if !already_failed.contains(name) {
            report.failures.push((name.clone(), why.clone()));
            newly_failed += 1;
        }
    }
    report.failed += newly_failed;
    Ok(refused.len())
}
