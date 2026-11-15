// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The inductive half of Lean's replay for the `.olean` re-check lanes.
//!
//! The lanes register a module's inductive types, constructors and recursors
//! through the loader's structural tier, which since 2026-09-26 refuses a
//! recursor, constructor or inductive record the kernel does not derive from
//! the stored family (clean-kernel `env/imported_family.rs`); before that, and
//! for the family declaration itself still, they were taken as stored, and
//! the lanes checked only that each stored TYPE is a type. Lean's replay (`src/lean/Lean/Replay.lean`) trusts
//! none of the stored fields: it rebuilds each block's `inductDecl` from the
//! stored types, lets the kernel regenerate the constructors and recursors,
//! and requires every stored constructor and recursor to be identical to the
//! regenerated one ("Invalid constructor", "Invalid recursor"), and one it does
//! not regenerate to be refused ("No such constructor", "No such recursor").
//! Measured 2026-09-24 on `.olean`s written with the kernel bypassed
//! (`replay_forged/ReplayForgedRec`, `ReplayForgedRule`, `ReplayForgedCtor`):
//! `per-constant-verify` and `stamp-verified --parallel` stamped `False`
//! proved through a recursor stored with no minor premises, and through a
//! constructor stored with type `False`.
//!
//! [`inductive_block_refusals`] runs
//! [`Environment::lean_replay_inductive_block`] once per block among a
//! replay's local declarations and returns the members to refuse. A refused
//! block refuses EVERY member it has among the replay's declarations, and the
//! replay's admission gate then refuses every declaration that uses one —
//! stricter than Lean, which refuses only the differing member and checks the
//! users against the regenerated block; for an honest `.olean` the two agree,
//! because every stored member IS the regenerated one.
//!
//! A block is FOUND through a type's stored `all` (its first name), which is
//! only a claim: a type whose `all` names a block that does not contain it is
//! never rebuilt by that block. Measured 2026-10-22 on `.olean`s written with
//! the kernel bypassed (`replay_forged/ReplayForgedAllGhost`,
//! `ReplayForgedAllOther`): `FAG : Prop | mk : (FAG → False) → FAG`, a
//! negative occurrence Lean's kernel refuses, stored with `all := [FAG_ghost]`
//! (no such type) or `all := [FAH, FAO]` (an honest type first), and no
//! recursor, was never sent to `add_inductive_core`, and every `.olean` re-check
//! lane but the sequential `stamp-verified` modes admitted a proof of `False`
//! through it (`clean olean replay`, `verify-batch --full-validation`,
//! `per-constant-verify`, `stamp-verified --parallel`). Pinned `leanchecker`
//! refuses both. So coverage is decided by what the replay GENERATED, never by
//! `all`: every local type and constructor a replay checks must be one that a
//! block it rebuilt through the kernel declares, or it is refused by name (the
//! "No such recursor" rule already held recursors to that).

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::Environment;
use clean_kernel::name::Name;

use crate::replay_order::ReplayRefusal;

/// The first type of the block `name` (a type or constructor) belongs to.
fn block_head(env: &Environment, name: &Name) -> Option<Name> {
    let inductive = match env.get_constructor(name) {
        Some(cv) => cv.inductive_name.clone(),
        None => name.clone(),
    };
    let ind = env.get_inductive(&inductive)?;
    Some(ind.all_names.first().cloned().unwrap_or(inductive))
}

/// Whether `rec` is `<T>.rec` or a nested auxiliary `<T>.rec_<n>` for a type
/// `T` of `block`.
fn is_block_recursor(rec: &Name, block: &[Name]) -> bool {
    let rendered = rec.to_string();
    block.iter().any(|ty| {
        let prefix = format!("{ty}.rec");
        rendered == prefix
            || rendered
                .strip_prefix(&prefix)
                .and_then(|rest| rest.strip_prefix('_'))
                .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
    })
}

/// Replay the inductive blocks among `local` (the declarations one replay
/// schedules) that have a member in `wanted` (the ones it will check), and
/// return the local types, constructors and recursors Lean's replay would not
/// admit, each with its reason. A declaration absent from the result is either
/// not an inductive-family member or a member of a block that replayed
/// identically (or of a block no wanted declaration reaches).
#[must_use]
pub fn inductive_block_refusals(
    env: &Environment,
    local: &BTreeSet<Name>,
    wanted: &BTreeSet<Name>,
) -> BTreeMap<Name, ReplayRefusal> {
    let mut refusals = BTreeMap::new();
    let refuse = |refusals: &mut BTreeMap<Name, ReplayRefusal>, name: &Name, reason: String| {
        refusals
            .entry(name.clone())
            .or_insert_with(|| ReplayRefusal::InductiveReplay {
                name: name.clone(),
                reason,
            });
    };

    // Blocks with a local type. A local constructor whose inductive is not a
    // local type extends a family this replay does not declare: Lean's replay
    // never generates it ("No such constructor").
    let mut local_heads: BTreeSet<Name> = BTreeSet::new();
    for name in local {
        if env.get_inductive(name).is_some() {
            if let Some(head) = block_head(env, name) {
                local_heads.insert(head);
            }
        } else if let Some(cv) = env.get_constructor(name) {
            let ind = &cv.inductive_name;
            if local.contains(ind) {
                if let Some(head) = block_head(env, ind) {
                    local_heads.insert(head);
                }
            } else if wanted.contains(name) {
                refuse(
                    &mut refusals,
                    name,
                    format!(
                        "No such constructor {name}: its inductive `{ind}` is not declared by \
                         this replay, so the kernel never generates it (Lean's replay: \
                         checkPostponedConstructors)"
                    ),
                );
            }
        }
    }

    let mut generated: BTreeSet<Name> = BTreeSet::new();
    let mut failed_blocks: Vec<(Vec<Name>, String)> = Vec::new();
    for head in &local_heads {
        let block = env
            .get_inductive(head)
            .map(|ind| ind.all_names.clone())
            .filter(|all| !all.is_empty())
            .unwrap_or_else(|| vec![head.clone()]);
        // A block is replayed when a declaration the replay checks is one of
        // its members (a recursor reaches its block by name, since a member's
        // references exclude its own block).
        let reached = wanted.iter().any(|w| {
            block.contains(w)
                || env
                    .get_constructor(w)
                    .is_some_and(|cv| block.contains(&cv.inductive_name))
                || (env.get_recursor(w).is_some() && is_block_recursor(w, &block))
        });
        if !reached {
            continue;
        }
        match env.lean_replay_inductive_block(std::slice::from_ref(head)) {
            Err(mismatch) => failed_blocks.push((block, mismatch.to_string())),
            Ok(names) => {
                // A declared recursor of this block that is NOT resident was
                // refused when the module was imported: the loader admits a
                // recursor record only if it equals the one the kernel
                // generates from the stored family (clean-kernel
                // `env/imported_family.rs`). Lean's replay refuses the block
                // for it ("Invalid recursor"), so this replay does too, rather
                // than pass a block whose stored recursor it never saw.
                let absent = local.iter().chain(wanted).find(|name| {
                    is_block_recursor(name, &block)
                        && env.get_recursor(name).is_none()
                        && env.get_const(name).is_none()
                });
                match absent {
                    Some(absent) => failed_blocks.push((
                        block,
                        format!(
                            "Invalid recursor {absent}: the stored record was refused when the \
                             module was imported, as it is not the recursor the kernel \
                             generates from the stored family (Lean's replay: \
                             checkPostponedRecursors)"
                        ),
                    )),
                    None => generated.extend(names),
                }
            }
        }
    }

    for (block, why) in &failed_blocks {
        for name in local {
            let member = block.contains(name)
                || env
                    .get_constructor(name)
                    .is_some_and(|cv| block.contains(&cv.inductive_name))
                || (env.get_recursor(name).is_some() && is_block_recursor(name, block));
            if member {
                refuse(&mut refusals, name, why.clone());
            }
        }
    }

    // A wanted type or constructor no replayed block declares. Lean's replay
    // adds a type only through the `inductDecl` it builds from the type's
    // stored `all`, and checks every stored constructor against the ones that
    // declaration generated ("No such constructor"); a type whose `all` names
    // a block that does not contain it is never declared by any block. Coverage
    // is what this replay rebuilt (`generated`), never the stored `all`.
    for name in wanted {
        if !local.contains(name) || refusals.contains_key(name) || generated.contains(name) {
            continue;
        }
        if let Some(ind) = env.get_inductive(name) {
            let all = ind
                .all_names
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            refuse(
                &mut refusals,
                name,
                format!(
                    "No such inductive {name}: no inductive block this replay rebuilt through \
                     the kernel declares it (its stored `all` is [{all}]; Lean's replay builds \
                     the block's inductDecl from `all`)"
                ),
            );
        } else if env.get_constructor(name).is_some() {
            refuse(
                &mut refusals,
                name,
                format!(
                    "No such constructor {name}: no inductive block this replay rebuilt through \
                     the kernel generates it (Lean's replay: checkPostponedConstructors)"
                ),
            );
        }
    }

    // A wanted recursor no local block generates: "No such recursor". A
    // VALUE-BEARING name with a mirrored rule table (`casesOn` / `recOn` from
    // Clean's own inductive elaboration) is not a recursor in Lean — it is a
    // definition checked by its value — and under Lean's theory the kernel
    // never reduces through its mirror (`tc/reduction`'s ι step declines), so
    // it is replayed as the definition it is, not refused here.
    for name in wanted {
        if local.contains(name)
            && env.get_recursor(name).is_some()
            && env.get_const(name).is_none_or(|c| c.value.is_none())
            && !generated.contains(name)
            && !refusals.contains_key(name)
        {
            refuse(
                &mut refusals,
                name,
                format!(
                    "No such recursor {name}: no inductive block of this replay generates it \
                     (Lean's replay: checkPostponedRecursors)"
                ),
            );
        }
    }
    refusals
}

#[cfg(test)]
#[path = "replay_families_tests.rs"]
mod tests;
