// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The cross-module half of Lean's replay order, for every multi-module
//! `stamp-verified` run: PARAGON, and the sequential `--single-pass` stream,
//! which verifies one module per call and so loses the masked-failure taint
//! between modules (measured 2026-09-24: `--single-pass` over ReplayCrossA and
//! ReplayCrossB stamped `cross_uses_forged : False` on top of the refused
//! `cross_forged`).
//!
//! `parallel_verify_replay.rs` orders each module's own constants. PARAGON
//! checks every target module against ONE base that holds all of them, so a
//! constant of module B that uses a constant of target module A is checked
//! against A's declared type whether or not A's constant was admitted: B could
//! be stamped `KernelVerified` on top of A's `forged : False`. Lean's replay
//! admits a constant only after everything it uses (`Replay.lean`,
//! `replayConstant`), and the sequential `stamp-verified` lane gets the same
//! effect from its masked-failure taint. This pass runs after every module's
//! verdict is in: it collects each target module's non-admitted constants
//! (refused, rejected, value-less, unreconstructable, or in a module that did
//! not convert), rebuilds the references of every `KernelVerified` constant
//! from its written shard, and demotes, to a fixpoint, every one that uses a
//! non-admitted constant of the run. Imports outside the run stay the trusted
//! starting environment, as in Lean's `replayFromImports`.

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::PathBuf;

use clean_olean::replay_order::expr_refs;
use rayon::prelude::*;

use crate::closure_source::constant_type_and_value;
use crate::shard::ShardMmapReader;
use crate::verify::incremental::IncrementalVerifyReport;

/// One module of the run: its `.olean` and the shard PARAGON wrote for it.
pub(in crate::cli) struct RunModule {
    pub(in crate::cli) olean: PathBuf,
    pub(in crate::cli) shard: PathBuf,
}

/// Demote every `KernelVerified` constant of `report` that transitively uses a
/// constant of another module of the run that was not admitted. Returns how
/// many were demoted; each is moved to `failures` with the constant it depends
/// on named.
pub(in crate::cli) fn demote_across_modules(
    report: &mut IncrementalVerifyReport,
    modules: &[RunModule],
    pool: &rayon::ThreadPool,
) -> usize {
    if modules.len() < 2 {
        return 0;
    }
    demote_users_of_not_admitted(report, modules, pool)
}

/// [`demote_across_modules`] without its multi-module precondition: demote,
/// to a fixpoint, every `KernelVerified` constant of the run's modules that
/// uses one of their constants that was not admitted, the module's own
/// included. The sequential lane needs it after a stored inductive-family
/// member was refused post hoc (`stamp_family_audit.rs`): that member's users
/// were checked while it still stood.
pub(in crate::cli) fn demote_users_of_not_admitted(
    report: &mut IncrementalVerifyReport,
    modules: &[RunModule],
    pool: &rayon::ThreadPool,
) -> usize {
    if modules.is_empty() {
        return 0;
    }
    // Every name the run's modules declare, interned. A module whose shard is
    // missing did not convert: none of its constants was admitted.
    let mut ids: HashMap<String, u32> = HashMap::new();
    let mut names: Vec<String> = Vec::new();
    let mut not_admitted: HashSet<u32> = HashSet::new();
    let mut readers: Vec<ShardMmapReader> = Vec::new();
    for module in modules {
        match ShardMmapReader::open_lazy(&module.shard) {
            Ok(reader) => {
                for c in &reader.constants {
                    if let Some(name) = reader.strings.get(c.name_idx as usize) {
                        intern(&mut ids, &mut names, name);
                    }
                }
                readers.push(reader);
            }
            Err(_) => {
                // The module's declared names as every reader reads them (its
                // authoritative part, R113); for an artifact the reader refuses,
                // its `.olean`'s names, so nothing it declares is admitted.
                let declared: Vec<String> = match clean_olean::read_artifact(
                    "",
                    &module.olean,
                    clean_olean::ArtifactDepth::Names,
                ) {
                    Ok(read) => read.names.iter().map(ToString::to_string).collect(),
                    Err(_) => std::fs::read(&module.olean)
                        .ok()
                        .and_then(|bytes| {
                            clean_olean::parse_imports_and_const_names_only(&bytes).ok()
                        })
                        .map(|(_, declared)| declared)
                        .unwrap_or_default(),
                };
                for name in declared {
                    not_admitted.insert(intern(&mut ids, &mut names, &name));
                }
            }
        }
    }
    let kv: HashSet<&str> = report
        .kernel_verified_names
        .iter()
        .map(String::as_str)
        .collect();
    // Everything the lanes record as not verified: refusals and kernel
    // rejections (`failures`), masked value failures (`axiom_fallback_names`),
    // and the sequential lane's two statement-only stand-in kinds.
    for (name, _) in report
        .failures
        .iter()
        .chain(&report.axiom_fallback_names)
        .chain(&report.family_standins)
        .chain(&report.standin_blocked_fallbacks)
    {
        if let Some(&id) = ids.get(name) {
            if !kv.contains(name.as_str()) {
                not_admitted.insert(id);
            }
        }
    }
    if not_admitted.is_empty() {
        return 0;
    }

    // The run-local references of every KernelVerified constant.
    let edges: Vec<(u32, Vec<u32>)> = pool.install(|| {
        readers
            .par_iter()
            .flat_map_iter(|reader| {
                let mut out = Vec::new();
                for (idx, c) in reader.constants.iter().enumerate() {
                    let Some(name) = reader.strings.get(c.name_idx as usize) else {
                        continue;
                    };
                    if !kv.contains(name.as_str()) {
                        continue;
                    }
                    let (Some(&id), Some((type_, value))) =
                        (ids.get(name), constant_type_and_value(reader, idx))
                    else {
                        continue;
                    };
                    let refs = expr_refs(&type_, value.as_ref())
                        .into_iter()
                        .filter_map(|r| ids.get(&r.to_string()).copied())
                        .filter(|&r| r != id)
                        .collect();
                    out.push((id, refs));
                }
                out
            })
            .collect()
    });
    let mut users: HashMap<u32, Vec<u32>> = HashMap::new();
    for (id, refs) in &edges {
        for r in refs {
            users.entry(*r).or_default().push(*id);
        }
    }

    let mut demoted: HashMap<u32, u32> = HashMap::new();
    let mut queue: VecDeque<u32> = not_admitted.iter().copied().collect();
    while let Some(bad) = queue.pop_front() {
        for &user in users.get(&bad).map_or(&[][..], Vec::as_slice) {
            if kv.contains(names[user as usize].as_str())
                && !not_admitted.contains(&user)
                && !demoted.contains_key(&user)
            {
                demoted.insert(user, bad);
                queue.push_back(user);
            }
        }
    }
    let count = demoted.len();
    if count == 0 {
        return 0;
    }
    let demoted_names: HashMap<&str, &str> = demoted
        .iter()
        .map(|(&user, &bad)| (names[user as usize].as_str(), names[bad as usize].as_str()))
        .collect();
    for (&user, &bad) in &demoted_names {
        report.failures.push((
            user.to_string(),
            format!(
                "replay order: `{user}` depends on `{bad}`, which was not admitted (a \
                 declaration of another module of this run; Lean's replay admits a \
                 constant only after everything it uses)"
            ),
        ));
    }
    report
        .kernel_verified_names
        .retain(|n| !demoted_names.contains_key(n.as_str()));
    report.kernel_verified = report.kernel_verified.saturating_sub(count);
    report.failed += count;
    count
}

fn intern(ids: &mut HashMap<String, u32>, names: &mut Vec<String>, name: &str) -> u32 {
    if let Some(&id) = ids.get(name) {
        return id;
    }
    let id = u32::try_from(names.len()).unwrap_or(u32::MAX);
    ids.insert(name.to_owned(), id);
    names.push(name.to_owned());
    id
}
