// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The large-elimination gate's nonzero rule across the `.olean` lanes
//! (fixture family `replay_forged`, pair `ReplayHonestSortU` /
//! `ReplayForgedSortULargeElim`; `leanchecker` verdicts in its README).
//!
//! Lean's kernel exempts a family from the restriction analysis only when its
//! result level is PROVABLY nonzero (`is_not_zero`), so
//! `FSU.{u} : Sort u | t | f` gets a `Prop`-only `FSU.rec`. `clean-ck0` read
//! `!is_zero` until 2026-10-17 (`crates/clean-ck0/tests/sort_u_elim_gate.rs`);
//! `clean-kernel` reads `Level::is_nonzero`, and this file pins that every
//! `.olean` lane keeps doing so: the loader refuses a stored large `FSU.rec`,
//! the three `verify_batch_full` lanes refuse the block and
//! `forged_su_false : False`, and the honest twin imports and verifies in full.
//!
//! It sits beside the `olean-replay-order` battery (`replay_forged_lanes.rs`),
//! not in it: that battery's mutation arms pin its file, and this guard has no
//! arm of its own.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::{Environment, ProofValueElision};
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::verify_batch_full::{
    typecheck_constants_full, typecheck_constants_full_streaming,
};
use clean_olean::verify_parallel::typecheck_constants_full_parallel;
use clean_olean::{
    default_search_paths, load_module_with_deps_shared_with_policy, parse_module_file,
    OleanImportPolicy,
};

const FAMILY: &str = "replay_forged";

type Outcome = (usize, usize, BTreeMap<String, String>);

/// Lean's replay environment plus `module`'s closure through the trusted
/// `.olean` path, and the loader's per-constant refusals.
fn load(module: &str) -> (Environment, BTreeMap<String, String>) {
    let mut env = Environment::for_lean_replay();
    let mut search = vec![compiled_fixture_dir(FAMILY)];
    search.extend(default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    let refusals = load_module_with_deps_shared_with_policy(
        &mut env,
        module,
        &search,
        &mut visited,
        OleanImportPolicy::default(),
    )
    .unwrap_or_else(|e| panic!("load {module}: {e}"))
    .into_iter()
    .flat_map(|summary| summary.skipped_constants)
    .filter(|s| s.reason.contains("imported family record"))
    .map(|s| (s.name, s.reason))
    .collect();
    env.regenerate_missing_no_confusion();
    (env, refusals)
}

/// The eager, parallel and streaming lanes' verdicts over `targets`.
fn lanes(env: Environment, targets: &BTreeSet<String>) -> Vec<(&'static str, Outcome)> {
    let eager = typecheck_constants_full(&env, targets, DEFAULT_HEARTBEAT_LIMIT);
    let parallel = typecheck_constants_full_parallel(&env, targets, 4, DEFAULT_HEARTBEAT_LIMIT);
    let mut env = env;
    let (pass, fail, errors, _stats) = typecheck_constants_full_streaming(
        &mut env,
        targets,
        DEFAULT_HEARTBEAT_LIMIT,
        ProofValueElision::OpaqueAndTheorem,
        Some(1),
    );
    vec![
        ("eager", eager),
        ("parallel", parallel),
        ("streaming", (pass, fail, errors)),
    ]
}

fn expect_refused(lane: &str, outcome: &Outcome, name: &str, needle: &str) {
    let message = outcome
        .2
        .get(name)
        .unwrap_or_else(|| panic!("{lane}: `{name}` must be refused; errors {:?}", outcome.2));
    assert!(
        message.contains(needle),
        "{lane}: `{name}` refused, but without `{needle}`: {message}"
    );
}

#[test]
fn test_sort_u_family_imports_and_replays_at_leans_nonzero_rule() {
    let (env, at_load) = load("ReplayForgedSortULargeElim");
    assert!(
        at_load.get("FSU.rec").is_some_and(|why| {
            why.contains("imported family record FSU.rec refused")
                && why.contains("elimination universe differs")
        }),
        "the loader must refuse the stored large `FSU.rec` by name: {at_load:?}"
    );
    let targets: BTreeSet<String> = ["FSU", "FSU.t", "FSU.f", "FSU.rec", "forged_su_false"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    for (lane, outcome) in lanes(env, &targets) {
        assert_eq!(
            (outcome.0, outcome.1),
            (0, targets.len()),
            "{lane}: {:?}",
            outcome.2
        );
        expect_refused(lane, &outcome, "FSU.rec", "missing requested target");
        for member in ["FSU", "FSU.t", "FSU.f"] {
            expect_refused(lane, &outcome, member, "replay order:");
        }
    }

    let (env, at_load) = load("ReplayHonestSortU");
    assert!(at_load.is_empty(), "{at_load:?}");
    let path = compiled_fixture_dir(FAMILY).join("ReplayHonestSortU.olean");
    let honest: BTreeSet<String> = parse_module_file(&path)
        .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
        .const_names
        .into_iter()
        .collect();
    for (lane, outcome) in lanes(env, &honest) {
        assert_eq!(
            (outcome.0, outcome.1),
            (honest.len(), 0),
            "{lane}: {:?}",
            outcome.2
        );
    }
}
