// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `verify_batch_full` re-check lanes against the declaration-header
//! forgeries of the `replay_forged` fixture family (see its README for
//! `leanchecker`'s verdicts), beside `replay_forged_lanes.rs`.
//!
//! Lean's `environment::add_theorem` (`src/kernel/environment.cpp`,
//! v4.30.0-rc2, lines 192-209) refuses a theorem whose type is not a
//! proposition (`theorem_type_is_not_prop`). Until 2026-09-25 every lane
//! admitted `forged_thm_nat : Nat := Nat.zero` stored as a `thmInfo`: the value
//! has the stored type, and the lanes' sort check only asked that `Nat` be a
//! type. `leanchecker ReplayForgedThmType`: `(kernel) type of theorem
//! 'forged_thm_nat' is not a proposition`.
//!
//! Lean's `check_constant_val` also requires the type's own type to reduce to
//! a sort (`ensure_sort`). The lanes' sort check (`infer_sort`) answered for a
//! term whose type is a FUNCTION type too, so until 2026-09-26 every lane
//! admitted `forged_lam_ax : fun (h : True) => h`. `leanchecker
//! ReplayForgedLamType`: `(kernel) type expected`.
//!
//! The environment is built as the production callers build it: Lean's replay
//! environment (`Environment::for_lean_replay`) plus the module's `.olean`
//! closure.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::{Environment, ProofValueElision};
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::verify_batch_full::{
    typecheck_constants_full, typecheck_constants_full_streaming,
};
use clean_olean::verify_parallel::typecheck_constants_full_parallel;
use clean_olean::{
    default_search_paths, load_module_with_deps_shared_with_policy, OleanImportPolicy,
};

const FAMILY: &str = "replay_forged";

type Outcome = (usize, usize, BTreeMap<String, String>);

/// The three lanes' verdicts over `targets` of `module`, loaded as the lanes'
/// callers load it.
fn lanes(module: &str, targets: &[&str]) -> Vec<(&'static str, Outcome)> {
    let targets: BTreeSet<String> = targets.iter().map(|s| (*s).to_owned()).collect();
    let mut env = Environment::for_lean_replay();
    let mut search = vec![compiled_fixture_dir(FAMILY)];
    search.extend(default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    load_module_with_deps_shared_with_policy(
        &mut env,
        module,
        &search,
        &mut visited,
        OleanImportPolicy::default(),
    )
    .unwrap_or_else(|e| panic!("load {module}: {e}"));
    env.regenerate_missing_no_confusion();
    let eager = typecheck_constants_full(&env, &targets, DEFAULT_HEARTBEAT_LIMIT);
    let parallel = typecheck_constants_full_parallel(&env, &targets, 4, DEFAULT_HEARTBEAT_LIMIT);
    let (pass, fail, errors, _stats) = typecheck_constants_full_streaming(
        &mut env,
        &targets,
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

#[test]
fn test_verify_batch_full_lanes_theorem_type_not_prop_is_refused() {
    for (lane, outcome) in lanes("ReplayForgedThmType", &["forged_thm_nat"]) {
        assert_eq!((outcome.0, outcome.1), (0, 1), "{lane}: {:?}", outcome.2);
        let message = outcome
            .2
            .get("forged_thm_nat")
            .unwrap_or_else(|| panic!("{lane}: must be refused: {:?}", outcome.2));
        assert!(message.contains("not a proposition"), "{lane}: {message}");
    }
}

/// The checked control: a universe-polymorphic theorem whose type IS a
/// proposition at every universe (`∀ (α : Sort u) (a : α), a = a`).
#[test]
fn test_verify_batch_full_lanes_polymorphic_proposition_theorem_verifies() {
    for (lane, outcome) in lanes("ReplayHonestUniv", &["honest_univ"]) {
        assert_eq!((outcome.0, outcome.1), (1, 0), "{lane}: {:?}", outcome.2);
    }
}

/// Lean's `ensure_sort`: an axiom whose "type" is a lambda (of type
/// `True → True`) is refused `type expected` by every lane.
#[test]
fn test_verify_batch_full_lanes_lambda_typed_axiom_is_refused() {
    for (lane, outcome) in lanes("ReplayForgedLamType", &["forged_lam_ax"]) {
        assert_eq!((outcome.0, outcome.1), (0, 1), "{lane}: {:?}", outcome.2);
        let message = outcome
            .2
            .get("forged_lam_ax")
            .unwrap_or_else(|| panic!("{lane}: must be refused: {:?}", outcome.2));
        assert!(message.contains("type expected"), "{lane}: {message}");
    }
}
