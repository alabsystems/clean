// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Error-path assertions for propositional proof reconstruction.

use super::*;

#[test]
#[timeout(30000)]
fn test_and_intro_with_unprovable_conjuncts_returns_error() {
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let and_pq = mk_and(&p, &q);

    // No hypotheses -> And.intro tries to prove P and Q, both fail
    let goal_class = bridge.classify_prop(&and_pq);
    let result = bridge.build_propositional_proof(&goal_class, &and_pq);
    assert!(
        result.is_err(),
        "And.intro with unprovable conjuncts should fail"
    );
}

#[test]
#[timeout(30000)]
fn test_unsupported_atom_returns_error() {
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let p = prop("P");

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_propositional_proof(&goal_class, &p);
    assert!(
        matches!(result, Err(BridgeError::UnsupportedExpr { .. })),
        "Atom with no hypothesis should fail with UnsupportedExpr, got {:?}",
        result
    );
}

#[test]
#[timeout(30000)]
fn test_depth_limit_guard_returns_exact_error() {
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let result = bridge.build_prop_proof_inner(&LogicalForm::True, &prop("P"), 51);
    assert!(
        matches!(result, Err(BridgeError::ProofTraceFailed(ref msg)) if msg == "propositional proof reconstruction depth exceeded"),
        "depth guard should return the dedicated overflow error, got {:?}",
        result
    );
}
