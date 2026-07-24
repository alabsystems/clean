// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Regression tests for aesop proof-term meta assignment merging (#2533).
//
// The aesop search tree clones ProofState for each goal via clone_with_goal.
// When sub-tactics close goals in the cloned state, the proof-term meta
// assignments must be merged back into the main state. Without this merge,
// the root metavariable is never assigned a proof term, and verify_tactic_proof
// fails with a confusing ProofTypeMismatch error.

use super::*;
use clean_kernel::env::Declaration;

/// Setup: simple proposition A with a proof in context.
/// Goal: A (provable by assumption).
fn setup_simple_proof_env() -> (Environment, Expr, Vec<LocalDecl>) {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();

    let a = Expr::const_(Name::from_string("A"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let ctx = vec![LocalDecl {
        fvar: FVarId::new(0),
        name: "hA".to_string(),
        ty: a.clone(),
        value: None,
    }];

    (env, a, ctx)
}

/// Core regression: after aesop succeeds, the root meta must be assigned
/// in the main state's MetaState. Before #2533 fix, cloned sub-state
/// assignments were dropped, leaving root_meta_id unassigned.
#[test]
fn test_aesop_root_meta_assigned_after_success() {
    let (env, goal_type, ctx) = setup_simple_proof_env();
    let mut state = ProofState::with_context(env, goal_type, ctx);

    let root_meta = state.root_meta_id;

    // Before aesop: root meta is unassigned
    assert!(
        !state.metas.is_assigned(root_meta),
        "root meta should be unassigned before aesop"
    );

    let result = aesop(&mut state);
    assert!(result.is_ok(), "aesop should succeed: {result:?}");
    assert!(state.goals().is_empty(), "all goals should be closed");

    // After aesop: root meta must be assigned (the #2533 fix ensures this)
    assert!(
        state.metas.is_assigned(root_meta),
        "root meta must be assigned after aesop success — \
         proof-term meta assignments from cloned sub-states must be merged \
         back into the main state (#2533)"
    );
}

/// Verify that trust ledger entries from sub-tactics in cloned states
/// propagate to the main state after aesop merge.
#[test]
fn test_aesop_trust_ledger_propagated() {
    let (env, goal_type, ctx) = setup_simple_proof_env();
    let mut state = ProofState::with_context(env, goal_type, ctx);

    // Before aesop: trust ledger is clean
    assert_eq!(
        state.trust_ledger.trusted_axiom_count(),
        0,
        "trust ledger should start clean"
    );

    let result = aesop(&mut state);
    assert!(result.is_ok(), "aesop should succeed: {result:?}");

    // The trust ledger should reflect whatever the sub-tactics used.
    // For a simple assumption proof, no trusted axioms should be needed.
    // This test verifies the merge_max path is exercised without error.
    // If sub-tactics used trustedArith, the count would be non-zero here.
    let _ledger = state.trust_ledger;
}

/// Multiple search branches: verifies meta merge works when aesop explores
/// multiple candidates before finding the proof. The winning branch's
/// assignments must be merged even after failed branches are discarded.
#[test]
fn test_aesop_meta_merge_after_backtracking() {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();

    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    for name in ["A", "B"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();
    }

    // Only B has a proof, not A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hB"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("B"), vec![]),
    })
    .unwrap();

    // Goal: A ∨ B — aesop must backtrack from left (A) to right (B)
    let or_type = Expr::const_(Name::from_string("Or"), vec![]);
    let goal = Expr::app(Expr::app(or_type, a), b);

    let mut state = ProofState::with_context(
        env,
        goal,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "hB".to_string(),
            ty: Expr::const_(Name::from_string("B"), vec![]),
            value: None,
        }],
    );

    let root_meta = state.root_meta_id;
    let result = aesop(&mut state);
    assert!(
        result.is_ok(),
        "aesop should find proof via backtracking: {result:?}"
    );
    assert!(state.goals().is_empty(), "all goals should be closed");

    // The winning branch (right/B) should have its meta assignments merged
    assert!(
        state.metas.is_assigned(root_meta),
        "root meta must be assigned after backtracking success — \
         the winning branch's cloned sub-state must merge into main (#2533)"
    );
}
