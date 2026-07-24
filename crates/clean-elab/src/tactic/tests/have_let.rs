// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `let_` forward reasoning tactic.
//!
//! Covers: local definition introduction with and without provided values,
//! type checking, context transparency, and error paths.

use super::*;

// =========================================================================
// let_ with provided value
// =========================================================================

#[test]
fn test_let_with_value_adds_definition() {
    // Setup: Goal is B, and we have a : A
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: B
    let mut state = ProofState::new(env, b_ty.clone());

    // let x : A := a
    let result = let_(&mut state, "x", a_ty.clone(), Some(a.clone()));
    assert!(result.is_ok(), "let with value should succeed");

    // Should still have 1 goal (the original B)
    assert_eq!(state.goals().len(), 1);

    // New goal should have x in context with value
    let new_goal = state.current_goal().unwrap();
    assert_eq!(new_goal.local_ctx.len(), 1);
    assert_eq!(new_goal.local_ctx[0].name, "x");

    // The local decl should have a value (transparent definition)
    assert!(
        new_goal.local_ctx[0].value.is_some(),
        "let binding should retain value for transparency"
    );

    // Goal should still be B
    assert!(
        matches!(new_goal.target.kind(), ExprKind::Const(name, _) if name.to_string() == "B"),
        "goal target should remain B"
    );
}

#[test]
fn test_let_value_type_mismatch_fails() {
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: A
    let mut state = ProofState::new(env, a_ty.clone());

    // let x : B := a (wrong - a has type A, not B)
    let result = let_(&mut state, "x", b_ty, Some(a));
    assert!(result.is_err(), "let with wrong type should fail");

    // State should be unchanged
    assert_eq!(state.goals().len(), 1);
    assert!(
        state.current_goal().unwrap().local_ctx.is_empty(),
        "context should be unchanged on failure"
    );
}

// =========================================================================
// let_ without value (creates subgoals)
// =========================================================================

#[test]
fn test_let_without_value_creates_two_goals() {
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);

    // Goal: B
    let mut state = ProofState::new(env, b_ty.clone());

    // let x : A (without value)
    let result = let_(&mut state, "x", a_ty.clone(), None);
    assert!(result.is_ok(), "let without value should succeed");

    // Should have 2 goals
    assert_eq!(state.goals().len(), 2);

    // First goal should be: produce value of type A
    let first_goal = &state.goals()[0];
    assert!(
        matches!(first_goal.target.kind(), ExprKind::Const(name, _) if name.to_string() == "A"),
        "first goal should be A"
    );

    // Second goal should be: prove B with x : A available
    let second_goal = &state.goals()[1];
    assert!(
        matches!(second_goal.target.kind(), ExprKind::Const(name, _) if name.to_string() == "B"),
        "second goal should be B"
    );
    assert_eq!(second_goal.local_ctx.len(), 1);
    assert_eq!(second_goal.local_ctx[0].name, "x");

    // The continuation's local decl should have value (the meta expr)
    assert!(
        second_goal.local_ctx[0].value.is_some(),
        "let binding continuation should have meta value for transparency"
    );
}

// =========================================================================
// let_ error paths
// =========================================================================

#[test]
fn test_let_no_goals_fails() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Create and immediately complete a state
    let mut state = ProofState::new(env, a_ty.clone());
    exact(&mut state, a.clone()).unwrap();

    // Now try let on completed proof
    let result = let_(&mut state, "x", a_ty, Some(a));
    assert!(
        matches!(result, Err(TacticError::NoGoals)),
        "let on complete proof should fail with NoGoals"
    );
}

#[test]
fn test_let_no_goals_without_value_fails() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    let mut state = ProofState::new(env, a_ty.clone());
    exact(&mut state, a).unwrap();

    let result = let_(&mut state, "x", a_ty, None);
    assert!(
        matches!(result, Err(TacticError::NoGoals)),
        "let without value on complete proof should fail with NoGoals"
    );
}

// =========================================================================
// let_ vs have_ distinction: value transparency
// =========================================================================

#[test]
fn test_let_retains_value_have_does_not_for_opaque() {
    // Verify that let_ adds LocalDecl with value, while have_ with proof
    // also stores value (both use let-binding proof terms), but the semantic
    // distinction is that let_ is for definitions while have_ is for proofs.
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Test let_
    let mut let_state = ProofState::new(env.clone(), b_ty.clone());
    let_(&mut let_state, "x", a_ty.clone(), Some(a.clone())).unwrap();
    let let_decl = &let_state.current_goal().unwrap().local_ctx[0];
    assert!(let_decl.value.is_some(), "let_ should retain value");

    // Test have_ without proof (creates 2 goals, second has h in context)
    let mut have_state = ProofState::new(env, b_ty);
    have_(&mut have_state, "h", a_ty, None).unwrap();
    let have_decl = &have_state.goals()[1].local_ctx[0];
    assert!(
        have_decl.value.is_none(),
        "have_ without proof should have no value (opaque hypothesis)"
    );
}

// =========================================================================
// let_ complete proof flow
// =========================================================================

#[test]
fn test_let_complete_proof_with_value() {
    // Prove B using let x : A := a, then apply f
    let env = setup_env();

    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);

    // Goal: B
    let mut state = ProofState::new(env, b_ty);

    // let x : A := a
    let_(&mut state, "x", a_ty, Some(a)).unwrap();

    // Now goal is still B with x : A := a in context
    // Apply f : A -> B to get goal A
    apply(&mut state, f).unwrap();

    // Now we need to prove A - use x from context
    let x_fvar = state.current_goal().unwrap().local_ctx[0].fvar;
    exact(&mut state, Expr::fvar(x_fvar)).unwrap();

    assert!(state.is_complete(), "proof should be complete");
}

#[test]
fn test_let_complete_proof_without_value() {
    // Prove B using let x : A, provide a for x, then apply f
    let env = setup_env();

    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);

    // Goal: B
    let mut state = ProofState::new(env, b_ty);

    // let x : A (no value)
    let_(&mut state, "x", a_ty, None).unwrap();

    // Goal 1: produce A (the value)
    exact(&mut state, a).unwrap();

    // Goal 2: prove B with x : A in context
    // Apply f : A -> B
    apply(&mut state, f).unwrap();

    // Now need A - use x from context
    let x_fvar = state.current_goal().unwrap().local_ctx[0].fvar;
    exact(&mut state, Expr::fvar(x_fvar)).unwrap();

    assert!(state.is_complete(), "proof should be complete");
}

// =========================================================================
// let_ with pre-existing context
// =========================================================================

#[test]
fn test_let_preserves_existing_context() {
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Create state with existing hypothesis
    let existing_decl = LocalDecl {
        fvar: FVarId::new(0),
        name: "h".to_string(),
        ty: a_ty.clone(),
        value: None,
    };

    let mut state = ProofState::with_context(env, b_ty, vec![existing_decl]);

    // let x : A := a
    let_(&mut state, "x", a_ty, Some(a)).unwrap();

    // Should have both h and x in context
    let goal = state.current_goal().unwrap();
    assert_eq!(goal.local_ctx.len(), 2);
    assert_eq!(goal.local_ctx[0].name, "h");
    assert_eq!(goal.local_ctx[1].name, "x");
}
