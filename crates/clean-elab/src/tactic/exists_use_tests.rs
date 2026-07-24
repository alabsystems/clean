// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for exists_use tactics (use_tactic, refine_constructor, use_with_constructor).

use super::*;

fn prop_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn and_target(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(Expr::app(prop_const("And"), lhs), rhs)
}

fn or_target(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(Expr::app(prop_const("Or"), lhs), rhs)
}

fn exists_prop_identity_target() -> Expr {
    let pred = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            Expr::prop(),
        ),
        pred,
    )
}

#[test]
fn test_use_tactic_provides_witness() {
    let env = tests::setup_env_with_prop_ext();
    let target = exists_prop_identity_target();
    let witness = prop_const("False");
    let mut state = ProofState::new(env, target);

    let result = exists_use::use_tactic(&mut state, vec![witness]);

    // use_tactic returns Ok even if the remaining goal can't be closed by rfl
    assert!(result.is_ok(), "use_tactic failed unexpectedly: {result:?}");
    // After providing False as witness for Exists {Prop} (fun x => x),
    // the remaining goal is (fun x => x) False which beta-reduces to False
    assert_eq!(state.goals.len(), 1);
}

#[test]
fn test_use_tactic_empty_witnesses_fails() {
    let env = tests::setup_env_with_prop_ext();
    let target = exists_prop_identity_target();
    let mut state = ProofState::new(env, target);

    let result = exists_use::use_tactic(&mut state, vec![]);

    assert!(matches!(result, Err(TacticError::MissingArgument { .. })));
}

#[test]
fn test_use_tactic_non_exists_fails() {
    let env = tests::setup_env();
    let mut state = ProofState::new(env, Expr::prop());

    let result = exists_use::use_tactic(&mut state, vec![Expr::type_()]);

    // existsi fails because goal target is not Exists -- either GoalMismatch
    // or EnvironmentMissing (no Exists.intro in basic env)
    assert!(result.is_err(), "use_tactic should fail on non-exists goal");
}

#[test]
fn test_refine_constructor_and_split() {
    let env = tests::setup_env_with_and_or();
    let p = prop_const("P");
    let q = prop_const("Q");
    let mut state = ProofState::new(env, and_target(p.clone(), q.clone()));

    let result = exists_use::refine_constructor(&mut state);

    assert!(result.is_ok());
    assert_eq!(state.goals.len(), 2);
    assert_eq!(state.goals[0].target, p);
    assert_eq!(state.goals[1].target, q);
}

#[test]
fn test_refine_constructor_or_left() {
    let env = tests::setup_env_with_and_or();
    let p = prop_const("P");
    let q = prop_const("Q");
    let mut state = ProofState::new(env, or_target(p.clone(), q));

    let result = exists_use::refine_constructor(&mut state);

    assert!(result.is_ok());
    assert_eq!(state.goals.len(), 1);
    assert_eq!(state.goals[0].target, p);
}

#[test]
fn test_refine_constructor_exists_split() {
    let env = tests::setup_env_with_prop_ext();
    let target = exists_prop_identity_target();
    let mut state = ProofState::new(env, target);

    let result = exists_use::refine_constructor(&mut state);

    assert!(result.is_ok());
    assert_eq!(state.goals.len(), 2);
}

#[test]
fn test_refine_constructor_non_inductive_fails() {
    let env = tests::setup_env();
    let mut state = ProofState::new(env, prop_const("A"));

    let result = exists_use::refine_constructor(&mut state);

    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_left_applies_or_inl() {
    let env = tests::setup_env_with_and_or();
    let p = prop_const("P");
    let q = prop_const("Q");
    let mut state = ProofState::new(env, or_target(p.clone(), q));

    let result = left_(&mut state);

    assert!(result.is_ok());
    assert_eq!(state.goals.len(), 1);
    assert_eq!(state.goals[0].target, p);
}

#[test]
fn test_right_applies_or_inr() {
    let env = tests::setup_env_with_and_or();
    let p = prop_const("P");
    let q = prop_const("Q");
    let mut state = ProofState::new(env, or_target(p, q.clone()));

    let result = right_(&mut state);

    assert!(result.is_ok());
    assert_eq!(state.goals.len(), 1);
    assert_eq!(state.goals[0].target, q);
}

// =============================================================================
// Additional edge case tests
// =============================================================================

#[test]
fn test_refine_constructor_non_const_fails() {
    // Goal target is Sort 0 (Prop), not a const application
    let env = tests::setup_env();
    let mut state = ProofState::new(env, Expr::prop());

    let result = exists_use::refine_constructor(&mut state);

    assert!(
        matches!(result, Err(TacticError::GoalMismatch(_))),
        "expected GoalMismatch on Sort target, got: {result:?}"
    );
}

#[test]
fn test_use_tactic_no_goals_fails() {
    let env = tests::setup_env_with_prop_ext();
    let target = exists_prop_identity_target();
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = exists_use::use_tactic(&mut state, vec![prop_const("True")]);

    assert!(
        matches!(result, Err(TacticError::NoGoals)),
        "expected NoGoals, got: {result:?}"
    );
}

#[test]
fn test_use_with_constructor_empty_witnesses_fails() {
    let env = tests::setup_env_with_prop_ext();
    let target = exists_prop_identity_target();
    let mut state = ProofState::new(env, target);

    let result = exists_use::use_with_constructor(&mut state, vec![]);

    assert!(
        matches!(result, Err(TacticError::MissingArgument { .. })),
        "expected MissingArgument, got: {result:?}"
    );
}

#[test]
fn test_refine_constructor_exists_split_goal_types() {
    // Verify the specific subgoal types produced by refine_constructor on Exists
    let env = tests::setup_env_with_prop_ext();
    let target = exists_prop_identity_target();
    let mut state = ProofState::new(env, target);

    exists_use::refine_constructor(&mut state).expect("refine_constructor should succeed");

    assert_eq!(state.goals.len(), 2);
    // First subgoal: the witness type (Prop, since Exists {Prop} ...)
    assert_eq!(state.goals[0].target, Expr::prop());
    // Second subgoal: the predicate applied to witness (a meta)
    // It should be a FVar (meta) since pred = (fun x => x) and beta-reducing
    // (fun x => x) meta = meta
}
