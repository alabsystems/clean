// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the `and_intros` tactic.
//!
//! `and_intros` flattens a (possibly nested) conjunction goal into one subgoal
//! per conjunct by building a single kernel-checked nested `And.intro` proof
//! term. These tests confirm:
//! - the kernel accepts the `And.intro` tree (each goal closed only through
//!   `close_goal`'s type check),
//! - nested conjunctions are flattened left-to-right,
//! - the resulting subgoals are independently closable to a complete proof,
//! - misuse (no goals) errors rather than panics.

use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};

use super::and_intros;
use super::core::{ProofState, TacticError};
use super::proof_term::exact;

/// Build an environment with `And` plus three propositions `A`, `B`, `C` and
/// matching proof witnesses `ha : A`, `hb : B`, `hc : C`.
fn setup_env_with_three_props() -> Environment {
    let mut env = Environment::new();
    env.init_and().expect("init_and should succeed");

    let prop = Expr::prop();
    for name in ["A", "B", "C"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("add proposition axiom");
    }
    for (witness, prop_name) in [("ha", "A"), ("hb", "B"), ("hc", "C")] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(witness),
            level_params: vec![],
            type_: Expr::const_(Name::from_string(prop_name), vec![]),
        })
        .expect("add proof witness axiom");
    }
    env
}

fn prop_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `And X Y` as a kernel application.
fn and(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(Expr::app(prop_const("And"), lhs), rhs)
}

#[test]
fn test_and_intros_binary_conjunction_splits_into_two_goals() {
    let env = setup_env_with_three_props();
    let target = and(prop_const("A"), prop_const("B"));
    let mut state = ProofState::new(env, target);

    and_intros(&mut state).expect("and_intros should split A ∧ B");

    // Two subgoals, left-to-right: A then B.
    assert_eq!(state.goals().len(), 2, "expected one goal per conjunct");
    assert_eq!(state.goals()[0].target, prop_const("A"));
    assert_eq!(state.goals()[1].target, prop_const("B"));
}

#[test]
fn test_and_intros_nested_conjunction_flattens_left_to_right() {
    let env = setup_env_with_three_props();
    // A ∧ (B ∧ C)
    let target = and(prop_const("A"), and(prop_const("B"), prop_const("C")));
    let mut state = ProofState::new(env, target);

    and_intros(&mut state).expect("and_intros should flatten A ∧ (B ∧ C)");

    // Three leaf subgoals in source order: A, B, C.
    assert_eq!(state.goals().len(), 3, "nested conjunction should flatten");
    assert_eq!(state.goals()[0].target, prop_const("A"));
    assert_eq!(state.goals()[1].target, prop_const("B"));
    assert_eq!(state.goals()[2].target, prop_const("C"));
}

#[test]
fn test_and_intros_left_nested_conjunction_flattens() {
    let env = setup_env_with_three_props();
    // (A ∧ B) ∧ C
    let target = and(and(prop_const("A"), prop_const("B")), prop_const("C"));
    let mut state = ProofState::new(env, target);

    and_intros(&mut state).expect("and_intros should flatten (A ∧ B) ∧ C");

    assert_eq!(state.goals().len(), 3, "left-nested conjunction flattens");
    assert_eq!(state.goals()[0].target, prop_const("A"));
    assert_eq!(state.goals()[1].target, prop_const("B"));
    assert_eq!(state.goals()[2].target, prop_const("C"));
}

#[test]
fn test_and_intros_full_proof_is_kernel_complete() {
    let env = setup_env_with_three_props();
    // A ∧ B ∧ C  (right-associated, as Lean parses conjunction)
    let target = and(prop_const("A"), and(prop_const("B"), prop_const("C")));
    let mut state = ProofState::new(env, target);

    and_intros(&mut state).expect("and_intros should flatten A ∧ B ∧ C");
    assert_eq!(state.goals().len(), 3);

    // Discharge each leaf with its witness. `exact` kernel-checks each closure,
    // and the surrounding And.intro tree was already kernel-checked by
    // `and_intros`' `close_goal`.
    exact(&mut state, prop_const("ha")).expect("close A with ha");
    exact(&mut state, prop_const("hb")).expect("close B with hb");
    exact(&mut state, prop_const("hc")).expect("close C with hc");

    assert!(state.is_complete(), "all conjunct subgoals discharged");
    // A fully-instantiated, kernel-connected proof term exists.
    assert!(
        state.instantiated_proof().is_some(),
        "complete and_intros proof should yield a proof term"
    );
}

#[test]
fn test_and_intros_non_conjunction_goal_is_noop() {
    let env = setup_env_with_three_props();
    // A single (non-And) proposition: `and_intros` makes no progress but
    // succeeds, matching Mathlib's `repeat'` (zero iterations allowed).
    let mut state = ProofState::new(env, prop_const("A"));

    and_intros(&mut state).expect("and_intros on non-conjunction should be a no-op");

    assert_eq!(state.goals().len(), 1, "goal count unchanged");
    assert_eq!(state.goals()[0].target, prop_const("A"));
}

#[test]
fn test_and_intros_no_goals_errors_not_panics() {
    let env = setup_env_with_three_props();
    let mut state = ProofState::new(env, prop_const("A"));

    // Close the only goal, leaving no goals.
    exact(&mut state, prop_const("ha")).expect("close A with ha");
    assert!(state.is_complete());

    // Misuse: running and_intros with no goals must error, never panic.
    let result = and_intros(&mut state);
    assert!(
        matches!(result, Err(TacticError::NoGoals)),
        "and_intros with no goals should return NoGoals, got {result:?}"
    );
}
