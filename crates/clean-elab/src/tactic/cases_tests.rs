// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for structured `cases`, `eval_rcases`, and `induction` tactics.
//!
//! Part of #3082: validates pattern-directed case analysis and induction
//! hypothesis generation for Bool, Nat, and nested inductive types.

use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};

use super::cases::{eval_cases, eval_rcases, eval_rcases_depth, RCasesPattern};
use super::core::{ProofState, TacticError};
use super::induction::InductionCase;
use super::proof_term::{exact, intro};

// ---------------------------------------------------------------------------
// Environment setup helpers
// ---------------------------------------------------------------------------

fn setup_bool_env() -> Environment {
    let mut env = Environment::new();
    env.init_bool().unwrap();
    env
}

fn setup_nat_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env
}

// ---------------------------------------------------------------------------
// RCasesPattern unit tests
// ---------------------------------------------------------------------------

#[test]
fn test_rcases_pattern_name_eq() {
    let p1 = RCasesPattern::Name("x".into());
    let p2 = RCasesPattern::Name("x".into());
    assert_eq!(p1, p2);
}

#[test]
fn test_rcases_pattern_wildcard_eq() {
    assert_eq!(RCasesPattern::Wildcard, RCasesPattern::Wildcard);
}

#[test]
fn test_rcases_pattern_tuple_eq() {
    let t1 = RCasesPattern::Tuple(vec![
        RCasesPattern::Name("a".into()),
        RCasesPattern::Wildcard,
    ]);
    let t2 = RCasesPattern::Tuple(vec![
        RCasesPattern::Name("a".into()),
        RCasesPattern::Wildcard,
    ]);
    assert_eq!(t1, t2);
}

#[test]
fn test_rcases_pattern_name_ne() {
    let p1 = RCasesPattern::Name("x".into());
    let p2 = RCasesPattern::Name("y".into());
    assert_ne!(p1, p2);
}

#[test]
fn test_rcases_pattern_clone() {
    let p = RCasesPattern::Tuple(vec![RCasesPattern::Name("n".into())]);
    let p2 = p.clone();
    assert_eq!(p, p2);
}

// ---------------------------------------------------------------------------
// eval_cases tests
// ---------------------------------------------------------------------------

#[test]
fn test_eval_cases_bool_creates_two_goals() {
    let env = setup_bool_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "b").unwrap();
    eval_cases(&mut state, "b").unwrap();

    assert_eq!(
        state.goals().len(),
        2,
        "Bool case split should produce 2 goals"
    );
}

#[test]
fn test_eval_cases_completes_proof() {
    let env = setup_bool_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "b").unwrap();
    eval_cases(&mut state, "b").unwrap();

    // Close false case
    exact(
        &mut state,
        Expr::const_(Name::from_string("Bool.false"), vec![]),
    )
    .unwrap();
    // Close true case
    exact(
        &mut state,
        Expr::const_(Name::from_string("Bool.true"), vec![]),
    )
    .unwrap();

    assert!(
        state.is_complete(),
        "proof should be complete after both cases"
    );
}

#[test]
fn test_eval_cases_unknown_hyp_errors() {
    let env = setup_bool_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let mut state = ProofState::new(env, bool_ty);

    let result = eval_cases(&mut state, "ghost");
    assert!(matches!(result, Err(TacticError::UnknownIdent(_))));
}

#[test]
fn test_eval_cases_no_goals_errors() {
    let env = setup_bool_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "b").unwrap();
    eval_cases(&mut state, "b").unwrap();

    // Close both goals
    exact(
        &mut state,
        Expr::const_(Name::from_string("Bool.false"), vec![]),
    )
    .unwrap();
    exact(
        &mut state,
        Expr::const_(Name::from_string("Bool.true"), vec![]),
    )
    .unwrap();

    // Now no goals remain
    let result = eval_cases(&mut state, "b");
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

// ---------------------------------------------------------------------------
// eval_rcases with pattern tests
// ---------------------------------------------------------------------------

#[test]
fn test_eval_rcases_wildcard_pattern_same_as_cases() {
    let env = setup_bool_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "b").unwrap();
    eval_rcases(
        &mut state,
        "b",
        &[RCasesPattern::Wildcard, RCasesPattern::Wildcard],
    )
    .unwrap();

    assert_eq!(
        state.goals().len(),
        2,
        "wildcard patterns should produce 2 goals"
    );
}

#[test]
fn test_eval_rcases_name_pattern_renames_field() {
    let env = setup_nat_env();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::arrow(nat_ty.clone(), nat_ty.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "n").unwrap();

    // Apply rcases with a name pattern for the succ constructor.
    // Bool-like ctors have 0 fields (zero) and 1 field (succ).
    eval_rcases(
        &mut state,
        "n",
        &[
            RCasesPattern::Wildcard,            // zero: no fields
            RCasesPattern::Name("pred".into()), // succ: rename field
        ],
    )
    .unwrap();

    assert_eq!(state.goals().len(), 2);

    // The succ goal (second) should have a hypothesis named "pred".
    let succ_goal = &state.goals()[1];
    let has_pred = succ_goal.local_ctx.iter().any(|d| d.name == "pred");
    assert!(
        has_pred,
        "succ case should have a hypothesis named 'pred', got: {:?}",
        succ_goal
            .local_ctx
            .iter()
            .map(|d| &d.name)
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_eval_rcases_empty_patterns_same_as_cases() {
    let env = setup_bool_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "b").unwrap();
    // Empty patterns should fall back to wildcard behavior.
    eval_rcases(&mut state, "b", &[]).unwrap();

    assert_eq!(state.goals().len(), 2);
}

#[test]
fn test_eval_rcases_fewer_patterns_than_ctors() {
    let env = setup_bool_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "b").unwrap();
    // Only supply one pattern for two constructors.
    eval_rcases(&mut state, "b", &[RCasesPattern::Wildcard]).unwrap();

    assert_eq!(state.goals().len(), 2, "should still produce 2 goals");
}

// ---------------------------------------------------------------------------
// eval_rcases_depth tests (depth-limited, no patterns)
// ---------------------------------------------------------------------------

#[test]
fn test_eval_rcases_depth_zero_noop() {
    let env = setup_bool_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "b").unwrap();
    let goals_before = state.goals().len();

    eval_rcases_depth(&mut state, "b", 0).unwrap();

    assert_eq!(
        state.goals().len(),
        goals_before,
        "depth 0 should be a no-op"
    );
}

#[test]
fn test_eval_rcases_depth_one_same_as_cases() {
    let env = setup_bool_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "b").unwrap();
    eval_rcases_depth(&mut state, "b", 1).unwrap();

    assert_eq!(state.goals().len(), 2);
}

// ---------------------------------------------------------------------------
// InductionCase visibility test
// ---------------------------------------------------------------------------

#[test]
fn test_induction_case_struct_accessible() {
    // Verify InductionCase fields are accessible from within the crate.
    let ic = InductionCase {
        case_meta: crate::unify::MetaId(0),
        new_ctx: vec![],
        new_target: Expr::prop(),
        field_fvars: vec![],
        ih_fvars: vec![],
        ctor_tag: "zero".into(),
    };
    assert_eq!(ic.ctor_tag, "zero");
    assert!(ic.field_fvars.is_empty());
    assert!(ic.ih_fvars.is_empty());
}

// ---------------------------------------------------------------------------
// Induction tactic tests (exercising InductionCase generation)
// ---------------------------------------------------------------------------

#[test]
fn test_induction_nat_creates_base_and_step() {
    let env = setup_nat_env();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::arrow(nat_ty.clone(), nat_ty.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "n").unwrap();
    super::induction::induction(&mut state, "n").unwrap();

    assert_eq!(
        state.goals().len(),
        2,
        "Nat induction should produce 2 goals"
    );

    // Zero case: no hypotheses (original n removed).
    let zero_goal = &state.goals()[0];
    assert!(
        zero_goal.local_ctx.is_empty(),
        "zero case should have no hypotheses"
    );
    assert_eq!(zero_goal.tag.as_deref(), Some("zero"));

    // Succ case: should have field + IH.
    let succ_goal = &state.goals()[1];
    assert_eq!(succ_goal.tag.as_deref(), Some("succ"));
    assert!(
        succ_goal.local_ctx.len() >= 2,
        "succ case should have at least field + IH"
    );
    let has_ih = succ_goal
        .local_ctx
        .iter()
        .any(|d| d.name.starts_with("ih_"));
    assert!(has_ih, "succ case should contain an IH hypothesis");
}

#[test]
fn test_induction_proof_completes_with_ih() {
    let env = setup_nat_env();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::arrow(nat_ty.clone(), nat_ty.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "n").unwrap();
    super::induction::induction(&mut state, "n").unwrap();

    // Zero case: exact Nat.zero
    exact(
        &mut state,
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    )
    .unwrap();

    // Succ case: use IH
    let succ_goal = state.current_goal().unwrap().clone();
    let ih = succ_goal
        .local_ctx
        .iter()
        .find(|d| d.name.starts_with("ih_"))
        .expect("succ case should have IH");
    exact(&mut state, Expr::fvar(ih.fvar)).unwrap();

    assert!(state.is_complete(), "proof should be complete");
}

#[test]
fn test_induction_bool_no_ih() {
    // Bool is not recursive, so induction produces no IH.
    let env = setup_bool_env();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "b").unwrap();
    super::induction::induction(&mut state, "b").unwrap();

    assert_eq!(state.goals().len(), 2);

    // Neither case should have IH.
    for goal in state.goals() {
        let has_ih = goal.local_ctx.iter().any(|d| d.name.starts_with("ih_"));
        assert!(
            !has_ih,
            "Bool induction should not produce IH, got {:?}",
            goal.tag
        );
    }
}
