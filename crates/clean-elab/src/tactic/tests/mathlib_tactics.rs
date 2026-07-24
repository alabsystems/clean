// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathlib-style tactic tests (simpa, continuity, measurability)
//! Split from advanced.rs
//!
//! Related test files:
//! - advanced.rs: remaining advanced tactics
//! - conv.rs: conv tactic tests
//! - library_search.rs: library search tests
//! - mono_tactics.rs: mono tactic tests
//! - pattern_tactics.rs: rintro, peel, split_ifs tests
//! - propositional.rs: contrapose, push_neg, tauto tests

use super::*;

// ========== Tests for simpa tactic ==========

#[test]
fn test_simpa_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    // Should succeed vacuously (simpa on empty goals)
    simpa(&mut state).expect("simpa should succeed on already-complete states");
    assert!(
        state.is_complete(),
        "simpa should keep empty-goal states complete"
    );
}

#[test]
fn test_simpa_with_hypothesis() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    // Add a hypothesis h : A
    let goal = &mut state.goals[0];
    goal.local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "h".to_string(),
        ty: Expr::const_(Name::from_string("A"), vec![]),
        value: None,
    });

    // simpa should find the hypothesis
    simpa(&mut state).expect("simpa should close goal when matching hypothesis exists");
    assert!(state.is_complete());
}

#[test]
fn test_simpa_only_empty() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    // Add h : A
    let goal = &mut state.goals[0];
    goal.local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "h".to_string(),
        ty: Expr::const_(Name::from_string("A"), vec![]),
        value: None,
    });

    simpa_only(&mut state, vec![])
        .expect("simpa_only should fallback to assumption for exact hypothesis");
    assert!(
        state.is_complete(),
        "simpa_only should close the goal with matching context hypothesis"
    );
}

// ========== Tests for continuity tactic ==========

#[test]
fn test_continuity_config_default() {
    let config = ContinuityConfig::default();
    assert_eq!(config.max_depth, 8);
    assert!(config.use_all_hyps);
}

#[test]
fn test_continuity_config_new() {
    let config = ContinuityConfig::new();
    assert_eq!(config.max_depth, 8);
}

#[test]
fn test_continuity_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let err = continuity(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::NoGoals),
        "continuity on empty goals should produce NoGoals, got: {err:?}"
    );
}

#[test]
fn test_continuity_not_continuity_goal() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    // Should fail since A is not Continuous f
    let err = continuity(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::GoalMismatch(ref msg) if msg.contains("continuity")),
        "continuity on non-continuity goal should produce GoalMismatch error, got: {err:?}"
    );
}

#[test]
fn test_is_continuity_goal_true() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let cont = Expr::app(Expr::const_(Name::from_string("Continuous"), vec![]), f);
    assert!(is_continuity_goal(&cont));
}

#[test]
fn test_is_continuity_goal_continuous_at() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let cont_at = Expr::app(
        Expr::app(Expr::const_(Name::from_string("ContinuousAt"), vec![]), f),
        x,
    );
    assert!(is_continuity_goal(&cont_at));
}

#[test]
fn test_is_continuity_goal_false() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    assert!(!is_continuity_goal(&a));
}

#[test]
fn test_get_app_head_const() {
    let c = Expr::const_(Name::from_string("C"), vec![]);
    let head = get_app_head(&c);
    assert!(matches!(head.kind(), ExprKind::Const(_, _)));
}

#[test]
fn test_get_app_head_nested() {
    let f = Expr::const_(Name::from_string("F"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let app = Expr::app(Expr::app(f.clone(), a), b);
    let head = get_app_head(&app);
    assert!(exprs_equal(head, &f));
}

// ========== Tests for measurability tactic ==========

#[test]
fn test_measurability_config_default() {
    let config = MeasurabilityConfig::default();
    assert_eq!(config.max_depth, 8);
    assert!(config.use_all_hyps);
}

#[test]
fn test_measurability_config_new() {
    let config = MeasurabilityConfig::new();
    assert_eq!(config.max_depth, 8);
}

#[test]
fn test_measurability_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let err = measurability(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::NoGoals),
        "measurability on empty goals should produce NoGoals, got: {err:?}"
    );
}

#[test]
fn test_measurability_not_measurability_goal() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let err = measurability(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::GoalMismatch(ref msg) if msg.contains("measurability")),
        "measurability on non-measurability goal should produce GoalMismatch error, got: {err:?}"
    );
}

#[test]
fn test_is_measurability_goal_true() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let meas = Expr::app(Expr::const_(Name::from_string("Measurable"), vec![]), f);
    assert!(is_measurability_goal(&meas));
}

#[test]
fn test_is_measurability_goal_ae_measurable() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let ae_meas = Expr::app(Expr::const_(Name::from_string("AEMeasurable"), vec![]), f);
    assert!(is_measurability_goal(&ae_meas));
}

#[test]
fn test_is_measurability_goal_false() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    assert!(!is_measurability_goal(&a));
}
