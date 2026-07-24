// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `nn_verify` tactic.

use super::*;
use clean_kernel::{Environment, Expr, Level};

/// Helper: build a proof state with a single goal targeting `ty`.
fn ps_with_goal(ty: Expr) -> ProofState {
    let env = Environment::new();
    ProofState::new(env, ty)
}

// -- classify_goal tests --

#[test]
fn test_classify_goal_ibp_soundness() {
    // Goal head: ibp_linear_sound
    let goal = Expr::app(Expr::const_str("ibp_linear_sound"), Expr::const_str("x"));
    assert_eq!(classify_goal(&goal), Some(NnVerifyPattern::IbpSoundness));
}

#[test]
fn test_classify_goal_crown_relaxation() {
    let goal = Expr::app(
        Expr::const_str("crown_backward_valid"),
        Expr::const_str("layer"),
    );
    assert_eq!(classify_goal(&goal), Some(NnVerifyPattern::CrownRelaxation));
}

#[test]
fn test_classify_goal_cert_composition() {
    // Both "cert_" and "compose" must be present in the spine.
    let goal = Expr::app(Expr::const_str("cert_layer_compose"), Expr::const_str("c1"));
    assert_eq!(classify_goal(&goal), Some(NnVerifyPattern::CertComposition));
}

#[test]
fn test_classify_goal_bound_propagation() {
    // Head: IntervalBounds.contains
    let goal = Expr::app(
        Expr::const_str("IntervalBounds.contains"),
        Expr::const_str("bounds"),
    );
    assert_eq!(
        classify_goal(&goal),
        Some(NnVerifyPattern::BoundPropagation)
    );
}

#[test]
fn test_classify_goal_abstract_domain() {
    let goal = Expr::app(
        Expr::const_str("AbstractDomain.gamma_sound"),
        Expr::const_str("dom"),
    );
    assert_eq!(classify_goal(&goal), Some(NnVerifyPattern::AbstractDomain));
}

#[test]
fn test_classify_goal_unrelated_returns_none() {
    let goal = Expr::const_str("Nat.add");
    assert_eq!(classify_goal(&goal), None);
}

#[test]
fn test_classify_goal_empty_expr_returns_none() {
    // A sort expression has no constants.
    let goal = Expr::sort(Level::zero());
    assert_eq!(classify_goal(&goal), None);
}

#[test]
fn test_classify_goal_ibp_without_sound_returns_none() {
    // Only "ibp_" but not "sound" -> no match
    let goal = Expr::const_str("ibp_linear_forward");
    assert_eq!(classify_goal(&goal), None);
}

#[test]
fn test_classify_goal_cert_without_compose_returns_none() {
    // Only "cert_" but not "compose"
    let goal = Expr::const_str("cert_layer_valid");
    assert_eq!(classify_goal(&goal), None);
}

// -- nn_verify tactic tests --

#[test]
fn test_nn_verify_no_goals_returns_error() {
    let dummy = Expr::const_str("Prop");
    let mut ps = ps_with_goal(dummy);
    ps.goals.clear();
    let result = nn_verify(&mut ps);
    assert!(result.is_err());
    match result.unwrap_err() {
        TacticError::NoGoals => {}
        other => panic!("expected NoGoals, got: {other:?}"),
    }
}

#[test]
fn test_nn_verify_true_falls_through_to_auto_cascade() {
    // Goal: True — no NN pattern matches, so auto_cascade handles it.
    let true_expr = Expr::const_str("True");
    let mut ps = ps_with_goal(true_expr);
    let result = nn_verify(&mut ps);
    assert!(
        result.is_ok(),
        "nn_verify should close `True` via auto_cascade fallback: {result:?}"
    );
    assert!(ps.goals.is_empty(), "goal should be closed");
}

#[test]
fn test_nn_verify_with_info_true_reports_auto_cascade() {
    let true_expr = Expr::const_str("True");
    let mut ps = ps_with_goal(true_expr);
    let result = nn_verify_with_info(&mut ps);
    assert!(result.is_ok());
    let info = result.expect("should succeed");
    assert_eq!(info.pattern, "auto_cascade");
}

#[test]
fn test_nn_verify_unsolvable_fails_cleanly() {
    // Goal: False — should not be closable
    let false_expr = Expr::const_str("False");
    let mut ps = ps_with_goal(false_expr);
    let goal_count_before = ps.goals.len();
    let result = nn_verify(&mut ps);
    assert!(result.is_err(), "nn_verify should not close `False`");
    assert_eq!(
        ps.goals.len(),
        goal_count_before,
        "state should be unchanged after failure"
    );
}

#[test]
fn test_nn_verify_prop_eq_refl_fallback() {
    // Goal: @Eq Prop True True — falls through to auto_cascade
    let prop = Expr::sort(Level::zero());
    let true_c = Expr::const_str("True");
    let eq_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                prop,
            ),
            true_c.clone(),
        ),
        true_c,
    );
    let mut ps = ps_with_goal(eq_expr);
    let result = nn_verify(&mut ps);
    assert!(
        result.is_ok(),
        "nn_verify should close `True = True` via fallback: {result:?}"
    );
}

// -- Pattern display --

#[test]
fn test_pattern_display() {
    assert_eq!(NnVerifyPattern::IbpSoundness.to_string(), "IBP soundness");
    assert_eq!(
        NnVerifyPattern::CrownRelaxation.to_string(),
        "CROWN relaxation"
    );
    assert_eq!(
        NnVerifyPattern::CertComposition.to_string(),
        "certificate composition"
    );
    assert_eq!(
        NnVerifyPattern::BoundPropagation.to_string(),
        "bound propagation"
    );
    assert_eq!(
        NnVerifyPattern::AbstractDomain.to_string(),
        "abstract domain"
    );
}

// -- Spine collection --

#[test]
fn test_collect_spine_const_names_simple() {
    let expr = Expr::app(Expr::const_str("f"), Expr::const_str("x"));
    let names = collect_spine_const_names(&expr);
    assert!(names.contains(&"f".to_string()));
    assert!(names.contains(&"x".to_string()));
}

#[test]
fn test_collect_spine_const_names_nested_app() {
    // (f x y) = App(App(f, x), y)
    let expr = Expr::app(
        Expr::app(Expr::const_str("f"), Expr::const_str("x")),
        Expr::const_str("y"),
    );
    let names = collect_spine_const_names(&expr);
    assert!(names.contains(&"f".to_string()));
    assert!(names.contains(&"x".to_string()));
    assert!(names.contains(&"y".to_string()));
}

#[test]
fn test_collect_spine_const_names_sort_returns_empty() {
    let expr = Expr::sort(Level::zero());
    let names = collect_spine_const_names(&expr);
    assert!(names.is_empty());
}
