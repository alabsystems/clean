// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for tactic state and goal pretty-printing.
//!
//! Covers ExprFormatter configuration, goal formatting with and without
//! hypotheses, proof state formatting for single and multiple goals,
//! and expression formatting for the major ExprKind variants.

use std::sync::Arc;

use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Level};

use super::core::{Goal, LocalDecl, ProofState};
use super::display::{
    format_expr, format_goal, format_local_context, format_proof_state, ExprFormatter,
};
use crate::unify::MetaState;

/// Helper: create a minimal environment with Nat and Prop constants.
fn setup_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("should init Nat");
    env.init_eq().expect("should init Eq");
    env.init_true_false().expect("should init True/False");
    env
}

/// Helper: build a Goal with the given target and local context.
fn make_goal(
    metas: &mut MetaState,
    target: Expr,
    local_ctx: Vec<LocalDecl>,
    tag: Option<&str>,
) -> Goal {
    let meta_id = metas.fresh(target.clone());
    Goal {
        meta_id,
        target,
        local_ctx,
        tag: tag.map(String::from),
    }
}

/// Helper: build a LocalDecl for a hypothesis.
fn make_hyp(id: u64, name: &str, ty: Expr) -> LocalDecl {
    LocalDecl {
        fvar: FVarId::new(id),
        name: name.to_string(),
        ty,
        value: None,
    }
}

// =============================================================================
// ExprFormatter defaults
// =============================================================================

#[test]
fn test_expr_formatter_defaults() {
    let config = ExprFormatter::default();
    assert!(!config.pp_all, "pp_all should default to false");
    assert!(config.pp_notation, "pp_notation should default to true");
    assert!(!config.pp_universes, "pp_universes should default to false");
    assert_eq!(config.max_depth, 64);
    assert_eq!(config.line_width, 100);
}

#[test]
fn test_expr_formatter_pp_all() {
    let config = ExprFormatter {
        pp_all: true,
        ..Default::default()
    };
    assert!(config.pp_all);
}

// =============================================================================
// Expression formatting
// =============================================================================

#[test]
fn test_format_expr_const() {
    let env = setup_env();
    let config = ExprFormatter::default();
    let nat = Expr::const_str("Nat");
    let result = format_expr(&nat, &env, &config);
    assert_eq!(result, "Nat");
}

#[test]
fn test_format_expr_prop() {
    let env = setup_env();
    let config = ExprFormatter::default();
    let prop = Expr::prop();
    let result = format_expr(&prop, &env, &config);
    assert_eq!(result, "Prop");
}

#[test]
fn test_format_expr_type() {
    let env = setup_env();
    let config = ExprFormatter::default();
    let type_expr = Expr::sort(Level::Succ(Arc::new(Level::Zero)));
    let result = format_expr(&type_expr, &env, &config);
    assert_eq!(result, "Type");
}

#[test]
fn test_format_expr_type_n() {
    let env = setup_env();
    let config = ExprFormatter::default();
    // Type 2 = Sort 3
    let type2 = Expr::sort(Level::Succ(Arc::new(Level::Succ(Arc::new(Level::Succ(
        Arc::new(Level::Zero),
    ))))));
    let result = format_expr(&type2, &env, &config);
    assert_eq!(result, "Type 2");
}

#[test]
fn test_format_expr_app() {
    let env = setup_env();
    let config = ExprFormatter::default();
    // Nat.succ 0
    let succ = Expr::const_str("Nat.succ");
    let zero = Expr::const_str("Nat.zero");
    let app = Expr::app(succ, zero);
    let result = format_expr(&app, &env, &config);
    assert_eq!(result, "Nat.succ Nat.zero");
}

#[test]
fn test_format_expr_lambda() {
    let env = setup_env();
    let config = ExprFormatter::default();
    // fun (x : Nat) => x
    let nat = Expr::const_str("Nat");
    let body = Expr::bvar(0);
    let lam = Expr::lam(BinderInfo::Default, nat, body);
    let result = format_expr(&lam, &env, &config);
    assert_eq!(result, "fun (: Nat) => #B0");
}

#[test]
fn test_format_expr_pi_nondep() {
    let env = setup_env();
    let config = ExprFormatter::default();
    // Nat → Nat (non-dependent, body has no loose bvars)
    let nat = Expr::const_str("Nat");
    let pi = Expr::pi(BinderInfo::Default, nat.clone(), nat);
    let result = format_expr(&pi, &env, &config);
    assert_eq!(result, "Nat \u{2192} Nat");
}

#[test]
fn test_format_expr_pi_dep() {
    let env = setup_env();
    let config = ExprFormatter::default();
    // ∀ (x : Nat), #B0  (dependent — body references bound var)
    let nat = Expr::const_str("Nat");
    let body = Expr::bvar(0);
    let pi = Expr::pi(BinderInfo::Default, nat, body);
    let result = format_expr(&pi, &env, &config);
    assert!(
        result.contains('\u{2200}'),
        "dependent Pi should use ∀: got {result}"
    );
    assert!(
        result.contains("Nat"),
        "should contain binder type: got {result}"
    );
}

#[test]
fn test_format_expr_pi_implicit() {
    let env = setup_env();
    let config = ExprFormatter::default();
    // ∀ {x : Nat}, #B0
    let nat = Expr::const_str("Nat");
    let body = Expr::bvar(0);
    let pi = Expr::pi(BinderInfo::Implicit, nat, body);
    let result = format_expr(&pi, &env, &config);
    assert!(
        result.contains('{'),
        "implicit binder should use braces: got {result}"
    );
}

#[test]
fn test_format_expr_lit() {
    let env = setup_env();
    let config = ExprFormatter::default();
    let lit = Expr::nat_lit(42);
    let result = format_expr(&lit, &env, &config);
    assert_eq!(result, "42");
}

#[test]
fn test_format_expr_universes() {
    let env = setup_env();
    let config = ExprFormatter {
        pp_universes: true,
        ..Default::default()
    };
    let prop = Expr::prop();
    let result = format_expr(&prop, &env, &config);
    assert_eq!(result, "Sort 0");
}

#[test]
fn test_format_expr_depth_limit() {
    let env = setup_env();
    let config = ExprFormatter {
        max_depth: 2,
        ..Default::default()
    };
    // Build nested apps: f (f (f x)) — depth should truncate
    let x = Expr::const_str("x");
    let f = Expr::const_str("f");
    let inner = Expr::app(f.clone(), x);
    let mid = Expr::app(f.clone(), inner);
    let outer = Expr::app(f, mid);
    let result = format_expr(&outer, &env, &config);
    assert!(
        result.contains("..."),
        "should truncate at depth limit: got {result}"
    );
}

// =============================================================================
// Local context formatting
// =============================================================================

#[test]
fn test_format_local_context_empty() {
    let env = setup_env();
    let config = ExprFormatter::default();
    let result = format_local_context(&[], &env, &config);
    assert!(result.is_empty());
}

#[test]
fn test_format_local_context() {
    let env = setup_env();
    let config = ExprFormatter::default();
    let nat = Expr::const_str("Nat");
    let prop = Expr::prop();
    let decls = vec![make_hyp(0, "x", nat), make_hyp(1, "h", prop)];
    let result = format_local_context(&decls, &env, &config);
    assert!(result.contains("x : Nat"), "got: {result}");
    assert!(result.contains("h : Prop"), "got: {result}");
}

#[test]
fn test_format_local_context_let_binding() {
    let env = setup_env();
    let config = ExprFormatter::default();
    let nat = Expr::const_str("Nat");
    let val = Expr::nat_lit(5);
    let decl = LocalDecl {
        fvar: FVarId::new(0),
        name: "n".to_string(),
        ty: nat,
        value: Some(val),
    };
    let result = format_local_context(&[decl], &env, &config);
    assert!(
        result.contains("n : Nat := 5"),
        "let-binding should show value: got {result}"
    );
}

// =============================================================================
// Goal formatting
// =============================================================================

#[test]
fn test_format_empty_goal() {
    let env = setup_env();
    let mut metas = MetaState::new();
    let target = Expr::const_str("True");
    let goal = make_goal(&mut metas, target, vec![], None);
    let result = format_goal(&goal, &env);
    assert!(
        result.contains("\u{22a2} True"),
        "should have turnstile: got {result}"
    );
    // No hypotheses means no lines before the turnstile
    assert!(
        result.starts_with('\u{22a2}'),
        "empty goal should start with turnstile: got {result}"
    );
}

#[test]
fn test_format_goal_with_tag() {
    let env = setup_env();
    let mut metas = MetaState::new();
    let target = Expr::const_str("True");
    let goal = make_goal(&mut metas, target, vec![], Some("intro"));
    let result = format_goal(&goal, &env);
    assert!(
        result.starts_with("case intro"),
        "should start with case tag: got {result}"
    );
}

#[test]
fn test_format_goal_with_hyps() {
    let env = setup_env();
    let mut metas = MetaState::new();
    let nat = Expr::const_str("Nat");
    let prop = Expr::prop();
    let target = Expr::const_str("True");
    let hyps = vec![make_hyp(0, "x", nat), make_hyp(1, "h", prop)];
    let goal = make_goal(&mut metas, target, hyps, None);
    let result = format_goal(&goal, &env);
    assert!(result.contains("x : Nat"), "got: {result}");
    assert!(result.contains("h : Prop"), "got: {result}");
    assert!(result.contains("\u{22a2} True"), "got: {result}");
}

// =============================================================================
// Proof state formatting
// =============================================================================

#[test]
fn test_format_proof_state_complete() {
    let env = setup_env();
    let target = Expr::const_str("True");
    let mut state = ProofState::new(env.clone(), target);
    // Manually clear goals to simulate completion
    state.goals.clear();
    let result = format_proof_state(&state, &env);
    assert_eq!(result, "no goals");
}

#[test]
fn test_format_proof_state_single() {
    let env = setup_env();
    let target = Expr::const_str("Nat");
    let state = ProofState::new(env.clone(), target);
    let result = format_proof_state(&state, &env);
    // Single goal — no count header
    assert!(
        !result.contains("goals"),
        "single goal should not show count: got {result}"
    );
    assert!(
        result.contains("\u{22a2} Nat"),
        "should contain goal: got {result}"
    );
}

#[test]
fn test_format_proof_state_multiple() {
    let env = setup_env();
    let target_p = Expr::const_str("P");
    let target_q = Expr::const_str("Q");

    let mut metas = MetaState::new();
    let goal_left = make_goal(&mut metas, target_p, vec![], Some("left"));
    let goal_right = make_goal(&mut metas, target_q, vec![], Some("right"));

    // Build a ProofState with two goals
    let base_target = Expr::const_str("dummy");
    let mut state = ProofState::new(env.clone(), base_target);
    state.goals.clear();
    state.goals.push_back(goal_left);
    state.goals.push_back(goal_right);

    let result = format_proof_state(&state, &env);
    assert!(
        result.contains("2 goals"),
        "should show goal count: got {result}"
    );
    assert!(result.contains("case left"), "got: {result}");
    assert!(result.contains("case right"), "got: {result}");
    assert!(
        result.contains("\u{22a2} P"),
        "should contain first goal target: got {result}"
    );
    assert!(
        result.contains("\u{22a2} Q"),
        "should contain second goal target: got {result}"
    );
}
