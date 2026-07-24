// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-carry regressions for focused `conv_rw` target rewrites.
//!
//! Direct API tests live here; position-specific and compound handler
//! tests are in child modules. Part of #2504.

use super::*;
use clean_kernel::env::Declaration;
use clean_parser::{Span, SurfaceExpr, SurfaceRwRule};
use serial_test::serial;

// Child modules (split out in #2547/#2504). These declarations were missing, so
// `compound.rs` and `position.rs` — and their conv proof-carry tests — were
// orphaned (never compiled). Wiring them back in restores that coverage.
mod compound;
mod multi_focus;
mod position;

// =========================================================================
// Shared helpers (visible to child modules)
// =========================================================================

fn assert_no_trusted_fallback(state: &ProofState, tactic_name: &str, before: (u64, u64)) {
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "{tactic_name} must not record trusted axiom usage"
    );
    assert_no_trusted_axiom_usage(tactic_name, "focused conv rewrite", before);
}

fn expr_contains_const(expr: &Expr, needle: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name == &Name::from_string(needle),
        ExprKind::App(f, a) => expr_contains_const(f, needle) || expr_contains_const(a, needle),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, needle) || expr_contains_const(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, needle)
                || expr_contains_const(val, needle)
                || expr_contains_const(body, needle)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            expr_contains_const(inner, needle)
        }
        _ => false,
    }
}

fn rw_rule(name: &str) -> SurfaceRwRule {
    SurfaceRwRule {
        span: Span::dummy(),
        reverse: false,
        term: SurfaceExpr::Ident(Span::dummy(), name.to_string()),
    }
}

fn local_fvar_by_name(state: &ProofState, name: &str) -> FVarId {
    state
        .current_goal()
        .expect("test state should have a current goal")
        .local_ctx
        .iter()
        .find(|decl| decl.name == name)
        .map(|decl| decl.fvar)
        .expect("named local should exist")
}

// =========================================================================
// Direct conv_rw / conv_lhs / conv_rhs API tests
// =========================================================================

#[test]
#[serial]
fn test_conv_rw_direct_path_uses_checked_rewrite() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq_n(x.clone(), y.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality proof");
    let axiom_before = axiom_snapshot();

    conv_rw(&mut state, vec![ConvPosition::EqLhs], "hxy", false)
        .expect("conv_rw should rewrite the focused equality side");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(y.clone(), y),
        "conv_rw should rebuild the equality target without trusted fallback"
    );

    rfl(&mut state).expect("rewritten equality should close by reflexivity");
    assert_no_trusted_fallback(&state, "conv_rw direct path", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "conv_rw direct path must preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "conv_rw direct path must preserve closed_proof() extraction"
    );
}

#[test]
#[serial]
fn test_conv_rw_reverse_path_uses_eq_symm_without_trust() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq_n(y.clone(), x.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality proof");
    let axiom_before = axiom_snapshot();

    conv_rw(&mut state, vec![ConvPosition::EqLhs], "hxy", true)
        .expect("reverse conv_rw should orient the local equality with Eq.symm");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(x.clone(), x.clone()),
        "reverse conv_rw should rewrite only the focused side"
    );

    rfl(&mut state).expect("reverse rewrite should close by reflexivity");
    assert_no_trusted_fallback(&state, "conv_rw reverse path", axiom_before);

    let proof = state
        .instantiated_proof()
        .expect("reverse conv_rw should leave an instantiated proof");
    assert!(
        expr_contains_const(&proof, "Eq.symm"),
        "reverse conv_rw proof should reference Eq.symm, got: {proof:?}"
    );
}

#[test]
#[serial]
fn test_conv_rw_lhs_wrapper_preserves_proof_chain_without_trust() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality proof");
    let axiom_before = axiom_snapshot();

    conv_lhs(&mut state, "hxy", false).expect("conv_lhs should rewrite inside the lhs focus");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(Expr::prop(), make_p(y.clone()), make_p(y)),
        "conv_lhs should rewrite only the selected equality side without trusted fallback"
    );

    rfl(&mut state).expect("conv_lhs rewrite should close by reflexivity");
    assert_no_trusted_fallback(&state, "conv_lhs wrapper", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "conv_lhs wrapper must preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "conv_lhs wrapper must preserve closed_proof() extraction"
    );
}

#[test]
#[serial]
fn test_conv_rw_rhs_wrapper_preserves_proof_chain_without_trust() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(y.clone(), x.clone()),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hyx").expect("intro should create the local equality proof");
    let axiom_before = axiom_snapshot();

    conv_rhs(&mut state, "hyx", false).expect("conv_rhs should rewrite inside the rhs focus");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(Expr::prop(), make_p(x.clone()), make_p(x)),
        "conv_rhs should rewrite only the selected equality side without trusted fallback"
    );

    rfl(&mut state).expect("conv_rhs rewrite should close by reflexivity");
    assert_no_trusted_fallback(&state, "conv_rhs wrapper", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "conv_rhs wrapper must preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "conv_rhs wrapper must preserve closed_proof() extraction"
    );
}

#[test]
#[serial]
fn test_conv_rw_deep_path_preserves_proof_chain_without_trust() {
    reset_all_counters();
    let mut env = setup_env_with_full_eq();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("N"), vec![]),
            Expr::const_(Name::from_string("N"), vec![]),
        ),
    })
    .unwrap();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let qx = Expr::app(q.clone(), x.clone());
    let qy = Expr::app(q, y.clone());
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq_n(qx, qy.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality proof");
    let axiom_before = axiom_snapshot();

    conv_rw(
        &mut state,
        vec![ConvPosition::EqLhs, ConvPosition::AppArg],
        "hxy",
        false,
    )
    .expect("deep-path conv_rw should rewrite inside the focused application");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(qy.clone(), qy),
        "deep-path conv_rw should rewrite only the focused nested occurrence"
    );

    rfl(&mut state).expect("deep-path rewrite should close by reflexivity");
    assert_no_trusted_fallback(&state, "conv_rw deep path", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "deep-path conv_rw must preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "deep-path conv_rw must preserve closed_proof() extraction"
    );
}

#[test]
#[serial]
fn test_conv_rw_duplicate_occurrence_rewrites_only_focused_path() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let target = make_eq(Expr::prop(), make_p(x.clone()), make_p(x.clone()));
    let goal = Expr::pi(BinderInfo::Default, make_eq_n(x.clone(), y.clone()), target);
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality proof");
    let first_axiom_before = axiom_snapshot();

    conv_rw(
        &mut state,
        vec![ConvPosition::EqLhs, ConvPosition::AppArg],
        "hxy",
        false,
    )
    .expect("conv_rw should rewrite only the selected duplicate occurrence");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(Expr::prop(), make_p(y.clone()), make_p(x.clone())),
        "path-specific conv_rw must not rewrite duplicate occurrences outside the selected path"
    );
    assert_no_trusted_fallback(&state, "conv_rw duplicate occurrence", first_axiom_before);
    let second_axiom_before = axiom_snapshot();

    conv_rw(
        &mut state,
        vec![ConvPosition::EqRhs, ConvPosition::AppArg],
        "hxy",
        false,
    )
    .expect("second focused rewrite should finish the duplicate-occurrence goal");
    rfl(&mut state).expect("duplicate-occurrence goal should close after both focused rewrites");

    assert_no_trusted_fallback(
        &state,
        "conv_rw duplicate occurrence closeout",
        second_axiom_before,
    );
    assert!(
        state.closed_proof().is_some(),
        "duplicate-occurrence path must preserve closed_proof() extraction"
    );
}
