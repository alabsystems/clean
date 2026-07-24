// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real carrier proof-carry regressions for linear_combination (#2635).
//!
//! Phase A: Real fractional coefficient support via Real.div(Real.ofInt, Real.ofNat).
//! Phase B: Real cancellation bridge via Real.add_right_cancel.

use super::*;
use clean_kernel::{env::Declaration, ExprKind};
use pattern::{linear_combination, linear_combination_proof::build_linear_combination_eq_proof};

fn real_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn real_of_int(n: i64) -> Expr {
    let int_expr = if n >= 0 {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(n as u64),
        )
    } else {
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(n.unsigned_abs() - 1),
        )
    };
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    )
}

fn real_mul_expr(coeff: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.mul"), vec![]), coeff),
        rhs,
    )
}

fn real_div(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.div"), vec![]), lhs),
        rhs,
    )
}

fn real_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn real_fraction(num: i64, den: u64) -> Expr {
    real_div(real_of_int(num), real_of_nat(den))
}

fn real_scaled(num: i64, den: u64, var: Expr) -> Expr {
    real_mul_expr(real_fraction(num, den), var)
}

fn setup_real_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_real_complex_analysis()
        .expect("Real complex analysis should initialize");
    env.init_cast_simp_lemmas()
        .expect("Cast simp lemmas should initialize");
    env
}

fn setup_real_identity_goal() -> ProofState {
    let mut env = setup_real_env();

    let real = Expr::const_(Name::from_string("Real"), vec![]);
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: real.clone(),
        })
        .expect("Real variable axiom should add");
    }

    // h : a = b, goal: a = b
    ProofState::with_context(
        env,
        make_eq(real.clone(), real_var("a"), real_var("b")),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: make_eq(real, real_var("a"), real_var("b")),
            value: None,
        }],
    )
}

/// Single-hypothesis fractional goal: h : a = b ⊢ (1/2)*a = (1/2)*b.
///
/// Uses one hypothesis with fractional coefficient so the proof builder can
/// close via `congr_arg (fun x => (1/2)*x) h` directly without needing the
/// cancellation bridge or ring_nf.
fn setup_real_fractional_direct_goal() -> ProofState {
    let mut env = setup_real_env();

    let real = Expr::const_(Name::from_string("Real"), vec![]);
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: real.clone(),
        })
        .expect("Real variable axiom should add");
    }

    // goal: (1/2)*a = (1/2)*b
    let goal_lhs = real_scaled(1, 2, real_var("a"));
    let goal_rhs = real_scaled(1, 2, real_var("b"));

    ProofState::with_context(
        env,
        make_eq(real.clone(), goal_lhs, goal_rhs),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: make_eq(real, real_var("a"), real_var("b")),
            value: None,
        }],
    )
}

fn setup_real_add_right_cancel_goal() -> ProofState {
    let mut env = setup_real_env();

    let real = Expr::const_(Name::from_string("Real"), vec![]);
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: real.clone(),
        })
        .expect("Real variable axiom should add");
    }

    ProofState::with_context(
        env,
        make_eq(real.clone(), real_var("a"), real_var("b")),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: make_eq(real.clone(), real_var("a"), real_var("b")),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: make_eq(real.clone(), real_var("c"), real_var("c")),
                value: None,
            },
        ],
    )
}

fn assert_clean_real_proof(state: &ProofState, context: &str) {
    assert!(state.is_complete(), "{context}: state should be complete");
    assert!(
        state.proof_term().is_some(),
        "{context}: proof_term() should be extractable"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "{context}: trustedArith should stay at 0"
    );
    assert_eq!(ledger.sorry_count, 0, "{context}: sorry should stay at 0");
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "{context}: trustedAy should stay at 0"
    );
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

// ============================================================================
// Phase A: Real integer coefficient (existing den=1 path, regression)
// ============================================================================

/// Real carrier with integer coefficient (1) closes without trustedArith.
///
/// Part of #2635.
#[test]
fn test_linear_combination_real_integer_coeff_closes_without_trust() {
    let mut state = setup_real_identity_goal();

    linear_combination(&mut state, vec![LinearCoeff::one("h")])
        .expect("linear_combination should close the Real identity goal");

    assert!(
        state.is_complete(),
        "linear_combination should close the Real identity goal"
    );
    assert!(
        state.proof_term().is_some(),
        "linear_combination should leave an extractable Real proof term"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "Real integer-coeff linear_combination must avoid trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "Real integer-coeff linear_combination must avoid sorry"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "Real integer-coeff linear_combination must avoid trustedAy"
    );
}

/// Real carrier with negative coefficient (-1) closes without trustedArith.
///
/// Part of #2635.
#[test]
fn test_linear_combination_real_negative_coeff_closes_without_trust() {
    let mut env = setup_real_env();

    let real = Expr::const_(Name::from_string("Real"), vec![]);
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: real.clone(),
        })
        .expect("Real variable axiom should add");
    }

    // h : a = b, goal: b = a (reversed — needs Eq.symm)
    let mut state = ProofState::with_context(
        env,
        make_eq(real.clone(), real_var("b"), real_var("a")),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: make_eq(real, real_var("a"), real_var("b")),
            value: None,
        }],
    );

    linear_combination(&mut state, vec![LinearCoeff::int("h", -1)])
        .expect("linear_combination should close the Real symmetry goal");

    assert!(
        state.is_complete(),
        "linear_combination should close the Real symmetry goal"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "Real negative-coeff linear_combination must avoid trustedArith"
    );
}

// ============================================================================
// Phase A: Real fractional coefficient (new path)
// ============================================================================

/// Phase A: Real proof-builder with fractional coefficient (1/2) produces a
/// proof via direct congr_arg close. Single hypothesis, no cancellation bridge
/// needed: congr_arg (fun x => (1/2)*x) h gives (1/2)*a = (1/2)*b directly.
///
/// Before #2635, make_coeff_expr returned None for Real fractional coefficients.
///
/// Part of #2635.
#[test]
fn test_proof_builder_real_fractional_direct_close() {
    let mut state = setup_real_fractional_direct_goal();
    let goal = state.current_goal().expect("goal should exist").clone();

    let proof = build_linear_combination_eq_proof(&state, &goal, &[LinearCoeff::new("h", 1, 2)])
        .expect("Real fractional direct close should produce a proof via congr_arg");

    state
        .close_goal(&goal, proof)
        .expect("Real fractional direct-close proof should type-check and close the goal");
    assert!(
        state.is_complete(),
        "state should be complete after Real fractional direct close"
    );
    assert!(
        state.proof_term().is_some(),
        "proof_term() should be extractable after Real fractional direct close"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "Real fractional direct close must not use trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "Real fractional direct close must not use sorry"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "Real fractional direct close must not use trustedAy"
    );
}

/// Phase A: End-to-end tactic-level Real fractional direct close.
///
/// Part of #2635.
#[test]
fn test_linear_combination_tactic_real_fractional_direct_closes_without_trust() {
    let mut state = setup_real_fractional_direct_goal();

    linear_combination(&mut state, vec![LinearCoeff::new("h", 1, 2)])
        .expect("linear_combination should close Real fractional direct goal without trustedArith");

    assert!(
        state.is_complete(),
        "linear_combination should close the Real fractional direct goal"
    );
    assert!(
        state.proof_term().is_some(),
        "linear_combination should leave an extractable Real proof term"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "Real fractional linear_combination must avoid trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "Real fractional linear_combination must avoid sorry"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "Real fractional linear_combination must avoid trustedAy"
    );
}

/// Phase B: the Real cancellation bridge should recover `a = b` from the
/// combined equality `a + c = b + c` via `Real.add_right_cancel`.
///
/// Part of #2635.
#[test]
fn test_proof_builder_real_add_right_cancel_closes_without_trust() {
    let mut state = setup_real_add_right_cancel_goal();
    let goal = state.current_goal().expect("goal should exist").clone();

    let proof = build_linear_combination_eq_proof(
        &state,
        &goal,
        &[LinearCoeff::one("h1"), LinearCoeff::one("h2")],
    )
    .expect("Real cancellation bridge should reconstruct the proof");

    assert!(
        expr_contains_const(&proof, "Real.add_right_cancel"),
        "Real cancellation proof should use Real.add_right_cancel"
    );

    state
        .close_goal(&goal, proof)
        .expect("Real cancellation proof should close the goal");
    assert_clean_real_proof(&state, "Real cancellation proof builder");
}

/// End-to-end tactic regression for the Real cancellation bridge.
///
/// Part of #2635.
#[test]
fn test_linear_combination_real_cancellation_bridge_closes_without_trust() {
    let mut state = setup_real_add_right_cancel_goal();

    linear_combination(
        &mut state,
        vec![LinearCoeff::one("h1"), LinearCoeff::one("h2")],
    )
    .expect("linear_combination should close the Real cancellation goal");

    let proof = state
        .proof_term()
        .expect("completed Real cancellation goal should retain a proof term");
    assert!(
        expr_contains_const(&proof, "Real.add_right_cancel"),
        "Real cancellation tactic proof should use Real.add_right_cancel"
    );
    assert_clean_real_proof(&state, "Real cancellation linear_combination");
}
