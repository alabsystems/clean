// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavioral regression tests for Nat SortLeAcc accumulator proof reconstruction.
//!
//! Covers the #2493 design test plan:
//! 1. 3-hyp non-chaining Nat contradiction closes False
//! 2. Mixed-scaled Nat contradiction closes False
//! 3. Counter regression: full linarith() produces 0 trustedArith
//!
//! Split from the linarith proof-type family to stay under file-size limit.

use super::*;
use clean_kernel::expr::ExprKind;
use serial_test::serial;

/// Recursive check whether an expression tree contains a specific constant name.
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

// =========================================================================
// #2493 design test plan — behavioral regressions for Nat SortLeAcc
// =========================================================================

/// TP-1: 3-hyp non-chaining Nat contradiction closes False.
///
/// h1: 3≤1, h2: 4≤2, h3: 5≤0 with coeff=[1,1,1] → add_le_add accumulates
/// (3+4+5) ≤ (1+2+0) = 12 ≤ 3 which is a concrete Nat contradiction.
/// The SortLeAcc accumulator derives False from the accumulated bounds.
///
/// Part of #2493.
#[test]
fn test_linarith_three_hyp_non_chain_contradiction_closes_false() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};
    let env = Environment::with_prelude();
    let false_const = Expr::const_(Name::from_string("False"), vec![]);

    let h1_id = FVarId::new(0);
    let h2_id = FVarId::new(1);
    let h3_id = FVarId::new(2);

    let h1_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(1));
    let h2_ty = make_nat_le_tc(Expr::nat_lit(4), Expr::nat_lit(2));
    let h3_ty = make_nat_le_tc(Expr::nat_lit(5), Expr::nat_lit(0));

    let mut state = ProofState::with_context(
        env,
        false_const,
        vec![
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_id,
                name: "h2".into(),
                ty: h2_ty,
                value: None,
            },
            LocalDecl {
                fvar: h3_id,
                name: "h3".into(),
                ty: h3_ty,
                value: None,
            },
        ],
    );
    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients: vec![1, 1, 1],
        result_constant: 9,
    };

    let proof = build_linarith_proof(&state, &goal, &certificate, &[h1_id, h2_id, h3_id])
        .expect("3-hyp non-chaining Nat contradiction should produce a False proof");

    assert!(
        expr_contains_const(&proof, "False.elim"),
        "3-hyp accumulated proof must derive False from 12 ≤ 3 contradiction"
    );

    let result = state.close_goal(&goal, proof);
    assert!(
        result.is_ok(),
        "close_goal should accept 3-hyp accumulated proof, got: {result:?}"
    );
    assert!(state.is_complete(), "goal should be closed");
}

/// TP-2: Mixed-scaled Nat contradiction closes False.
///
/// h1: 2≤0 coeff=1, h2: 3≤1 coeff=2 → scaled combination:
/// 1·(2≤0) gives 2≤0, 2·(3≤1) gives 6≤2, add_le_add: (2+6) ≤ (0+2) = 8≤2.
/// Concrete Nat contradiction → False.
///
/// Part of #2493.
#[test]
fn test_linarith_mixed_scaled_nat_contradiction_closes_false() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};
    let env = Environment::with_prelude();
    let false_const = Expr::const_(Name::from_string("False"), vec![]);

    let h1_id = FVarId::new(0);
    let h2_id = FVarId::new(1);

    let h1_ty = make_nat_le_tc(Expr::nat_lit(2), Expr::nat_lit(0));
    let h2_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(1));

    let mut state = ProofState::with_context(
        env,
        false_const,
        vec![
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_id,
                name: "h2".into(),
                ty: h2_ty,
                value: None,
            },
        ],
    );
    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients: vec![1, 2],
        result_constant: 6,
    };

    let proof = build_linarith_proof(&state, &goal, &certificate, &[h1_id, h2_id])
        .expect("mixed-scaled Nat contradiction should produce a False proof");

    assert!(
        expr_contains_const(&proof, "False.elim"),
        "mixed-scaled proof must derive False from 8 ≤ 2 contradiction"
    );

    let result = state.close_goal(&goal, proof);
    assert!(
        result.is_ok(),
        "close_goal should accept mixed-scaled contradiction proof, got: {result:?}"
    );
    assert!(state.is_complete(), "goal should be closed");
}

/// TP-3: Counter regression — full linarith() on concrete Nat contradiction
/// must close the goal with 0 trustedArith and 0 sorry.
///
/// Uses `linarith` entry point (not build_linarith_proof) to test the entire
/// pipeline end-to-end: FM search → certificate → build_linarith_proof →
/// close_goal with kernel-checked proof term.
///
/// Part of #2493.
#[test]
#[serial]
fn test_linarith_concrete_nat_no_trusted_arith() {
    use crate::tactic::arith_linarith::linarith;

    reset_arith_counter();
    reset_sorry_counter();

    let env = Environment::with_prelude();
    let false_const = Expr::const_(Name::from_string("False"), vec![]);

    let h1_id = FVarId::new(0);
    let h2_id = FVarId::new(1);

    // h1: 5 ≤ 2, h2: 3 ≤ 0 — concrete Nat contradiction
    let h1_ty = make_nat_le_tc(Expr::nat_lit(5), Expr::nat_lit(2));
    let h2_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(0));

    let mut state = ProofState::with_context(
        env,
        false_const,
        vec![
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_id,
                name: "h2".into(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    linarith(&mut state).expect("linarith should close concrete Nat contradiction");
    assert!(state.is_complete(), "goal should be closed by linarith");

    assert_eq!(
        arith_proof_count(),
        0,
        "concrete Nat contradiction must NOT use trustedArith (counter regression)"
    );
    assert_eq!(
        sorry_count(),
        0,
        "concrete Nat contradiction must NOT use sorry"
    );
}

#[test]
#[serial]
fn test_linarith_large_nat_coefficients_avoid_trusted_arith() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    const LARGE: u64 = 4_000_000_000;
    let large_i128 = i128::from(LARGE);

    reset_arith_counter();
    reset_sorry_counter();

    let env = Environment::with_prelude();
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let h_id = FVarId::new(0);
    let h_ty = make_nat_le_tc(Expr::nat_lit(1), Expr::nat_lit(0));

    let mut state = ProofState::with_context(
        env,
        false_const,
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );

    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients: vec![large_i128],
        result_constant: large_i128,
    };
    let proof = build_linarith_proof(&state, &goal, &certificate, &[h_id])
        .expect("build_linarith_proof should replay the widened Nat contradiction");
    state
        .close_goal(&goal, proof)
        .expect("close_goal should accept the widened Nat contradiction proof");
    assert!(
        state.is_complete(),
        "goal should be closed after widened linarith proof replay"
    );
    assert_eq!(
        arith_proof_count(),
        0,
        "widened linarith proof replay must not fall back to trustedArith"
    );
    assert_eq!(
        sorry_count(),
        0,
        "widened linarith proof replay must not use sorry"
    );
}
