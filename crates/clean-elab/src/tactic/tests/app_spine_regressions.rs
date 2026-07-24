// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::tactic::nat_expr_eval::eval_nat_expr;
use crate::tactic::positivity::{self, ComparisonKind};
use crate::tactic::tc_app;

fn nat_hadd(lhs: Expr, rhs: Expr) -> Expr {
    tc_app::mk_tc_hbinop(
        Expr::const_(Name::from_string("HAdd.hAdd"), vec![]),
        tc_app::nat_type(),
        tc_app::nat_type(),
        tc_app::nat_type(),
        tc_app::nat_arith_inst("HAdd.hAdd"),
        lhs,
        rhs,
    )
}

fn nat_hmul(lhs: Expr, rhs: Expr) -> Expr {
    tc_app::mk_tc_hbinop(
        Expr::const_(Name::from_string("HMul.hMul"), vec![]),
        tc_app::nat_type(),
        tc_app::nat_type(),
        tc_app::nat_type(),
        tc_app::nat_arith_inst("HMul.hMul"),
        lhs,
        rhs,
    )
}

fn nat_hpow(base: Expr, exp: Expr) -> Expr {
    tc_app::mk_tc_hbinop(
        Expr::const_(Name::from_string("HPow.hPow"), vec![]),
        tc_app::nat_type(),
        tc_app::nat_type(),
        tc_app::nat_type(),
        tc_app::nat_arith_inst("HPow.hPow"),
        base,
        exp,
    )
}

#[test]
fn test_norm_eval_nat_expr_handles_fully_applied_typeclass_ops() {
    let add = nat_hadd(Expr::nat_lit(2), Expr::nat_lit(3));
    let mul = nat_hmul(Expr::nat_lit(4), Expr::nat_lit(5));
    let pow = nat_hpow(Expr::nat_lit(3), Expr::nat_lit(2));

    assert_eq!(crate::tactic::norm::eval_nat_expr(&add), Some(5));
    assert_eq!(crate::tactic::norm::eval_nat_expr(&mul), Some(20));
    assert_eq!(crate::tactic::norm::eval_nat_expr(&pow), Some(9));
}

#[test]
fn test_positivity_patterns_handle_fully_applied_typeclass_spines() {
    let lhs = Expr::const_(Name::from_string("lhs"), vec![]);
    let rhs = Expr::const_(Name::from_string("rhs"), vec![]);
    let add = nat_hadd(lhs.clone(), rhs.clone());
    let mul = nat_hmul(lhs.clone(), rhs.clone());
    let pow = nat_hpow(lhs.clone(), Expr::nat_lit(2));
    let cube = nat_hpow(lhs.clone(), Expr::nat_lit(3));
    let cmp = tc_app::nat_le_tc(add.clone(), Expr::nat_lit(0));

    let (extracted, kind) =
        positivity::extract_comparison_expr(&cmp).expect("comparison extractor should match LE");
    assert_eq!(extracted, add);
    assert!(matches!(kind, ComparisonKind::Le));
    assert_eq!(
        positivity::is_add_pattern(&nat_hadd(lhs.clone(), rhs.clone())),
        Some((lhs.clone(), rhs.clone()))
    );
    assert_eq!(positivity::is_mul_pattern(&mul), Some((lhs.clone(), rhs)));
    assert!(positivity::get_square_base(&pow).is_some());
    assert!(positivity::get_square_base(&cube).is_none());
}

#[test]
fn test_push_neg_matchers_handle_fully_applied_comparison_spines() {
    let lhs = Expr::nat_lit(2);
    let rhs = Expr::nat_lit(5);
    let le = tc_app::nat_le_tc(lhs.clone(), rhs.clone());
    let lt = tc_app::nat_lt_tc(lhs.clone(), rhs.clone());

    assert_eq!(
        match_le(&le),
        Some((tc_app::nat_type(), lhs.clone(), rhs.clone()))
    );
    assert_eq!(match_lt(&lt), Some((tc_app::nat_type(), lhs, rhs)));
}

#[test]
fn test_norm_num_handles_fully_applied_comparison_spines() {
    let true_goal = tc_app::nat_lt_tc(Expr::nat_lit(2), Expr::nat_lit(5));
    let false_goal = tc_app::nat_le_tc(Expr::nat_lit(5), Expr::nat_lit(2));

    let mut true_state = ProofState::new(setup_env_with_nat(), true_goal);
    norm_num(&mut true_state).expect("norm_num should close fully-applied Nat.lt goals");
    assert!(true_state.goals().is_empty());

    let mut false_state = ProofState::new(setup_env_with_nat(), false_goal);
    let err = norm_num(&mut false_state).unwrap_err();
    assert!(
        matches!(err, TacticError::ArithmeticFailed { .. }),
        "expected ArithmeticFailed for false fully-applied Nat.le goal, got: {err:?}"
    );
}

// --- Overflow regression tests for shared eval_nat_expr (#2542) ---

#[test]
fn test_eval_nat_expr_addition_overflow_returns_none() {
    let add = nat_hadd(Expr::nat_lit(u64::MAX), Expr::nat_lit(1));
    assert_eq!(
        eval_nat_expr(&add),
        None,
        "u64 addition overflow must return None, not wrap"
    );
}

#[test]
fn test_eval_nat_expr_multiplication_overflow_returns_none() {
    let mul = nat_hmul(Expr::nat_lit(u64::MAX), Expr::nat_lit(2));
    assert_eq!(
        eval_nat_expr(&mul),
        None,
        "u64 multiplication overflow must return None, not wrap"
    );
}

#[test]
fn test_eval_nat_expr_large_exponent_returns_none() {
    let pow = nat_hpow(Expr::nat_lit(2), Expr::nat_lit(u64::from(u32::MAX) + 1));
    assert_eq!(
        eval_nat_expr(&pow),
        None,
        "exponent > u32::MAX must return None, not truncate"
    );
}

#[test]
fn test_eval_nat_expr_pow_overflow_returns_none() {
    let pow = nat_hpow(Expr::nat_lit(2), Expr::nat_lit(64));
    assert_eq!(eval_nat_expr(&pow), None, "2^64 overflow must return None");
    let pow_ok = nat_hpow(Expr::nat_lit(2), Expr::nat_lit(63));
    assert_eq!(eval_nat_expr(&pow_ok), Some(1u64 << 63));
}

// --- Nat.gcd evaluation (tactic-divergence-12) -----------------------------
//
// Lean 4's `norm_num` / `decide` evaluate ground `Nat.gcd`; the kernel reduces
// it natively (`reduce_nat`). The shared `eval_nat_expr` previously returned
// `None` for `Nat.gcd`, so comparison goals such as `Nat.gcd 12 18 <= 6` were
// never recognized as ground-decidable. These pin the evaluator parity.

fn nat_gcd_expr(a: u64, b: u64) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.gcd"), vec![]),
            Expr::nat_lit(a),
        ),
        Expr::nat_lit(b),
    )
}

#[test]
fn test_eval_nat_expr_gcd_coprime_returns_one() {
    assert_eq!(eval_nat_expr(&nat_gcd_expr(12, 18)), Some(6));
    assert_eq!(eval_nat_expr(&nat_gcd_expr(35, 12)), Some(1));
}

#[test]
fn test_eval_nat_expr_gcd_zero_identities_match_lean() {
    // Lean 4: gcd 0 y = y, gcd x 0 = x, gcd 0 0 = 0.
    assert_eq!(eval_nat_expr(&nat_gcd_expr(0, 7)), Some(7));
    assert_eq!(eval_nat_expr(&nat_gcd_expr(7, 0)), Some(7));
    assert_eq!(eval_nat_expr(&nat_gcd_expr(0, 0)), Some(0));
}

#[test]
fn test_eval_nat_expr_gcd_nested_argument_evaluates() {
    // gcd (4 * 6) (8 + 10) = gcd 24 18 = 6 — operands are themselves ground.
    let lhs = nat_hmul(Expr::nat_lit(4), Expr::nat_lit(6));
    let rhs = nat_hadd(Expr::nat_lit(8), Expr::nat_lit(10));
    let gcd = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.gcd"), vec![]), lhs),
        rhs,
    );
    assert_eq!(eval_nat_expr(&gcd), Some(6));
}

#[test]
fn test_eval_nat_expr_gcd_symbolic_argument_returns_none() {
    // A non-ground operand must keep the whole expression symbolic.
    let gcd = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.gcd"), vec![]),
            Expr::const_(Name::from_string("n"), vec![]),
        ),
        Expr::nat_lit(6),
    );
    assert_eq!(eval_nat_expr(&gcd), None);
}
