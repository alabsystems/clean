// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the linarith expression parser (`parse.rs`).

use super::*;
use clean_kernel::name::Name;

/// Helper: build `Const(name, [])`.
fn mk_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Helper: build `App(f, arg)`.
fn mk_app(f: Expr, arg: Expr) -> Expr {
    Expr::app(f, arg)
}

/// Helper: build a free variable expression.
fn mk_fvar(id: u64) -> Expr {
    Expr::fvar(FVarId::new(id))
}

/// Helper: run parse_linear_expr_direct with fresh state.
fn parse_direct(expr: &Expr) -> Option<LinearExpr> {
    let mut var_map = std::collections::HashMap::new();
    let mut next_var = 0;
    parse_linear_expr_direct(expr, &mut var_map, &mut next_var, None)
}

// ---- Rat.zero / Rat.one constant recognition ----

#[test]
fn test_linarith_parse_rat_zero() {
    let expr = mk_const("Rat.zero");
    let result = parse_direct(&expr).expect("Rat.zero should parse");
    assert!(result.is_constant());
    assert_eq!(result.constant, 0);
}

#[test]
fn test_linarith_parse_rat_one() {
    let expr = mk_const("Rat.one");
    let result = parse_direct(&expr).expect("Rat.one should parse");
    assert!(result.is_constant());
    assert_eq!(result.constant, 1);
}

#[test]
fn test_linarith_parse_existing_zero_constants_still_work() {
    for name in &["Nat.zero", "Int.zero", "Real.zero", "Rat.zero"] {
        let expr = mk_const(name);
        let result = parse_direct(&expr).unwrap_or_else(|| panic!("{name} should parse as zero"));
        assert_eq!(result.constant, 0, "{name} should be 0");
        assert!(result.is_constant(), "{name} should be constant");
    }
}

#[test]
fn test_linarith_parse_existing_one_constants_still_work() {
    for name in &["Nat.one", "Int.one", "Real.one", "Rat.one"] {
        let expr = mk_const(name);
        let result = parse_direct(&expr).unwrap_or_else(|| panic!("{name} should parse as one"));
        assert_eq!(result.constant, 1, "{name} should be 1");
        assert!(result.is_constant(), "{name} should be constant");
    }
}

// ---- Rat.ofInt embedding ----

#[test]
fn test_linarith_parse_rat_of_int_zero() {
    // Rat.ofInt (Int.zero)  =>  0
    let inner = mk_const("Int.zero");
    let expr = mk_app(mk_const("Rat.ofInt"), inner);
    let result = parse_direct(&expr).expect("Rat.ofInt Int.zero should parse");
    assert!(result.is_constant());
    assert_eq!(result.constant, 0);
}

#[test]
fn test_linarith_parse_rat_of_int_variable() {
    // Rat.ofInt x  =>  x (preserves linearity)
    let x = mk_fvar(100);
    let expr = mk_app(mk_const("Rat.ofInt"), x);
    let result = parse_direct(&expr).expect("Rat.ofInt fvar should parse");
    assert!(!result.is_constant());
    assert_eq!(result.get_coeff(0), 1);
}

// ---- Unary negation: direct Rat.neg / Int.neg ----

#[test]
fn test_linarith_parse_rat_neg_constant() {
    // Rat.neg (Rat.one)  =>  -1
    let inner = mk_const("Rat.one");
    let expr = mk_app(mk_const("Rat.neg"), inner);
    let result = parse_direct(&expr).expect("Rat.neg Rat.one should parse");
    assert!(result.is_constant());
    assert_eq!(result.constant, -1);
}

#[test]
fn test_linarith_parse_int_neg_variable() {
    // Int.neg x  =>  -x
    let x = mk_fvar(200);
    let expr = mk_app(mk_const("Int.neg"), x);
    let result = parse_direct(&expr).expect("Int.neg fvar should parse");
    assert!(!result.is_constant());
    assert_eq!(result.get_coeff(0), -1);
    assert_eq!(result.constant, 0);
}

#[test]
fn test_linarith_parse_rat_neg_variable() {
    // Rat.neg x  =>  -x
    let x = mk_fvar(300);
    let expr = mk_app(mk_const("Rat.neg"), x);
    let result = parse_direct(&expr).expect("Rat.neg fvar should parse");
    assert!(!result.is_constant());
    assert_eq!(result.get_coeff(0), -1);
}

// ---- Unary negation: typeclass Neg.neg / HNeg.hNeg ----

#[test]
fn test_linarith_parse_neg_neg_typeclass() {
    // Neg.neg T inst x  =>  App(App(App(Neg.neg, T), inst), x)
    let neg = mk_const("Neg.neg");
    let ty = mk_const("Rat");
    let inst = mk_const("instNegRat");
    let x = mk_fvar(400);
    let expr = mk_app(mk_app(mk_app(neg, ty), inst), x);
    let result = parse_direct(&expr).expect("Neg.neg Rat inst x should parse");
    assert!(!result.is_constant());
    assert_eq!(result.get_coeff(0), -1);
    assert_eq!(result.constant, 0);
}

#[test]
fn test_linarith_parse_hneg_hneg_typeclass() {
    // HNeg.hNeg T T inst x  =>  App(App(App(App(HNeg.hNeg, T), T), inst), x)
    let hneg = mk_const("HNeg.hNeg");
    let ty = mk_const("Rat");
    let inst = mk_const("instHNegRat");
    let x = mk_fvar(500);
    let expr = mk_app(mk_app(mk_app(mk_app(hneg, ty.clone()), ty), inst), x);
    let result = parse_direct(&expr).expect("HNeg.hNeg Rat Rat inst x should parse");
    assert!(!result.is_constant());
    assert_eq!(result.get_coeff(0), -1);
    assert_eq!(result.constant, 0);
}

#[test]
fn test_linarith_parse_hneg_hneg_constant() {
    // HNeg.hNeg Rat Rat inst (Rat.one)  =>  -1
    let hneg = mk_const("HNeg.hNeg");
    let ty = mk_const("Rat");
    let inst = mk_const("instHNegRat");
    let one = mk_const("Rat.one");
    let expr = mk_app(mk_app(mk_app(mk_app(hneg, ty.clone()), ty), inst), one);
    let result = parse_direct(&expr).expect("HNeg.hNeg on Rat.one should parse");
    assert!(result.is_constant());
    assert_eq!(result.constant, -1);
}

// ---- Rat.le / Rat.lt comparison operator recognition ----

/// Helper: run parse_linear_constraint with fresh state.
fn parse_constraint(expr: &Expr) -> Option<LinearConstraint> {
    let mut var_map = std::collections::HashMap::new();
    let mut next_var = 0;
    parse_linear_constraint(expr, &mut var_map, &mut next_var, None)
}

/// Build a 4-arg comparison: `Op T inst lhs rhs`
/// Pattern: App(App(App(App(op, ty), inst), lhs), rhs)
fn mk_comparison(op: &str, lhs: Expr, rhs: Expr) -> Expr {
    let ty = mk_const("Rat");
    let inst = mk_const("instOrdRat");
    mk_app(mk_app(mk_app(mk_app(mk_const(op), ty), inst), lhs), rhs)
}

#[test]
fn test_linarith_parse_rat_le_constraint() {
    // Rat.le Rat instOrdRat x y  =>  Le(x - y)
    let x = mk_fvar(600);
    let y = mk_fvar(601);
    let expr = mk_comparison("Rat.le", x, y);
    let result = parse_constraint(&expr).expect("Rat.le should parse as Le constraint");
    assert!(matches!(result, LinearConstraint::Le(_)));
}

#[test]
fn test_linarith_parse_rat_lt_constraint() {
    // Rat.lt Rat instOrdRat x y  =>  Lt(x - y)
    let x = mk_fvar(700);
    let y = mk_fvar(701);
    let expr = mk_comparison("Rat.lt", x, y);
    let result = parse_constraint(&expr).expect("Rat.lt should parse as Lt constraint");
    assert!(matches!(result, LinearConstraint::Lt(_)));
}

#[test]
fn test_linarith_parse_rat_le_constants() {
    // Rat.le Rat inst (Rat.zero) (Rat.one)  =>  Le(0 - 1) = Le(-1)
    let expr = mk_comparison("Rat.le", mk_const("Rat.zero"), mk_const("Rat.one"));
    let result = parse_constraint(&expr).expect("Rat.le with constants should parse");
    assert!(matches!(result, LinearConstraint::Le(_)));
}

#[test]
fn test_linarith_parse_int_le_constraint() {
    // Int.le also recognized after WHNF reduction
    let x = mk_fvar(800);
    let y = mk_fvar(801);
    let expr = mk_comparison("Int.le", x, y);
    let result = parse_constraint(&expr).expect("Int.le should parse as Le constraint");
    assert!(matches!(result, LinearConstraint::Le(_)));
}

#[test]
fn test_linarith_parse_real_lt_constraint() {
    // Real.lt also recognized after WHNF reduction
    let x = mk_fvar(900);
    let y = mk_fvar(901);
    let expr = mk_comparison("Real.lt", x, y);
    let result = parse_constraint(&expr).expect("Real.lt should parse as Lt constraint");
    assert!(matches!(result, LinearConstraint::Lt(_)));
}

// ---- Unrecognized constants should return None ----

#[test]
fn test_linarith_parse_unknown_const_returns_none() {
    let expr = mk_const("Complex.zero");
    assert!(parse_direct(&expr).is_none());
}
