// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct unit tests for arith_chain.rs functions (#302 proof coverage).
//!
//! Exercises `detect_sort`, `combine_ops`, `mk_le_of_lt`, `mk_le_refl`,
//! `mk_lt_irrefl_false` for Int and Real sorts. Prior to this file,
//! only Nat sort had any direct or indirect test coverage.

use super::super::arith_chain::{
    combine_ops, detect_sort, mk_le_of_lt, mk_le_refl, mk_lt_irrefl_false, ArithSort, CmpOp,
};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

fn assert_head_const_name(expr: &Expr, expected: &str) {
    let head = expr.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if name.to_string() == expected),
        "expected proof term head {expected}, got {head:?}"
    );
}

// ================================================================
// detect_sort unit tests for Int and Real
// ================================================================

#[test]
fn test_detect_sort_nat() {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    assert_eq!(detect_sort(&nat), Some(ArithSort::Nat));
}

#[test]
fn test_detect_sort_int() {
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    assert_eq!(detect_sort(&int), Some(ArithSort::Int));
}

#[test]
fn test_detect_sort_real() {
    let real = Expr::const_(Name::from_string("Real"), vec![]);
    assert_eq!(detect_sort(&real), Some(ArithSort::Real));
}

#[test]
fn test_detect_sort_unknown_returns_none() {
    let unknown = Expr::const_(Name::from_string("Complex"), vec![]);
    assert_eq!(detect_sort(&unknown), None);
}

#[test]
fn test_detect_sort_non_const_returns_none() {
    assert_eq!(detect_sort(&Expr::bvar(0)), None);
}

// ================================================================
// combine_ops unit tests
// ================================================================

#[test]
fn test_combine_ops_le_le_is_le() {
    assert_eq!(combine_ops(CmpOp::Le, CmpOp::Le), CmpOp::Le);
}

#[test]
fn test_combine_ops_le_lt_is_lt() {
    assert_eq!(combine_ops(CmpOp::Le, CmpOp::Lt), CmpOp::Lt);
}

#[test]
fn test_combine_ops_lt_le_is_lt() {
    assert_eq!(combine_ops(CmpOp::Lt, CmpOp::Le), CmpOp::Lt);
}

#[test]
fn test_combine_ops_lt_lt_is_lt() {
    assert_eq!(combine_ops(CmpOp::Lt, CmpOp::Lt), CmpOp::Lt);
}

// ================================================================
// mk_le_of_lt sort-gating tests
// ================================================================

#[test]
fn test_mk_le_of_lt_nat_produces_proof() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let h = Expr::const_(Name::from_string("h"), vec![]);

    let result = mk_le_of_lt(ArithSort::Nat, &a, &b, &h);
    assert!(result.is_some(), "Nat le_of_lt should produce a proof");
    assert_head_const_name(&result.unwrap(), "Nat.le_of_lt");
}

#[test]
fn test_mk_le_of_lt_int_produces_proof() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let h = Expr::const_(Name::from_string("h"), vec![]);

    let result = mk_le_of_lt(ArithSort::Int, &a, &b, &h);
    assert!(result.is_some(), "Int le_of_lt should produce a proof");
    assert_head_const_name(&result.unwrap(), "Int.le_of_lt");
}

#[test]
fn test_mk_le_of_lt_real_returns_none() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let h = Expr::const_(Name::from_string("h"), vec![]);

    let result = mk_le_of_lt(ArithSort::Real, &a, &b, &h);
    assert!(
        result.is_none(),
        "Real le_of_lt must return None (not supported)"
    );
}

// ================================================================
// mk_le_refl for Int and Real
// ================================================================

#[test]
fn test_mk_le_refl_int() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let proof = mk_le_refl(ArithSort::Int, &a);
    assert_head_const_name(&proof, "Int.le_refl");
}

#[test]
fn test_mk_le_refl_real() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let proof = mk_le_refl(ArithSort::Real, &a);
    assert_head_const_name(&proof, "Real.le_refl");
}

// ================================================================
// mk_lt_irrefl_false for Int and Real
// ================================================================

#[test]
fn test_mk_lt_irrefl_false_int() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let h = Expr::const_(Name::from_string("h"), vec![]);
    let proof = mk_lt_irrefl_false(ArithSort::Int, &a, &h);
    assert_head_const_name(&proof, "Int.lt_irrefl");
}

#[test]
fn test_mk_lt_irrefl_false_real() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let h = Expr::const_(Name::from_string("h"), vec![]);
    let proof = mk_lt_irrefl_false(ArithSort::Real, &a, &h);
    assert_head_const_name(&proof, "Real.lt_irrefl");
}
