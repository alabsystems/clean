// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended Bool/Nat native reducer functions (native_reducers_bool_ext.rs).
//!
//! This module tests Bool.beq and Nat.gcd reducers. Tests for Nat.div, Nat.mod,
//! Nat.beq, Nat.ble, Nat.pow, and bitwise/shift operations are in
//! native_reducers_arith_tests.rs (Part of #3251).

use super::*;
use crate::expr::Literal;

// === Assertion helpers ===

fn assert_nat_result(result: Option<Expr>, expected: u64) {
    let result = result.expect("expected reducer to produce a Nat literal");
    if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
        assert_eq!(n.to_u64(), Some(expected));
    } else {
        panic!("expected Nat literal {expected}, got {:?}", result);
    }
}

fn assert_bool_result(result: Option<Expr>, expected: bool) {
    let result = result.expect("expected reducer to produce a Bool constructor");
    let head = result.get_app_fn();
    let expected_name = if expected { "Bool.true" } else { "Bool.false" };
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), expected_name);
    } else {
        panic!("expected {expected_name}, got {:?}", head);
    }
}

fn mk_bool_expr(val: bool) -> Expr {
    mk_bool(val)
}

// === Bool.beq tests ===

#[test]
fn test_reduce_bool_beq_true_true() {
    let a = mk_bool_expr(true);
    let b = mk_bool_expr(true);
    assert_bool_result(reduce_bool_beq(&[&a, &b]), true);
}

#[test]
fn test_reduce_bool_beq_true_false() {
    let a = mk_bool_expr(true);
    let b = mk_bool_expr(false);
    assert_bool_result(reduce_bool_beq(&[&a, &b]), false);
}

#[test]
fn test_reduce_bool_beq_false_false() {
    let a = mk_bool_expr(false);
    let b = mk_bool_expr(false);
    assert_bool_result(reduce_bool_beq(&[&a, &b]), true);
}

#[test]
fn test_reduce_bool_beq_false_true() {
    let a = mk_bool_expr(false);
    let b = mk_bool_expr(true);
    assert_bool_result(reduce_bool_beq(&[&a, &b]), false);
}

#[test]
fn test_reduce_bool_beq_insufficient_args() {
    let a = mk_bool_expr(true);
    assert!(reduce_bool_beq(&[&a]).is_none());
    assert!(reduce_bool_beq(&[]).is_none());
}

#[test]
fn test_reduce_bool_beq_non_bool_returns_none() {
    let nat = Expr::nat_lit(42);
    let b = mk_bool_expr(true);
    assert!(reduce_bool_beq(&[&nat, &b]).is_none());
}

// === Nat.gcd tests ===

#[test]
fn test_reduce_nat_gcd_basic() {
    let a = Expr::nat_lit(12);
    let b = Expr::nat_lit(8);
    assert_nat_result(reduce_nat_gcd(&[&a, &b]), 4);
}

#[test]
fn test_reduce_nat_gcd_with_zero() {
    let a = Expr::nat_lit(12);
    let b = Expr::nat_lit(0);
    assert_nat_result(reduce_nat_gcd(&[&a, &b]), 12);
}

#[test]
fn test_reduce_nat_gcd_coprime() {
    let a = Expr::nat_lit(7);
    let b = Expr::nat_lit(13);
    assert_nat_result(reduce_nat_gcd(&[&a, &b]), 1);
}

#[test]
fn test_reduce_nat_gcd_insufficient_args() {
    let a = Expr::nat_lit(12);
    assert!(reduce_nat_gcd(&[&a]).is_none());
    assert!(reduce_nat_gcd(&[]).is_none());
}

#[test]
fn test_reduce_nat_gcd_non_literal_returns_none() {
    let bvar = Expr::bvar(0);
    let nat = Expr::nat_lit(1);
    assert!(reduce_nat_gcd(&[&bvar, &nat]).is_none());
}

// === Cross-cutting edge case tests ===

#[test]
fn test_all_reducers_non_literal_args_return_none() {
    // Use a bound variable expression, which is not a literal
    let bvar = Expr::bvar(0);
    let nat = Expr::nat_lit(1);
    let bool_true = mk_bool_expr(true);

    assert!(reduce_bool_beq(&[&bvar, &bool_true]).is_none());
    assert!(reduce_nat_gcd(&[&bvar, &nat]).is_none());
}

// === Registration test ===

#[test]
fn test_bool_ext_reducers_registered() {
    let mut env = Environment::new();
    env.init_bool_ext_native_reducers();

    let expected_names = ["Bool.beq", "Nat.gcd"];

    for name_str in &expected_names {
        let name = Name::from_string(name_str);
        assert!(
            env.get_native_reducer(&name).is_some(),
            "expected native reducer for {name_str} to be registered"
        );
    }
}
