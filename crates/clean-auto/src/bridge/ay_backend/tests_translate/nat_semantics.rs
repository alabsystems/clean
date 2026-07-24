// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat/Int arithmetic semantics tests (#2243).

use super::support::{build_eq_expr, build_nat_binop};
use super::*;
use clean_kernel::Expr;

/// Test Nat.sub monus semantics: Nat.sub(3, 5) = 0
///
/// Lean's Nat.sub is truncated subtraction (monus): max(a - b, 0).
/// Nat.sub 3 5 = 0, not -2. This test verifies the ay translation
/// encodes monus correctly via ite(a >= b, a - b, 0).
#[test]
fn test_nat_sub_monus_underflow_equals_zero() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let goal = build_eq_expr(build_nat_binop("Nat.sub", 3, 5), Expr::nat_lit(0));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(
        result,
        "Nat.sub(3, 5) = 0 should be provable (monus semantics)"
    );
}

/// Test Nat.sub monus semantics: Nat.sub(5, 3) = 2
///
/// When a >= b, Nat.sub a b = a - b (regular subtraction).
#[test]
fn test_nat_sub_monus_normal_subtraction() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let goal = build_eq_expr(build_nat_binop("Nat.sub", 5, 3), Expr::nat_lit(2));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(result, "Nat.sub(5, 3) = 2 should be provable");
}

/// Test Nat.div total semantics: Nat.div(5, 0) = 0
///
/// Lean's Nat.div is total: div by zero returns 0.
#[test]
fn test_nat_div_by_zero_equals_zero() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let goal = build_eq_expr(build_nat_binop("Nat.div", 5, 0), Expr::nat_lit(0));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(
        result,
        "Nat.div(5, 0) = 0 should be provable (total division)"
    );
}

/// Test Nat.mod total semantics: Nat.mod(5, 0) = 5
///
/// Lean's Nat.mod is total: mod by zero returns the dividend.
#[test]
fn test_nat_mod_by_zero_equals_dividend() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let goal = build_eq_expr(build_nat_binop("Nat.mod", 5, 0), Expr::nat_lit(5));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(
        result,
        "Nat.mod(5, 0) = 5 should be provable (total modulo)"
    );
}

/// Test that Int.sub is NOT monus (can produce negative results)
///
/// Int.sub(3, 5) should NOT equal 0; it equals -2.
/// This ensures the Nat.sub fix doesn't accidentally affect Int.sub.
#[test]
fn test_int_sub_is_not_monus() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    // Use build_nat_binop with Int.sub — works because the helper
    // just constructs Expr nodes; the op name determines translation
    let goal = build_eq_expr(build_nat_binop("Int.sub", 3, 5), Expr::nat_lit(0));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(
        !result,
        "Int.sub(3, 5) = 0 should NOT be provable (it equals -2)"
    );
}
