// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Nat reduction in the type checker.
//!
//! The `reduce_nat` function (tc/mod.rs:4045) and its helpers are entirely
//! untested. This module covers:
//! - Nat.succ reduction
//! - Nat.add, Nat.sub, Nat.mul, Nat.div, Nat.mod
//! - Nat.gcd, Nat.pow
//! - Nat.beq, Nat.ble predicates
//! - Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft, Nat.shiftRight
//! - Edge cases: overflow, division by zero, large exponents
//!
//! Tests work via `is_def_eq`, which calls `lazy_delta_reduction`, which calls
//! `reduce_nat` on Nat-headed applications with literal arguments.
//!
//! Filed as part of proof_coverage phase (P263).

use super::*;

/// Build a Nat literal expression.
fn nat(v: u64) -> Expr {
    Expr::nat_lit(v)
}

/// Build `Nat.succ(n)` as an application.
fn nat_succ(n: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), n)
}

/// Build a binary Nat operation: `op(a, b)`.
fn nat_binop(op_name: &str, a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string(op_name), vec![]), a),
        b,
    )
}

// =============================================================================
// Nat.succ reduction
// =============================================================================

#[test]
fn test_reduce_nat_succ_literal() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.succ(5) should be def_eq to 6
    assert!(
        tc.is_def_eq(&nat_succ(nat(5)), &nat(6)),
        "Nat.succ(5) should reduce to 6"
    );
}

#[test]
fn test_reduce_nat_succ_zero() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.succ(0) should be def_eq to 1
    assert!(
        tc.is_def_eq(&nat_succ(nat(0)), &nat(1)),
        "Nat.succ(0) should reduce to 1"
    );
}

#[test]
fn test_reduce_nat_succ_not_equal() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.succ(5) should NOT be def_eq to 5
    assert!(
        !tc.is_def_eq(&nat_succ(nat(5)), &nat(5)),
        "Nat.succ(5) should NOT be def_eq to 5"
    );
}

// =============================================================================
// Nat.add reduction
// =============================================================================

#[test]
fn test_reduce_nat_add_basic() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.add(2, 3) = 5
    assert!(
        tc.is_def_eq(&nat_binop("Nat.add", nat(2), nat(3)), &nat(5)),
        "Nat.add(2, 3) should reduce to 5"
    );
}

#[test]
fn test_reduce_nat_add_zero() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.add(0, 0) = 0
    assert!(
        tc.is_def_eq(&nat_binop("Nat.add", nat(0), nat(0)), &nat(0)),
        "Nat.add(0, 0) should reduce to 0"
    );

    // Nat.add(7, 0) = 7
    assert!(
        tc.is_def_eq(&nat_binop("Nat.add", nat(7), nat(0)), &nat(7)),
        "Nat.add(7, 0) should reduce to 7"
    );
}

#[test]
fn test_reduce_nat_add_commutativity() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.add(3, 7) = Nat.add(7, 3)
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.add", nat(3), nat(7)),
            &nat_binop("Nat.add", nat(7), nat(3))
        ),
        "Nat.add should be commutative on literals"
    );
}

// =============================================================================
// Nat.sub reduction (saturating subtraction)
// =============================================================================

#[test]
fn test_reduce_nat_sub_basic() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.sub(7, 3) = 4
    assert!(
        tc.is_def_eq(&nat_binop("Nat.sub", nat(7), nat(3)), &nat(4)),
        "Nat.sub(7, 3) should reduce to 4"
    );
}

#[test]
fn test_reduce_nat_sub_saturating() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.sub(3, 7) = 0 (saturating)
    assert!(
        tc.is_def_eq(&nat_binop("Nat.sub", nat(3), nat(7)), &nat(0)),
        "Nat.sub(3, 7) should saturate to 0"
    );
}

// =============================================================================
// Nat.mul reduction
// =============================================================================

#[test]
fn test_reduce_nat_mul_basic() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.mul(6, 7) = 42
    assert!(
        tc.is_def_eq(&nat_binop("Nat.mul", nat(6), nat(7)), &nat(42)),
        "Nat.mul(6, 7) should reduce to 42"
    );
}

#[test]
fn test_reduce_nat_mul_zero() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.mul(0, 100) = 0
    assert!(
        tc.is_def_eq(&nat_binop("Nat.mul", nat(0), nat(100)), &nat(0)),
        "Nat.mul(0, 100) should reduce to 0"
    );
}

// =============================================================================
// Nat.div reduction
// =============================================================================

#[test]
fn test_reduce_nat_div_basic() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.div(10, 3) = 3
    assert!(
        tc.is_def_eq(&nat_binop("Nat.div", nat(10), nat(3)), &nat(3)),
        "Nat.div(10, 3) should reduce to 3"
    );
}

#[test]
fn test_reduce_nat_div_by_zero() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.div(10, 0) = 0 (Lean 4 convention)
    assert!(
        tc.is_def_eq(&nat_binop("Nat.div", nat(10), nat(0)), &nat(0)),
        "Nat.div(10, 0) should reduce to 0 per Lean convention"
    );
}

// =============================================================================
// Nat.mod reduction
// =============================================================================

#[test]
fn test_reduce_nat_mod_basic() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.mod(10, 3) = 1
    assert!(
        tc.is_def_eq(&nat_binop("Nat.mod", nat(10), nat(3)), &nat(1)),
        "Nat.mod(10, 3) should reduce to 1"
    );
}

#[test]
fn test_reduce_nat_mod_by_zero() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.mod(10, 0) = 10 (Lean 4 convention: n % 0 = n)
    assert!(
        tc.is_def_eq(&nat_binop("Nat.mod", nat(10), nat(0)), &nat(10)),
        "Nat.mod(10, 0) should reduce to 10 per Lean convention"
    );
}

// =============================================================================
// Nat.gcd reduction
// =============================================================================

#[test]
fn test_reduce_nat_gcd() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.gcd(12, 8) = 4
    assert!(
        tc.is_def_eq(&nat_binop("Nat.gcd", nat(12), nat(8)), &nat(4)),
        "Nat.gcd(12, 8) should reduce to 4"
    );
}

#[test]
fn test_reduce_nat_gcd_with_zero() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.gcd(0, 5) = 5
    assert!(
        tc.is_def_eq(&nat_binop("Nat.gcd", nat(0), nat(5)), &nat(5)),
        "Nat.gcd(0, 5) should reduce to 5"
    );
}

// =============================================================================
// Nat.pow reduction
// =============================================================================

#[test]
fn test_reduce_nat_pow_basic() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.pow(2, 10) = 1024
    assert!(
        tc.is_def_eq(&nat_binop("Nat.pow", nat(2), nat(10)), &nat(1024)),
        "Nat.pow(2, 10) should reduce to 1024"
    );
}

#[test]
fn test_reduce_nat_pow_zero_exp() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.pow(5, 0) = 1
    assert!(
        tc.is_def_eq(&nat_binop("Nat.pow", nat(5), nat(0)), &nat(1)),
        "Nat.pow(5, 0) should reduce to 1"
    );
}

#[test]
fn test_reduce_nat_pow_large_exponent_no_reduce() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.pow(2, 2^24 + 1) should NOT reduce (exponent cap)
    let large_exp = (1u64 << 24) + 1;
    // Two different representations should not be def_eq if reduction fails
    // Nat.pow(2, large) won't reduce, so it stays as Nat.pow(2, large)
    // and won't match the literal
    assert!(
        !tc.is_def_eq(&nat_binop("Nat.pow", nat(2), nat(large_exp)), &nat(0)),
        "Nat.pow with huge exponent should not reduce"
    );
}

// =============================================================================
// Nat.beq / Nat.ble predicates
// =============================================================================

#[test]
fn test_reduce_nat_beq_equal() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.beq(5, 5) = Bool.true
    let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.beq", nat(5), nat(5)), &bool_true),
        "Nat.beq(5, 5) should reduce to Bool.true"
    );
}

#[test]
fn test_reduce_nat_beq_not_equal() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.beq(5, 6) = Bool.false
    let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.beq", nat(5), nat(6)), &bool_false),
        "Nat.beq(5, 6) should reduce to Bool.false"
    );
}

#[test]
fn test_reduce_nat_ble_true() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.ble(3, 5) = Bool.true
    let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.ble", nat(3), nat(5)), &bool_true),
        "Nat.ble(3, 5) should reduce to Bool.true"
    );
}

#[test]
fn test_reduce_nat_ble_false() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.ble(5, 3) = Bool.false
    let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.ble", nat(5), nat(3)), &bool_false),
        "Nat.ble(5, 3) should reduce to Bool.false"
    );
}

// =============================================================================
// Bitwise operations
// =============================================================================

#[test]
fn test_reduce_nat_land() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.land(0xFF, 0x0F) = 0x0F = 15
    assert!(
        tc.is_def_eq(&nat_binop("Nat.land", nat(0xFF), nat(0x0F)), &nat(15)),
        "Nat.land(0xFF, 0x0F) should reduce to 15"
    );
}

#[test]
fn test_reduce_nat_lor() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.lor(0xF0, 0x0F) = 0xFF = 255
    assert!(
        tc.is_def_eq(&nat_binop("Nat.lor", nat(0xF0), nat(0x0F)), &nat(0xFF)),
        "Nat.lor(0xF0, 0x0F) should reduce to 255"
    );
}

#[test]
fn test_reduce_nat_xor() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.xor(0xFF, 0x0F) = 0xF0 = 240
    assert!(
        tc.is_def_eq(&nat_binop("Nat.xor", nat(0xFF), nat(0x0F)), &nat(0xF0)),
        "Nat.xor(0xFF, 0x0F) should reduce to 240"
    );
}

#[test]
fn test_reduce_nat_shift_left() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.shiftLeft(1, 10) = 1024
    assert!(
        tc.is_def_eq(&nat_binop("Nat.shiftLeft", nat(1), nat(10)), &nat(1024)),
        "Nat.shiftLeft(1, 10) should reduce to 1024"
    );
}

#[test]
fn test_reduce_nat_shift_right() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.shiftRight(1024, 5) = 32
    assert!(
        tc.is_def_eq(&nat_binop("Nat.shiftRight", nat(1024), nat(5)), &nat(32)),
        "Nat.shiftRight(1024, 5) should reduce to 32"
    );
}

#[test]
fn test_reduce_nat_shift_left_large() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.shiftLeft(1, 64) should NOT reduce (shift >= 64)
    // It stays unreduced and won't match a literal
    assert!(
        !tc.is_def_eq(&nat_binop("Nat.shiftLeft", nat(1), nat(64)), &nat(0)),
        "Nat.shiftLeft(1, 64) should not reduce"
    );
}

#[test]
fn test_reduce_nat_shift_right_large() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.shiftRight(1024, 64) = 0 (shift >= 64 returns 0)
    assert!(
        tc.is_def_eq(&nat_binop("Nat.shiftRight", nat(1024), nat(64)), &nat(0)),
        "Nat.shiftRight(1024, 64) should reduce to 0"
    );
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_reduce_nat_add_not_wrong() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.add(2, 3) != 6
    assert!(
        !tc.is_def_eq(&nat_binop("Nat.add", nat(2), nat(3)), &nat(6)),
        "Nat.add(2, 3) should NOT be def_eq to 6"
    );
}

#[test]
fn test_reduce_nat_succ_nested() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.succ(Nat.succ(0)) = 2
    assert!(
        tc.is_def_eq(&nat_succ(nat_succ(nat(0))), &nat(2)),
        "Nat.succ(Nat.succ(0)) should reduce to 2"
    );
}

// =============================================================================
// Algorithm audit boundary condition tests (P1 iter 583)
// =============================================================================

/// Nat.shiftLeft boundary: y=63 is the last reducible shift for u64.
/// The implementation returns None for y >= 64. Verify the boundary is exact.
#[test]
fn test_reduce_nat_shift_left_boundary_63() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.shiftLeft(1, 63) = 2^63 = 9223372036854775808
    // This is the maximum shift that fits: 1u64.checked_shl(63) = Some(2^63)
    let expected = 1u64 << 63;
    assert!(
        tc.is_def_eq(&nat_binop("Nat.shiftLeft", nat(1), nat(63)), &nat(expected)),
        "Nat.shiftLeft(1, 63) should reduce to 2^63"
    );
}

/// Nat.shiftLeft: y=63 with base > 1 would overflow u64 — returns None (unreduced).
/// Lean 4 uses arbitrary-precision integers (mpz) so 2 << 63 = 2^64 is exact.
/// With u64 representation, we must leave such shifts unreduced rather than
/// silently wrapping to 0.
#[test]
fn test_reduce_nat_shift_left_overflow_returns_none() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.shiftLeft(2, 63) would produce 2^64 which overflows u64.
    // Must NOT reduce (returns None) — not silently wrap to 0.
    assert!(
        !tc.is_def_eq(&nat_binop("Nat.shiftLeft", nat(2), nat(63)), &nat(0)),
        "Nat.shiftLeft(2, 63) should NOT reduce to 0 (overflow leaves unreduced)"
    );
}

/// Nat.shiftRight boundary: y=63 should reduce to 0 for any value < 2^63.
#[test]
fn test_reduce_nat_shift_right_boundary_63() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.shiftRight(u64::MAX, 63) = 1 (only the top bit survives)
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.shiftRight", nat(u64::MAX), nat(63)),
            &nat(u64::MAX >> 63)
        ),
        "Nat.shiftRight(u64::MAX, 63) should reduce to 1"
    );
}

/// Nat.add: u64::MAX + 1 overflows, checked_add returns None.
/// Verify no panic and no incorrect reduction.
#[test]
fn test_reduce_nat_add_u64_overflow_no_panic() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.add(u64::MAX, 1) overflows u64. checked_add returns None.
    // The expression stays unreduced. It should NOT equal any literal.
    assert!(
        !tc.is_def_eq(&nat_binop("Nat.add", nat(u64::MAX), nat(1)), &nat(0)),
        "Nat.add(u64::MAX, 1) should not reduce (u64 overflow)"
    );
}

/// Nat.mul: boundary at u64 overflow.
/// 2^32 * 2^32 = 2^64, overflows u64.
#[test]
fn test_reduce_nat_mul_u64_overflow_no_panic() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let two_pow_32 = 1u64 << 32;
    // 2^32 * 2^32 = 2^64, overflows u64. checked_mul returns None.
    assert!(
        !tc.is_def_eq(
            &nat_binop("Nat.mul", nat(two_pow_32), nat(two_pow_32)),
            &nat(0)
        ),
        "Nat.mul(2^32, 2^32) should not reduce (u64 overflow)"
    );
}

/// Nat.succ: u64::MAX + 1 overflows, checked_add returns None.
#[test]
fn test_reduce_nat_succ_u64_max_no_panic() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.succ(u64::MAX) overflows u64. checked_add returns None.
    // The expression stays unreduced.
    assert!(
        !tc.is_def_eq(&nat_succ(nat(u64::MAX)), &nat(0)),
        "Nat.succ(u64::MAX) should not reduce (u64 overflow)"
    );
}

/// Nat.pow: boundary at exponent cap. 2^24 is the max exponent.
/// pow(2, 2^24) may overflow u64 (checked_pow returns None for 2^(2^24)),
/// but the exponent cap check should pass since v2 <= REDUCE_POW_MAX_EXP.
#[test]
fn test_reduce_nat_pow_at_exponent_cap() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.pow(1, 2^24) = 1 (1^n = 1 for all n)
    // This tests that the exponent cap allows exactly 2^24.
    let max_exp = 1u64 << 24;
    assert!(
        tc.is_def_eq(&nat_binop("Nat.pow", nat(1), nat(max_exp)), &nat(1)),
        "Nat.pow(1, 2^24) should reduce to 1"
    );
}

/// Nat.pow: verify that pow(2, 63) = 2^63 (within u64 range and exponent cap).
#[test]
fn test_reduce_nat_pow_2_63() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^63 = 9223372036854775808, fits in u64
    let expected = 1u64 << 63;
    assert!(
        tc.is_def_eq(&nat_binop("Nat.pow", nat(2), nat(63)), &nat(expected)),
        "Nat.pow(2, 63) should reduce to 2^63"
    );
}

/// Nat.pow: pow(2, 64) overflows u64 even though exponent is within cap.
/// checked_pow returns None, so the expression stays unreduced.
#[test]
fn test_reduce_nat_pow_2_64_overflow() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^64 overflows u64. checked_pow returns None.
    assert!(
        !tc.is_def_eq(&nat_binop("Nat.pow", nat(2), nat(64)), &nat(0)),
        "Nat.pow(2, 64) should not reduce (u64 overflow)"
    );
}
