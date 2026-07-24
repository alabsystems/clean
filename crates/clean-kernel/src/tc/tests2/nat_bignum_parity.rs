// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arbitrary-precision Nat literal reduction regression tests (kernel parity
//! gap #9).
//!
//! The tc-side `reduce_nat` (tc/reduction/nat.rs) used to extract operands via
//! u128 (capped at 2 limbs), so closed Nats >= 2^128 stayed unreduced — the
//! last computational divergence from Lean 4's mpz kernel. `reduce_nat` now
//! computes on the full multi-limb `BigNat` path (`expr/bignat_ops.rs`).
//!
//! These tests pin the behavior at and beyond the old u128 boundary: each op is
//! exercised on >= 2^128 (3-limb) operands through BOTH `whnf` and `is_def_eq`,
//! with the expected literal computed directly via the same `BigNat` ops the
//! reducer calls (so the test is a cross-check on the wiring, not a tautology).

use super::*;
use crate::expr::{BigNat, ExprKind, Literal};

/// Build a Nat literal from a u64.
fn nat(v: u64) -> Expr {
    Expr::nat_lit(v)
}

/// Build a Nat literal directly from a BigNat value.
fn big(n: BigNat) -> Expr {
    Expr::bignat_lit(n)
}

/// 2^128 as a 3-limb BigNat (limbs [0, 0, 1], little-endian).
fn two_pow_128() -> BigNat {
    BigNat::Big(vec![0, 0, 1])
}

/// Build `Nat.succ(n)`.
fn nat_succ(n: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), n)
}

/// Build a binary Nat operation `op(a, b)`.
fn nat_binop(op_name: &str, a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string(op_name), vec![]), a),
        b,
    )
}

/// Bool.true / Bool.false constants.
fn bool_true() -> Expr {
    Expr::const_(Name::from_string("Bool.true"), vec![])
}
fn bool_false() -> Expr {
    Expr::const_(Name::from_string("Bool.false"), vec![])
}

/// Extract the BigNat from a reduced Nat-literal expression (panics otherwise).
fn expect_bignat(e: &Expr) -> BigNat {
    match &e.kind {
        ExprKind::Lit(Literal::Nat(n)) => n.clone(),
        other => panic!("expected reduced Nat literal, got {other:?}"),
    }
}

/// Assert that `op(a, b)` reduces (via whnf AND is_def_eq) to `expected`.
fn assert_binop_reduces(op: &str, a: Expr, b: Expr, expected: &Expr) {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let e = nat_binop(op, a, b);

    let reduced = tc.whnf(&e);
    assert_eq!(
        expect_bignat(&reduced),
        expect_bignat(expected),
        "{op}: whnf result mismatch"
    );
    assert!(
        tc.is_def_eq(&e, expected),
        "{op}: is_def_eq with expected literal should hold"
    );
}

// =============================================================================
// 3-limb (>= 2^128) arithmetic — each op cross-checked against the BigNat ops.
// =============================================================================

#[test]
fn test_bignum_add_3limb_reduces() {
    let a = two_pow_128(); // 2^128
    let b = BigNat::Small(12345);
    let expected = big(a.checked_add_big(&b));
    assert_binop_reduces("Nat.add", big(a), big(b), &expected);
}

#[test]
fn test_bignum_sub_3limb_reduces() {
    // (2^128 + 5) - 2^128 = 5, exercising multi-limb borrow.
    let a = two_pow_128().checked_add_big(&BigNat::Small(5));
    let b = two_pow_128();
    let expected = big(a.saturating_sub_big(&b));
    assert_eq!(expect_bignat(&expected), BigNat::Small(5));
    assert_binop_reduces("Nat.sub", big(a), big(b), &expected);
}

#[test]
fn test_bignum_mul_3limb_reduces() {
    // 2^128 * 7 stays within the 16-limb bound.
    let a = two_pow_128();
    let b = BigNat::Small(7);
    let expected = big(a.checked_mul_big(&b).expect("within 16-limb bound"));
    assert_binop_reduces("Nat.mul", big(a), big(b), &expected);
}

#[test]
fn test_bignum_div_3limb_reduces() {
    // (2^128 + 100) / 2.
    let a = two_pow_128().checked_add_big(&BigNat::Small(100));
    let b = BigNat::Small(2);
    let expected = big(a.checked_div_big(&b));
    assert_binop_reduces("Nat.div", big(a), big(b), &expected);
}

#[test]
fn test_bignum_mod_3limb_reduces() {
    // (2^128 + 7) % 3.
    let a = two_pow_128().checked_add_big(&BigNat::Small(7));
    let b = BigNat::Small(3);
    let expected = big(a.checked_mod_big(&b));
    assert_binop_reduces("Nat.mod", big(a), big(b), &expected);
}

#[test]
fn test_bignum_gcd_3limb_reduces() {
    // gcd(2^128, 2^130) = 2^128 (2^130 = 2^128 * 4).
    let a = two_pow_128();
    let b = a.checked_mul_big(&BigNat::Small(4)).expect("within bound");
    let expected = big(a.gcd_big(&b));
    assert_eq!(expect_bignat(&expected), a);
    assert_binop_reduces("Nat.gcd", big(a), big(b), &expected);
}

#[test]
fn test_bignum_pow_small_3limb_base_reduces() {
    // (2^128)^2 = 2^256, well within the 1024-bit bound.
    let base = two_pow_128();
    let exp = BigNat::Small(2);
    let expected = big(base.checked_pow_big(&exp).expect("within 1024-bit bound"));
    assert_binop_reduces("Nat.pow", big(base), big(exp), &expected);
}

#[test]
fn test_bignum_beq_3limb_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let a = two_pow_128();
    let a_plus_1 = a.checked_add_big(&BigNat::Small(1));

    // 2^128 == 2^128 -> true
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.beq", big(a.clone()), big(a.clone())),
            &bool_true()
        ),
        "Nat.beq(2^128, 2^128) should reduce to Bool.true"
    );
    assert_eq!(
        tc.whnf(&nat_binop("Nat.beq", big(a.clone()), big(a.clone()))),
        bool_true()
    );

    // 2^128 == 2^128 + 1 -> false
    assert!(
        tc.is_def_eq(&nat_binop("Nat.beq", big(a), big(a_plus_1)), &bool_false()),
        "Nat.beq(2^128, 2^128+1) should reduce to Bool.false"
    );
}

#[test]
fn test_bignum_ble_3limb_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let a = two_pow_128();
    let a_plus_1 = a.checked_add_big(&BigNat::Small(1));

    // 2^128 <= 2^128 + 1 -> true
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.ble", big(a.clone()), big(a_plus_1.clone())),
            &bool_true()
        ),
        "Nat.ble(2^128, 2^128+1) should reduce to Bool.true"
    );
    // 2^128 + 1 <= 2^128 -> false
    assert!(
        tc.is_def_eq(&nat_binop("Nat.ble", big(a_plus_1), big(a)), &bool_false()),
        "Nat.ble(2^128+1, 2^128) should reduce to Bool.false"
    );
}

// =============================================================================
// Soundness sanity: (2^200 + 1) - 2^200 == 1.
// =============================================================================

#[test]
fn test_bignum_soundness_add_sub_roundtrip() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^200 = limbs [0, 0, 0, 2^8] (200 = 3*64 + 8).
    let two_pow_200 = BigNat::Big(vec![0, 0, 0, 1u64 << 8]);
    let plus_one = two_pow_200.checked_add_big(&BigNat::Small(1));

    // (2^200 + 1) - 2^200 == 1
    let expr = nat_binop("Nat.sub", big(plus_one), big(two_pow_200));
    assert_eq!(
        expect_bignat(&tc.whnf(&expr)),
        BigNat::Small(1),
        "(2^200 + 1) - 2^200 should reduce to 1"
    );
    assert!(
        tc.is_def_eq(&expr, &nat(1)),
        "(2^200 + 1) - 2^200 should be def_eq to 1"
    );
}

#[test]
fn test_bignum_succ_3limb_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // succ(2^128) = 2^128 + 1.
    let a = two_pow_128();
    let expected = big(a.checked_add_big(&BigNat::Small(1)));
    let e = nat_succ(big(a));
    assert_eq!(expect_bignat(&tc.whnf(&e)), expect_bignat(&expected));
    assert!(
        tc.is_def_eq(&e, &expected),
        "Nat.succ(2^128) should reduce to 2^128 + 1"
    );
}

// =============================================================================
// Allocation-bound guard: results past the 16-limb / 1024-bit cap stay stuck.
// =============================================================================

#[test]
fn test_bignum_pow_past_bound_stays_unreduced() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^128 raised to a large exponent would exceed 1024 bits; checked_pow_big
    // returns None there, so the application stays stuck (same bound the env
    // native reducer uses). 2 ^ 2000 has exponent > 1023.
    let e = nat_binop("Nat.pow", nat(2), nat(2000));
    let reduced = tc.whnf(&e);
    // Stays as the original application (head is still Nat.pow), not a literal.
    assert!(
        !matches!(reduced.kind, ExprKind::Lit(Literal::Nat(_))),
        "Nat.pow(2, 2000) should stay unreduced (exceeds 1024-bit bound)"
    );
}
