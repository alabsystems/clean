// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4 parity tests for clean's kernel type checker.
//!
//! Tests for 6 divergences identified by conformance audit (TL-TT, #3134):
//!
//! 1. **App-vs-App struct-eta gap** (REAL): structural.rs:27-29 — App comparison
//!    doesn't fall through to try_structure_eta_expansion.
//! 2. **Nat.pow base limited to u64** (CLOSED — kernel parity gap #9):
//!    reduce_nat_pow now uses checked_pow_big over the full BigNat base AND
//!    exponent (bounded at 1024 bits / exp 1023). BigNat bases reduce.
//! 3. **Nat arithmetic limited to u64/u128** (CLOSED — kernel parity gap #9):
//!    reduce_nat now extracts full BigNats and computes via the multi-limb
//!    bignat_ops path, matching Lean 4's arbitrary-precision mpz kernel.
//! 4. **Bidirectional proof-by-reflection** (BENIGN EXTENSION): clean checks
//!    both directions for reduceBool (Lean 4 only checks one direction).
//! 5. **MData asymmetric stripping** (BENIGN EXTENSION): clean strips MData
//!    from left side only in quick_is_def_eq (Lean 4 strips via WHNF).
//! 6. **lazy_delta_step_both fallback** (BENIGN EXTENSION): clean tries
//!    unfolding other side as fallback when primary unfold fails.
//!
//! Part of #3134.

use super::*;
use crate::expr::{BigNat, Literal, MDataMap};
use std::sync::Arc;

// =============================================================================
// Helpers
// =============================================================================

/// Build a Nat literal expression from u64.
fn nat(v: u64) -> Expr {
    Expr::nat_lit(v)
}

/// Build a BigNat literal from two u64 limbs (little-endian).
/// Represents a value = lo + hi * 2^64.
fn bignat_2limb(lo: u64, hi: u64) -> Expr {
    Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![lo, hi]))))
}

/// Build a BigNat literal from three u64 limbs (little-endian).
/// Values exceeding u128 — these should stay stuck in clean.
fn bignat_3limb(lo: u64, mid: u64, hi: u64) -> Expr {
    Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![lo, mid, hi]))))
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

/// Wrap an expression in MData with empty metadata.
fn mdata(inner: Expr) -> Expr {
    Expr::from_kind(ExprKind::MData(MDataMap::new(), Arc::new(inner)))
}

/// Bool.true constant.
fn bool_true() -> Expr {
    Expr::const_(Name::from_string("Bool.true"), vec![])
}

/// Bool.false constant.
fn bool_false() -> Expr {
    Expr::const_(Name::from_string("Bool.false"), vec![])
}

// =============================================================================
// Divergence 2: Nat.pow base limited to u64
// =============================================================================

/// Nat.pow with BigNat base reduces at all exponents within the allocation
/// bound. PIN UPDATE (kernel parity gap #9): BigNat^(exp >= 2) now reduces
/// via checked_pow_big (was stuck — "no mpz"). n^0 = 1 and n^1 = n unchanged.
#[test]
fn test_nat_pow_bignat_base() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let big_base = bignat_2limb(1, 1); // = 2^64 + 1

    // BigNat^1 = BigNat (identity exponent reduces)
    assert!(
        tc.is_def_eq(&nat_binop("Nat.pow", big_base.clone(), nat(1)), &big_base),
        "Nat.pow(BigNat, 1) should reduce to BigNat (n^1 = n)"
    );

    // BigNat^0 = 1 (zero exponent reduces)
    assert!(
        tc.is_def_eq(&nat_binop("Nat.pow", big_base.clone(), nat(0)), &nat(1)),
        "Nat.pow(BigNat, 0) should reduce to 1 (n^0 = 1)"
    );

    // BigNat^2 now reduces: (2^64 + 1)^2 = 2^128 + 2^65 + 1 = limbs [1, 2, 1].
    let squared = bignat_3limb(1, 2, 1);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.pow", big_base, nat(2)), &squared),
        "Nat.pow(2^64+1, 2) should reduce to 2^128+2^65+1 (arbitrary precision)"
    );
}

/// Nat.pow with u64 base and small exponent should still work.
#[test]
fn test_nat_pow_u64_base_normal() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 3^4 = 81
    assert!(
        tc.is_def_eq(&nat_binop("Nat.pow", nat(3), nat(4)), &nat(81)),
        "Nat.pow(3, 4) should reduce to 81"
    );
}

/// Nat.pow producing a result > u64 but within u128 should produce BigNat.
#[test]
fn test_nat_pow_result_exceeds_u64() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^64 overflows u64 but fits in u128.
    // Result: BigNat::Big([0, 1]) = 2^64.
    let expected = bignat_2limb(0, 1);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.pow", nat(2), nat(64)), &expected),
        "Nat.pow(2, 64) should reduce to BigNat(2^64)"
    );
}

/// Nat.pow(0, 0) = 1 (standard convention).
#[test]
fn test_nat_pow_zero_zero() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert!(
        tc.is_def_eq(&nat_binop("Nat.pow", nat(0), nat(0)), &nat(1)),
        "Nat.pow(0, 0) should reduce to 1"
    );
}

// =============================================================================
// Divergence 3: Nat arithmetic limited to u64/u128
// =============================================================================

/// Nat.add with u128-range inputs should produce correct BigNat results.
#[test]
fn test_nat_add_u64_overflow_produces_bignat() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // u64::MAX + 1 = 2^64 = BigNat::Big([0, 1])
    let expected = bignat_2limb(0, 1);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.add", nat(u64::MAX), nat(1)), &expected),
        "Nat.add(u64::MAX, 1) should produce BigNat 2^64"
    );
}

/// Nat.add with two large u64 values producing a 2-limb BigNat.
#[test]
fn test_nat_add_two_large_u64() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // (2^63) + (2^63) = 2^64 = BigNat::Big([0, 1])
    let half = 1u64 << 63;
    let expected = bignat_2limb(0, 1);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.add", nat(half), nat(half)), &expected),
        "Nat.add(2^63, 2^63) should produce BigNat 2^64"
    );
}

/// Nat.mul with u64 overflow should produce BigNat.
#[test]
fn test_nat_mul_u64_overflow_produces_bignat() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^32 * 2^32 = 2^64 = BigNat::Big([0, 1])
    let two_pow_32 = 1u64 << 32;
    let expected = bignat_2limb(0, 1);
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.mul", nat(two_pow_32), nat(two_pow_32)),
            &expected
        ),
        "Nat.mul(2^32, 2^32) should produce BigNat 2^64"
    );
}

/// Nat.succ at u64::MAX boundary should produce BigNat.
#[test]
fn test_nat_succ_u64_max_produces_bignat() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.succ(u64::MAX) = 2^64 = BigNat::Big([0, 1])
    let expected = bignat_2limb(0, 1);
    assert!(
        tc.is_def_eq(&nat_succ(nat(u64::MAX)), &expected),
        "Nat.succ(u64::MAX) should produce BigNat 2^64"
    );
}

/// PIN UPDATE (kernel parity gap #9): values exceeding u128 (3-limb BigNat)
/// now reduce via the arbitrary-precision BigNat path, matching Lean 4's mpz.
/// Previously stuck at the u128 cap.
#[test]
fn test_nat_add_3limb_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // (2^128 + 1) + 1 = 2^128 + 2 = limbs [2, 0, 1].
    let big3 = bignat_3limb(1, 0, 1); // = 2^128 + 1
    let expected = bignat_3limb(2, 0, 1); // = 2^128 + 2
    assert!(
        tc.is_def_eq(&nat_binop("Nat.add", big3, nat(1)), &expected),
        "Nat.add(2^128+1, 1) should reduce to 2^128+2 (arbitrary precision)"
    );
}

/// BigNat comparison (beq) with 2-limb values should work.
#[test]
fn test_nat_beq_bignat_equal() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // beq(2^64, 2^64) should reduce to Bool.true
    let big = bignat_2limb(0, 1);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.beq", big.clone(), big), &bool_true()),
        "Nat.beq(2^64, 2^64) should reduce to Bool.true"
    );
}

/// BigNat comparison (beq) with different 2-limb values.
#[test]
fn test_nat_beq_bignat_not_equal() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let a = bignat_2limb(0, 1); // 2^64
    let b = bignat_2limb(1, 1); // 2^64 + 1
    assert!(
        tc.is_def_eq(&nat_binop("Nat.beq", a, b), &bool_false()),
        "Nat.beq(2^64, 2^64+1) should reduce to Bool.false"
    );
}

/// BigNat comparison (ble) with 2-limb values.
#[test]
fn test_nat_ble_bignat() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let a = bignat_2limb(0, 1); // 2^64
    let b = bignat_2limb(1, 1); // 2^64 + 1
    assert!(
        tc.is_def_eq(&nat_binop("Nat.ble", a, b), &bool_true()),
        "Nat.ble(2^64, 2^64+1) should reduce to Bool.true"
    );
}

/// PIN UPDATE (kernel parity gap #9): ble on 3-limb values now reduces.
/// Previously stuck because 3-limb values could not convert to u128.
#[test]
fn test_nat_ble_3limb_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let big3 = bignat_3limb(0, 0, 1); // 2^128
                                      // 2^128 <= 0 is false -> reduces to Bool.false.
    assert!(
        tc.is_def_eq(&nat_binop("Nat.ble", big3, nat(0)), &bool_false()),
        "Nat.ble(2^128, 0) should reduce to Bool.false (arbitrary precision)"
    );
}

/// PIN UPDATE (kernel parity gap #9): Nat.div on BigNat operands now reduces
/// via checked_div_big. Previously stuck on the u64-only get_nat_val path.
#[test]
fn test_nat_div_bignat_operands_reduce() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let big = bignat_2limb(100, 1); // = 100 + 2^64
                                    // (100 + 2^64) / 2 = 9223372036854775858 (fits in u64).
    let expected = nat(9_223_372_036_854_775_858);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.div", big, nat(2)), &expected),
        "Nat.div(100+2^64, 2) should reduce (arbitrary precision)"
    );
}

/// PIN UPDATE (kernel parity gap #9): Nat.mod on BigNat operands now reduces
/// via checked_mod_big. Previously stuck on the u64-only get_nat_val path.
#[test]
fn test_nat_mod_bignat_operands_reduce() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let big = bignat_2limb(7, 1); // = 7 + 2^64
                                  // (7 + 2^64) % 3 = 2.
    assert!(
        tc.is_def_eq(&nat_binop("Nat.mod", big, nat(3)), &nat(2)),
        "Nat.mod(7+2^64, 3) should reduce to 2 (arbitrary precision)"
    );
}

/// Division by zero returns 0, even at u64 boundary values.
#[test]
fn test_nat_div_by_zero_u64_max() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert!(
        tc.is_def_eq(&nat_binop("Nat.div", nat(u64::MAX), nat(0)), &nat(0)),
        "Nat.div(u64::MAX, 0) should reduce to 0"
    );
}

/// Modulo by zero returns the dividend.
#[test]
fn test_nat_mod_by_zero_u64_max() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert!(
        tc.is_def_eq(&nat_binop("Nat.mod", nat(u64::MAX), nat(0)), &nat(u64::MAX)),
        "Nat.mod(u64::MAX, 0) should reduce to u64::MAX"
    );
}

/// PIN UPDATE (kernel parity gap #9): shiftLeft past the old u64 width now
/// reduces via the multi-limb BigNat path. shiftLeft(1, 64) = 2^64.
#[test]
fn test_nat_shift_left_at_64_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // shiftLeft(1, 64) = 2^64 = limbs [0, 1].
    let expected = bignat_2limb(0, 1);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.shiftLeft", nat(1), nat(64)), &expected),
        "Nat.shiftLeft(1, 64) should reduce to 2^64 (arbitrary precision)"
    );
}

/// PIN UPDATE (kernel parity gap #9): shiftLeft that previously overflowed u64
/// now reduces. shiftLeft(3, 63) = 3 * 2^63 = limbs [2^63, 1].
#[test]
fn test_nat_shift_left_value_overflow_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 3 << 63 = 27670116110564327424 = limbs [2^63, 1].
    let expected = bignat_2limb(1u64 << 63, 1);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.shiftLeft", nat(3), nat(63)), &expected),
        "Nat.shiftLeft(3, 63) should reduce to 3*2^63 (arbitrary precision)"
    );
}

/// Shift right >= 64 produces 0.
#[test]
fn test_nat_shift_right_large_shift() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.shiftRight", nat(u64::MAX), nat(100)),
            &nat(0)
        ),
        "Nat.shiftRight(u64::MAX, 100) should reduce to 0"
    );
}

/// PIN UPDATE (kernel parity gap #9): Nat.mul past u128 now reduces via the
/// multi-limb BigNat path (within the 16-limb / 1024-bit allocation bound).
#[test]
fn test_nat_mul_past_u128_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^64 * 2^64 = 2^128 = limbs [0, 0, 1].
    let two_pow_64 = bignat_2limb(0, 1);
    let expected = bignat_3limb(0, 0, 1);
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.mul", two_pow_64.clone(), two_pow_64),
            &expected
        ),
        "Nat.mul(2^64, 2^64) should reduce to 2^128 (arbitrary precision)"
    );
}

/// PIN UPDATE (kernel parity gap #9): Nat.add across the old u128 boundary now
/// reduces. u128::MAX + 1 = 2^128 = limbs [0, 0, 1].
#[test]
fn test_nat_add_past_u128_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // u128::MAX = BigNat::Big([u64::MAX, u64::MAX]); +1 = 2^128.
    let u128_max = bignat_2limb(u64::MAX, u64::MAX);
    let expected = bignat_3limb(0, 0, 1);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.add", u128_max, nat(1)), &expected),
        "Nat.add(u128::MAX, 1) should reduce to 2^128 (arbitrary precision)"
    );
}

// =============================================================================
// Divergence 4: Bidirectional proof-by-reflection
// =============================================================================

/// The bidirectional reduceBool check in is_def_eq_core (lines 286-297)
/// checks both directions: Bool.true on left and Bool.true on right.
/// Lean 4 only checks one direction. This test verifies both work.
#[test]
fn test_reduce_bool_left_is_true() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Bool.true =?= Bool.true should trivially pass
    assert!(
        tc.is_def_eq(&bool_true(), &bool_true()),
        "Bool.true =?= Bool.true"
    );
}

/// Bool.true =?= Bool.false should fail.
#[test]
fn test_reduce_bool_not_equal() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert!(
        !tc.is_def_eq(&bool_true(), &bool_false()),
        "Bool.true should not be def_eq to Bool.false"
    );
}

/// Bool.false =?= Bool.false should pass.
#[test]
fn test_reduce_bool_false_reflexive() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert!(
        tc.is_def_eq(&bool_false(), &bool_false()),
        "Bool.false =?= Bool.false"
    );
}

// =============================================================================
// Divergence 5: MData stripping behavior
// =============================================================================

/// MData is transparent: MData(_, e) =?= e should hold.
#[test]
fn test_mdata_left_transparent() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let inner = nat(42);
    assert!(
        tc.is_def_eq(&mdata(inner.clone()), &inner),
        "MData(_, 42) should be def_eq to 42"
    );
}

/// MData on right side: e =?= MData(_, e) should also hold.
#[test]
fn test_mdata_right_transparent() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let inner = nat(42);
    assert!(
        tc.is_def_eq(&inner, &mdata(inner.clone())),
        "42 should be def_eq to MData(_, 42)"
    );
}

/// Both sides wrapped in MData.
#[test]
fn test_mdata_both_sides() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let a = mdata(nat(100));
    let b = mdata(nat(100));
    assert!(
        tc.is_def_eq(&a, &b),
        "MData(_, 100) should be def_eq to MData(_, 100)"
    );
}

/// Nested MData: MData(_, MData(_, e)) =?= e.
#[test]
fn test_mdata_nested() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let inner = nat(7);
    let nested = mdata(mdata(inner.clone()));
    assert!(
        tc.is_def_eq(&nested, &inner),
        "MData(_, MData(_, 7)) should be def_eq to 7"
    );
}

/// MData wrapping different values should not be equal.
#[test]
fn test_mdata_different_values() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let a = mdata(nat(1));
    let b = mdata(nat(2));
    assert!(
        !tc.is_def_eq(&a, &b),
        "MData(_, 1) should not be def_eq to MData(_, 2)"
    );
}

/// MData wrapping Sort expressions.
#[test]
fn test_mdata_sort_transparent() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let sort = Expr::type_(); // Sort(Level::Succ(Level::Zero))
    assert!(
        tc.is_def_eq(&mdata(sort.clone()), &sort),
        "MData(_, Type) should be def_eq to Type"
    );
}

/// MData wrapping Const expressions.
#[test]
fn test_mdata_const_transparent() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let c = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert!(
        tc.is_def_eq(&mdata(c.clone()), &c),
        "MData(_, Nat.zero) should be def_eq to Nat.zero"
    );
}

// =============================================================================
// Universe level normalization
// =============================================================================

/// Sort(max(0, u)) =?= Sort(u) — max with zero is identity.
#[test]
fn test_level_max_zero_identity() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let u = Level::param(Name::from_string("u"));
    let max_0_u = Level::max(Level::zero(), u.clone());
    let sort_max = Expr::from_kind(ExprKind::Sort(max_0_u));
    let sort_u = Expr::from_kind(ExprKind::Sort(u));
    assert!(
        tc.is_def_eq(&sort_max, &sort_u),
        "Sort(max(0, u)) should be def_eq to Sort(u)"
    );
}

/// Sort(imax(0, u)) =?= Sort(u) when u is known non-zero.
/// Actually, imax(0, u) normalizes differently: imax(l1, l2) = 0 if l2=0,
/// else max(l1, l2). For param u, it stays as imax(0, u).
#[test]
fn test_level_imax_normalization() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // imax(u, 0) = 0 (second arg is zero)
    let u = Level::param(Name::from_string("u"));
    let imax_u_0 = Level::imax(u, Level::zero());
    let sort_imax = Expr::from_kind(ExprKind::Sort(imax_u_0));
    let sort_0 = Expr::from_kind(ExprKind::Sort(Level::zero()));
    assert!(
        tc.is_def_eq(&sort_imax, &sort_0),
        "Sort(imax(u, 0)) should be def_eq to Sort(0) (Prop)"
    );
}

/// Sort(succ(succ(0))) =?= Sort(succ(succ(0))) — concrete levels.
#[test]
fn test_level_concrete_succ() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let l2 = Level::succ(Level::succ(Level::zero()));
    let sort_a = Expr::from_kind(ExprKind::Sort(l2.clone()));
    let sort_b = Expr::from_kind(ExprKind::Sort(l2));
    assert!(
        tc.is_def_eq(&sort_a, &sort_b),
        "Sort(2) should be def_eq to Sort(2)"
    );
}

/// Different universe levels should not be equal.
#[test]
fn test_level_different_params_not_equal() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let sort_u = Expr::from_kind(ExprKind::Sort(u));
    let sort_v = Expr::from_kind(ExprKind::Sort(v));
    assert!(
        !tc.is_def_eq(&sort_u, &sort_v),
        "Sort(u) should not be def_eq to Sort(v)"
    );
}

/// max is commutative: max(u, v) =?= max(v, u).
#[test]
fn test_level_max_commutative() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let sort_uv = Expr::from_kind(ExprKind::Sort(Level::max(u.clone(), v.clone())));
    let sort_vu = Expr::from_kind(ExprKind::Sort(Level::max(v, u)));
    assert!(
        tc.is_def_eq(&sort_uv, &sort_vu),
        "Sort(max(u, v)) should be def_eq to Sort(max(v, u))"
    );
}

// =============================================================================
// Nat.succ BigNat boundary
// =============================================================================

/// Nat.succ on a BigNat (2-limb) value.
#[test]
fn test_nat_succ_bignat_2limb() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.succ(2^64) = 2^64 + 1
    let big = bignat_2limb(0, 1); // 2^64
    let expected = bignat_2limb(1, 1); // 2^64 + 1
    assert!(
        tc.is_def_eq(&nat_succ(big), &expected),
        "Nat.succ(2^64) should reduce to BigNat(2^64 + 1)"
    );
}

/// Chained Nat.succ producing BigNat.
#[test]
fn test_nat_succ_chain_to_bignat() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Nat.succ(Nat.succ(u64::MAX - 1)) = u64::MAX + 1 = 2^64
    let expected = bignat_2limb(0, 1);
    assert!(
        tc.is_def_eq(&nat_succ(nat_succ(nat(u64::MAX - 1))), &expected),
        "Nat.succ(Nat.succ(u64::MAX - 1)) should produce BigNat 2^64"
    );
}

// =============================================================================
// Nat.add with BigNat inputs
// =============================================================================

/// Nat.add with one BigNat and one small value.
#[test]
fn test_nat_add_bignat_plus_small() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^64 + 5 = BigNat([5, 1])
    let big = bignat_2limb(0, 1);
    let expected = bignat_2limb(5, 1);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.add", big, nat(5)), &expected),
        "Nat.add(2^64, 5) should produce BigNat(2^64 + 5)"
    );
}

/// Nat.add with two BigNat values (both 2-limb).
#[test]
fn test_nat_add_two_bignats() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^64 + 2^64 = 2^65 = BigNat([0, 2])
    let a = bignat_2limb(0, 1);
    let b = bignat_2limb(0, 1);
    let expected = bignat_2limb(0, 2);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.add", a, b), &expected),
        "Nat.add(2^64, 2^64) should produce BigNat(2^65)"
    );
}

/// Nat.mul with BigNat input and small multiplier.
#[test]
fn test_nat_mul_bignat_times_small() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^64 * 2 = 2^65 = BigNat([0, 2])
    let big = bignat_2limb(0, 1);
    let expected = bignat_2limb(0, 2);
    assert!(
        tc.is_def_eq(&nat_binop("Nat.mul", big, nat(2)), &expected),
        "Nat.mul(2^64, 2) should produce BigNat(2^65)"
    );
}

// =============================================================================
// Nat GCD edge cases
// =============================================================================

/// gcd(0, 0) = 0.
#[test]
fn test_nat_gcd_zero_zero() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert!(
        tc.is_def_eq(&nat_binop("Nat.gcd", nat(0), nat(0)), &nat(0)),
        "Nat.gcd(0, 0) should reduce to 0"
    );
}

/// gcd(n, n) = n.
#[test]
fn test_nat_gcd_same() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert!(
        tc.is_def_eq(&nat_binop("Nat.gcd", nat(42), nat(42)), &nat(42)),
        "Nat.gcd(42, 42) should reduce to 42"
    );
}

// =============================================================================
// Structural equality: is_def_eq_offset (Nat successor peeling)
// =============================================================================

/// Nat zero vs zero via is_def_eq_offset.
#[test]
fn test_offset_zero_zero() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert!(
        tc.is_def_eq(&nat(0), &nat(0)),
        "Nat.zero =?= Nat.zero via offset peeling"
    );
}

/// Nat.succ peeling: succ(succ(0)) =?= 2.
#[test]
fn test_offset_succ_peeling() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert!(
        tc.is_def_eq(&nat_succ(nat_succ(nat(0))), &nat(2)),
        "Nat.succ(Nat.succ(0)) =?= 2 via offset peeling"
    );
}

/// Different Nat values via offset: succ(0) != 0.
#[test]
fn test_offset_succ_not_zero() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert!(
        !tc.is_def_eq(&nat_succ(nat(0)), &nat(0)),
        "Nat.succ(0) should not be def_eq to 0"
    );
}
