// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rational edge cases, overflow boundaries, and large-coefficient simplex
//! guardrails.

use super::super::types::*;
use super::super::*;
use super::{insert_bound, make_lit};
use crate::theories::rational::{DeltaRational, Rational};
use std::collections::BTreeMap;

/// Rational::new with negative denominator normalizes sign.
#[test]
fn test_rational_negative_den() {
    let r = Rational::new(3, -4);
    assert_eq!(r, Rational::new(-3, 4));
}

/// Rational::new reduces large coprime numerator/denominator.
#[test]
fn test_rational_gcd_reduction() {
    let r = Rational::new(12, 18);
    assert_eq!(r, Rational::new(2, 3));
}

/// Rational comparison uses cross-multiplication — verify negative values.
#[test]
fn test_rational_negative_comparison() {
    let a = Rational::new(-1, 3);
    let b = Rational::new(-1, 2);
    // -1/3 > -1/2
    assert!(a > b);
}

/// Rational::neg of zero is zero.
#[test]
fn test_rational_neg_zero() {
    let r = Rational::ZERO.neg();
    assert_eq!(r, Rational::ZERO);
}

/// Rational::from_int creates an integer with den=1.
#[test]
fn test_rational_from_int() {
    let r = Rational::from_int(-7);
    assert_eq!(r, Rational::new(-7, 1));
    assert!(r.is_negative());
}

/// Rational predicates: is_zero, is_positive, is_negative.
#[test]
fn test_rational_predicates() {
    assert!(Rational::ZERO.is_zero());
    assert!(!Rational::ZERO.is_positive());
    assert!(!Rational::ZERO.is_negative());

    assert!(Rational::ONE.is_positive());
    assert!(!Rational::ONE.is_negative());
    assert!(!Rational::ONE.is_zero());

    assert!(Rational::NEG_ONE.is_negative());
    assert!(!Rational::NEG_ONE.is_positive());
}

/// Rational::add with large values now uses i128 intermediates (#2324).
/// MAX/2 + MAX/2 = MAX-1, fits in i64 after normalization.
#[test]
fn test_rational_large_value_add() {
    let large = Rational::from_int(i64::MAX / 2);
    let result = large.add(&large).unwrap();
    assert!(
        result.is_positive(),
        "sum of two large positives should be positive"
    );
}

/// Rational::mul with large-but-fitting values (#2324).
/// 2^31 * 2^31 = 2^62, fits in i64.
#[test]
fn test_rational_large_mul_fits() {
    let a = Rational::from_int(1 << 31);
    let b = Rational::from_int(1 << 31);
    let product = a.mul(&b).unwrap();
    assert!(product.is_positive(), "2^31 * 2^31 should fit in i64");
}

/// Regression test for #2324: Rational::mul returns None on overflow
/// instead of silently wrapping or panicking. With i128 intermediates,
/// the product 2^32 * 2^32 = 2^64, which exceeds i64 after normalization.
#[test]
fn test_rational_overflow_mul_returns_none() {
    let c = Rational::from_int(1 << 32);
    let d = Rational::from_int(1 << 32);
    assert!(
        c.mul(&d).is_none(),
        "overflow should return None, not panic or wrap"
    );
}

/// Rational comparison with large values (#1845).
/// a/b cmp c/d uses a*d cmp c*b — at extreme values cross-products can overflow.
/// This test verifies correctness near the boundary where cross-products still fit:
/// (MAX/2)/1 cmp 1/2 → cross-products (MAX/2)*2 = MAX-1 and 1*1, both in-range.
#[test]
fn test_rational_comparison_overflow_boundary() {
    let a = Rational::new(i64::MAX / 2, 1);
    let b = Rational::new(1, 2);
    assert!(
        a > b,
        "large rational should compare greater than small one"
    );
}

/// DeltaRational div_rational exercises division path.
#[test]
fn test_delta_rational_div() {
    let a = DeltaRational::new(Rational::from_int(6), Rational::from_int(4));
    let c = Rational::from_int(2);
    let result = a.div_rational(&c).unwrap();
    assert_eq!(result.real, Rational::from_int(3));
    assert_eq!(result.delta, Rational::from_int(2));
}

/// DeltaRational ordering: real part dominates, then delta.
#[test]
fn test_delta_rational_ordering_comprehensive() {
    let a = DeltaRational::new(Rational::from_int(1), Rational::from_int(100));
    let b = DeltaRational::new(Rational::from_int(2), Rational::NEG_ONE);
    // (1, 100) < (2, -1) because real 1 < 2
    assert!(a < b);

    // Same real, different delta
    let c = DeltaRational::new(Rational::from_int(5), Rational::from_int(-1));
    let d = DeltaRational::new(Rational::from_int(5), Rational::ZERO);
    let e = DeltaRational::new(Rational::from_int(5), Rational::ONE);
    assert!(c < d);
    assert!(d < e);
}

/// Regression test: Rational::neg() must handle i64::MIN correctly.
///
/// `i64::MIN.wrapping_neg() == i64::MIN`, so neg() would silently return
/// the same value. The simplex pivot uses neg() on tableau coefficients
/// (simplex.rs:261,267) — a corrupted negation produces wrong row coefficients,
/// leading to potential false conflicts (unsoundness).
///
/// After the fix, neg() should either return the correct negation or
/// the callers should use checked_neg() which returns None for i64::MIN.
#[test]
fn test_rational_neg_i64_min_boundary() {
    let r = Rational::new(i64::MIN + 1, 1); // -2^63 + 1, fits safely
    let neg_r = r.neg();
    assert_eq!(
        neg_r,
        Rational::from_int(i64::MAX),
        "-(-2^63 + 1) = 2^63 - 1 = i64::MAX"
    );

    // i64::MIN itself: neg() with wrapping would silently return i64::MIN.
    // checked_neg() must return None for this case.
    let min_rat = Rational::new(i64::MIN / 2, 1); // -2^62 — safe to negate
    let neg_min = min_rat.checked_neg().unwrap();
    assert_eq!(
        neg_min,
        Rational::from_int(i64::MAX / 2 + 1),
        "-(−2^62) = 2^62"
    );

    // The actual i64::MIN boundary: checked_neg returns None
    // Rational::from_int(i64::MIN) is valid (no normalization arithmetic needed)
    let extreme = Rational::from_int(i64::MIN);
    assert!(
        extreme.checked_neg().is_none(),
        "checked_neg() must return None for i64::MIN numerator"
    );
}

/// Verify that the pivot path handles extreme coefficients without corruption.
/// Uses checked_neg() so that i64::MIN coefficients produce None (overflow)
/// rather than silently wrong values.
fn extreme_coefficient_fixture() -> (ArithmeticTheory, ArithVar, ArithVar) {
    let mut arith = ArithmeticTheory::new();
    let x = ArithVar::new(0);
    let y = ArithVar::new(1);
    let slack = ArithVar::new(2);
    arith.next_id = 3;

    let mut coeffs = BTreeMap::new();
    coeffs.insert(x, Rational::from_int(i64::MAX));
    coeffs.insert(y, Rational::ONE);
    arith.tableau.push(TableauRow {
        basic_var: slack,
        constant: Rational::ZERO,
        coeffs,
    });
    arith.rebuild_basic_var_index();

    arith
        .assignment
        .insert(x, DeltaRational::from_rational(Rational::ZERO));
    arith
        .assignment
        .insert(y, DeltaRational::from_rational(Rational::ZERO));

    (arith, x, slack)
}

/// Verify that the pivot path handles extreme coefficients without corruption.
/// Uses checked_neg() so that i64::MIN coefficients produce None (overflow)
/// rather than silently wrong values.
#[test]
fn test_simplex_pivot_extreme_coefficient_overflow() {
    let (mut arith, x, slack) = extreme_coefficient_fixture();

    // slack lower bound: slack >= 1
    insert_bound(
        &mut arith.lower_bounds,
        slack,
        Rational::ONE,
        make_lit(0, true),
        0,
    );

    // x upper bound: x <= 0 (blocks increasing x)
    insert_bound(
        &mut arith.upper_bounds,
        x,
        Rational::ZERO,
        make_lit(1, true),
        0,
    );

    // check_and_repair should either:
    // - Successfully pivot y to satisfy the constraint, OR
    // - Return Consistent (incomplete) if overflow prevents pivot
    // It must NOT return a false conflict.
    let result = arith.check_and_repair();
    // With y unbounded above, the system is satisfiable (y = 1 works).
    // A false Conflict here would indicate neg() corruption.
    assert!(
        !matches!(result, TheoryCheckResult::Conflict(_)),
        "system with large coefficient must not produce false conflict: {result:?}"
    );
}
