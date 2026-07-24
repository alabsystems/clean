// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the interval arithmetic library.

use num_rational::Rational64;

use super::ops;
use super::theorems;
use super::theorems_algebraic;
use super::types::{Interval, IntervalError};

// ============================================================================
// Unit tests: Interval type
// ============================================================================

#[test]
fn test_interval_new_valid() {
    let iv = Interval::from_integers(1, 5).unwrap();
    assert_eq!(iv.lo(), Rational64::from_integer(1));
    assert_eq!(iv.hi(), Rational64::from_integer(5));
}

#[test]
fn test_interval_new_point() {
    let iv = Interval::from_integers(3, 3).unwrap();
    assert_eq!(iv.lo(), iv.hi());
}

#[test]
fn test_interval_new_invalid() {
    let result = Interval::from_integers(5, 1);
    assert!(matches!(result, Err(IntervalError::InvalidBounds { .. })));
}

#[test]
fn test_interval_contains() {
    let iv = Interval::from_integers(2, 7).unwrap();
    assert!(iv.contains(Rational64::from_integer(2)));
    assert!(iv.contains(Rational64::from_integer(5)));
    assert!(iv.contains(Rational64::from_integer(7)));
    assert!(!iv.contains(Rational64::from_integer(1)));
    assert!(!iv.contains(Rational64::from_integer(8)));
}

#[test]
fn test_interval_contains_interval() {
    let outer = Interval::from_integers(0, 10).unwrap();
    let inner = Interval::from_integers(3, 7).unwrap();
    assert!(outer.contains_interval(&inner));
    assert!(!inner.contains_interval(&outer));
}

#[test]
fn test_interval_width() {
    let iv = Interval::from_integers(2, 9).unwrap();
    assert_eq!(iv.width(), Rational64::from_integer(7));
}

#[test]
fn test_interval_midpoint() {
    let iv = Interval::from_integers(2, 8).unwrap();
    assert_eq!(iv.midpoint(), Rational64::from_integer(5));
}

#[test]
fn test_interval_contains_zero() {
    assert!(!Interval::from_integers(1, 5).unwrap().contains_zero());
    assert!(!Interval::from_integers(-5, -1).unwrap().contains_zero());
    assert!(Interval::from_integers(-2, 3).unwrap().contains_zero());
    assert!(Interval::from_integers(0, 3).unwrap().contains_zero());
}

#[test]
fn test_interval_point_constructor() {
    let iv = Interval::point(Rational64::from_integer(42));
    assert_eq!(iv.width(), Rational64::from_integer(0));
    assert!(iv.contains(Rational64::from_integer(42)));
    assert!(!iv.contains(Rational64::from_integer(41)));
}

#[test]
fn test_interval_display() {
    let iv = Interval::from_integers(1, 5).unwrap();
    assert_eq!(format!("{}", iv), "[1, 5]");
}

#[test]
fn test_interval_strictly_positive() {
    assert!(Interval::from_integers(1, 5)
        .unwrap()
        .is_strictly_positive());
    assert!(!Interval::from_integers(0, 5)
        .unwrap()
        .is_strictly_positive());
    assert!(!Interval::from_integers(-1, 5)
        .unwrap()
        .is_strictly_positive());
}

#[test]
fn test_interval_strictly_negative() {
    assert!(Interval::from_integers(-5, -1)
        .unwrap()
        .is_strictly_negative());
    assert!(!Interval::from_integers(-5, 0)
        .unwrap()
        .is_strictly_negative());
    assert!(!Interval::from_integers(-5, 1)
        .unwrap()
        .is_strictly_negative());
}

// ============================================================================
// Unit tests: operations
// ============================================================================

#[test]
fn test_add_basic() {
    let a = Interval::from_integers(1, 3).unwrap();
    let b = Interval::from_integers(2, 5).unwrap();
    let sum = ops::add(&a, &b);
    assert_eq!(sum.lo(), Rational64::from_integer(3));
    assert_eq!(sum.hi(), Rational64::from_integer(8));
}

#[test]
fn test_sub_basic() {
    let a = Interval::from_integers(3, 7).unwrap();
    let b = Interval::from_integers(1, 2).unwrap();
    let diff = ops::sub(&a, &b);
    assert_eq!(diff.lo(), Rational64::from_integer(1));
    assert_eq!(diff.hi(), Rational64::from_integer(6));
}

#[test]
fn test_neg_basic() {
    let a = Interval::from_integers(2, 5).unwrap();
    let n = ops::neg(&a);
    assert_eq!(n.lo(), Rational64::from_integer(-5));
    assert_eq!(n.hi(), Rational64::from_integer(-2));
}

#[test]
fn test_mul_both_positive() {
    let a = Interval::from_integers(2, 3).unwrap();
    let b = Interval::from_integers(4, 5).unwrap();
    let prod = ops::mul(&a, &b);
    assert_eq!(prod.lo(), Rational64::from_integer(8));
    assert_eq!(prod.hi(), Rational64::from_integer(15));
}

#[test]
fn test_mul_mixed_signs() {
    let a = Interval::from_integers(-2, 3).unwrap();
    let b = Interval::from_integers(-1, 4).unwrap();
    let prod = ops::mul(&a, &b);
    assert_eq!(prod.lo(), Rational64::from_integer(-8));
    assert_eq!(prod.hi(), Rational64::from_integer(12));
}

#[test]
fn test_div_basic() {
    let a = Interval::from_integers(4, 8).unwrap();
    let b = Interval::from_integers(2, 4).unwrap();
    let quot = ops::div(&a, &b).unwrap();
    assert_eq!(quot.lo(), Rational64::from_integer(1));
    assert_eq!(quot.hi(), Rational64::from_integer(4));
}

#[test]
fn test_div_zero_error() {
    let a = Interval::from_integers(1, 3).unwrap();
    let b = Interval::from_integers(-1, 1).unwrap();
    assert!(matches!(
        ops::div(&a, &b),
        Err(IntervalError::DivisionByZero { .. })
    ));
}

#[test]
fn test_abs_positive() {
    let a = Interval::from_integers(2, 5).unwrap();
    let r = ops::abs(&a);
    assert_eq!(r.lo(), Rational64::from_integer(2));
    assert_eq!(r.hi(), Rational64::from_integer(5));
}

#[test]
fn test_abs_negative() {
    let a = Interval::from_integers(-5, -2).unwrap();
    let r = ops::abs(&a);
    assert_eq!(r.lo(), Rational64::from_integer(2));
    assert_eq!(r.hi(), Rational64::from_integer(5));
}

#[test]
fn test_abs_straddling() {
    let a = Interval::from_integers(-3, 5).unwrap();
    let r = ops::abs(&a);
    assert_eq!(r.lo(), Rational64::from_integer(0));
    assert_eq!(r.hi(), Rational64::from_integer(5));
}

#[test]
fn test_pow_square_positive() {
    let a = Interval::from_integers(2, 3).unwrap();
    let r = ops::pow(&a, 2).unwrap();
    assert_eq!(r.lo(), Rational64::from_integer(4));
    assert_eq!(r.hi(), Rational64::from_integer(9));
}

#[test]
fn test_pow_square_straddling() {
    let a = Interval::from_integers(-3, 2).unwrap();
    let r = ops::pow(&a, 2).unwrap();
    assert_eq!(r.lo(), Rational64::from_integer(0));
    assert_eq!(r.hi(), Rational64::from_integer(9));
}

#[test]
fn test_pow_cube() {
    let a = Interval::from_integers(-2, 3).unwrap();
    let r = ops::pow(&a, 3).unwrap();
    assert_eq!(r.lo(), Rational64::from_integer(-8));
    assert_eq!(r.hi(), Rational64::from_integer(27));
}

#[test]
fn test_pow_zero() {
    let a = Interval::from_integers(2, 5).unwrap();
    let r = ops::pow(&a, 0).unwrap();
    assert_eq!(r.lo(), Rational64::from_integer(1));
    assert_eq!(r.hi(), Rational64::from_integer(1));
}

#[test]
fn test_pow_one() {
    let a = Interval::from_integers(2, 5).unwrap();
    let r = ops::pow(&a, 1).unwrap();
    assert_eq!(r, a);
}

#[test]
fn test_sqrt_perfect_squares() {
    let a = Interval::from_integers(4, 9).unwrap();
    let r = ops::sqrt(&a).unwrap();
    // sqrt(4) = 2, sqrt(9) = 3 (approximately)
    let two = Rational64::from_integer(2);
    let three = Rational64::from_integer(3);
    // The Newton approximation should be very close
    assert!(r.lo() <= two, "sqrt(4) lo should be <= 2, got {}", r.lo());
    assert!(r.hi() >= three, "sqrt(9) hi should be >= 3, got {}", r.hi());
}

#[test]
fn test_sqrt_negative_error() {
    let a = Interval::from_integers(-4, -1).unwrap();
    assert!(matches!(
        ops::sqrt(&a),
        Err(IntervalError::SqrtNegative { .. })
    ));
}

#[test]
fn test_sqrt_zero() {
    let a = Interval::from_integers(0, 0).unwrap();
    let r = ops::sqrt(&a).unwrap();
    assert_eq!(r.lo(), Rational64::from_integer(0));
    assert_eq!(r.hi(), Rational64::from_integer(0));
}

#[test]
fn test_intersect_overlapping() {
    let a = Interval::from_integers(1, 5).unwrap();
    let b = Interval::from_integers(3, 7).unwrap();
    let inter = ops::intersect(&a, &b).unwrap();
    assert_eq!(inter.lo(), Rational64::from_integer(3));
    assert_eq!(inter.hi(), Rational64::from_integer(5));
}

#[test]
fn test_intersect_disjoint() {
    let a = Interval::from_integers(1, 3).unwrap();
    let b = Interval::from_integers(5, 7).unwrap();
    assert!(matches!(
        ops::intersect(&a, &b),
        Err(IntervalError::DisjointIntervals { .. })
    ));
}

#[test]
fn test_intersect_touching() {
    let a = Interval::from_integers(1, 5).unwrap();
    let b = Interval::from_integers(5, 9).unwrap();
    let inter = ops::intersect(&a, &b).unwrap();
    assert_eq!(inter.lo(), Rational64::from_integer(5));
    assert_eq!(inter.hi(), Rational64::from_integer(5));
}

#[test]
fn test_hull_basic() {
    let a = Interval::from_integers(1, 3).unwrap();
    let b = Interval::from_integers(5, 7).unwrap();
    let h = ops::hull(&a, &b);
    assert_eq!(h.lo(), Rational64::from_integer(1));
    assert_eq!(h.hi(), Rational64::from_integer(7));
}

#[test]
fn test_hull_overlapping() {
    let a = Interval::from_integers(1, 5).unwrap();
    let b = Interval::from_integers(3, 7).unwrap();
    let h = ops::hull(&a, &b);
    assert_eq!(h.lo(), Rational64::from_integer(1));
    assert_eq!(h.hi(), Rational64::from_integer(7));
}

// ============================================================================
// Unit tests: theorems
// ============================================================================

#[test]
fn test_t01_add_containment() {
    let a = Interval::from_integers(1, 3).unwrap();
    let b = Interval::from_integers(2, 5).unwrap();
    let w = theorems::verify_t01_add_containment(
        Rational64::from_integer(2),
        Rational64::from_integer(4),
        &a,
        &b,
    );
    assert!(w.verified, "T01 failed");
}

#[test]
fn test_t02_sub_containment() {
    let a = Interval::from_integers(3, 7).unwrap();
    let b = Interval::from_integers(1, 2).unwrap();
    let w = theorems::verify_t02_sub_containment(
        Rational64::from_integer(5),
        Rational64::from_integer(1),
        &a,
        &b,
    );
    assert!(w.verified, "T02 failed");
}

#[test]
fn test_t03_neg_containment() {
    let a = Interval::from_integers(-3, 5).unwrap();
    let w = theorems::verify_t03_neg_containment(Rational64::from_integer(2), &a);
    assert!(w.verified, "T03 failed");
}

#[test]
fn test_t04_mul_containment() {
    let a = Interval::from_integers(-2, 3).unwrap();
    let b = Interval::from_integers(-1, 4).unwrap();
    let w = theorems::verify_t04_mul_containment(
        Rational64::from_integer(1),
        Rational64::from_integer(3),
        &a,
        &b,
    );
    assert!(w.verified, "T04 failed");
}

#[test]
fn test_t05_div_containment() {
    let a = Interval::from_integers(4, 8).unwrap();
    let b = Interval::from_integers(2, 4).unwrap();
    let w = theorems::verify_t05_div_containment(
        Rational64::from_integer(6),
        Rational64::from_integer(3),
        &a,
        &b,
    );
    assert!(w.verified, "T05 failed");
}

#[test]
fn test_t06_abs_containment() {
    let a = Interval::from_integers(-3, 5).unwrap();
    let w = theorems::verify_t06_abs_containment(Rational64::from_integer(-2), &a);
    assert!(w.verified, "T06 failed");
}

#[test]
fn test_t07_pow_containment() {
    let a = Interval::from_integers(2, 4).unwrap();
    let w = theorems::verify_t07_pow_containment_nonneg(Rational64::from_integer(3), &a, 2);
    assert!(w.verified, "T07 failed");
}

#[test]
fn test_t08_sqrt_containment() {
    let a = Interval::from_integers(4, 9).unwrap();
    let w = theorems::verify_t08_sqrt_containment(Rational64::from_integer(4), &a);
    assert!(w.verified, "T08 failed");
}

#[test]
fn test_t09_intersection_containment() {
    let a = Interval::from_integers(1, 5).unwrap();
    let b = Interval::from_integers(3, 7).unwrap();
    let w = theorems::verify_t09_intersection_containment(Rational64::from_integer(4), &a, &b);
    assert!(w.verified, "T09 failed");
}

#[test]
fn test_t10_hull_containment() {
    let a = Interval::from_integers(1, 3).unwrap();
    let b = Interval::from_integers(5, 7).unwrap();
    let w = theorems::verify_t10_hull_containment(&a, &b);
    assert!(w.verified, "T10 failed");
}

#[test]
fn test_t11_subset_transitivity() {
    let a = Interval::from_integers(3, 5).unwrap();
    let b = Interval::from_integers(2, 6).unwrap();
    let c = Interval::from_integers(1, 7).unwrap();
    let w = theorems::verify_t11_subset_transitivity(&a, &b, &c);
    assert!(w.verified, "T11 failed");
}

#[test]
fn test_t12_containment_transitivity() {
    let a = Interval::from_integers(3, 5).unwrap();
    let b = Interval::from_integers(1, 7).unwrap();
    let w = theorems::verify_t12_containment_transitivity(Rational64::from_integer(4), &a, &b);
    assert!(w.verified, "T12 failed");
}

#[test]
fn test_t13_point_interval() {
    let w = theorems::verify_t13_point_interval(Rational64::from_integer(42));
    assert!(w.verified, "T13 failed");
}

#[test]
fn test_t14_contains_reflexive() {
    let a = Interval::from_integers(-3, 7).unwrap();
    let w = theorems::verify_t14_contains_reflexive(&a);
    assert!(w.verified, "T14 failed");
}

#[test]
fn test_t15_add_width() {
    let a = Interval::from_integers(1, 4).unwrap();
    let b = Interval::from_integers(2, 7).unwrap();
    let w = theorems_algebraic::verify_t15_add_width(&a, &b);
    assert!(w.verified, "T15 failed");
}

#[test]
fn test_t16_sub_width() {
    let a = Interval::from_integers(1, 4).unwrap();
    let b = Interval::from_integers(2, 7).unwrap();
    let w = theorems_algebraic::verify_t16_sub_width(&a, &b);
    assert!(w.verified, "T16 failed");
}

#[test]
fn test_t17_neg_width() {
    let a = Interval::from_integers(-3, 7).unwrap();
    let w = theorems_algebraic::verify_t17_neg_width(&a);
    assert!(w.verified, "T17 failed");
}

#[test]
fn test_t18_add_commutativity() {
    let a = Interval::from_integers(-2, 3).unwrap();
    let b = Interval::from_integers(1, 5).unwrap();
    let w = theorems_algebraic::verify_t18_add_commutativity(&a, &b);
    assert!(w.verified, "T18 failed");
}

#[test]
fn test_t19_mul_commutativity() {
    let a = Interval::from_integers(-2, 3).unwrap();
    let b = Interval::from_integers(1, 5).unwrap();
    let w = theorems_algebraic::verify_t19_mul_commutativity(&a, &b);
    assert!(w.verified, "T19 failed");
}

#[test]
fn test_t20_add_associativity() {
    let a = Interval::from_integers(1, 2).unwrap();
    let b = Interval::from_integers(3, 4).unwrap();
    let c = Interval::from_integers(5, 6).unwrap();
    let w = theorems_algebraic::verify_t20_add_associativity(&a, &b, &c);
    assert!(w.verified, "T20 failed");
}

#[test]
fn test_all_proof_statuses() {
    let statuses = theorems::all_proof_statuses();
    assert_eq!(statuses.len(), 20, "should have 20 theorems");

    // `all_proof_statuses` reports the REGISTRATION-TIME values (hardcoded
    // `TXX_PROOF_STATUS = DerivedPending` constants). Post-registration the
    // kernel-verified status comes from the promote pipeline — see
    // `interval_arith::tests_promote::test_compute_proof_statuses_dynamically_20_proved_0_pending`
    // for the dynamic verification.
    let proved = statuses
        .iter()
        .filter(|(_, _, s)| matches!(s, crate::spec::ProofStatus::DerivedProved))
        .count();
    let pending = statuses
        .iter()
        .filter(|(_, _, s)| matches!(s, crate::spec::ProofStatus::DerivedPending))
        .count();
    assert_eq!(proved, 0, "expected 0 DerivedProved at registration time");
    assert_eq!(
        pending, 20,
        "expected 20 DerivedPending at registration time"
    );

    // Every id must have a canonical spec name — the mapping feeds the
    // dynamic promote pipeline.
    for (id, _, _) in &statuses {
        assert!(
            super::theorems_promote::spec_name_for(id).is_some(),
            "missing spec_name_for mapping for {id}"
        );
    }
}

// Property-based tests are in tests_proptest.rs
