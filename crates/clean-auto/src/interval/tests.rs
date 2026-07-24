// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the interval arithmetic library.
//!
//! Combines unit tests for specific cases with property-based tests
//! (proptest) for the containment theorems.

use num_rational::Rational64;
use proptest::prelude::*;
use proptest::strategy::ValueTree;

use super::ops;
use super::theorems;
use super::theorems_monotone;
use super::types::{Interval, IntervalError};

// ============================================================================
// Unit tests: types
// ============================================================================

#[test]
fn test_interval_new_valid() {
    let iv = Interval::new(Rational64::new(1, 3), Rational64::new(2, 3));
    assert!(iv.is_ok());
    let iv = iv.unwrap();
    assert_eq!(*iv.lower(), Rational64::new(1, 3));
    assert_eq!(*iv.upper(), Rational64::new(2, 3));
}

#[test]
fn test_interval_new_point() {
    let iv = Interval::new(Rational64::from_integer(5), Rational64::from_integer(5));
    assert!(iv.is_ok());
}

#[test]
fn test_interval_new_invalid() {
    let iv = Interval::new(Rational64::from_integer(3), Rational64::from_integer(1));
    assert!(matches!(iv, Err(IntervalError::InvalidBounds { .. })));
}

#[test]
fn test_interval_contains() {
    let iv = Interval::from_integers(1, 5).unwrap();
    assert!(iv.contains(&Rational64::from_integer(1)));
    assert!(iv.contains(&Rational64::from_integer(3)));
    assert!(iv.contains(&Rational64::from_integer(5)));
    assert!(!iv.contains(&Rational64::from_integer(0)));
    assert!(!iv.contains(&Rational64::from_integer(6)));
}

#[test]
fn test_interval_contains_interval() {
    let outer = Interval::from_integers(0, 10).unwrap();
    let inner = Interval::from_integers(2, 8).unwrap();
    assert!(outer.contains_interval(&inner));
    assert!(!inner.contains_interval(&outer));
}

#[test]
fn test_interval_width() {
    let iv = Interval::from_integers(3, 7).unwrap();
    assert_eq!(iv.width(), Rational64::from_integer(4));
}

#[test]
fn test_interval_midpoint() {
    let iv = Interval::from_integers(2, 6).unwrap();
    assert_eq!(iv.midpoint(), Rational64::from_integer(4));
}

#[test]
fn test_interval_contains_zero() {
    let pos = Interval::from_integers(1, 5).unwrap();
    let neg = Interval::from_integers(-5, -1).unwrap();
    let straddle = Interval::from_integers(-2, 3).unwrap();
    assert!(!pos.contains_zero());
    assert!(!neg.contains_zero());
    assert!(straddle.contains_zero());
}

#[test]
fn test_interval_point() {
    let iv = Interval::point(Rational64::from_integer(7));
    assert_eq!(iv.width(), Rational64::from_integer(0));
    assert!(iv.contains(&Rational64::from_integer(7)));
}

// ============================================================================
// Unit tests: operations (rational)
// ============================================================================

#[test]
fn test_add_rational_basic() {
    let a = Interval::from_integers(1, 3).unwrap();
    let b = Interval::from_integers(2, 5).unwrap();
    let sum = ops::add_rational(&a, &b);
    assert_eq!(*sum.lower(), Rational64::from_integer(3));
    assert_eq!(*sum.upper(), Rational64::from_integer(8));
}

#[test]
fn test_sub_rational_basic() {
    let a = Interval::from_integers(3, 7).unwrap();
    let b = Interval::from_integers(1, 2).unwrap();
    let diff = ops::sub_rational(&a, &b);
    assert_eq!(*diff.lower(), Rational64::from_integer(1));
    assert_eq!(*diff.upper(), Rational64::from_integer(6));
}

#[test]
fn test_neg_rational_basic() {
    let a = Interval::from_integers(2, 5).unwrap();
    let neg = ops::neg_rational(&a);
    assert_eq!(*neg.lower(), Rational64::from_integer(-5));
    assert_eq!(*neg.upper(), Rational64::from_integer(-2));
}

#[test]
fn test_mul_rational_both_positive() {
    let a = Interval::from_integers(2, 3).unwrap();
    let b = Interval::from_integers(4, 5).unwrap();
    let prod = ops::mul_rational(&a, &b);
    assert_eq!(*prod.lower(), Rational64::from_integer(8));
    assert_eq!(*prod.upper(), Rational64::from_integer(15));
}

#[test]
fn test_mul_rational_mixed_signs() {
    let a = Interval::from_integers(-2, 3).unwrap();
    let b = Interval::from_integers(-1, 4).unwrap();
    let prod = ops::mul_rational(&a, &b);
    // min(-2*-1, -2*4, 3*-1, 3*4) = min(2, -8, -3, 12) = -8
    // max(...) = 12
    assert_eq!(*prod.lower(), Rational64::from_integer(-8));
    assert_eq!(*prod.upper(), Rational64::from_integer(12));
}

#[test]
fn test_div_rational_basic() {
    let a = Interval::from_integers(4, 8).unwrap();
    let b = Interval::from_integers(2, 4).unwrap();
    let quot = ops::div_rational(&a, &b).unwrap();
    assert_eq!(*quot.lower(), Rational64::from_integer(1));
    assert_eq!(*quot.upper(), Rational64::from_integer(4));
}

#[test]
fn test_div_rational_zero_divisor() {
    let a = Interval::from_integers(1, 3).unwrap();
    let b = Interval::from_integers(-1, 1).unwrap();
    let result = ops::div_rational(&a, &b);
    assert!(matches!(result, Err(IntervalError::DivisionByZero { .. })));
}

#[test]
fn test_intersect_rational_overlap() {
    let a = Interval::from_integers(1, 5).unwrap();
    let b = Interval::from_integers(3, 7).unwrap();
    let inter = ops::intersect_rational(&a, &b).unwrap();
    assert_eq!(*inter.lower(), Rational64::from_integer(3));
    assert_eq!(*inter.upper(), Rational64::from_integer(5));
}

#[test]
fn test_intersect_rational_disjoint() {
    let a = Interval::from_integers(1, 3).unwrap();
    let b = Interval::from_integers(5, 7).unwrap();
    assert!(ops::intersect_rational(&a, &b).is_none());
}

#[test]
fn test_hull_rational() {
    let a = Interval::from_integers(1, 3).unwrap();
    let b = Interval::from_integers(5, 7).unwrap();
    let hull = ops::hull_rational(&a, &b);
    assert_eq!(*hull.lower(), Rational64::from_integer(1));
    assert_eq!(*hull.upper(), Rational64::from_integer(7));
}

// ============================================================================
// Unit tests: operations (f64)
// ============================================================================

#[test]
fn test_add_f64_basic() {
    let a = Interval::new(1.0, 3.0).unwrap();
    let b = Interval::new(2.0, 5.0).unwrap();
    let sum = ops::add_f64(&a, &b);
    assert_eq!(*sum.lower(), 3.0);
    assert_eq!(*sum.upper(), 8.0);
}

#[test]
fn test_mul_f64_mixed() {
    let a = Interval::new(-2.0, 3.0).unwrap();
    let b = Interval::new(-1.0, 4.0).unwrap();
    let prod = ops::mul_f64(&a, &b);
    assert_eq!(*prod.lower(), -8.0);
    assert_eq!(*prod.upper(), 12.0);
}

#[test]
fn test_sqrt_f64_basic() {
    let iv = Interval::new(4.0, 9.0).unwrap();
    let result = ops::sqrt_f64(&iv).unwrap();
    assert!((result.lower() - 2.0).abs() < 1e-10);
    assert!((result.upper() - 3.0).abs() < 1e-10);
}

#[test]
fn test_sqrt_f64_negative() {
    let iv = Interval::new(-4.0, -1.0).unwrap();
    assert!(matches!(
        ops::sqrt_f64(&iv),
        Err(IntervalError::SqrtNegative { .. })
    ));
}

#[test]
fn test_exp_f64_basic() {
    let iv = Interval::new(0.0, 1.0).unwrap();
    let result = ops::exp_f64(&iv);
    assert!((result.lower() - 1.0).abs() < 1e-10);
    assert!((result.upper() - std::f64::consts::E).abs() < 1e-10);
}

#[test]
fn test_ln_f64_basic() {
    let iv = Interval::new(1.0, std::f64::consts::E).unwrap();
    let result = ops::ln_f64(&iv).unwrap();
    assert!(result.lower().abs() < 1e-10);
    assert!((result.upper() - 1.0).abs() < 1e-10);
}

#[test]
fn test_ln_f64_non_positive() {
    let iv = Interval::new(-1.0, 2.0).unwrap();
    assert!(matches!(
        ops::ln_f64(&iv),
        Err(IntervalError::LogNonPositive { .. })
    ));
}

#[test]
fn test_abs_f64_positive() {
    let iv = Interval::new(2.0, 5.0).unwrap();
    let result = ops::abs_f64(&iv);
    assert_eq!(*result.lower(), 2.0);
    assert_eq!(*result.upper(), 5.0);
}

#[test]
fn test_abs_f64_negative() {
    let iv = Interval::new(-5.0, -2.0).unwrap();
    let result = ops::abs_f64(&iv);
    assert_eq!(*result.lower(), 2.0);
    assert_eq!(*result.upper(), 5.0);
}

#[test]
fn test_abs_f64_straddling() {
    let iv = Interval::new(-3.0, 5.0).unwrap();
    let result = ops::abs_f64(&iv);
    assert_eq!(*result.lower(), 0.0);
    assert_eq!(*result.upper(), 5.0);
}

#[test]
fn test_pow_f64_square_positive() {
    let iv = Interval::new(2.0, 3.0).unwrap();
    let result = ops::pow_f64(&iv, 2).unwrap();
    assert_eq!(*result.lower(), 4.0);
    assert_eq!(*result.upper(), 9.0);
}

#[test]
fn test_pow_f64_square_straddling() {
    let iv = Interval::new(-3.0, 2.0).unwrap();
    let result = ops::pow_f64(&iv, 2).unwrap();
    assert_eq!(*result.lower(), 0.0);
    assert_eq!(*result.upper(), 9.0);
}

#[test]
fn test_pow_f64_cube() {
    let iv = Interval::new(-2.0, 3.0).unwrap();
    let result = ops::pow_f64(&iv, 3).unwrap();
    assert_eq!(*result.lower(), -8.0);
    assert_eq!(*result.upper(), 27.0);
}

#[test]
fn test_pow_f64_zero() {
    let iv = Interval::new(2.0, 5.0).unwrap();
    let result = ops::pow_f64(&iv, 0).unwrap();
    assert_eq!(*result.lower(), 1.0);
    assert_eq!(*result.upper(), 1.0);
}

// ============================================================================
// Unit tests: theorems
// ============================================================================

#[test]
fn test_theorem_add_containment() {
    let iv_x = Interval::from_integers(1, 3).unwrap();
    let iv_y = Interval::from_integers(2, 5).unwrap();
    let w = theorems::verify_add_containment(
        Rational64::from_integer(2),
        Rational64::from_integer(4),
        &iv_x,
        &iv_y,
    );
    assert!(w.verified, "T_IA_01 failed: {}", w.theorem);
}

#[test]
fn test_theorem_sub_containment() {
    let iv_x = Interval::from_integers(3, 7).unwrap();
    let iv_y = Interval::from_integers(1, 2).unwrap();
    let w = theorems::verify_sub_containment(
        Rational64::from_integer(5),
        Rational64::from_integer(1),
        &iv_x,
        &iv_y,
    );
    assert!(w.verified, "T_IA_02 failed: {}", w.theorem);
}

#[test]
fn test_theorem_neg_containment() {
    let iv_x = Interval::from_integers(-3, 5).unwrap();
    let w = theorems::verify_neg_containment(Rational64::from_integer(2), &iv_x);
    assert!(w.verified, "T_IA_03 failed: {}", w.theorem);
}

#[test]
fn test_theorem_mul_containment() {
    let iv_x = Interval::from_integers(-2, 3).unwrap();
    let iv_y = Interval::from_integers(-1, 4).unwrap();
    let w = theorems::verify_mul_containment(
        Rational64::from_integer(1),
        Rational64::from_integer(3),
        &iv_x,
        &iv_y,
    );
    assert!(w.verified, "T_IA_04 failed: {}", w.theorem);
}

#[test]
fn test_theorem_div_containment() {
    let iv_x = Interval::from_integers(4, 8).unwrap();
    let iv_y = Interval::from_integers(2, 4).unwrap();
    let w = theorems::verify_div_containment(
        Rational64::from_integer(6),
        Rational64::from_integer(3),
        &iv_x,
        &iv_y,
    );
    assert!(w.verified, "T_IA_05 failed: {}", w.theorem);
}

#[test]
fn test_theorem_subset_transitivity() {
    let iv1 = Interval::from_integers(3, 5).unwrap();
    let iv2 = Interval::from_integers(2, 6).unwrap();
    let iv3 = Interval::from_integers(1, 7).unwrap();
    let w = theorems::verify_subset_transitivity(&iv1, &iv2, &iv3);
    assert!(w.verified, "T_IA_06 failed: {}", w.theorem);
}

#[test]
fn test_theorem_intersection_containment() {
    let iv1 = Interval::from_integers(1, 5).unwrap();
    let iv2 = Interval::from_integers(3, 7).unwrap();
    let w = theorems::verify_intersection_containment(Rational64::from_integer(4), &iv1, &iv2);
    assert!(w.verified, "T_IA_07 failed: {}", w.theorem);
}

#[test]
fn test_theorem_hull_containment() {
    let iv1 = Interval::from_integers(1, 3).unwrap();
    let iv2 = Interval::from_integers(5, 7).unwrap();
    let w = theorems::verify_hull_containment(&iv1, &iv2);
    assert!(w.verified, "T_IA_08 failed: {}", w.theorem);
}

#[test]
fn test_theorem_add_width() {
    let iv1 = Interval::from_integers(1, 4).unwrap();
    let iv2 = Interval::from_integers(2, 7).unwrap();
    let w = theorems::verify_add_width(&iv1, &iv2);
    assert!(w.verified, "T_IA_09 failed: {}", w.theorem);
}

#[test]
fn test_theorem_point_interval() {
    let w = theorems::verify_point_interval(Rational64::from_integer(42));
    assert!(w.verified, "T_IA_10 failed: {}", w.theorem);
}

#[test]
fn test_theorem_scalar_mul() {
    let iv_x = Interval::from_integers(2, 5).unwrap();
    let w = theorems::verify_scalar_mul_containment(
        Rational64::from_integer(3),
        Rational64::from_integer(-2),
        &iv_x,
    );
    assert!(w.verified, "T_IA_11 failed: {}", w.theorem);
}

#[test]
fn test_theorem_exp_containment() {
    let iv = Interval::new(0.0, 1.0).unwrap();
    let w = theorems_monotone::verify_exp_containment(0.5, &iv);
    assert!(w.verified, "T_IA_13 failed: {}", w.theorem);
}

#[test]
fn test_theorem_ln_containment() {
    let iv = Interval::new(1.0, 10.0).unwrap();
    let w = theorems_monotone::verify_ln_containment(5.0, &iv);
    assert!(w.verified, "T_IA_14 failed: {}", w.theorem);
}

#[test]
fn test_theorem_sqrt_containment() {
    let iv = Interval::new(4.0, 16.0).unwrap();
    let w = theorems_monotone::verify_sqrt_containment(9.0, &iv);
    assert!(w.verified, "T_IA_15 failed: {}", w.theorem);
}

#[test]
fn test_theorem_sub_width() {
    let iv1 = Interval::from_integers(1, 4).unwrap();
    let iv2 = Interval::from_integers(2, 7).unwrap();
    let w = theorems_monotone::verify_sub_width(&iv1, &iv2);
    assert!(w.verified, "T_IA_16 failed: {}", w.theorem);
}

#[test]
fn test_theorem_double_negation() {
    let iv = Interval::from_integers(-3, 7).unwrap();
    let w = theorems_monotone::verify_double_negation(&iv);
    assert!(w.verified, "T_IA_17 failed: {}", w.theorem);
}

#[test]
fn test_theorem_mul_commutativity() {
    let iv1 = Interval::from_integers(-2, 3).unwrap();
    let iv2 = Interval::from_integers(1, 5).unwrap();
    let w = theorems_monotone::verify_mul_commutativity(&iv1, &iv2);
    assert!(w.verified, "T_IA_18 failed: {}", w.theorem);
}

#[test]
fn test_theorem_add_commutativity() {
    let iv1 = Interval::from_integers(-2, 3).unwrap();
    let iv2 = Interval::from_integers(1, 5).unwrap();
    let w = theorems_monotone::verify_add_commutativity(&iv1, &iv2);
    assert!(w.verified, "T_IA_19 failed: {}", w.theorem);
}

#[test]
fn test_theorem_add_associativity() {
    let iv1 = Interval::from_integers(1, 2).unwrap();
    let iv2 = Interval::from_integers(3, 4).unwrap();
    let iv3 = Interval::from_integers(5, 6).unwrap();
    let w = theorems_monotone::verify_add_associativity(&iv1, &iv2, &iv3);
    assert!(w.verified, "T_IA_20 failed: {}", w.theorem);
}

// ============================================================================
// Property-based tests (proptest)
// ============================================================================

/// Strategy for generating valid rational intervals with small numerators/denominators.
fn rational_interval_strategy() -> impl Strategy<Value = Interval<Rational64>> {
    // Generate pairs where a <= b with denominators 1..=10
    (1i64..=10, 1i64..=10, -50i64..=50, -50i64..=50).prop_flat_map(|(d1, d2, n1, n2)| {
        let r1 = Rational64::new(n1, d1);
        let r2 = Rational64::new(n2, d2);
        let (lo, hi) = if r1 <= r2 { (r1, r2) } else { (r2, r1) };
        Just(Interval::new(lo, hi).unwrap())
    })
}

/// Strategy for generating a value inside a given rational interval.
fn value_in_interval(iv: &Interval<Rational64>) -> impl Strategy<Value = Rational64> {
    // Generate a rational t in [0, 1] and compute lo + t * (hi - lo)
    let lo = *iv.lower();
    let hi = *iv.upper();
    (0u32..=100).prop_map(move |pct| {
        let t = Rational64::new(pct as i64, 100);
        lo + t * (hi - lo)
    })
}

proptest! {
    #[test]
    fn proptest_add_containment(iv_x in rational_interval_strategy(), iv_y in rational_interval_strategy()) {
        let x_strat = value_in_interval(&iv_x);
        let y_strat = value_in_interval(&iv_y);
        // Test a few sample values
        let mut runner = proptest::test_runner::TestRunner::default();
        for _ in 0..5 {
            let x = x_strat.new_tree(&mut runner).unwrap().current();
            let y = y_strat.new_tree(&mut runner).unwrap().current();
            let w = theorems::verify_add_containment(x, y, &iv_x, &iv_y);
            prop_assert!(w.verified, "T_IA_01 failed for x={}, y={}, iv_x={:?}, iv_y={:?}", x, y, iv_x, iv_y);
        }
    }

    #[test]
    fn proptest_sub_containment(iv_x in rational_interval_strategy(), iv_y in rational_interval_strategy()) {
        let x_strat = value_in_interval(&iv_x);
        let y_strat = value_in_interval(&iv_y);
        let mut runner = proptest::test_runner::TestRunner::default();
        for _ in 0..5 {
            let x = x_strat.new_tree(&mut runner).unwrap().current();
            let y = y_strat.new_tree(&mut runner).unwrap().current();
            let w = theorems::verify_sub_containment(x, y, &iv_x, &iv_y);
            prop_assert!(w.verified, "T_IA_02 failed for x={}, y={}", x, y);
        }
    }

    #[test]
    fn proptest_neg_containment(iv_x in rational_interval_strategy()) {
        let x_strat = value_in_interval(&iv_x);
        let mut runner = proptest::test_runner::TestRunner::default();
        for _ in 0..5 {
            let x = x_strat.new_tree(&mut runner).unwrap().current();
            let w = theorems::verify_neg_containment(x, &iv_x);
            prop_assert!(w.verified, "T_IA_03 failed for x={}", x);
        }
    }

    #[test]
    fn proptest_mul_containment(iv_x in rational_interval_strategy(), iv_y in rational_interval_strategy()) {
        let x_strat = value_in_interval(&iv_x);
        let y_strat = value_in_interval(&iv_y);
        let mut runner = proptest::test_runner::TestRunner::default();
        for _ in 0..5 {
            let x = x_strat.new_tree(&mut runner).unwrap().current();
            let y = y_strat.new_tree(&mut runner).unwrap().current();
            let w = theorems::verify_mul_containment(x, y, &iv_x, &iv_y);
            prop_assert!(w.verified, "T_IA_04 failed for x={}, y={}", x, y);
        }
    }

    #[test]
    fn proptest_div_containment(iv_x in rational_interval_strategy(), iv_y in rational_interval_strategy()) {
        // Skip if divisor contains zero
        let zero = Rational64::from_integer(0);
        prop_assume!(!iv_y.contains(&zero));

        let x_strat = value_in_interval(&iv_x);
        let y_strat = value_in_interval(&iv_y);
        let mut runner = proptest::test_runner::TestRunner::default();
        for _ in 0..5 {
            let x = x_strat.new_tree(&mut runner).unwrap().current();
            let y = y_strat.new_tree(&mut runner).unwrap().current();
            if y == zero { continue; }
            let w = theorems::verify_div_containment(x, y, &iv_x, &iv_y);
            prop_assert!(w.verified, "T_IA_05 failed for x={}, y={}", x, y);
        }
    }

    #[test]
    fn proptest_hull_containment(iv1 in rational_interval_strategy(), iv2 in rational_interval_strategy()) {
        let w = theorems::verify_hull_containment(&iv1, &iv2);
        prop_assert!(w.verified, "T_IA_08 failed");
    }

    #[test]
    fn proptest_add_width(iv1 in rational_interval_strategy(), iv2 in rational_interval_strategy()) {
        let w = theorems::verify_add_width(&iv1, &iv2);
        prop_assert!(w.verified, "T_IA_09 failed");
    }

    #[test]
    fn proptest_double_negation(iv in rational_interval_strategy()) {
        let w = theorems_monotone::verify_double_negation(&iv);
        prop_assert!(w.verified, "T_IA_17 failed");
    }

    #[test]
    fn proptest_mul_commutativity(iv1 in rational_interval_strategy(), iv2 in rational_interval_strategy()) {
        let w = theorems_monotone::verify_mul_commutativity(&iv1, &iv2);
        prop_assert!(w.verified, "T_IA_18 failed");
    }

    #[test]
    fn proptest_add_commutativity(iv1 in rational_interval_strategy(), iv2 in rational_interval_strategy()) {
        let w = theorems_monotone::verify_add_commutativity(&iv1, &iv2);
        prop_assert!(w.verified, "T_IA_19 failed");
    }

    #[test]
    fn proptest_add_associativity(
        iv1 in rational_interval_strategy(),
        iv2 in rational_interval_strategy(),
        iv3 in rational_interval_strategy()
    ) {
        let w = theorems_monotone::verify_add_associativity(&iv1, &iv2, &iv3);
        prop_assert!(w.verified, "T_IA_20 failed");
    }
}

// ============================================================================
// f64 conversion tests
// ============================================================================

#[test]
fn test_f64_from_rational_containment() {
    let exact = Interval::new(Rational64::new(1, 3), Rational64::new(2, 3)).unwrap();
    let approx = Interval::<f64>::from_rational(&exact);
    // The f64 interval should contain the rational bounds (approximately)
    let one_third = 1.0 / 3.0;
    let two_thirds = 2.0 / 3.0;
    assert!(*approx.lower() <= one_third);
    assert!(*approx.upper() >= two_thirds);
}

#[test]
fn test_display_interval() {
    let iv = Interval::from_integers(1, 5).unwrap();
    let s = format!("{}", iv);
    assert_eq!(s, "[1, 5]");
}
