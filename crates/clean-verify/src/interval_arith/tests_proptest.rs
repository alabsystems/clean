// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property-based tests for interval arithmetic soundness theorems.

use num_rational::Rational64;
use proptest::prelude::*;
use proptest::strategy::ValueTree;

use super::theorems;
use super::theorems_algebraic;
use super::types::Interval;

/// Strategy for generating valid rational intervals with small values.
fn rational_interval_strategy() -> impl Strategy<Value = Interval> {
    (1i64..=10, 1i64..=10, -50i64..=50, -50i64..=50).prop_flat_map(|(d1, d2, n1, n2)| {
        let r1 = Rational64::new(n1, d1);
        let r2 = Rational64::new(n2, d2);
        let (lo, hi) = if r1 <= r2 { (r1, r2) } else { (r2, r1) };
        Just(Interval::new(lo, hi).unwrap())
    })
}

/// Generate a value within an interval.
fn value_in_interval(iv: &Interval) -> impl Strategy<Value = Rational64> {
    let lo = iv.lo();
    let hi = iv.hi();
    (0u32..=100).prop_map(move |pct| {
        let t = Rational64::new(pct as i64, 100);
        lo + t * (hi - lo)
    })
}

proptest! {
    #[test]
    fn proptest_add_containment(
        a in rational_interval_strategy(),
        b in rational_interval_strategy()
    ) {
        let x_strat = value_in_interval(&a);
        let y_strat = value_in_interval(&b);
        let mut runner = proptest::test_runner::TestRunner::default();
        for _ in 0..5 {
            let x = x_strat.new_tree(&mut runner).unwrap().current();
            let y = y_strat.new_tree(&mut runner).unwrap().current();
            let w = theorems::verify_t01_add_containment(x, y, &a, &b);
            prop_assert!(w.verified, "T01 failed for x={}, y={}", x, y);
        }
    }

    #[test]
    fn proptest_sub_containment(
        a in rational_interval_strategy(),
        b in rational_interval_strategy()
    ) {
        let x_strat = value_in_interval(&a);
        let y_strat = value_in_interval(&b);
        let mut runner = proptest::test_runner::TestRunner::default();
        for _ in 0..5 {
            let x = x_strat.new_tree(&mut runner).unwrap().current();
            let y = y_strat.new_tree(&mut runner).unwrap().current();
            let w = theorems::verify_t02_sub_containment(x, y, &a, &b);
            prop_assert!(w.verified, "T02 failed for x={}, y={}", x, y);
        }
    }

    #[test]
    fn proptest_neg_containment(a in rational_interval_strategy()) {
        let x_strat = value_in_interval(&a);
        let mut runner = proptest::test_runner::TestRunner::default();
        for _ in 0..5 {
            let x = x_strat.new_tree(&mut runner).unwrap().current();
            let w = theorems::verify_t03_neg_containment(x, &a);
            prop_assert!(w.verified, "T03 failed for x={}", x);
        }
    }

    #[test]
    fn proptest_mul_containment(
        a in rational_interval_strategy(),
        b in rational_interval_strategy()
    ) {
        let x_strat = value_in_interval(&a);
        let y_strat = value_in_interval(&b);
        let mut runner = proptest::test_runner::TestRunner::default();
        for _ in 0..5 {
            let x = x_strat.new_tree(&mut runner).unwrap().current();
            let y = y_strat.new_tree(&mut runner).unwrap().current();
            let w = theorems::verify_t04_mul_containment(x, y, &a, &b);
            prop_assert!(w.verified, "T04 failed for x={}, y={}", x, y);
        }
    }

    #[test]
    fn proptest_div_containment(
        a in rational_interval_strategy(),
        b in rational_interval_strategy()
    ) {
        let zero = Rational64::from_integer(0);
        prop_assume!(!b.contains(zero));

        let x_strat = value_in_interval(&a);
        let y_strat = value_in_interval(&b);
        let mut runner = proptest::test_runner::TestRunner::default();
        for _ in 0..5 {
            let x = x_strat.new_tree(&mut runner).unwrap().current();
            let y = y_strat.new_tree(&mut runner).unwrap().current();
            if y == zero { continue; }
            let w = theorems::verify_t05_div_containment(x, y, &a, &b);
            prop_assert!(w.verified, "T05 failed for x={}, y={}", x, y);
        }
    }

    #[test]
    fn proptest_abs_containment(a in rational_interval_strategy()) {
        let x_strat = value_in_interval(&a);
        let mut runner = proptest::test_runner::TestRunner::default();
        for _ in 0..5 {
            let x = x_strat.new_tree(&mut runner).unwrap().current();
            let w = theorems::verify_t06_abs_containment(x, &a);
            prop_assert!(w.verified, "T06 failed for x={}", x);
        }
    }

    #[test]
    fn proptest_hull_containment(
        a in rational_interval_strategy(),
        b in rational_interval_strategy()
    ) {
        let w = theorems::verify_t10_hull_containment(&a, &b);
        prop_assert!(w.verified, "T10 failed");
    }

    #[test]
    fn proptest_add_width(
        a in rational_interval_strategy(),
        b in rational_interval_strategy()
    ) {
        let w = theorems_algebraic::verify_t15_add_width(&a, &b);
        prop_assert!(w.verified, "T15 failed");
    }

    #[test]
    fn proptest_sub_width(
        a in rational_interval_strategy(),
        b in rational_interval_strategy()
    ) {
        let w = theorems_algebraic::verify_t16_sub_width(&a, &b);
        prop_assert!(w.verified, "T16 failed");
    }

    #[test]
    fn proptest_neg_width(a in rational_interval_strategy()) {
        let w = theorems_algebraic::verify_t17_neg_width(&a);
        prop_assert!(w.verified, "T17 failed");
    }

    #[test]
    fn proptest_add_commutativity(
        a in rational_interval_strategy(),
        b in rational_interval_strategy()
    ) {
        let w = theorems_algebraic::verify_t18_add_commutativity(&a, &b);
        prop_assert!(w.verified, "T18 failed");
    }

    #[test]
    fn proptest_mul_commutativity(
        a in rational_interval_strategy(),
        b in rational_interval_strategy()
    ) {
        let w = theorems_algebraic::verify_t19_mul_commutativity(&a, &b);
        prop_assert!(w.verified, "T19 failed");
    }

    #[test]
    fn proptest_add_associativity(
        a in rational_interval_strategy(),
        b in rational_interval_strategy(),
        c in rational_interval_strategy()
    ) {
        let w = theorems_algebraic::verify_t20_add_associativity(&a, &b, &c);
        prop_assert!(w.verified, "T20 failed");
    }
}
