// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the decreasing-obligation model: the `Nat.lt` goal builder,
//! obligation construction, and the strategy enum. Split out of
//! `decreasing.rs` for file size.

use super::*;

#[test]
fn test_build_nat_decreasing_goal() {
    let measure = Expr::const_str("myMeasure");
    let rec_arg = Expr::const_str("smaller_x");
    let current_arg = Expr::const_str("x");

    let goal = build_nat_decreasing_goal(&measure, &rec_arg, &current_arg);

    // Should produce: Nat.lt (myMeasure smaller_x) (myMeasure x)
    let expected_lhs = Expr::app(Expr::const_str("myMeasure"), Expr::const_str("smaller_x"));
    let expected_rhs = Expr::app(Expr::const_str("myMeasure"), Expr::const_str("x"));
    let expected = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.lt"), vec![]),
            expected_lhs,
        ),
        expected_rhs,
    );
    assert_eq!(format!("{goal:?}"), format!("{expected:?}"));
}

#[test]
fn test_decreasing_obligation_creation() {
    let goal = Expr::const_str("SomeGoal");
    let rec_arg = Expr::const_str("n_minus_1");
    let cur_arg = Expr::const_str("n");
    let ob = DecreasingObligation::new(goal.clone(), rec_arg.clone(), cur_arg.clone());
    assert_eq!(format!("{:?}", ob.goal_type), format!("{goal:?}"));
    assert_eq!(format!("{:?}", ob.rec_arg), format!("{rec_arg:?}"));
    assert_eq!(format!("{:?}", ob.current_arg), format!("{cur_arg:?}"));
}

#[test]
fn test_decreasing_strategy_variants() {
    assert_ne!(DecreasingStrategy::UserTactic, DecreasingStrategy::Sorry);
    assert_eq!(DecreasingStrategy::Mathverse, DecreasingStrategy::Mathverse);
}
