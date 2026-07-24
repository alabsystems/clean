// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Basic SAT/UNSAT smoke tests for the Ay backend.

use super::*;

#[test]
fn test_basic_sat() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let x = backend.fresh_int("x");
    let zero = backend.int_const(0);
    let x_gt_zero = backend.gt(x, zero);
    backend.assert_term(x_gt_zero);
    assert_eq!(backend.check_sat(), AySolveResult::Sat);
}

#[test]
fn test_basic_unsat() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let x = backend.fresh_int("x");
    let zero = backend.int_const(0);
    let x_lt_zero = backend.lt(x, zero);
    let x_gt_zero = backend.gt(x, zero);
    let both = backend.and(x_lt_zero, x_gt_zero);
    backend.assert_term(both);
    assert_eq!(backend.check_sat(), AySolveResult::Unsat);
}

#[test]
fn test_equality_transitivity() {
    let mut backend = AyBackend::new(AyLogic::QfUf);
    let x = backend.fresh_int("x");
    let y = backend.fresh_int("y");
    let z = backend.fresh_int("z");
    let x_eq_y = backend.eq(x, y);
    let y_eq_z = backend.eq(y, z);
    let x_neq_z = backend.neq(x, z);
    backend.assert_term(x_eq_y);
    backend.assert_term(y_eq_z);
    backend.assert_term(x_neq_z);
    assert_eq!(backend.check_sat(), AySolveResult::Unsat);
}

#[test]
fn test_incremental() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let x = backend.fresh_int("x");
    let zero = backend.int_const(0);
    let ten = backend.int_const(10);
    let x_gt_zero = backend.gt(x, zero);
    backend.assert_term(x_gt_zero);
    backend.push();
    let x_lt_ten = backend.lt(x, ten);
    backend.assert_term(x_lt_ten);
    assert_eq!(backend.check_sat(), AySolveResult::Sat);
    backend.pop();
    let hundred = backend.int_const(100);
    let x_gt_hundred = backend.gt(x, hundred);
    backend.assert_term(x_gt_hundred);
    assert_eq!(backend.check_sat(), AySolveResult::Sat);
}
