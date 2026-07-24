// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! In-process ay goal solving tests (Part of #1598 AC6: 20+ goals)
//!
//! These tests verify that ay solves goals in-process across all 4 theory
//! areas: propositional, integer arithmetic, bitvectors, arrays.

use super::*;
use ay::Sort;

// --- Propositional goals ---

/// Goal: p | !p (tautology)
#[test]
fn test_goal_prop_excluded_middle() {
    let mut b = AyBackend::new(AyLogic::QfUf);
    let p = b.fresh_bool("p");
    let not_p = b.not(p);
    let taut = b.or(p, not_p);
    // Negate the tautology — should be UNSAT
    let neg = b.not(taut);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: (p -> q) -> (!q -> !p) (contrapositive)
#[test]
fn test_goal_prop_contrapositive() {
    let mut b = AyBackend::new(AyLogic::QfUf);
    let p = b.fresh_bool("p");
    let q = b.fresh_bool("q");
    let p_imp_q = b.implies(p, q);
    let not_q = b.not(q);
    let not_p = b.not(p);
    let contra = b.implies(not_q, not_p);
    let full = b.implies(p_imp_q, contra);
    let neg = b.not(full);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: (p & q) -> p (conjunction elimination)
#[test]
fn test_goal_prop_and_elim() {
    let mut b = AyBackend::new(AyLogic::QfUf);
    let p = b.fresh_bool("p");
    let q = b.fresh_bool("q");
    let p_and_q = b.and(p, q);
    let goal = b.implies(p_and_q, p);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: p -> (p | q) (disjunction introduction)
#[test]
fn test_goal_prop_or_intro() {
    let mut b = AyBackend::new(AyLogic::QfUf);
    let p = b.fresh_bool("p");
    let q = b.fresh_bool("q");
    let p_or_q = b.or(p, q);
    let goal = b.implies(p, p_or_q);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: (p -> q) & (q -> r) -> (p -> r) (hypothetical syllogism)
#[test]
fn test_goal_prop_syllogism() {
    let mut b = AyBackend::new(AyLogic::QfUf);
    let p = b.fresh_bool("p");
    let q = b.fresh_bool("q");
    let r = b.fresh_bool("r");
    let p_imp_q = b.implies(p, q);
    let q_imp_r = b.implies(q, r);
    let premise = b.and(p_imp_q, q_imp_r);
    let p_imp_r = b.implies(p, r);
    let goal = b.implies(premise, p_imp_r);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

// --- Integer arithmetic goals ---

/// Goal: x > 0 & y > 0 -> x + y > 0
#[test]
fn test_goal_arith_sum_positive() {
    let mut b = AyBackend::new(AyLogic::QfLia);
    let x = b.fresh_int("x");
    let y = b.fresh_int("y");
    let zero = b.int_const(0);
    let x_pos = b.gt(x, zero);
    let y_pos = b.gt(y, zero);
    let xy = b.add(x, y);
    let sum_pos = b.gt(xy, zero);
    let premise = b.and(x_pos, y_pos);
    let goal = b.implies(premise, sum_pos);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: x >= 5 -> x >= 3
#[test]
fn test_goal_arith_transitivity_le() {
    let mut b = AyBackend::new(AyLogic::QfLia);
    let x = b.fresh_int("x");
    let five = b.int_const(5);
    let three = b.int_const(3);
    let x_ge_5 = b.ge(x, five);
    let x_ge_3 = b.ge(x, three);
    let goal = b.implies(x_ge_5, x_ge_3);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: x = 2 & y = 3 -> x + y = 5
#[test]
fn test_goal_arith_concrete_addition() {
    let mut b = AyBackend::new(AyLogic::QfLia);
    let x = b.fresh_int("x");
    let y = b.fresh_int("y");
    let two = b.int_const(2);
    let three = b.int_const(3);
    let five = b.int_const(5);
    let x_eq_2 = b.eq(x, two);
    let y_eq_3 = b.eq(y, three);
    let xy = b.add(x, y);
    let sum_eq_5 = b.eq(xy, five);
    let premise = b.and(x_eq_2, y_eq_3);
    let goal = b.implies(premise, sum_eq_5);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: x * 2 = x + x
#[test]
fn test_goal_arith_double() {
    let mut b = AyBackend::new(AyLogic::QfLia);
    let x = b.fresh_int("x");
    let two = b.int_const(2);
    let x_times_2 = b.mul(x, two);
    let x_plus_x = b.add(x, x);
    let goal = b.eq(x_times_2, x_plus_x);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: 0 <= x & x < 10 -> x <= 9
#[test]
fn test_goal_arith_bound() {
    let mut b = AyBackend::new(AyLogic::QfLia);
    let x = b.fresh_int("x");
    let zero = b.int_const(0);
    let nine = b.int_const(9);
    let ten = b.int_const(10);
    let x_ge_0 = b.ge(x, zero);
    let x_lt_10 = b.lt(x, ten);
    let x_le_9 = b.le(x, nine);
    let premise = b.and(x_ge_0, x_lt_10);
    let goal = b.implies(premise, x_le_9);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: x - x = 0
#[test]
fn test_goal_arith_sub_self() {
    let mut b = AyBackend::new(AyLogic::QfLia);
    let x = b.fresh_int("x");
    let zero = b.int_const(0);
    let x_sub_x = b.sub(x, x);
    let goal = b.eq(x_sub_x, zero);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

// --- Bitvector goals ---

/// Goal: bvadd(x, 0) = x (BV identity)
#[test]
fn test_goal_bv_add_zero() {
    let mut b = AyBackend::new(AyLogic::QfBv);
    let x = b.fresh_bv("x", 32);
    let zero = b.bv_const(0, 32);
    let x_add_0 = b.bvadd(x, zero);
    let goal = b.eq(x_add_0, x);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: bvsub(x, x) = 0 (BV self-subtraction)
#[test]
fn test_goal_bv_sub_self() {
    let mut b = AyBackend::new(AyLogic::QfBv);
    let x = b.fresh_bv("x", 32);
    let zero = b.bv_const(0, 32);
    let x_sub_x = b.bvsub(x, x);
    let goal = b.eq(x_sub_x, zero);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: bvult(x, y) & bvult(y, z) -> bvult(x, z) (BV unsigned lt transitivity)
#[test]
fn test_goal_bv_ult_transitive() {
    let mut b = AyBackend::new(AyLogic::QfBv);
    let x = b.fresh_bv("x", 8);
    let y = b.fresh_bv("y", 8);
    let z = b.fresh_bv("z", 8);
    let x_lt_y = b.bvult(x, y);
    let y_lt_z = b.bvult(y, z);
    let x_lt_z = b.bvult(x, z);
    let premise = b.and(x_lt_y, y_lt_z);
    let goal = b.implies(premise, x_lt_z);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: bvmul(x, 1) = x (BV multiply by 1)
#[test]
fn test_goal_bv_mul_one() {
    let mut b = AyBackend::new(AyLogic::QfBv);
    let x = b.fresh_bv("x", 16);
    let one = b.bv_const(1, 16);
    let x_mul_1 = b.bvmul(x, one);
    let goal = b.eq(x_mul_1, x);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

// --- Array goals ---

/// Goal: select(store(a, i, v), i) = v (array read-after-write, same index)
#[test]
fn test_goal_array_read_after_write_same() {
    let mut b = AyBackend::new(AyLogic::QfAuflia);
    let a = b.fresh_array("a", Sort::Int, Sort::Int);
    let i = b.fresh_int("i");
    let v = b.fresh_int("v");
    let stored = b.store(a, i, v);
    let read = b.select(stored, i);
    let goal = b.eq(read, v);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: i != j -> select(store(a, i, v), j) = select(a, j) (read-after-write, different index)
#[test]
fn test_goal_array_read_after_write_diff() {
    let mut b = AyBackend::new(AyLogic::QfAuflia);
    let a = b.fresh_array("a", Sort::Int, Sort::Int);
    let i = b.fresh_int("i");
    let j = b.fresh_int("j");
    let v = b.fresh_int("v");
    let i_neq_j = b.neq(i, j);
    let stored = b.store(a, i, v);
    let read_stored = b.select(stored, j);
    let read_orig = b.select(a, j);
    let same = b.eq(read_stored, read_orig);
    let goal = b.implies(i_neq_j, same);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: select(const_array(0), i) = 0 (constant array)
#[test]
fn test_goal_array_const_read() {
    let mut b = AyBackend::new(AyLogic::QfAuflia);
    let zero = b.int_const(0);
    let arr = b.const_array(Sort::Int, zero);
    let i = b.fresh_int("i");
    let read = b.select(arr, i);
    let zero2 = b.int_const(0);
    let goal = b.eq(read, zero2);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: store(store(a, i, v1), i, v2) and reading at i gives v2 (last write wins)
#[test]
fn test_goal_array_last_write_wins() {
    let mut b = AyBackend::new(AyLogic::QfAuflia);
    let a = b.fresh_array("a", Sort::Int, Sort::Int);
    let i = b.fresh_int("i");
    let v1 = b.fresh_int("v1");
    let v2 = b.fresh_int("v2");
    let first_store = b.store(a, i, v1);
    let second_store = b.store(first_store, i, v2);
    let read = b.select(second_store, i);
    let goal = b.eq(read, v2);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

// --- Mixed/equality goals ---

/// Goal: x = y & y = z -> x = z (equality transitivity via UF)
#[test]
fn test_goal_uf_equality_transitivity() {
    let mut b = AyBackend::new(AyLogic::QfUf);
    let x = b.fresh_int("x");
    let y = b.fresh_int("y");
    let z = b.fresh_int("z");
    let x_eq_y = b.eq(x, y);
    let y_eq_z = b.eq(y, z);
    let x_eq_z = b.eq(x, z);
    let premise = b.and(x_eq_y, y_eq_z);
    let goal = b.implies(premise, x_eq_z);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: ite(true, a, b) = a
#[test]
fn test_goal_ite_true() {
    let mut b = AyBackend::new(AyLogic::QfUf);
    let a = b.fresh_int("a");
    let b_var = b.fresh_int("b");
    let t = b.bool_const(true);
    let result = b.ite(t, a, b_var);
    let goal = b.eq(result, a);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}

/// Goal: ite(false, a, b) = b
#[test]
fn test_goal_ite_false() {
    let mut b = AyBackend::new(AyLogic::QfUf);
    let a = b.fresh_int("a");
    let b_var = b.fresh_int("b");
    let f = b.bool_const(false);
    let result = b.ite(f, a, b_var);
    let goal = b.eq(result, b_var);
    let neg = b.not(goal);
    b.assert_term(neg);
    assert_eq!(b.check_sat(), AySolveResult::Unsat);
}
