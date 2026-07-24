// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core simplex behavior and overflow-state regression coverage.

use super::super::types::*;
use super::super::*;
use super::{insert_bound, make_lit, set_zero_assignments};
use crate::smt::TheorySolver;
use crate::theories::rational::{DeltaRational, Rational};
use std::collections::BTreeMap;

/// Simplex: simple feasible system with one constraint.
#[test]
fn test_simplex_single_upper_bound_feasible() {
    let mut arith = ArithmeticTheory::new();
    let x = TermId(0);
    let v = arith.get_or_create_var(x);

    // x <= 10
    let result = arith.assert_upper_bound(
        v,
        DeltaRational::from_rational(Rational::from_int(10)),
        make_lit(0, true),
    );
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // check_and_repair should find no violations
    let check = arith.check_and_repair();
    assert!(
        matches!(check, TheoryCheckResult::Consistent),
        "single upper bound should be feasible"
    );
}

/// Simplex: conflicting bounds on a single variable.
#[test]
fn test_simplex_conflicting_bounds_single_var() {
    let mut arith = ArithmeticTheory::new();
    let x = TermId(0);
    let v = arith.get_or_create_var(x);

    // x >= 10 (set lower bound directly)
    insert_bound(
        &mut arith.lower_bounds,
        v,
        Rational::from_int(10),
        make_lit(0, true),
        0,
    );

    // x <= 5 — conflicts with x >= 10
    let r2 = arith.assert_upper_bound(
        v,
        DeltaRational::from_rational(Rational::from_int(5)),
        make_lit(1, true),
    );
    assert!(
        matches!(r2, TheoryCheckResult::Conflict(_)),
        "x >= 10 AND x <= 5 must be UNSAT"
    );
}

/// Simplex: tableau with two variables, no bound violation.
/// slack = x + y = 5, slack <= 10 — satisfied without pivot.
#[test]
fn test_simplex_tableau_no_violation() {
    let mut arith = ArithmeticTheory::new();
    let x = ArithVar::new(0);
    let y = ArithVar::new(1);
    let slack = ArithVar::new(2);
    arith.next_id = 3;

    // Tableau: slack = x + y
    let mut coeffs = BTreeMap::new();
    coeffs.insert(x, Rational::ONE);
    coeffs.insert(y, Rational::ONE);
    arith.tableau.push(TableauRow {
        basic_var: slack,
        constant: Rational::ZERO,
        coeffs,
    });
    arith.rebuild_basic_var_index();

    // Assignments: x = 3, y = 2 → slack = 5
    arith
        .assignment
        .insert(x, DeltaRational::from_rational(Rational::from_int(3)));
    arith
        .assignment
        .insert(y, DeltaRational::from_rational(Rational::from_int(2)));

    // slack <= 10 (easily satisfied since slack = 5)
    insert_bound(
        &mut arith.upper_bounds,
        slack,
        Rational::from_int(10),
        make_lit(0, true),
        0,
    );

    let check = arith.check_and_repair();
    assert!(
        matches!(check, TheoryCheckResult::Consistent),
        "slack = x + y = 5 <= 10 should be feasible"
    );
}

/// Simplex: infeasible tableau produces non-empty conflict clause.
fn infeasible_sum_fixture() -> (ArithmeticTheory, Lit) {
    let mut arith = ArithmeticTheory::new();
    let x = ArithVar::new(0);
    let y = ArithVar::new(1);
    let slack = ArithVar::new(2);
    arith.next_id = 3;

    let mut coeffs = BTreeMap::new();
    coeffs.insert(x, Rational::ONE);
    coeffs.insert(y, Rational::ONE);
    arith.tableau.push(TableauRow {
        basic_var: slack,
        constant: Rational::ZERO,
        coeffs,
    });
    arith.rebuild_basic_var_index();

    arith
        .assignment
        .insert(x, DeltaRational::from_rational(Rational::from_int(3)));
    arith
        .assignment
        .insert(y, DeltaRational::from_rational(Rational::from_int(4)));

    let lit_slack = make_lit(0, true);
    insert_bound(
        &mut arith.upper_bounds,
        slack,
        Rational::from_int(5),
        lit_slack,
        0,
    );
    insert_bound(
        &mut arith.lower_bounds,
        x,
        Rational::from_int(3),
        make_lit(1, true),
        0,
    );
    insert_bound(
        &mut arith.lower_bounds,
        y,
        Rational::from_int(4),
        make_lit(2, true),
        0,
    );

    (arith, lit_slack)
}

/// Simplex: infeasible tableau produces non-empty conflict clause.
#[test]
fn test_simplex_infeasible_produces_conflict() {
    let (mut arith, lit_slack) = infeasible_sum_fixture();

    let check = arith.check_and_repair();
    match check {
        TheoryCheckResult::Conflict(clause) => {
            assert!(!clause.is_empty(), "conflict clause must be non-empty");
            assert!(
                clause.contains(&lit_slack),
                "conflict should reference slack upper bound"
            );
        }
        other => {
            panic!(
                "slack = x + y = 7 > 5 with x >= 3, y >= 4 should be infeasible, got: {other:?}"
            );
        }
    }
}

/// Build a 2-row tableau designed to overflow during `substitute_pivot_row`:
///   Row 0: slack1 = BIG + x + y  (pivot row)
///   Row 1: slack2 = BIG*x + y    (dependent — BIG * (-BIG) overflows)
///
/// y is bounded at 0 so `find_pivot` deterministically selects x.
/// Returns (arith, slack1, big) for test assertions.
fn setup_overflow_tableau() -> (ArithmeticTheory, ArithVar, Rational) {
    let mut arith = ArithmeticTheory::new();
    let x = ArithVar::new(0);
    let y = ArithVar::new(1);
    let slack1 = ArithVar::new(2);
    let slack2 = ArithVar::new(3);
    arith.next_id = 4;
    let big = Rational::from_int(1_i64 << 32);

    let mut coeffs1 = BTreeMap::new();
    coeffs1.insert(x, Rational::ONE);
    coeffs1.insert(y, Rational::ONE);
    arith.tableau.push(TableauRow {
        basic_var: slack1,
        constant: big,
        coeffs: coeffs1,
    });

    let mut coeffs2 = BTreeMap::new();
    coeffs2.insert(x, big);
    coeffs2.insert(y, Rational::ONE);
    arith.tableau.push(TableauRow {
        basic_var: slack2,
        constant: Rational::ZERO,
        coeffs: coeffs2,
    });
    arith.rebuild_basic_var_index();

    set_zero_assignments(&mut arith, &[x, y]);

    // Block y from pivot candidacy so find_pivot deterministically picks x.
    insert_bound(
        &mut arith.upper_bounds,
        y,
        Rational::ZERO,
        make_lit(1, true),
        0,
    );

    (arith, slack1, big)
}

/// Force a lower-bound violation on slack1 that triggers the overflowing pivot.
fn trigger_overflow_pivot(
    arith: &mut ArithmeticTheory,
    slack1: ArithVar,
    big: Rational,
    level: u32,
) {
    let bound_val = big.add(&Rational::ONE).unwrap();
    insert_bound(
        &mut arith.lower_bounds,
        slack1,
        bound_val,
        make_lit(0, true),
        level,
    );
}

/// Regression: partial pivot corruption (#2324/#2399). Verifies overflow_corrupted
/// flag is set and no false conflict is produced from corrupted tableau state.
#[test]
fn test_pivot_partial_overflow_corrupts_tableau_state() {
    let (mut arith, slack1, big) = setup_overflow_tableau();
    trigger_overflow_pivot(&mut arith, slack1, big, 0);

    let result = arith.check_and_repair();
    assert!(
        !matches!(result, TheoryCheckResult::Conflict(_)),
        "overflow during pivot substitution must not produce false conflict: {result:?}"
    );
    assert!(
        arith.overflow_corrupted,
        "overflow_corrupted flag must be set after substitute_pivot_row overflow"
    );

    // Second check on corrupted state must also not produce false conflict.
    let result2 = arith.check_and_repair();
    assert!(
        !matches!(result2, TheoryCheckResult::Conflict(_)),
        "second check after pivot overflow must not produce false conflict: {result2:?}"
    );
}

/// Regression: overflow_corrupted flag preserved across push/backtrack (#2399).
/// Corruption at level 1 must survive backtrack to 1, clear on backtrack to 0.
#[test]
fn test_overflow_corrupted_flag_backtrack_restore() {
    let (mut arith, slack1, big) = setup_overflow_tableau();

    arith.push(); // level 0 → 1 (clean snapshot)
    assert!(
        !arith.overflow_corrupted,
        "flag must be false before corruption"
    );

    trigger_overflow_pivot(&mut arith, slack1, big, 1);
    let _ = arith.check_and_repair();
    assert!(
        arith.overflow_corrupted,
        "flag must be set after overflow at level 1"
    );

    arith.push(); // level 1 → 2 (corrupted snapshot)
    assert!(arith.overflow_corrupted, "flag persists at level 2");

    arith.backtrack(1);
    assert!(
        arith.overflow_corrupted,
        "backtrack to level 1 must preserve corruption flag"
    );

    arith.backtrack(0);
    assert!(
        !arith.overflow_corrupted,
        "backtrack to level 0 must clear corruption flag"
    );
}
