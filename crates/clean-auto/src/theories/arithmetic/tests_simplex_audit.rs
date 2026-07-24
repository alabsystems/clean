// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boundary-condition audits for arithmetic and simplex helpers.

use super::super::types::*;
use super::super::*;
use super::{insert_bound, make_lit, set_zero_assignments};
use crate::cdcl::Lit;
use crate::theories::rational::{DeltaRational, Rational};
use std::collections::BTreeMap;

/// Algorithm audit (regression): `Rational::new()` no longer panics on sign
/// flip when num = i64::MIN and den < 0. Sign normalization is done in i128, so
/// `-i64::MIN` cannot overflow; the result saturates to the in-range boundary.
/// Previously this input triggered "attempt to negate with overflow".
#[test]
fn test_rational_new_i64_min_negative_den_no_panic() {
    // Rational::new(i64::MIN, -1) previously computed (-i64::MIN, 1) and overflowed.
    // Now it saturates the numerator instead of panicking. Value must be positive
    // (mathematically +2^63) and in range.
    let r = Rational::new(i64::MIN, -1);
    assert_eq!(r.numerator(), i64::MAX, "saturates to i64::MAX (was panic)");
    assert_eq!(r.denominator(), 1);
    assert!(r.is_positive());
}

/// Algorithm audit (regression): `Rational::new()` no longer panics when
/// den = i64::MIN. Previously the sign flip `-den` overflowed regardless of
/// the numerator. Zero numerator normalizes cleanly to 0/1.
#[test]
fn test_rational_new_i64_min_den_no_panic() {
    let r = Rational::new(1, i64::MIN);
    // 1 / -2^63 : sign flips to num=-1, den=2^63 (unrepresentable) -> saturates den.
    assert_eq!(r.numerator(), -1);
    assert_eq!(r.denominator(), i64::MAX);
    assert!(r.is_negative());

    // The special zero case reduces exactly to 0/1 with no saturation.
    let z = Rational::new(0, i64::MIN);
    assert_eq!(z.numerator(), 0);
    assert_eq!(z.denominator(), 1);
    assert!(z.is_zero());
}

/// Algorithm audit: Arithmetic operations (add/sub/mul/div) can produce a
/// Rational with num = i64::MIN via `new_checked()`, since `i64::try_from(-2^63)`
/// succeeds. Subsequent `neg()` on such a value silently returns the same
/// negative value due to `wrapping_neg()`.
///
/// This demonstrates the gap between `checked_neg()` (correct) and `neg()`
/// (unsound for i64::MIN numerators).
#[test]
fn test_arithmetic_produces_i64_min_and_neg_wraps() {
    // -(2^32) * 2^31 = -2^63 = i64::MIN
    let a = Rational::from_int(-(1_i64 << 32));
    let b = Rational::from_int(1_i64 << 31);
    let result = a.mul(&b).unwrap();

    // Verify the numerator IS i64::MIN
    assert_eq!(
        result.numerator(),
        i64::MIN,
        "mul should be able to produce i64::MIN as numerator"
    );
    assert_eq!(result.denominator(), 1);

    // neg() with wrapping_neg silently returns the same value — this is WRONG.
    // The mathematical result should be positive 2^63, which doesn't fit in i64.
    let neg_result = result.neg();
    assert_eq!(
        neg_result.numerator(),
        i64::MIN,
        "neg() wrapping produces i64::MIN again (wrapping_neg identity at i64::MIN)"
    );
    assert!(
        neg_result.is_negative(),
        "neg() of a negative Rational with i64::MIN num is still negative — BUG"
    );

    // checked_neg correctly returns None for this case
    assert!(
        result.checked_neg().is_none(),
        "checked_neg() must return None for i64::MIN numerator"
    );
}

/// Algorithm audit: abs() with saturating_abs on i64::MIN produces i64::MAX,
/// which is off-by-one from the true absolute value 2^63.
#[test]
fn test_abs_i64_min_off_by_one() {
    let r = Rational::from_int(i64::MIN);
    let abs_r = r.abs();
    assert_eq!(
        abs_r.numerator(),
        i64::MAX,
        "saturating_abs of i64::MIN produces i64::MAX (off by 1)"
    );
    assert!(abs_r.is_positive(), "abs should produce a positive value");

    // The true absolute value would be i64::MAX + 1 = 2^63, unrepresentable
    // in i64. saturating_abs returns i64::MAX = 2^63 - 1 instead.
    // This is a known approximation, not a crash, but it means
    // abs(r).neg() != r for r = i64::MIN.
}

/// Algorithm audit: pivot path correctly uses checked_neg, not neg, preventing
/// silent corruption when inverse coefficients approach i64::MIN.
///
/// Constructs a tableau where the pivot coefficient is -1 and the constant is
/// a large value, forcing checked_neg on a large magnitude. Verifies the pivot
/// either succeeds correctly or returns Unknown (overflow), never false conflict.
#[test]
fn test_pivot_checked_neg_prevents_corruption() {
    let mut arith = ArithmeticTheory::new();
    let x = ArithVar::new(0);
    let y = ArithVar::new(1);
    let slack = ArithVar::new(2);
    arith.next_id = 3;

    // Tableau: slack = (-1)*x + y
    // Pivoting with x when coeff = -1 computes inv_coeff = 1/(-1) = -1,
    // then negates other coefficients and the constant.
    let mut coeffs = BTreeMap::new();
    coeffs.insert(x, Rational::NEG_ONE);
    coeffs.insert(y, Rational::ONE);
    arith.tableau.push(TableauRow {
        basic_var: slack,
        constant: Rational::from_int(i64::MAX),
        coeffs,
    });
    arith.rebuild_basic_var_index();

    arith
        .assignment
        .insert(x, DeltaRational::from_rational(Rational::ZERO));
    arith
        .assignment
        .insert(y, DeltaRational::from_rational(Rational::ZERO));

    // Force slack to violate its lower bound
    insert_bound(
        &mut arith.lower_bounds,
        slack,
        Rational::from_int(i64::MAX),
        make_lit(0, true),
        0,
    );

    let result = arith.check_and_repair();
    // Must not produce a false conflict from corrupted coefficients
    assert!(
        !matches!(result, TheoryCheckResult::Conflict(_)),
        "pivot with large constant and negative coefficient must not produce false conflict: {result:?}"
    );
}

/// Build a 3-variable infeasible system for conflict clause testing.
/// Tableau: slack = 2x + 3y + z, with slack >= 10 and all non-basics <= 0.
/// Returns (arith, [lit_slack_lower, lit_x_upper, lit_y_upper, lit_z_upper]).
fn setup_conflict_clause_tableau() -> (ArithmeticTheory, [Lit; 4]) {
    let mut arith = ArithmeticTheory::new();
    let x = ArithVar::new(0);
    let y = ArithVar::new(1);
    let z = ArithVar::new(2);
    let slack = ArithVar::new(3);
    arith.next_id = 4;

    let mut coeffs = BTreeMap::new();
    coeffs.insert(x, Rational::from_int(2));
    coeffs.insert(y, Rational::from_int(3));
    coeffs.insert(z, Rational::ONE);
    arith.tableau.push(TableauRow {
        basic_var: slack,
        constant: Rational::ZERO,
        coeffs,
    });
    arith.rebuild_basic_var_index();

    set_zero_assignments(&mut arith, &[x, y, z]);

    let lits = [
        make_lit(0, true),
        make_lit(1, true),
        make_lit(2, true),
        make_lit(3, true),
    ];

    insert_bound(
        &mut arith.lower_bounds,
        slack,
        Rational::from_int(10),
        lits[0],
        0,
    );

    for (var, lit) in [(x, lits[1]), (y, lits[2]), (z, lits[3])] {
        insert_bound(&mut arith.upper_bounds, var, Rational::ZERO, lit, 0);
    }

    (arith, lits)
}

/// Algorithm audit: conflict clause from explain_conflict contains the violated
/// bound plus exactly the blocking bounds (no extra, no missing).
#[test]
fn test_explain_conflict_clause_completeness() {
    let (mut arith, lits) = setup_conflict_clause_tableau();
    let [lit_slack_lower, lit_x_upper, lit_y_upper, lit_z_upper] = lits;

    let result = arith.check_and_repair();
    match result {
        TheoryCheckResult::Conflict(clause) => {
            assert!(
                clause.contains(&lit_slack_lower),
                "must include violated bound"
            );
            assert!(
                clause.contains(&lit_x_upper),
                "must include blocking bound on x"
            );
            assert!(
                clause.contains(&lit_y_upper),
                "must include blocking bound on y"
            );
            assert!(
                clause.contains(&lit_z_upper),
                "must include blocking bound on z"
            );
            assert_eq!(clause.len(), 4, "exactly 4 literals: {clause:?}");
        }
        other => {
            panic!("system is infeasible (slack >= 10, all non-basics <= 0), got: {other:?}");
        }
    }
}

/// Soundness invariant: after assert_literal returns Consistent through
/// the TheorySolver trait, is_consistent() must hold. This exercises the
/// invariant that the `debug_assert!` in check() relies on (solver_impl.rs:45-48)
/// but which only fires in debug builds.
///
/// Uses a multi-variable system that forces simplex pivots through a chain
/// of inequalities. Verifies is_consistent() after every successful assertion
/// and after every backtrack.
#[test]
fn test_is_consistent_invariant_multi_variable_pivots() {
    use crate::smt::{TheoryLiteral, TheorySolver};

    let mut arith = ArithmeticTheory::new();

    // Assert x < y (creates slack, triggers check_and_repair)
    let result = arith.assert_literal(make_lit(0, true), &TheoryLiteral::Lt(TermId(0), TermId(1)));
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert!(
        arith.is_consistent(),
        "invariant: is_consistent must hold after Consistent assert_literal (x < y)"
    );

    // Assert y ≤ z
    let result = arith.assert_literal(make_lit(1, true), &TheoryLiteral::Le(TermId(1), TermId(2)));
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert!(
        arith.is_consistent(),
        "invariant: is_consistent must hold after adding y ≤ z"
    );

    // Assert z ≤ w (builds a chain: x < y ≤ z ≤ w)
    let result = arith.assert_literal(make_lit(2, true), &TheoryLiteral::Le(TermId(2), TermId(3)));
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert!(
        arith.is_consistent(),
        "invariant: is_consistent must hold after adding z ≤ w"
    );

    // Push and add tighter constraints
    arith.push();

    // Assert w < x at level 1 — should conflict with x < y ≤ z ≤ w
    let result = arith.assert_literal(make_lit(3, true), &TheoryLiteral::Lt(TermId(3), TermId(0)));
    assert!(
        matches!(result, TheoryCheckResult::Conflict(_)),
        "cycle x < y ≤ z ≤ w < x must be UNSAT, got: {result:?}"
    );

    // Backtrack and verify invariant still holds
    arith.backtrack(0);
    assert!(
        arith.is_consistent(),
        "invariant: is_consistent must hold after backtrack"
    );
    // Also verify check() agrees
    let check = arith.check();
    assert!(
        matches!(check, TheoryCheckResult::Consistent),
        "check() must return Consistent after backtrack to level 0 with valid chain"
    );
}

/// Soundness invariant: ArithmeticTheory trail lengths must equal the level
/// at all points during push/backtrack sequences. The `if let Some(snapshot)`
/// pattern in backtrack() silently skips restoration when a trail entry is
/// missing. This test verifies the structural invariant that prevents that
/// silent failure from ever being reachable.
#[test]
fn test_arithmetic_trail_length_invariant() {
    use crate::smt::{TheoryLiteral, TheorySolver};

    let mut arith = ArithmeticTheory::new();

    fn assert_trails_match_level(arith: &ArithmeticTheory, ctx: &str) {
        let lvl = arith.level as usize;
        assert_eq!(
            arith.tableau_trail.len(),
            lvl,
            "tableau_trail length mismatch at {ctx}"
        );
        assert_eq!(
            arith.assignment_trail.len(),
            lvl,
            "assignment_trail length mismatch at {ctx}"
        );
        assert_eq!(
            arith.next_id_trail.len(),
            lvl,
            "next_id_trail length mismatch at {ctx}"
        );
        assert_eq!(
            arith.term_to_var_trail.len(),
            lvl,
            "term_to_var_trail length mismatch at {ctx}"
        );
        assert_eq!(
            arith.overflow_corrupted_trail.len(),
            lvl,
            "overflow_corrupted_trail length mismatch at {ctx}"
        );
    }

    assert_trails_match_level(&arith, "initial state");

    arith.push();
    assert_trails_match_level(&arith, "after push to level 1");

    let _ = arith.assert_literal(make_lit(0, true), &TheoryLiteral::Lt(TermId(0), TermId(1)));
    assert_trails_match_level(&arith, "after assert at level 1");

    arith.push();
    assert_trails_match_level(&arith, "after push to level 2");

    let _ = arith.assert_literal(make_lit(1, true), &TheoryLiteral::Le(TermId(2), TermId(3)));
    assert_trails_match_level(&arith, "after assert at level 2");

    arith.backtrack(1);
    assert_trails_match_level(&arith, "after backtrack to level 1");

    // Rebranch: push again from level 1
    arith.push();
    assert_trails_match_level(&arith, "after rebranch push to level 2");

    arith.backtrack(0);
    assert_trails_match_level(&arith, "after backtrack to level 0");
}

/// Algorithm audit: fix_nonbasic_bounds correctly clamps lower-then-upper,
/// ensuring the final assignment respects both bounds when compatible.
fn compatible_bounds_identity_fixture() -> (ArithmeticTheory, ArithVar) {
    let mut arith = ArithmeticTheory::new();
    let x = ArithVar::new(0);
    let slack = ArithVar::new(1);
    arith.next_id = 2;

    let mut coeffs = BTreeMap::new();
    coeffs.insert(x, Rational::ONE);
    arith.tableau.push(TableauRow {
        basic_var: slack,
        constant: Rational::ZERO,
        coeffs,
    });
    arith.rebuild_basic_var_index();

    arith
        .assignment
        .insert(x, DeltaRational::from_rational(Rational::from_int(-5)));

    insert_bound(
        &mut arith.lower_bounds,
        x,
        Rational::from_int(2),
        make_lit(0, true),
        0,
    );
    insert_bound(
        &mut arith.upper_bounds,
        x,
        Rational::from_int(7),
        make_lit(1, true),
        0,
    );

    (arith, x)
}

/// Algorithm audit: fix_nonbasic_bounds correctly clamps lower-then-upper,
/// ensuring the final assignment respects both bounds when compatible.
#[test]
fn test_fix_nonbasic_bounds_clamp_ordering() {
    let (mut arith, x) = compatible_bounds_identity_fixture();

    // After check_and_repair, x should be clamped to lower bound (2)
    let result = arith.check_and_repair();
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "compatible bounds with identity tableau should be satisfiable"
    );

    let x_val = arith.assignment.get(&x).unwrap();
    assert!(
        *x_val >= DeltaRational::from_rational(Rational::from_int(2)),
        "x must satisfy lower bound >= 2, got: {x_val}"
    );
    assert!(
        *x_val <= DeltaRational::from_rational(Rational::from_int(7)),
        "x must satisfy upper bound <= 7, got: {x_val}"
    );
}
