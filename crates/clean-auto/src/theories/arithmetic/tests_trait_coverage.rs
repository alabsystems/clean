// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof coverage: TheorySolver trait methods that lacked direct unit tests.
//!
//! Gaps identified by P1 proof_coverage audit (smt-soundness theme):
//! - check() returning Unknown when overflow_corrupted (#2384, #2399)
//! - suggest_phase() / suggest_relation_phase() / current_term_value()
//! - assert_shared_equality() / assert_shared_disequality()
//! - collect_statistics()

use super::super::*;
use super::make_lit;
use crate::smt::{TheoryLiteral, TheorySolver};
use crate::theories::rational::{DeltaRational, Rational};
use std::collections::HashMap;

const EXPECTED_ARITH_STAT_KEYS: [&str; 5] = [
    "arith_vars",
    "arith_rows",
    "arith_lower_bounds",
    "arith_upper_bounds",
    "arith_pending_deduced",
];

fn assert_expected_arith_stat_keys(stats: &[(&'static str, u64)]) {
    assert_eq!(
        stats.len(),
        EXPECTED_ARITH_STAT_KEYS.len(),
        "collect_statistics() must return exactly 5 entries, got: {stats:?}"
    );

    let mut actual_keys: Vec<_> = stats.iter().map(|(key, _)| *key).collect();
    actual_keys.sort_unstable();

    let mut expected_keys = EXPECTED_ARITH_STAT_KEYS.to_vec();
    expected_keys.sort_unstable();

    assert_eq!(
        actual_keys, expected_keys,
        "collect_statistics() returned unexpected stat keys: {stats:?}"
    );
}

// =========================================================================
// check() returning Unknown on overflow_corrupted
// =========================================================================

/// The trait-level check() must return Unknown when overflow_corrupted is
/// true. Existing tests only verify check_and_repair() in this scenario;
/// this test exercises the TheorySolver::check(&self) path directly.
#[test]
fn test_check_returns_unknown_when_overflow_corrupted() {
    let mut arith = ArithmeticTheory::new();

    // Directly set the flag rather than triggering a real overflow —
    // we are testing the trait method's branch, not the pivot code.
    arith.overflow_corrupted = true;

    let result = arith.check();
    assert!(
        matches!(result, TheoryCheckResult::Unknown),
        "check() must return Unknown when overflow_corrupted is true, got: {result:?}"
    );
}

/// check() must return Consistent when overflow_corrupted is false and
/// the solver is in a trivially-consistent empty state.
#[test]
fn test_check_returns_consistent_when_clean() {
    let arith = ArithmeticTheory::new();
    let result = arith.check();
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "check() on empty solver must be Consistent, got: {result:?}"
    );
}

/// After overflow corruption, backtrack to clean level, check() must
/// return Consistent again. Exercises the full lifecycle through the
/// trait method.
#[test]
fn test_check_consistent_after_backtrack_clears_corruption() {
    let mut arith = ArithmeticTheory::new();

    arith.push(); // level 0 → 1, snapshot clean state
    arith.overflow_corrupted = true;

    let result = arith.check();
    assert!(
        matches!(result, TheoryCheckResult::Unknown),
        "check() at corrupted level 1 must be Unknown"
    );

    arith.backtrack(0);

    let result = arith.check();
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "check() after backtrack to clean level 0 must be Consistent, got: {result:?}"
    );
}

// =========================================================================
// suggest_phase() / suggest_relation_phase() / current_term_value()
// =========================================================================

/// suggest_phase for Lt: returns Some(true) when current model satisfies
/// lhs < rhs, Some(false) when it doesn't.
#[test]
fn test_suggest_phase_lt_satisfied() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);

    // Create vars and set assignments: x=2, y=5 → x < y is true
    let vx = arith.get_or_create_var(x);
    let vy = arith.get_or_create_var(y);
    arith
        .assignment
        .insert(vx, DeltaRational::from_rational(Rational::from_int(2)));
    arith
        .assignment
        .insert(vy, DeltaRational::from_rational(Rational::from_int(5)));

    let phase = arith.suggest_phase(&TheoryLiteral::Lt(x, y));
    assert_eq!(phase, Some(true), "x=2 < y=5 should suggest positive phase");
}

#[test]
fn test_suggest_phase_lt_unsatisfied() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);
    let vx = arith.get_or_create_var(x);
    let vy = arith.get_or_create_var(y);
    arith
        .assignment
        .insert(vx, DeltaRational::from_rational(Rational::from_int(5)));
    arith
        .assignment
        .insert(vy, DeltaRational::from_rational(Rational::from_int(2)));

    let phase = arith.suggest_phase(&TheoryLiteral::Lt(x, y));
    assert_eq!(
        phase,
        Some(false),
        "x=5 < y=2 is false; should suggest negative phase"
    );
}

#[test]
fn test_suggest_phase_lt_equal_values() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);
    let vx = arith.get_or_create_var(x);
    let vy = arith.get_or_create_var(y);
    arith
        .assignment
        .insert(vx, DeltaRational::from_rational(Rational::from_int(3)));
    arith
        .assignment
        .insert(vy, DeltaRational::from_rational(Rational::from_int(3)));

    let phase = arith.suggest_phase(&TheoryLiteral::Lt(x, y));
    assert_eq!(
        phase,
        Some(false),
        "x=3 < y=3 is false (strict); should suggest negative phase"
    );
}

/// suggest_phase for Le: non-strict comparison.
#[test]
fn test_suggest_phase_le_equal_values() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);
    let vx = arith.get_or_create_var(x);
    let vy = arith.get_or_create_var(y);
    arith
        .assignment
        .insert(vx, DeltaRational::from_rational(Rational::from_int(3)));
    arith
        .assignment
        .insert(vy, DeltaRational::from_rational(Rational::from_int(3)));

    let phase = arith.suggest_phase(&TheoryLiteral::Le(x, y));
    assert_eq!(
        phase,
        Some(true),
        "x=3 <= y=3 is true (non-strict); should suggest positive phase"
    );
}

#[test]
fn test_suggest_phase_le_unsatisfied() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);
    let vx = arith.get_or_create_var(x);
    let vy = arith.get_or_create_var(y);
    arith
        .assignment
        .insert(vx, DeltaRational::from_rational(Rational::from_int(7)));
    arith
        .assignment
        .insert(vy, DeltaRational::from_rational(Rational::from_int(3)));

    let phase = arith.suggest_phase(&TheoryLiteral::Le(x, y));
    assert_eq!(
        phase,
        Some(false),
        "x=7 <= y=3 is false; should suggest negative phase"
    );
}

/// suggest_phase for Eq: returns Some(true) when both sides have equal
/// model values, Some(false) otherwise.
#[test]
fn test_suggest_phase_eq_satisfied() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);
    let vx = arith.get_or_create_var(x);
    let vy = arith.get_or_create_var(y);
    arith
        .assignment
        .insert(vx, DeltaRational::from_rational(Rational::from_int(4)));
    arith
        .assignment
        .insert(vy, DeltaRational::from_rational(Rational::from_int(4)));

    let phase = arith.suggest_phase(&TheoryLiteral::Eq(x, y));
    assert_eq!(
        phase,
        Some(true),
        "x=4 == y=4 should suggest positive phase"
    );
}

#[test]
fn test_suggest_phase_eq_unsatisfied() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);
    let vx = arith.get_or_create_var(x);
    let vy = arith.get_or_create_var(y);
    arith
        .assignment
        .insert(vx, DeltaRational::from_rational(Rational::from_int(4)));
    arith
        .assignment
        .insert(vy, DeltaRational::from_rational(Rational::from_int(5)));

    let phase = arith.suggest_phase(&TheoryLiteral::Eq(x, y));
    assert_eq!(
        phase,
        Some(false),
        "x=4 != y=5 should suggest negative phase"
    );
}

/// suggest_phase for non-arithmetic literals (Neq, Bool) returns None.
#[test]
fn test_suggest_phase_non_arithmetic_returns_none() {
    let arith = ArithmeticTheory::new();

    assert_eq!(
        arith.suggest_phase(&TheoryLiteral::Neq(TermId(0), TermId(1))),
        None,
        "Neq is not handled by LRA; should return None"
    );
    assert_eq!(
        arith.suggest_phase(&TheoryLiteral::Bool(0)),
        None,
        "Bool is not handled by LRA; should return None"
    );
}

/// suggest_phase returns None when terms have no model assignment
/// (not yet internalized).
#[test]
fn test_suggest_phase_unknown_terms_returns_none() {
    let arith = ArithmeticTheory::new();

    let phase = arith.suggest_phase(&TheoryLiteral::Lt(TermId(99), TermId(100)));
    assert_eq!(
        phase, None,
        "unknown terms with no assignment should return None"
    );
}

/// current_term_value returns the model value for an internalized term,
/// None for an unknown term.
#[test]
fn test_current_term_value_known_and_unknown() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let vx = arith.get_or_create_var(x);
    let expected = DeltaRational::from_rational(Rational::from_int(42));
    arith.assignment.insert(vx, expected);

    assert_eq!(
        arith.current_term_value(x),
        Some(expected),
        "known term should return its assignment"
    );
    assert_eq!(
        arith.current_term_value(TermId(99)),
        None,
        "unknown term should return None"
    );
}

// =========================================================================
// assert_shared_equality() / assert_shared_disequality()
// =========================================================================

/// assert_shared_equality decomposes t1 = t2 into t1 ≤ t2 ∧ t2 ≤ t1,
/// same as the Eq path in assert_literal. Consistent case.
#[test]
fn test_assert_shared_equality_consistent() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);
    arith.get_or_create_var(x);
    arith.get_or_create_var(y);

    let result = arith.assert_shared_equality(x, y, make_lit(0, true));
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "x = y alone should be consistent, got: {result:?}"
    );
    assert!(arith.is_consistent());
}

/// assert_shared_equality detects conflict when existing constraints
/// make the equality impossible.
#[test]
fn test_assert_shared_equality_conflict() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);

    // First assert x < y (strict inequality)
    let lt_result = arith.assert_literal(make_lit(0, true), &TheoryLiteral::Lt(x, y));
    assert!(matches!(lt_result, TheoryCheckResult::Consistent));

    // Now assert x = y via shared equality — should conflict with x < y
    let eq_result = arith.assert_shared_equality(x, y, make_lit(1, true));
    assert!(
        matches!(eq_result, TheoryCheckResult::Conflict(_)),
        "x < y ∧ x = y must be UNSAT, got: {eq_result:?}"
    );
}

/// assert_shared_disequality always returns Consistent — Neq is handled
/// by EqualityTheory via disjunctive reasoning.
#[test]
fn test_assert_shared_disequality_always_consistent() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);
    arith.get_or_create_var(x);
    arith.get_or_create_var(y);

    let result = arith.assert_shared_disequality(x, y, make_lit(0, true));
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "assert_shared_disequality must always return Consistent, got: {result:?}"
    );
}

// =========================================================================
// collect_statistics()
// =========================================================================

/// collect_statistics returns the correct counts for an empty solver.
/// Must also verify 5 entries are present (prevents trivial pass on empty vec).
#[test]
fn test_collect_statistics_empty() {
    let arith = ArithmeticTheory::new();
    let stats = arith.collect_statistics();

    assert_expected_arith_stat_keys(&stats);
    assert!(
        stats.iter().all(|(_, v)| *v == 0),
        "empty solver should have all-zero statistics, got: {stats:?}"
    );
}

/// collect_statistics returns correct non-zero counts after assertions.
#[test]
fn test_collect_statistics_after_assertions() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);

    // Le creates vars + bounds
    let result = arith.assert_literal(make_lit(0, true), &TheoryLiteral::Le(x, y));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    let stats = arith.collect_statistics();
    assert_expected_arith_stat_keys(&stats);
    let stat_map: HashMap<&str, u64> = stats.into_iter().collect();

    assert!(
        *stat_map.get("arith_vars").unwrap_or(&0) > 0,
        "should have created simplex variables"
    );
    assert!(
        *stat_map.get("arith_upper_bounds").unwrap_or(&0) > 0,
        "Le creates at least one upper bound"
    );
}

// =========================================================================
// internalize_atom pre-allocation
// =========================================================================

/// internalize_atom pre-allocates simplex variables so assert_literal
/// skips the HashMap insert path. Verify the variable count increases
/// after internalization.
#[test]
fn test_internalize_atom_preallocates_vars() {
    let mut arith = ArithmeticTheory::new();

    assert_eq!(arith.stats().num_vars, 0, "fresh solver has 0 vars");

    arith.internalize_atom(&TheoryLiteral::Lt(TermId(0), TermId(1)));
    assert!(
        arith.stats().num_vars >= 2,
        "internalize_atom(Lt) should pre-allocate at least 2 vars, got: {}",
        arith.stats().num_vars
    );

    // Subsequent assert_literal should reuse the pre-allocated vars
    let result = arith.assert_literal(make_lit(0, true), &TheoryLiteral::Lt(TermId(0), TermId(1)));
    assert!(matches!(result, TheoryCheckResult::Consistent));
}

/// internalize_atom ignores non-arithmetic literals (Neq, Bool).
#[test]
fn test_internalize_atom_ignores_non_arithmetic() {
    let mut arith = ArithmeticTheory::new();

    arith.internalize_atom(&TheoryLiteral::Neq(TermId(0), TermId(1)));
    assert_eq!(
        arith.stats().num_vars,
        0,
        "Neq should not create any variables"
    );

    arith.internalize_atom(&TheoryLiteral::Bool(42));
    assert_eq!(
        arith.stats().num_vars,
        0,
        "Bool should not create any variables"
    );
}

// =========================================================================
// set_terms no-op
// =========================================================================

/// set_terms is intentionally a no-op (#2391). Verify it doesn't crash
/// or modify state.
#[test]
fn test_set_terms_is_noop() {
    use crate::smt::SmtTerm;
    use std::sync::Arc;

    let mut arith = ArithmeticTheory::new();
    let x = TermId(0);
    arith.get_or_create_var(x);
    let vars_before = arith.stats().num_vars;

    let terms: Arc<[SmtTerm]> = Arc::from(vec![SmtTerm::Int(0.into())]);
    arith.set_terms(terms);

    assert_eq!(
        arith.stats().num_vars,
        vars_before,
        "set_terms must not change internal state"
    );
}
