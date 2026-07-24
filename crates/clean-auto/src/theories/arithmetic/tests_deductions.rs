// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::smt::{TheoryLiteral, TheorySolver};

// =========================================================================
// Nelson-Oppen deduction tests (#2364)
// =========================================================================

/// drain_deduced_equalities returns empty when no equalities are implied.
#[test]
fn test_drain_deduced_empty_initial() {
    let mut arith = ArithmeticTheory::new();
    assert!(
        arith.drain_deduced_equalities().is_empty(),
        "no deductions before any assertions"
    );
}

/// When two terms are constrained to the same value, detect_model_equalities
/// should produce the equality.
#[test]
fn test_detect_model_equality_squeezed_bounds() {
    let mut arith = ArithmeticTheory::new();
    arith.push();

    let x = TermId(0);
    let c = TermId(1);
    let y = TermId(2);

    // x <= c (creates constraint: v_x - v_c <= 0)
    let r1 = arith.assert_literal(make_lit(0, true), &TheoryLiteral::Le(x, c));
    assert!(matches!(r1, TheoryCheckResult::Consistent));

    // c <= x (creates constraint: v_c - v_x <= 0, so x = c)
    let r2 = arith.assert_literal(make_lit(1, true), &TheoryLiteral::Le(c, x));
    assert!(matches!(r2, TheoryCheckResult::Consistent));

    // y <= c
    let r3 = arith.assert_literal(make_lit(2, true), &TheoryLiteral::Le(y, c));
    assert!(matches!(r3, TheoryCheckResult::Consistent));

    // c <= y (so y = c too, hence x = y)
    let r4 = arith.assert_literal(make_lit(3, true), &TheoryLiteral::Le(c, y));
    assert!(matches!(r4, TheoryCheckResult::Consistent));

    // Trigger detection
    arith.detect_model_equalities();
    let deduced = arith.drain_deduced_equalities();

    // Should detect at least one equality among {x, c, y}
    assert!(
        !deduced.is_empty(),
        "should deduce equalities when bounds squeeze x = c = y"
    );

    // Verify that x-y or x-c or c-y pair is present
    let has_pair = |a: TermId, b: TermId| -> bool {
        deduced
            .iter()
            .any(|(t1, t2, _)| (*t1 == a && *t2 == b) || (*t1 == b && *t2 == a))
    };
    assert!(
        has_pair(x, y) || (has_pair(x, c) && has_pair(c, y)),
        "should deduce x=y (directly or via x=c, c=y), got: {:?}",
        deduced
            .iter()
            .map(|(a, b, _)| (a.raw(), b.raw()))
            .collect::<Vec<_>>()
    );
}

/// Backtrack clears pending deduced equalities (#2364).
#[test]
fn test_deduced_cleared_on_backtrack() {
    let mut arith = ArithmeticTheory::new();
    arith.push();

    let x = TermId(0);
    let c = TermId(1);

    // x <= c and c <= x → x = c
    let r1 = arith.assert_literal(make_lit(0, true), &TheoryLiteral::Le(x, c));
    assert!(matches!(r1, TheoryCheckResult::Consistent));
    let r2 = arith.assert_literal(make_lit(1, true), &TheoryLiteral::Le(c, x));
    assert!(matches!(r2, TheoryCheckResult::Consistent));

    arith.detect_model_equalities();
    assert!(
        !arith.drain_deduced_equalities().is_empty(),
        "should have deduced x = c"
    );

    // Re-detect and drain again to populate
    arith.detect_model_equalities();

    // Backtrack should clear pending deductions
    arith.backtrack(0);
    let after_backtrack = arith.drain_deduced_equalities();
    assert!(
        after_backtrack.is_empty(),
        "pending deductions should be cleared after backtrack"
    );
}

/// Unconstrained variables should not produce spurious equalities.
#[test]
fn test_no_spurious_equality_unconstrained() {
    let mut arith = ArithmeticTheory::new();
    arith.push();

    // Create two term variables but don't constrain them
    let x = TermId(0);
    let y = TermId(1);
    arith.get_or_create_var(x);
    arith.get_or_create_var(y);

    // Both default to 0, but neither is constrained
    arith.detect_model_equalities();
    let deduced = arith.drain_deduced_equalities();
    assert!(
        deduced.is_empty(),
        "unconstrained variables should not produce spurious equalities, got: {:?}",
        deduced
            .iter()
            .map(|(a, b, _)| (a.raw(), b.raw()))
            .collect::<Vec<_>>()
    );
}

/// drain_deduced_equalities is incremental — second drain returns empty.
#[test]
fn test_drain_deduced_incremental() {
    let mut arith = ArithmeticTheory::new();
    arith.push();

    let x = TermId(0);
    let c = TermId(1);

    let r1 = arith.assert_literal(make_lit(0, true), &TheoryLiteral::Le(x, c));
    assert!(matches!(r1, TheoryCheckResult::Consistent));
    let r2 = arith.assert_literal(make_lit(1, true), &TheoryLiteral::Le(c, x));
    assert!(matches!(r2, TheoryCheckResult::Consistent));

    arith.detect_model_equalities();
    let first = arith.drain_deduced_equalities();
    assert!(!first.is_empty(), "first drain should produce equalities");

    // Second drain without re-detecting should be empty
    let second = arith.drain_deduced_equalities();
    assert!(
        second.is_empty(),
        "second drain should be empty (incremental)"
    );
}
