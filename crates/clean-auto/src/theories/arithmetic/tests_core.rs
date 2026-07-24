// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::smt::{TheoryLiteral, TheorySolver};
use std::collections::{BTreeMap, HashMap};

#[test]
fn test_arithmetic_basic_upper() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let v = arith.get_or_create_var(x);

    // Assert x ≤ 5
    let result = arith.assert_upper_bound(
        v,
        DeltaRational::from_rational(Rational::from_int(5)),
        make_lit(0, true),
    );
    assert!(matches!(result, TheoryCheckResult::Consistent));

    assert!(arith.is_consistent());
}

#[test]
fn test_arithmetic_constraint() {
    let mut arith = ArithmeticTheory::new();

    // x < y using theory literals
    let x = TermId(0);
    let y = TermId(1);

    let result = arith.assert_literal(make_lit(0, true), &TheoryLiteral::Lt(x, y));
    assert!(matches!(result, TheoryCheckResult::Consistent));
}

#[test]
fn test_arithmetic_backtrack() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let v = arith.get_or_create_var(x);

    // Level 0: x ≤ 10
    let result = arith.assert_upper_bound(
        v,
        DeltaRational::from_rational(Rational::from_int(10)),
        make_lit(0, true),
    );
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Push to level 1
    arith.push();

    // Level 1: x ≤ 5 (tighter)
    let result = arith.assert_upper_bound(
        v,
        DeltaRational::from_rational(Rational::from_int(5)),
        make_lit(1, true),
    );
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // x should have upper bound (5, 0)
    assert_eq!(
        arith.upper_bounds.get(&v).map(|b| b.value),
        Some(DeltaRational::from_rational(Rational::from_int(5)))
    );

    // Backtrack to level 0
    arith.backtrack(0);

    // x should have upper bound (10, 0) again
    assert_eq!(
        arith.upper_bounds.get(&v).map(|b| b.value),
        Some(DeltaRational::from_rational(Rational::from_int(10)))
    );
}

#[test]
fn test_linear_expr() {
    let mut expr = LinearExpr::new();
    let x = ArithVar::new(0);
    let y = ArithVar::new(1);

    // 2x + 3y
    expr.add_term(x, Rational::from_int(2)).unwrap();
    expr.add_term(y, Rational::from_int(3)).unwrap();

    let mut assignment = HashMap::new();
    assignment.insert(x, Rational::from_int(1));
    assignment.insert(y, Rational::from_int(2));

    // 2*1 + 3*2 = 8
    let result = expr.evaluate(&assignment).unwrap();
    assert_eq!(result, Rational::from_int(8));
}

#[test]
fn test_linear_expr_scale() {
    let mut expr = LinearExpr::new();
    let x = ArithVar::new(0);

    // 2x
    expr.add_term(x, Rational::from_int(2)).unwrap();

    // Scale by 3: 6x
    expr.scale(&Rational::from_int(3)).unwrap();

    assert_eq!(expr.coeffs.get(&x), Some(&Rational::from_int(6)));
}

#[test]
fn test_stats() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);
    let var_x = arith.get_or_create_var(x);
    let var_y = arith.get_or_create_var(y);
    assert_ne!(
        var_x, var_y,
        "distinct terms should have distinct ArithVars"
    );

    let stats = arith.stats();
    assert_eq!(stats.num_vars, 2);
}

/// Regression test for #2312: term_to_var is saved/restored by push/backtrack.
#[test]
fn test_term_to_var_restored_on_backtrack() {
    let mut arith = ArithmeticTheory::new();

    arith.push();
    let result = arith.assert_literal(make_lit(0, true), &TheoryLiteral::Lt(TermId(0), TermId(1)));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    assert_eq!(arith.next_id, 3, "3 vars should exist: x, y, slack");

    arith.backtrack(0);

    assert_eq!(arith.next_id, 0, "next_id should be restored to 0");
    assert!(
        arith.term_to_var.is_empty(),
        "all term_to_var entries should be cleared after backtrack"
    );

    let fresh_var = arith.next_var_id();
    assert_eq!(
        fresh_var,
        ArithVar::new(0),
        "first allocation after backtrack"
    );

    arith.push();
    let result = arith.assert_literal(make_lit(1, true), &TheoryLiteral::Lt(TermId(0), TermId(1)));
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "re-assertion after backtrack should succeed without ID collision"
    );
}

/// Regression for #2386: snapshot reuse must capture the current restored
/// level before a second branch. After backtracking to level 1, mutating that
/// restored state, and pushing again, the next backtrack must preserve the
/// updated level-1 term registrations instead of restoring a stale snapshot.
#[test]
fn test_backtrack_reuses_updated_level_snapshot_after_rebranch() {
    let mut arith = ArithmeticTheory::new();

    arith.push();
    let first_branch =
        arith.assert_literal(make_lit(0, true), &TheoryLiteral::Lt(TermId(0), TermId(1)));
    assert!(matches!(first_branch, TheoryCheckResult::Consistent));
    assert_eq!(arith.next_id, 3, "first branch should allocate x, y, slack");

    arith.push();
    let second_level =
        arith.assert_literal(make_lit(1, true), &TheoryLiteral::Lt(TermId(2), TermId(3)));
    assert!(matches!(second_level, TheoryCheckResult::Consistent));
    assert_eq!(
        arith.next_id, 6,
        "level 2 should allocate a distinct second comparison"
    );

    arith.backtrack(1);
    assert_eq!(arith.level, 1, "backtrack should restore level 1");
    assert_eq!(
        arith.next_id, 3,
        "backtrack to level 1 should drop the level-2 variables"
    );
    assert!(arith.term_to_var.contains_key(&TermId(0)));
    assert!(arith.term_to_var.contains_key(&TermId(1)));
    assert!(
        !arith.term_to_var.contains_key(&TermId(2)),
        "retracted level-2 terms must be removed after backtrack"
    );

    let rebranch_level1 =
        arith.assert_literal(make_lit(2, true), &TheoryLiteral::Lt(TermId(4), TermId(5)));
    assert!(matches!(rebranch_level1, TheoryCheckResult::Consistent));
    assert_eq!(
        arith.next_id, 6,
        "restored level 1 should accept new terms before the second push"
    );
    assert!(arith.term_to_var.contains_key(&TermId(4)));
    assert!(arith.term_to_var.contains_key(&TermId(5)));

    arith.push();
    let third_branch =
        arith.assert_literal(make_lit(3, true), &TheoryLiteral::Lt(TermId(6), TermId(7)));
    assert!(matches!(third_branch, TheoryCheckResult::Consistent));
    assert_eq!(
        arith.next_id, 9,
        "second level-2 branch should allocate another fresh comparison"
    );

    arith.backtrack(1);
    assert_eq!(arith.level, 1, "second backtrack should return to level 1");
    assert_eq!(
        arith.next_id, 6,
        "backtrack after rebranch must keep the updated level-1 snapshot"
    );
    assert!(arith.term_to_var.contains_key(&TermId(0)));
    assert!(arith.term_to_var.contains_key(&TermId(1)));
    assert!(arith.term_to_var.contains_key(&TermId(4)));
    assert!(arith.term_to_var.contains_key(&TermId(5)));
    assert!(
        !arith.term_to_var.contains_key(&TermId(6)),
        "latest level-2 terms must be removed after the second backtrack"
    );
    assert!(
        !arith.term_to_var.contains_key(&TermId(2)),
        "stale first-branch terms must not reappear after the second backtrack"
    );
}

/// Regression test for #2292 bug 1: is_consistent() detects artificial violations.
///
/// Manually creates a bound-violating state (bypassing assert_literal's incremental
/// check_and_repair). Verifies is_consistent() catches the violation. We do NOT
/// call check() here because check() now has a debug_assert!(is_consistent()),
/// and this artificial state is not reachable through normal API usage.
#[test]
fn test_is_consistent_detects_artificial_violation() {
    let mut arith = ArithmeticTheory::new();

    let x = ArithVar::new(0);
    arith.next_id = 1;
    arith
        .assignment
        .insert(x, DeltaRational::from_rational(Rational::from_int(10)));
    arith.upper_bounds.insert(
        x,
        Bound::new(
            DeltaRational::from_rational(Rational::from_int(5)),
            make_lit(0, true),
            0,
        ),
    );

    assert!(
        !arith.is_consistent(),
        "assignment=10 with upper_bound=5 should be inconsistent"
    );
}

/// Regression test for #2292 bug 2: explain_conflict must scope to the
/// violated variable's tableau row, not return all bounds.
#[test]
fn test_explain_conflict_scoped_to_tableau_row() {
    let mut arith = ArithmeticTheory::new();

    let x = ArithVar::new(0); // basic
    let y = ArithVar::new(1); // non-basic, in x's row
    let z = ArithVar::new(2); // non-basic, NOT in x's row
    arith.next_id = 3;

    let mut coeffs = BTreeMap::new();
    coeffs.insert(y, Rational::ONE);
    arith.tableau.push(TableauRow {
        basic_var: x,
        constant: Rational::ZERO,
        coeffs,
    });
    arith.rebuild_basic_var_index();

    arith
        .assignment
        .insert(y, DeltaRational::from_rational(Rational::ZERO));
    arith
        .assignment
        .insert(z, DeltaRational::from_rational(Rational::ZERO));

    let lit_x_lower = make_lit(0, true);
    let lit_y_upper = make_lit(1, true);
    let lit_z_upper = make_lit(2, true);

    arith.lower_bounds.insert(
        x,
        Bound::new(
            DeltaRational::from_rational(Rational::from_int(5)),
            lit_x_lower,
            0,
        ),
    );

    arith.upper_bounds.insert(
        y,
        Bound::new(DeltaRational::from_rational(Rational::ZERO), lit_y_upper, 0),
    );

    arith.upper_bounds.insert(
        z,
        Bound::new(
            DeltaRational::from_rational(Rational::from_int(10)),
            lit_z_upper,
            0,
        ),
    );

    let conflict = arith.explain_conflict(x, true);

    assert!(
        conflict.contains(&lit_x_lower),
        "conflict must include the violated lower bound on x"
    );
    assert!(
        conflict.contains(&lit_y_upper),
        "conflict must include y's bounding reason (prevents pivot)"
    );
    assert!(
        !conflict.contains(&lit_z_upper),
        "conflict must NOT include bounds on variables outside x's tableau row"
    );
}

#[test]
fn test_explain_conflict_orders_blocking_bounds_by_var_id() {
    let mut arith = ArithmeticTheory::new();

    let x = ArithVar::new(0);
    let y = ArithVar::new(1);
    let slack = ArithVar::new(2);
    arith.next_id = 3;

    let mut coeffs = BTreeMap::new();
    coeffs.insert(y, Rational::NEG_ONE);
    coeffs.insert(x, Rational::ONE);
    arith.tableau.push(TableauRow {
        basic_var: slack,
        constant: Rational::ZERO,
        coeffs,
    });
    arith.rebuild_basic_var_index();

    let lit_slack_upper = make_lit(0, true);
    let lit_x_lower = make_lit(1, true);
    let lit_y_upper = make_lit(2, true);

    arith.upper_bounds.insert(
        slack,
        Bound::new(
            DeltaRational::from_rational(Rational::ZERO),
            lit_slack_upper,
            0,
        ),
    );
    arith.lower_bounds.insert(
        x,
        Bound::new(DeltaRational::from_rational(Rational::ZERO), lit_x_lower, 0),
    );
    arith.upper_bounds.insert(
        y,
        Bound::new(DeltaRational::from_rational(Rational::ZERO), lit_y_upper, 0),
    );

    let conflict = arith.explain_conflict(slack, false);
    assert_eq!(
        conflict,
        vec![lit_slack_upper, lit_x_lower, lit_y_upper],
        "conflict explanation order should follow ascending ArithVar order"
    );
}

/// Regression test for #2311: Eq(t1, t2) decomposes into t1 ≤ t2 ∧ t2 ≤ t1.
#[test]
fn test_arith_eq_as_two_bounds() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);

    let bounds_before = arith.stats().num_upper_bounds;

    let lit_eq = make_lit(0, true);
    let result = arith.assert_literal(lit_eq, &TheoryLiteral::Eq(x, y));
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "x = y alone should be consistent"
    );

    let bounds_after = arith.stats().num_upper_bounds;
    assert!(
        bounds_after >= bounds_before + 2,
        "Eq should create at least 2 upper bounds (x-y ≤ 0 and y-x ≤ 0), \
         got {bounds_before} -> {bounds_after}"
    );

    assert!(
        arith.is_consistent(),
        "arithmetic state should be consistent after x = y"
    );
}

// =========================================================================
// proof_coverage: Le path, name(), Neq passthrough, Rational::abs (#982)
// =========================================================================

#[test]
fn test_arith_le_path() {
    let mut arith = ArithmeticTheory::new();

    let x = TermId(0);
    let y = TermId(1);

    let lit = make_lit(0, true);
    let result = arith.assert_literal(lit, &TheoryLiteral::Le(x, y));
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "x ≤ y alone should be consistent"
    );
    assert!(arith.is_consistent());
}

#[test]
fn test_arith_neq_passthrough() {
    let mut arith = ArithmeticTheory::new();

    let lit = make_lit(0, true);
    let result = arith.assert_literal(lit, &TheoryLiteral::Neq(TermId(0), TermId(1)));
    assert!(matches!(result, TheoryCheckResult::Consistent));
}

#[test]
fn test_arith_bool_passthrough() {
    let mut arith = ArithmeticTheory::new();
    let lit = make_lit(0, true);
    let result = arith.assert_literal(lit, &TheoryLiteral::Bool(0));
    assert!(matches!(result, TheoryCheckResult::Consistent));
}

#[test]
fn test_arith_name() {
    let arith = ArithmeticTheory::new();
    assert_eq!(arith.name(), "LRA");
}

#[test]
fn test_rational_abs() {
    let pos = Rational::new(3, 4);
    assert_eq!(pos.abs(), Rational::new(3, 4));

    let neg = Rational::new(-5, 3);
    assert_eq!(neg.abs(), Rational::new(5, 3));

    assert_eq!(Rational::ZERO.abs(), Rational::ZERO);
}

#[test]
fn test_rational_display() {
    assert_eq!(format!("{}", Rational::from_int(7)), "7");
    assert_eq!(format!("{}", Rational::new(3, 4)), "3/4");
    assert_eq!(format!("{}", Rational::new(-1, 2)), "-1/2");
    assert_eq!(format!("{}", Rational::ZERO), "0");
}

#[test]
fn test_linear_expr_var() {
    let expr = LinearExpr::var(ArithVar::new(0));
    let mut assignment = HashMap::new();
    assignment.insert(ArithVar::new(0), Rational::from_int(5));
    assert_eq!(expr.evaluate(&assignment).unwrap(), Rational::from_int(5));
}

#[test]
fn test_linear_expr_add_expr() {
    let mut e1 = LinearExpr::new();
    e1.add_term(ArithVar::new(0), Rational::from_int(2))
        .unwrap();
    e1.add_term(ArithVar::new(1), Rational::from_int(3))
        .unwrap();

    let mut e2 = LinearExpr::new();
    e2.add_term(ArithVar::new(1), Rational::from_int(4))
        .unwrap();
    e2.add_term(ArithVar::new(2), Rational::from_int(1))
        .unwrap();

    e1.add_expr(&e2).unwrap();

    let mut assignment = HashMap::new();
    assignment.insert(ArithVar::new(0), Rational::from_int(1));
    assignment.insert(ArithVar::new(1), Rational::from_int(1));
    assignment.insert(ArithVar::new(2), Rational::from_int(1));

    // e1 = 2*x0 + 7*x1 + 1*x2 = 2 + 7 + 1 = 10
    assert_eq!(e1.evaluate(&assignment).unwrap(), Rational::from_int(10));
}

fn make_bound(value: i64, lit_idx: u32) -> (Lit, Bound) {
    let lit = make_lit(lit_idx, true);
    (
        lit,
        Bound::new(
            DeltaRational::from_rational(Rational::from_int(value)),
            lit,
            0,
        ),
    )
}

/// Regression test for #2315: explain_conflict includes only the blocking
/// bound per non-basic variable, not both bounds.
#[test]
fn test_explain_conflict_minimal_clause_size() {
    let mut arith = ArithmeticTheory::new();
    let x = arith.get_or_create_var(TermId(0));
    let y = arith.get_or_create_var(TermId(1));

    let slack = arith.new_slack_var();
    let mut coeffs = BTreeMap::new();
    coeffs.insert(x, Rational::ONE);
    coeffs.insert(y, Rational::ONE.neg());
    arith.tableau.push(TableauRow {
        basic_var: slack,
        constant: Rational::ZERO,
        coeffs,
    });
    arith.rebuild_basic_var_index();

    let (lit_le, b) = make_bound(0, 0);
    arith.upper_bounds.insert(slack, b);
    let (lit_x_lo, b) = make_bound(5, 1);
    arith.lower_bounds.insert(x, b);
    let (lit_x_hi, b) = make_bound(100, 2);
    arith.upper_bounds.insert(x, b);
    let (lit_y_hi, b) = make_bound(3, 3);
    arith.upper_bounds.insert(y, b);
    let (lit_y_lo, b) = make_bound(-100, 4);
    arith.lower_bounds.insert(y, b);

    let conflict = arith.explain_conflict(slack, false);

    assert_eq!(conflict.len(), 3, "minimal: got {conflict:?}");
    assert!(conflict.contains(&lit_le), "need slack upper");
    assert!(conflict.contains(&lit_x_lo), "need x lower (blocking)");
    assert!(conflict.contains(&lit_y_hi), "need y upper (blocking)");
    assert!(!conflict.contains(&lit_x_hi), "x upper is non-blocking");
    assert!(!conflict.contains(&lit_y_lo), "y lower is non-blocking");
}

/// #2334: Strict inequality `c < d AND c = d` must be detected as UNSAT.
/// With delta-rationals, `c < d` becomes `c - d <= (0, -1)` and `c = d`
/// becomes `c - d <= (0, 0) AND d - c <= (0, 0)`. The simplex detects
/// the conflict without degenerate cycling.
#[test]
fn test_strict_eq_conflict_no_cycling() {
    let mut arith = ArithmeticTheory::new();

    let c = TermId(0);
    let d = TermId(1);

    // Assert c < d
    let lt_result = arith.assert_literal(make_lit(0, true), &TheoryLiteral::Lt(c, d));
    assert!(
        matches!(lt_result, TheoryCheckResult::Consistent),
        "c < d alone is consistent"
    );

    // Assert c = d (should conflict with c < d)
    let eq_result = arith.assert_literal(make_lit(1, true), &TheoryLiteral::Eq(c, d));
    assert!(
        matches!(eq_result, TheoryCheckResult::Conflict(_)),
        "c < d AND c = d must be UNSAT, got: {eq_result:?}"
    );
}
