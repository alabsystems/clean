// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::smt::{TheoryLiteral, TheorySolver};

struct ResetFixture {
    arith: ArithmeticTheory,
    x: TermId,
    c: TermId,
    y: TermId,
    level0_next_id: u32,
    level0_term_to_var: HashMap<TermId, ArithVar>,
    level0_assignment: HashMap<ArithVar, DeltaRational>,
}

fn new_reset_fixture() -> ResetFixture {
    let mut arith = ArithmeticTheory::new();
    let x = TermId(0);
    let c = TermId(1);
    let y = TermId(2);

    // Pre-allocate structural term state that should survive reset.
    arith.internalize_atom(&TheoryLiteral::Eq(x, c));
    arith.internalize_atom(&TheoryLiteral::Eq(c, y));

    ResetFixture {
        level0_next_id: arith.next_id,
        level0_term_to_var: arith.term_to_var.clone(),
        level0_assignment: arith.assignment.clone(),
        arith,
        x,
        c,
        y,
    }
}

fn assert_squeezed_equalities(
    arith: &mut ArithmeticTheory,
    x: TermId,
    c: TermId,
    y: TermId,
    lit_base: u32,
) {
    for (offset, theory_lit) in [
        TheoryLiteral::Le(x, c),
        TheoryLiteral::Le(c, x),
        TheoryLiteral::Le(y, c),
        TheoryLiteral::Le(c, y),
    ]
    .into_iter()
    .enumerate()
    {
        let result = arith.assert_literal(make_lit(lit_base + offset as u32, true), &theory_lit);
        assert!(
            matches!(result, TheoryCheckResult::Consistent),
            "assertion {} should be consistent, got: {result:?}",
            lit_base + offset as u32
        );
    }
}

fn assert_reset_trails_populated(arith: &ArithmeticTheory) {
    assert_eq!(arith.level, 1, "push should raise the decision level");
    assert!(
        !arith.bound_trail.is_empty(),
        "bound_trail should record asserted bounds before reset"
    );
    assert!(
        !arith.tableau_trail.is_empty(),
        "tableau_trail should contain the level-0 snapshot before reset"
    );
    assert!(
        !arith.assignment_trail.is_empty(),
        "assignment_trail should contain the level-0 snapshot before reset"
    );
    assert!(
        !arith.next_id_trail.is_empty(),
        "next_id_trail should contain the level-0 snapshot before reset"
    );
    assert!(
        !arith.term_to_var_trail.is_empty(),
        "term_to_var_trail should contain the level-0 snapshot before reset"
    );
    assert!(
        !arith.overflow_corrupted_trail.is_empty(),
        "overflow_corrupted_trail should contain the level-0 snapshot before reset"
    );
    assert!(
        !arith.pending_deduced.is_empty(),
        "pending_deduced should contain detected equalities before reset"
    );
    assert!(
        !arith.deduced_set.is_empty(),
        "deduced_set should contain detected equality keys before reset"
    );
}

fn assert_level0_assertion_state_populated(arith: &ArithmeticTheory) {
    assert_eq!(
        arith.level, 0,
        "level-0 assertions should keep decision level 0"
    );
    assert!(
        !arith.bound_trail.is_empty(),
        "bound_trail should record level-0 bounds before reset"
    );
    assert!(
        !arith.upper_bounds.is_empty(),
        "upper_bounds should contain asserted level-0 bounds before reset"
    );
    assert!(
        !arith.tableau.is_empty(),
        "tableau should contain asserted level-0 constraints before reset"
    );
    assert!(
        !arith.pending_deduced.is_empty(),
        "pending_deduced should contain detected equalities before reset"
    );
    assert!(
        !arith.deduced_set.is_empty(),
        "deduced_set should contain detected equality keys before reset"
    );
}

fn assert_reset_restores_level0_state(fixture: &ResetFixture) {
    let arith = &fixture.arith;
    assert_eq!(arith.level, 0, "reset should restore level 0");
    assert!(
        arith.bound_trail.is_empty(),
        "bound_trail should be empty after reset"
    );
    assert!(
        arith.tableau_trail.is_empty(),
        "tableau_trail should be empty after reset"
    );
    assert!(
        arith.assignment_trail.is_empty(),
        "assignment_trail should be empty after reset"
    );
    assert!(
        arith.next_id_trail.is_empty(),
        "next_id_trail should be empty after reset"
    );
    assert!(
        arith.term_to_var_trail.is_empty(),
        "term_to_var_trail should be empty after reset"
    );
    assert!(
        arith.overflow_corrupted_trail.is_empty(),
        "overflow_corrupted_trail should be empty after reset"
    );
    assert!(
        arith.pending_deduced.is_empty(),
        "pending_deduced should be empty after reset"
    );
    assert!(
        arith.deduced_set.is_empty(),
        "deduced_set should be empty after reset"
    );
    assert!(
        arith.lower_bounds.is_empty(),
        "lower_bounds should be empty after reset"
    );
    assert!(
        arith.upper_bounds.is_empty(),
        "upper_bounds should be empty after reset"
    );
    assert!(
        arith.tableau.is_empty(),
        "tableau should be empty after reset"
    );
    assert_eq!(
        arith.next_id, fixture.level0_next_id,
        "reset should restore the level-0 variable counter"
    );
    assert_eq!(
        arith.term_to_var, fixture.level0_term_to_var,
        "reset should preserve level-0 term_to_var entries"
    );
    assert_eq!(
        arith.assignment, fixture.level0_assignment,
        "reset should preserve level-0 variable assignments"
    );
}

/// Behavioral test for `ArithmeticTheory::reset()`: verifies that trails and
/// pending deduction state are actually cleared after reset, not just that the
/// dispatch happens. Closes the remaining arithmetic-side gap from #302.
#[test]
fn test_arithmetic_reset_clears_trails_and_pending_state() {
    let mut fixture = new_reset_fixture();

    fixture.arith.push();
    assert_squeezed_equalities(&mut fixture.arith, fixture.x, fixture.c, fixture.y, 0);
    fixture.arith.detect_model_equalities();

    assert_reset_trails_populated(&fixture.arith);
    fixture.arith.reset();
    assert_reset_restores_level0_state(&fixture);
}

#[test]
fn test_arithmetic_reset_clears_level0_assertion_state() {
    let mut fixture = new_reset_fixture();

    assert_squeezed_equalities(&mut fixture.arith, fixture.x, fixture.c, fixture.y, 30);
    fixture.arith.detect_model_equalities();

    assert_level0_assertion_state_populated(&fixture.arith);
    fixture.arith.reset();
    assert_reset_restores_level0_state(&fixture);
}

fn assert_reused_term_registration(fixture: &ResetFixture) {
    let x_var = fixture.level0_term_to_var[&fixture.x];
    let c_var = fixture.level0_term_to_var[&fixture.c];
    let y_var = fixture.level0_term_to_var[&fixture.y];

    assert_eq!(
        fixture.arith.term_to_var.get(&fixture.x),
        Some(&x_var),
        "x should keep its pre-internalized arithmetic variable after reset"
    );
    assert_eq!(
        fixture.arith.term_to_var.get(&fixture.c),
        Some(&c_var),
        "c should keep its pre-internalized arithmetic variable after reset"
    );
    assert_eq!(
        fixture.arith.term_to_var.get(&fixture.y),
        Some(&y_var),
        "y should keep its pre-internalized arithmetic variable after reset"
    );
    assert!(
        fixture.arith.assignment.contains_key(&x_var),
        "assignment should preserve x's pre-internalized variable after reset"
    );
    assert!(
        fixture.arith.assignment.contains_key(&c_var),
        "assignment should preserve c's pre-internalized variable after reset"
    );
    assert!(
        fixture.arith.assignment.contains_key(&y_var),
        "assignment should preserve y's pre-internalized variable after reset"
    );
}

/// Verifies that `ArithmeticTheory::reset()` preserves structural term
/// registration from `internalize_atom` so a fresh solve cycle can reuse the
/// same arithmetic variables instead of rebuilding them.
#[test]
fn test_arithmetic_reset_preserves_structural_state_for_reuse() {
    let mut fixture = new_reset_fixture();

    fixture.arith.push();
    assert_squeezed_equalities(&mut fixture.arith, fixture.x, fixture.c, fixture.y, 0);

    fixture.arith.reset();
    assert_reset_restores_level0_state(&fixture);
    assert_reused_term_registration(&fixture);

    fixture.arith.push();
    assert_squeezed_equalities(&mut fixture.arith, fixture.x, fixture.c, fixture.y, 10);
    fixture.arith.detect_model_equalities();

    let deduced = fixture.arith.drain_deduced_equalities();
    assert!(
        deduced
            .iter()
            .any(|(t1, t2, _)| (*t1 == fixture.x && *t2 == fixture.y)
                || (*t1 == fixture.y && *t2 == fixture.x)),
        "reused structural state should still support deducing x = y after reset, got: {:?}",
        deduced
            .iter()
            .map(|(a, b, _)| (a.raw(), b.raw()))
            .collect::<Vec<_>>()
    );
}
