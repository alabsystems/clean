// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn new_reset_fixture() -> (EqualityTheory, TermId, TermId, TermId) {
    let mut eq = EqualityTheory::new();
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
        SmtTerm::Const(Symbol::new("c")),
    ];
    eq.set_terms(terms);
    (eq, TermId(0), TermId(1), TermId(2))
}

fn assert_reset_clears_runtime_state(eq: &EqualityTheory) {
    assert_eq!(
        eq.equality_trail.len(),
        1,
        "equality_trail should have exactly one (empty) sentinel entry after reset"
    );
    assert!(
        eq.equality_trail[0].is_empty(),
        "equality_trail[0] should be empty after reset"
    );
    assert_eq!(
        eq.diseq_trail.len(),
        1,
        "diseq_trail should have exactly one sentinel entry after reset"
    );
    assert_eq!(
        eq.diseq_trail[0], 0,
        "diseq_trail[0] should be 0 after reset"
    );
    assert!(
        eq.egraph_trail.is_empty(),
        "egraph_trail should be empty after reset"
    );
    assert!(
        eq.term_to_eclass_trail.is_empty(),
        "term_to_eclass_trail should be empty after reset"
    );
    assert!(
        eq.proof_trace_len_trail.is_empty(),
        "proof_trace_len_trail should be empty after reset"
    );
    assert!(
        eq.term_to_hypothesis_trail.is_empty(),
        "term_to_hypothesis_trail should be empty after reset"
    );
    assert!(
        eq.pending_deduced.is_empty(),
        "pending_deduced should be empty after reset"
    );
}

/// Behavioral test for `EqualityTheory::reset()`: verifies that trails and
/// pending state are actually cleared after reset, not just that the dispatch
/// happens. Closes the gap identified in Prover iter 1091 (#302).
#[test]
fn test_reset_clears_trails_and_pending_state() {
    let (mut eq, a, b, c) = new_reset_fixture();

    // Internalize atoms to pre-populate E-graph nodes.
    eq.internalize_atom(&TheoryLiteral::Eq(a, b));
    eq.internalize_atom(&TheoryLiteral::Eq(b, c));

    // Push to level 1 and assert equalities.
    eq.push();
    let lit1 = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit1, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    let lit2 = Lit::pos(crate::cdcl::Var::new(1));
    let result = eq.assert_literal(lit2, &TheoryLiteral::Eq(b, c));
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert!(
        eq.are_equal(a, c),
        "a = c should hold after transitive chain"
    );

    // Verify trails are non-empty before reset.
    assert!(
        eq.equality_trail.len() > 1,
        "equality_trail should have entries at level 1 before reset"
    );

    // Reset.
    eq.reset();
    assert_reset_clears_runtime_state(&eq);
}

#[test]
fn test_reset_clears_level0_assertion_state() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("u")),
        SmtTerm::Const(Symbol::new("v")),
    ];
    eq.set_terms(terms);

    let u = TermId(0);
    let v = TermId(1);

    eq.internalize_atom(&TheoryLiteral::Eq(u, v));

    let lit = Lit::pos(crate::cdcl::Var::new(10));
    let result = eq.assert_literal(lit, &TheoryLiteral::Eq(u, v));
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert!(eq.are_equal(u, v), "u = v should hold before reset");

    eq.reset();

    assert!(
        !eq.are_equal(u, v),
        "level-0 asserted equalities must be cleared by reset"
    );
    assert_eq!(
        eq.equality_trail.len(),
        1,
        "equality_trail should reset to one empty sentinel entry"
    );
    assert!(
        eq.equality_trail[0].is_empty(),
        "equality_trail sentinel should be empty after reset"
    );
    assert_eq!(
        eq.diseq_trail,
        vec![0],
        "diseq_trail should reset to the level-0 sentinel after reset"
    );
    assert!(
        eq.term_to_eclass.contains_key(&u),
        "internalized u entry should survive reset"
    );
    assert!(
        eq.term_to_eclass.contains_key(&v),
        "internalized v entry should survive reset"
    );
}

/// Verifies that `EqualityTheory::reset()` preserves structural state
/// (set_terms / internalize_atom) while clearing assertion state.
/// After reset, re-asserting the same equalities must succeed - the
/// pre-built E-graph nodes from `internalize_atom` must survive.
#[test]
fn test_reset_preserves_structural_state_for_reuse() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("x")),
        SmtTerm::Const(Symbol::new("y")),
    ];
    eq.set_terms(terms);

    let x = TermId(0);
    let y = TermId(1);

    eq.internalize_atom(&TheoryLiteral::Eq(x, y));

    // Assert x = y, confirm equal.
    eq.push();
    let lit = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit, &TheoryLiteral::Eq(x, y));
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert!(eq.are_equal(x, y));

    // Reset.
    eq.reset();

    // After reset, x and y should NOT be equal (assertion state cleared).
    assert!(
        !eq.are_equal(x, y),
        "after reset, asserted equalities must be cleared"
    );

    // Structural state preserved: term_to_eclass still has entries from internalize_atom.
    assert!(
        eq.term_to_eclass.contains_key(&x),
        "term_to_eclass should preserve internalized entries after reset"
    );
    assert!(
        eq.term_to_eclass.contains_key(&y),
        "term_to_eclass should preserve internalized entries after reset"
    );

    // Re-asserting should work (fresh solve cycle).
    eq.push();
    let lit2 = Lit::pos(crate::cdcl::Var::new(2));
    let result = eq.assert_literal(lit2, &TheoryLiteral::Eq(x, y));
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "re-assertion after reset should succeed"
    );
    assert!(
        eq.are_equal(x, y),
        "x = y should hold again after re-assertion"
    );
}

#[test]
fn test_reset_preserves_registered_hypotheses() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let hyp = clean_kernel::FVarId::new(77);

    eq.register_hypothesis(a, b, hyp);
    eq.internalize_atom(&TheoryLiteral::Eq(a, b));

    let lit = Lit::pos(crate::cdcl::Var::new(12));
    let result = eq.assert_literal(lit, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    eq.reset();

    assert_eq!(
        eq.term_to_hypothesis.get(&(a, b)).copied(),
        Some(hyp),
        "reset should preserve forward hypothesis registration"
    );
    assert_eq!(
        eq.term_to_hypothesis.get(&(b, a)).copied(),
        Some(hyp),
        "reset should preserve reverse hypothesis registration"
    );
    assert!(
        eq.term_to_eclass.contains_key(&a),
        "reset should rebuild structural registrations needed for hypothesis reuse"
    );
    assert!(
        eq.term_to_eclass.contains_key(&b),
        "reset should rebuild both internalized hypothesis terms"
    );
}
