// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn new_arg_reason_fixture() -> (
    EqualityTheory,
    TermId,
    TermId,
    TermId,
    TermId,
    TermId,
    TermId,
) {
    let mut eq = EqualityTheory::new();
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),                           // 0
        SmtTerm::Const(Symbol::new("b")),                           // 1
        SmtTerm::Const(Symbol::new("c")),                           // 2
        SmtTerm::Const(Symbol::new("d")),                           // 3
        SmtTerm::App(Symbol::new("f"), vec![TermId(0), TermId(2)]), // 4: f(a, c)
        SmtTerm::App(Symbol::new("f"), vec![TermId(1), TermId(3)]), // 5: f(b, d)
    ];
    eq.set_terms(terms);
    (
        eq,
        TermId(0),
        TermId(1),
        TermId(2),
        TermId(3),
        TermId(4),
        TermId(5),
    )
}

fn assert_nontrivial_trace_proof(
    eq: &EqualityTheory,
    trace: &crate::proof::ProofTrace,
    lhs: TermId,
    rhs: TermId,
    context: &str,
) {
    let ec_lhs = eq.get_eclass(lhs).unwrap();
    let ec_rhs = eq.get_eclass(rhs).unwrap();
    let proof = trace
        .build_proof(ec_lhs, ec_rhs)
        .unwrap_or_else(|| panic!("Should be able to build proof for {context}"));
    assert!(
        !matches!(proof, crate::proof::ProofStep::Refl(_)),
        "proof for {context} should be non-trivial"
    );
}

#[test]
fn test_congruence_proof_with_arg_reasons() {
    // Test that congruence proofs properly include argument equality reasons
    use crate::proof::UnionReason;

    let (mut eq, a, b, c, d, fac, fbd) = new_arg_reason_fixture();

    // Build f(a,c) and f(b,d) first so E-graph can track congruence
    let ec_fac = eq.get_or_create_eclass(fac);
    let ec_fbd = eq.get_or_create_eclass(fbd);
    assert_ne!(
        ec_fac, ec_fbd,
        "f(a,c) and f(b,d) should have distinct eclasses before merge"
    );

    // Register hypotheses
    eq.register_hypothesis(a, b, clean_kernel::FVarId::new(1));
    eq.register_hypothesis(c, d, clean_kernel::FVarId::new(2));

    // Assert a = b
    let lit1 = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit1, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Assert c = d
    let lit2 = Lit::pos(crate::cdcl::Var::new(1));
    let result = eq.assert_literal(lit2, &TheoryLiteral::Eq(c, d));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Now f(a, c) = f(b, d) by congruence
    assert!(eq.are_equal(fac, fbd), "f(a,c) and f(b,d) should be equal");

    let trace = eq.proof_trace();

    // Should have at least 3 records: a=b, c=d, and f(a,c)=f(b,d) by congruence
    assert!(
        trace.steps.len() >= 3,
        "Proof trace should have at least 3 records, got {}",
        trace.steps.len()
    );

    // Find the congruence record
    let congruence_step = trace
        .steps
        .iter()
        .find(
            |(_, _, reason)| matches!(reason, UnionReason::Congruence { func, .. } if func == "f"),
        )
        .expect("Should have a congruence step for f");

    if let (_, _, UnionReason::Congruence { arg_reasons, .. }) = congruence_step {
        // For a 2-argument function with both args changing, we might have
        // 0, 1, or 2 arg_reasons depending on how the E-graph processes it
        // The important thing is we can build a valid proof
        assert!(
            arg_reasons.len() <= 2,
            "arg_reasons should have at most 2 entries for 2-arg function"
        );
    }

    assert_nontrivial_trace_proof(&eq, trace, fac, fbd, "f(a,c) = f(b,d)");
}

// =========================================================================
// proof_coverage: untested equality theory paths (#982)
// =========================================================================

#[test]
fn test_get_canonical_eclass() {
    let mut eq = EqualityTheory::new();
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
        SmtTerm::Const(Symbol::new("c")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let c = TermId(2);

    let lit0 = Lit::pos(crate::cdcl::Var::new(0));
    let lit1 = Lit::pos(crate::cdcl::Var::new(1));
    eq.push();

    // Assert a = b and a != c (this registers c in the e-graph)
    assert!(matches!(
        eq.assert_literal(lit0, &TheoryLiteral::Eq(a, b)),
        TheoryCheckResult::Consistent
    ));
    assert!(matches!(
        eq.assert_literal(lit1, &TheoryLiteral::Neq(a, c)),
        TheoryCheckResult::Consistent
    ));

    let ec_a = eq
        .get_canonical_eclass(a)
        .expect("a should have an e-class after a=b assertion");
    let ec_b = eq
        .get_canonical_eclass(b)
        .expect("b should have an e-class after a=b assertion");
    let ec_c = eq
        .get_canonical_eclass(c)
        .expect("c should have an e-class after a!=c assertion");

    // a and b should be in the same canonical class
    assert_eq!(
        ec_a, ec_b,
        "a and b should share canonical e-class after a=b"
    );

    // c should be in a different class (registered via disequality)
    assert_ne!(ec_a, ec_c, "c should be in a different e-class");

    // Unregistered term should return None
    assert!(
        eq.get_canonical_eclass(TermId(42)).is_none(),
        "unknown term should return None"
    );
}

#[test]
fn test_backtrack_noop_when_at_or_above_level() {
    let mut eq = EqualityTheory::new();
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);

    eq.push(); // level 1
    let lit = Lit::pos(crate::cdcl::Var::new(0));
    assert!(matches!(
        eq.assert_literal(lit, &TheoryLiteral::Eq(a, b)),
        TheoryCheckResult::Consistent
    ));

    // Backtrack to level >= current should be no-op
    eq.backtrack(1); // same level - no-op
    assert!(
        eq.are_equal(a, b),
        "equality should persist after no-op backtrack"
    );

    eq.backtrack(5); // above level - no-op
    assert!(
        eq.are_equal(a, b),
        "equality should persist after above-level backtrack"
    );
}

#[test]
fn test_assert_literal_non_eq_neq_returns_consistent() {
    let mut eq = EqualityTheory::new();
    let terms = vec![
        SmtTerm::Const(Symbol::new("x")),
        SmtTerm::Const(Symbol::new("y")),
    ];
    eq.set_terms(terms);

    let x = TermId(0);
    let y = TermId(1);

    // Lt, Le, Bool, NegBool should all return Consistent (not handled)
    let lit = Lit::pos(crate::cdcl::Var::new(0));
    assert!(matches!(
        eq.assert_literal(lit, &TheoryLiteral::Lt(x, y)),
        TheoryCheckResult::Consistent
    ));
    assert!(matches!(
        eq.assert_literal(lit, &TheoryLiteral::Le(x, y)),
        TheoryCheckResult::Consistent
    ));
    assert!(matches!(
        eq.assert_literal(lit, &TheoryLiteral::Bool(0)),
        TheoryCheckResult::Consistent
    ));
    assert!(matches!(
        eq.assert_literal(lit, &TheoryLiteral::NegBool(0)),
        TheoryCheckResult::Consistent
    ));
}

#[test]
fn test_equality_theory_name() {
    let eq = EqualityTheory::new();
    assert_eq!(eq.name(), "EUF");
}
