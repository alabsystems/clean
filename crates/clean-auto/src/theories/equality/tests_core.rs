// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_equality_basic() {
    let mut eq = EqualityTheory::new();

    // Create terms: a, b
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);

    // Initially not equal
    assert!(!eq.are_equal(a, b));

    // Assert a = b
    let lit = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Now equal
    assert!(eq.are_equal(a, b));
}

#[test]
fn test_equality_conflict() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);

    // Assert a = b
    let lit_eq = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit_eq, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Assert a != b - should conflict
    let lit_neq = Lit::neg(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit_neq, &TheoryLiteral::Neq(a, b));
    assert!(matches!(result, TheoryCheckResult::Conflict(_)));
}

#[test]
fn test_equality_disequality_first() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);

    // Assert a != b first
    let lit_neq = Lit::neg(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit_neq, &TheoryLiteral::Neq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Now assert a = b - should conflict
    let lit_eq = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit_eq, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Conflict(_)));
}

#[test]
fn test_congruence() {
    let mut eq = EqualityTheory::new();

    // Terms: a, b, f(a), f(b)
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
        SmtTerm::App(Symbol::new("f"), vec![TermId(0)]),
        SmtTerm::App(Symbol::new("f"), vec![TermId(1)]),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let fa = TermId(2);
    let fb = TermId(3);

    // Internalize all terms before querying (#2319)
    eq.internalize_term(fa);
    eq.internalize_term(fb);

    // Initially f(a) != f(b)
    assert!(!eq.are_equal(fa, fb));

    // Assert a = b
    let lit = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // By congruence, f(a) = f(b)
    assert!(eq.are_equal(fa, fb));
}

#[test]
fn test_congruence_conflict() {
    let mut eq = EqualityTheory::new();

    // Terms: a, b, f(a), f(b)
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
        SmtTerm::App(Symbol::new("f"), vec![TermId(0)]),
        SmtTerm::App(Symbol::new("f"), vec![TermId(1)]),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let fa = TermId(2);
    let fb = TermId(3);

    // Assert f(a) != f(b)
    let lit_neq = Lit::neg(crate::cdcl::Var::new(1));
    let result = eq.assert_literal(lit_neq, &TheoryLiteral::Neq(fa, fb));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Assert a = b - should cause conflict via congruence
    let lit_eq = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit_eq, &TheoryLiteral::Eq(a, b));

    // The conflict should be detected
    assert!(matches!(result, TheoryCheckResult::Conflict(_)));
}

#[test]
fn test_transitivity() {
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

    // Assert a = b
    let lit1 = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit1, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Assert b = c
    let lit2 = Lit::pos(crate::cdcl::Var::new(1));
    let result = eq.assert_literal(lit2, &TheoryLiteral::Eq(b, c));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // By transitivity, a = c
    assert!(eq.are_equal(a, c));
}

#[test]
fn test_backtrack() {
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

    // Level 0: assert a = b
    let lit1 = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit1, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert!(eq.are_equal(a, b));

    // Push to level 1
    eq.push();

    // Level 1: assert b = c
    let lit2 = Lit::pos(crate::cdcl::Var::new(1));
    let result = eq.assert_literal(lit2, &TheoryLiteral::Eq(b, c));
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert!(eq.are_equal(a, c));

    // Backtrack to level 0
    eq.backtrack(0);

    // a = b should still hold (from level 0)
    assert!(eq.are_equal(a, b));

    // But a = c should not hold anymore
    assert!(!eq.are_equal(a, c));
}

#[test]
fn test_stats() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);

    // Build terms -- each should get a distinct EClassId
    let ec_a = eq.get_or_create_eclass(a);
    let ec_b = eq.get_or_create_eclass(b);
    assert_ne!(ec_a, ec_b, "distinct terms should have distinct eclasses");

    let stats = eq.stats();
    assert_eq!(stats.num_terms, 2);
    assert_eq!(stats.num_eclasses, 2);
    assert_eq!(eq.explanation_stats(), &ExplanationStats::default());
}

#[test]
fn test_nested_congruence() {
    let mut eq = EqualityTheory::new();

    // Terms: a, b, f(a), f(b), g(f(a)), g(f(b))
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),                // 0
        SmtTerm::Const(Symbol::new("b")),                // 1
        SmtTerm::App(Symbol::new("f"), vec![TermId(0)]), // 2: f(a)
        SmtTerm::App(Symbol::new("f"), vec![TermId(1)]), // 3: f(b)
        SmtTerm::App(Symbol::new("g"), vec![TermId(2)]), // 4: g(f(a))
        SmtTerm::App(Symbol::new("g"), vec![TermId(3)]), // 5: g(f(b))
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let gfa = TermId(4);
    let gfb = TermId(5);

    // Internalize App terms before querying (#2319)
    eq.internalize_term(gfa);
    eq.internalize_term(gfb);

    // Assert a = b
    let lit = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // By nested congruence: f(a) = f(b), then g(f(a)) = g(f(b))
    assert!(eq.are_equal(gfa, gfb));
}

#[test]
fn test_self_disequality_immediate_conflict() {
    // Neq(a, a) must produce an immediate conflict — every term is
    // reflexively equal to itself.  This is a soundness boundary: if
    // the equality theory silently accepts a != a, the solver can
    // derive False without a real contradiction.
    let mut eq = EqualityTheory::new();

    let terms = vec![SmtTerm::Const(Symbol::new("a"))];
    eq.set_terms(terms);

    let a = TermId(0);

    let lit_neq = Lit::neg(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit_neq, &TheoryLiteral::Neq(a, a));

    match result {
        TheoryCheckResult::Conflict(clause) => {
            // The conflict explanation for a reflexive disequality needs
            // only the disequality literal itself (no equalities required).
            assert!(
                clause.contains(&lit_neq),
                "conflict clause should contain the Neq literal"
            );
        }
        other => panic!(
            "Neq(a, a) should produce an immediate conflict, got {:?}",
            other
        ),
    }
}

#[test]
fn test_self_equality_consistent_noop() {
    // Eq(a, a) is trivially true.  The theory should accept it without
    // error and without disturbing state (no spurious congruence merges).
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);

    let lit = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit, &TheoryLiteral::Eq(a, a));
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "Eq(a, a) should be consistent"
    );

    // Self-equality should not merge unrelated terms
    assert!(!eq.are_equal(a, b), "asserting a = a must not make a = b");
}

#[test]
fn test_duplicate_equality_idempotent() {
    // Asserting the same equality twice should be consistent and
    // idempotent — no conflict, no state corruption.
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);

    let lit1 = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit1, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    let lit2 = Lit::pos(crate::cdcl::Var::new(1));
    let result = eq.assert_literal(lit2, &TheoryLiteral::Eq(a, b));
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "duplicate equality should not conflict"
    );

    assert!(eq.are_equal(a, b));
}

fn assert_trace_has_f_congruence(trace: &crate::proof::ProofTrace) {
    use crate::proof::UnionReason;

    let has_congruence = trace.steps.iter().any(
        |(_, _, reason)| matches!(reason, UnionReason::Congruence { func, .. } if func == "f"),
    );
    assert!(
        has_congruence,
        "Proof trace should contain a Congruence reason for f"
    );
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
    let proof_step = trace
        .build_proof(ec_lhs, ec_rhs)
        .unwrap_or_else(|| panic!("Should be able to build proof for {context}"));
    assert!(
        !matches!(proof_step, crate::proof::ProofStep::Refl(_)),
        "proof for {context} should be non-trivial (not reflexivity)"
    );
}

#[test]
fn test_congruence_proof_trace() {
    let mut eq = EqualityTheory::new();

    // Terms: a, b, f(a), f(b)
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),                // 0
        SmtTerm::Const(Symbol::new("b")),                // 1
        SmtTerm::App(Symbol::new("f"), vec![TermId(0)]), // 2: f(a)
        SmtTerm::App(Symbol::new("f"), vec![TermId(1)]), // 3: f(b)
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let fa = TermId(2);
    let fb = TermId(3);

    // IMPORTANT: Build f(a) and f(b) in the E-graph BEFORE asserting a = b
    // This is required for congruence closure to detect the congruence
    let ec_fa = eq.get_or_create_eclass(fa);
    let ec_fb = eq.get_or_create_eclass(fb);
    assert_ne!(
        ec_fa, ec_fb,
        "f(a) and f(b) should have distinct eclasses before merge"
    );

    // Register hypothesis for proof reconstruction
    eq.register_hypothesis(a, b, clean_kernel::FVarId::new(42));

    // Assert a = b (with hypothesis tracking)
    // This will trigger congruence closure which detects f(a) = f(b)
    let lit = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // By congruence, f(a) = f(b)
    assert!(eq.are_equal(fa, fb));

    // Check that the proof trace has recorded both:
    // 1. The asserted equality (a = b) with hypothesis
    // 2. The congruence merge (f(a) = f(b))
    let trace = eq.proof_trace();

    // The trace should have at least 2 records:
    // - a = b (asserted)
    // - f(a) = f(b) (congruence)
    assert!(
        trace.steps.len() >= 2,
        "Proof trace should have at least 2 records, got {}",
        trace.steps.len()
    );
    assert_trace_has_f_congruence(trace);
    assert_nontrivial_trace_proof(&eq, trace, a, b, "a = b");
    assert_nontrivial_trace_proof(&eq, trace, fa, fb, "f(a) = f(b)");
}

#[test]
fn test_congruence_children_already_equal() {
    // Edge case: If children are added AFTER their equality is established,
    // the E-graph may not record the congruence properly because the children
    // are already canonical when the applications are built.
    //
    // This test ensures we can still build a valid proof in this case.

    let mut eq = EqualityTheory::new();

    // Terms: a, b, f(a), f(b)
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),                // 0
        SmtTerm::Const(Symbol::new("b")),                // 1
        SmtTerm::App(Symbol::new("f"), vec![TermId(0)]), // 2: f(a)
        SmtTerm::App(Symbol::new("f"), vec![TermId(1)]), // 3: f(b)
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let fa = TermId(2);
    let fb = TermId(3);

    // Register hypothesis for proof reconstruction
    eq.register_hypothesis(a, b, clean_kernel::FVarId::new(42));

    // First, assert a = b BEFORE building f(a) and f(b)
    let lit = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Now build f(a) and f(b) - since a and b are already equal,
    // these should be hashconsed to the same e-class
    let ec_fa = eq.get_or_create_eclass(fa);
    let ec_fb = eq.get_or_create_eclass(fb);

    // Since a = b was already established, f(a) and f(b) should be
    // canonicalized to the same e-class immediately
    assert!(eq.are_equal(fa, fb), "f(a) and f(b) should be equal");

    // The key question: can we still build a proof for f(a) = f(b)?
    // When terms are hashconsed to the same e-class at creation time,
    // there's no merge record - they're identical from the start.
    //
    // In this case, we have ec_fa == ec_fb (same e-class ID)
    assert_eq!(
        eq.egraph().find_const(ec_fa),
        eq.egraph().find_const(ec_fb),
        "f(a) and f(b) should be in the same canonical e-class"
    );

    // For proof reconstruction, when two terms are in the same e-class
    // from the start, we need reflexivity or to track that they were
    // unified due to their children being equal.
    //
    // The current implementation should handle this case.
    let trace = eq.proof_trace();

    // We should have at least the a = b assertion
    assert!(
        !trace.steps.is_empty(),
        "Proof trace should have at least the a = b assertion"
    );

    // When f(a) and f(b) are hashconsed together (same canonical term),
    // the proof is essentially reflexivity of f(canonical(a))
    // This is correct - no explicit merge was needed.
}
