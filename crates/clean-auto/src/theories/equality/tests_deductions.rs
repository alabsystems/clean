// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// =========================================================================
// Incremental drain_deduced tests (#2344)
// =========================================================================

/// Test that drain_deduced returns only NEW congruence equalities,
/// not directly asserted ones, and that subsequent drains return empty.
#[test]
fn test_drain_deduced_incremental() {
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

    // Build f(a) and f(b) first so congruence closure can fire
    eq.get_or_create_eclass(fa);
    eq.get_or_create_eclass(fb);

    // No deductions yet
    assert!(
        eq.drain_deduced_equalities().is_empty(),
        "no deductions before any assertions"
    );

    // Assert a = b -> triggers congruence: f(a) = f(b)
    let lit = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // drain_deduced should return the congruence-deduced f(a)=f(b) with explanation
    let deduced = eq.drain_deduced_equalities();
    assert!(
        !deduced.is_empty(),
        "should have deduced f(a)=f(b) via congruence"
    );
    // Verify the deduced pair contains fa and fb (order may vary)
    let has_fa_fb = deduced
        .iter()
        .any(|(t1, t2, _)| (*t1 == fa && *t2 == fb) || (*t1 == fb && *t2 == fa));
    assert!(
        has_fa_fb,
        "deduced equalities should contain (f(a), f(b)), got: {:?}",
        deduced
    );
    // Verify the explanation is precise: should contain the assertion lit,
    // not ALL asserted lits (#2344 criterion 4)
    let (_, _, ref explanation) = deduced
        .iter()
        .find(|(t1, t2, _)| (*t1 == fa && *t2 == fb) || (*t1 == fb && *t2 == fa))
        .expect("should have fa=fb deduction");
    assert!(
        !explanation.is_empty(),
        "explanation should contain at least one asserted literal"
    );
    // The explanation for f(a)=f(b) via congruence from a=b should
    // contain exactly the assertion literal for a=b
    assert!(
        explanation.contains(&lit),
        "explanation should contain the a=b assertion literal"
    );

    // Second drain should be empty - incremental, not batch
    assert!(
        eq.drain_deduced_equalities().is_empty(),
        "second drain should be empty (incremental)"
    );
}

/// Stress test: N-term chain should produce O(N) deductions, not O(N^2).
#[test]
fn test_drain_deduced_linear_not_quadratic() {
    let mut eq = EqualityTheory::new();

    // Create 50 terms: a0, a1, ..., a49 and f(a0), f(a1), ..., f(a49)
    let n = 50;
    let mut terms = Vec::new();
    for i in 0..n {
        terms.push(SmtTerm::Const(Symbol::new(format!("a{i}"))));
    }
    for i in 0..n {
        terms.push(SmtTerm::App(Symbol::new("f"), vec![TermId(i as u32)]));
    }
    eq.set_terms(terms);

    // Build all f(ai) terms in the E-graph first
    for i in 0..n {
        eq.get_or_create_eclass(TermId((n + i) as u32));
    }

    // Assert a0=a1, a1=a2, ..., a48=a49 (N-1 assertions)
    // Each assertion triggers at most one congruence merge: f(ai)=f(ai+1)
    let mut total_deduced = 0usize;
    for i in 0..(n - 1) {
        let lit = Lit::pos(crate::cdcl::Var::new(i as u32));
        let result = eq.assert_literal(
            lit,
            &TheoryLiteral::Eq(TermId(i as u32), TermId((i + 1) as u32)),
        );
        assert!(matches!(result, TheoryCheckResult::Consistent));
        total_deduced += eq.drain_deduced_equalities().len();
    }

    // With incremental tracking, total deductions should be O(N).
    // The old O(N^2) approach would produce N*(N-1)/2 = 1225 pairs.
    // Incremental approach produces at most N-1 = 49 pairs.
    assert!(
        total_deduced < n * 2,
        "total deductions ({total_deduced}) should be O(N) not O(N^2); \
         N={n}, O(N^2) would be {}",
        n * (n - 1) / 2
    );
}

/// Verify that backtrack clears pending deduced equalities (#2344).
#[test]
fn test_drain_deduced_cleared_on_backtrack() {
    let mut eq = EqualityTheory::new();

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

    // Build f(a) and f(b) first
    eq.get_or_create_eclass(fa);
    eq.get_or_create_eclass(fb);

    // Push to level 1
    eq.push();

    // Assert a = b at level 1 -> congruence: f(a) = f(b)
    let lit = Lit::pos(crate::cdcl::Var::new(0));
    assert!(matches!(
        eq.assert_literal(lit, &TheoryLiteral::Eq(a, b)),
        TheoryCheckResult::Consistent
    ));

    // Pending deduced should be non-empty
    assert!(
        !eq.pending_deduced.is_empty(),
        "pending_deduced should be populated after congruence"
    );

    // Backtrack to level 0 - should clear pending
    eq.backtrack(0);

    assert!(
        eq.drain_deduced_equalities().is_empty(),
        "drain_deduced should be empty after backtrack"
    );

    // a and b should not be equal anymore
    assert!(!eq.are_equal(a, b));
}

/// Test that E-graph explanation extraction returns a PRECISE subset of
/// asserted lits, not the full over-approximation (#2344 criterion 4).
///
/// Sets up two independent equality chains:
/// - Chain 1: a=b -> congruence f(a)=f(b)
/// - Chain 2: c=d (unrelated)
///
/// The explanation for f(a)=f(b) should contain only the a=b literal,
/// NOT the unrelated c=d literal.
#[test]
fn test_drain_deduced_explanation_is_precise() {
    let mut eq = EqualityTheory::new();

    // Terms: a, b, c, d, f(a), f(b)
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),                // 0
        SmtTerm::Const(Symbol::new("b")),                // 1
        SmtTerm::Const(Symbol::new("c")),                // 2
        SmtTerm::Const(Symbol::new("d")),                // 3
        SmtTerm::App(Symbol::new("f"), vec![TermId(0)]), // 4: f(a)
        SmtTerm::App(Symbol::new("f"), vec![TermId(1)]), // 5: f(b)
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let c = TermId(2);
    let d = TermId(3);
    let fa = TermId(4);
    let fb = TermId(5);

    // Build f(a) and f(b) first so congruence closure can fire
    eq.get_or_create_eclass(fa);
    eq.get_or_create_eclass(fb);

    // Assert c = d (unrelated chain)
    let lit_cd = Lit::pos(crate::cdcl::Var::new(10));
    assert!(matches!(
        eq.assert_literal(lit_cd, &TheoryLiteral::Eq(c, d)),
        TheoryCheckResult::Consistent
    ));
    // Drain the c=d deductions (none expected, no congruence for c/d)
    let cd_deduced = eq.drain_deduced_equalities();
    assert!(
        cd_deduced.is_empty(),
        "no congruence deductions expected for c=d, got: {:?}",
        cd_deduced
    );

    // Assert a = b -> triggers congruence: f(a) = f(b)
    let lit_ab = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit_ab, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    let deduced = eq.drain_deduced_equalities();
    let (_, _, ref explanation) = deduced
        .iter()
        .find(|(t1, t2, _)| (*t1 == fa && *t2 == fb) || (*t1 == fb && *t2 == fa))
        .expect("should deduce f(a)=f(b)");

    // PRECISE: explanation should contain the a=b assertion literal
    assert!(
        explanation.contains(&lit_ab),
        "explanation should contain the a=b literal, got: {:?}",
        explanation
    );

    // PRECISE: explanation should NOT contain the unrelated c=d literal
    assert!(
        !explanation.contains(&lit_cd),
        "explanation should NOT contain the unrelated c=d literal, got: {:?}",
        explanation
    );

    // The conservative over-approximation (explain_equality) would
    // return [lit_ab, lit_cd]. Our precise explanation is strictly smaller.
    let conservative = eq.explain_equality();
    assert!(
        explanation.len() < conservative.len(),
        "precise explanation ({}) should be smaller than conservative ({})",
        explanation.len(),
        conservative.len()
    );
}
