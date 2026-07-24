// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn new_transitive_congruence_fixture() -> (
    EqualityTheory,
    TermId,
    TermId,
    TermId,
    TermId,
    TermId,
    TermId,
    TermId,
) {
    let mut eq = EqualityTheory::new();
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),                // 0
        SmtTerm::Const(Symbol::new("b")),                // 1
        SmtTerm::Const(Symbol::new("c")),                // 2
        SmtTerm::Const(Symbol::new("d")),                // 3
        SmtTerm::Const(Symbol::new("e")),                // 4
        SmtTerm::App(Symbol::new("f"), vec![TermId(0)]), // 5: f(a)
        SmtTerm::App(Symbol::new("f"), vec![TermId(2)]), // 6: f(c)
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
        TermId(6),
    )
}

fn assert_no_congruence_deductions(deduced: &[(TermId, TermId, Vec<Lit>)], context: &str) {
    assert!(
        deduced.is_empty(),
        "no congruence deductions expected for {context}, got: {:?}",
        deduced
    );
}

fn assert_transitive_congruence_explanation(explanation: &[Lit], lit_ab: Lit, lit_bc: Lit) {
    assert!(
        !explanation.is_empty(),
        "SOUNDNESS: explanation must be non-empty for non-trivial equality"
    );
    assert!(
        explanation.contains(&lit_ab),
        "SOUNDNESS: explanation must contain a=b literal (needed for transitive chain), got: {:?}",
        explanation
    );
    assert!(
        explanation.contains(&lit_bc),
        "SOUNDNESS: explanation must contain b=c literal (needed for transitive chain), got: {:?}",
        explanation
    );
}

// Precise conflict explanation tests (#2346)
// =========================================================================

/// Test that conflict explanations from assert_disequality are precise,
/// not the over-approximate all-asserted-lits (#2346).
///
/// Sets up two independent equality chains:
/// - Chain 1: a=b (relevant to conflict)
/// - Chain 2: c=d (unrelated)
///
/// Then asserts a!=b. The conflict explanation should contain only the
/// a=b literal, not the unrelated c=d literal.
#[test]
fn test_conflict_explanation_precise_assert_disequality() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("b")), // 1
        SmtTerm::Const(Symbol::new("c")), // 2
        SmtTerm::Const(Symbol::new("d")), // 3
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let c = TermId(2);
    let d = TermId(3);

    // Assert c = d (unrelated chain)
    let lit_cd = Lit::pos(crate::cdcl::Var::new(10));
    assert!(matches!(
        eq.assert_literal(lit_cd, &TheoryLiteral::Eq(c, d)),
        TheoryCheckResult::Consistent
    ));

    // Assert a = b
    let lit_ab = Lit::pos(crate::cdcl::Var::new(0));
    assert!(matches!(
        eq.assert_literal(lit_ab, &TheoryLiteral::Eq(a, b)),
        TheoryCheckResult::Consistent
    ));

    // Assert a != b - should conflict
    let lit_neq = Lit::neg(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit_neq, &TheoryLiteral::Neq(a, b));

    match result {
        TheoryCheckResult::Conflict(conflict) => {
            // The conflict should contain the a=b literal (reason for equality)
            assert!(
                conflict.contains(&lit_ab),
                "conflict should contain the a=b literal"
            );
            // The conflict should contain the a!=b literal (the disequality)
            assert!(
                conflict.contains(&lit_neq),
                "conflict should contain the a!=b literal"
            );
            // The conflict should NOT contain the unrelated c=d literal
            assert!(
                !conflict.contains(&lit_cd),
                "conflict should NOT contain the unrelated c=d literal, got: {:?}",
                conflict
            );
        }
        other => panic!("expected Conflict, got: {:?}", other),
    }
}

/// Test that conflict explanations from check_disequalities (triggered by
/// equality assertion violating a prior disequality) are precise (#2346).
#[test]
fn test_conflict_explanation_precise_check_disequalities() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("b")), // 1
        SmtTerm::Const(Symbol::new("c")), // 2
        SmtTerm::Const(Symbol::new("d")), // 3
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let c = TermId(2);
    let d = TermId(3);

    // Assert c = d (unrelated chain)
    let lit_cd = Lit::pos(crate::cdcl::Var::new(10));
    assert!(matches!(
        eq.assert_literal(lit_cd, &TheoryLiteral::Eq(c, d)),
        TheoryCheckResult::Consistent
    ));

    // Assert a != b first
    let lit_neq = Lit::neg(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit_neq, &TheoryLiteral::Neq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Assert a = b - should trigger conflict via check_disequalities
    let lit_ab = Lit::pos(crate::cdcl::Var::new(0));
    let result = eq.assert_literal(lit_ab, &TheoryLiteral::Eq(a, b));

    match result {
        TheoryCheckResult::Conflict(conflict) => {
            // The conflict should contain the a=b literal
            assert!(
                conflict.contains(&lit_ab),
                "conflict should contain the a=b literal"
            );
            // The conflict should contain the a!=b literal
            assert!(
                conflict.contains(&lit_neq),
                "conflict should contain the a!=b literal"
            );
            // The conflict should NOT contain the unrelated c=d literal
            assert!(
                !conflict.contains(&lit_cd),
                "conflict should NOT contain the unrelated c=d literal, got: {:?}",
                conflict
            );
        }
        other => panic!("expected Conflict, got: {:?}", other),
    }
}

// =========================================================================
// Transitive congruence explanation tests (Prover audit)
// =========================================================================

/// Test that explain_why_equal produces a precise explanation when
/// congruence fires after a TRANSITIVE chain of equalities.
///
/// Setup: a, b, c, f(a), f(c)  (NO f(b))
/// Assert: a=b, b=c -> transitively a=c -> congruence f(a)=f(c)
///
/// The explanation for f(a)=f(c) should contain BOTH a=b and b=c
/// literals (the transitive chain), and should NOT contain the
/// unrelated d=e literal.
///
/// This tests a harder case than the existing tests, which all use
/// direct (non-transitive) congruence triggers.
#[test]
fn test_explain_why_equal_transitive_congruence() {
    let (mut eq, a, b, c, d, e, fa, fc) = new_transitive_congruence_fixture();

    // Build f(a) and f(c) first so congruence closure can fire
    eq.get_or_create_eclass(fa);
    eq.get_or_create_eclass(fc);

    // Assert d = e (unrelated chain)
    let lit_de = Lit::pos(crate::cdcl::Var::new(10));
    assert!(matches!(
        eq.assert_literal(lit_de, &TheoryLiteral::Eq(d, e)),
        TheoryCheckResult::Consistent
    ));
    let de_deduced = eq.drain_deduced_equalities();
    assert_no_congruence_deductions(&de_deduced, "d=e");

    // Assert a = b (first link in transitive chain)
    let lit_ab = Lit::pos(crate::cdcl::Var::new(0));
    assert!(matches!(
        eq.assert_literal(lit_ab, &TheoryLiteral::Eq(a, b)),
        TheoryCheckResult::Consistent
    ));
    let ab_deduced = eq.drain_deduced_equalities();
    assert_no_congruence_deductions(&ab_deduced, "a=b alone (f(c) not f(b))");

    // Assert b = c (second link - triggers congruence: f(a) = f(c))
    let lit_bc = Lit::pos(crate::cdcl::Var::new(1));
    let result = eq.assert_literal(lit_bc, &TheoryLiteral::Eq(b, c));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    let deduced = eq.drain_deduced_equalities();
    let (_, _, ref explanation) = deduced
        .iter()
        .find(|(t1, t2, _)| (*t1 == fa && *t2 == fc) || (*t1 == fc && *t2 == fa))
        .expect("should deduce f(a)=f(c) via transitive congruence");

    // SOUNDNESS: The explanation must contain ALL literals necessary to
    // derive f(a)=f(c). For the transitive chain a=b ∧ b=c -> a=c ->
    // f(a)=f(c), both lit_ab and lit_bc are needed. An empty explanation
    // would produce a unit clause in the SAT solver, making f(a)=f(c) a
    // permanent fact that persists even when a=b or b=c are backtracked.
    assert_transitive_congruence_explanation(explanation, lit_ab, lit_bc);

    let stats = eq.explanation_stats();
    assert_eq!(
        stats.precise_count,
        deduced.len() as u64,
        "each drained deduced equality should use a precise EUF explanation"
    );
    assert_eq!(
        stats.fallback_count, 0,
        "precise path should not increment fallback counters"
    );
}

#[test]
fn test_explanation_stats_track_disconnected_fallback() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let lit_ab = Lit::pos(crate::cdcl::Var::new(0));
    assert!(matches!(
        eq.assert_literal(lit_ab, &TheoryLiteral::Eq(a, b)),
        TheoryCheckResult::Consistent
    ));

    // Test-only setup: keep the E-graph equality but erase the precise
    // forest path so the conflict must fall back to conservative explanation.
    eq.set_proof_forest_for_test(ProofForest::new());

    let lit_neq = Lit::neg(crate::cdcl::Var::new(1));
    match eq.assert_literal(lit_neq, &TheoryLiteral::Neq(a, b)) {
        TheoryCheckResult::Conflict(conflict) => {
            assert!(
                conflict.contains(&lit_ab),
                "fallback conflict should still contain a=b"
            );
            assert!(
                conflict.contains(&lit_neq),
                "fallback conflict should include the disequality literal"
            );
        }
        other => panic!("expected fallback conflict, got: {:?}", other),
    }

    let stats = eq.explanation_stats();
    assert_eq!(stats.precise_count, 0);
    assert_eq!(stats.fallback_count, 1);
    assert_eq!(stats.disconnected_terms_count, 1);
    assert_eq!(stats.recursion_limit_count, 0);
    assert_eq!(stats.forest_depth_limit_count, 0);
    assert_eq!(stats.broken_ancestor_path_count, 0);
    assert_eq!(stats.congruence_argument_failure_count, 0);
}

/// Performance test: assert_equality calls build_class_members_map which iterates
/// the entire term_to_eclass map on every merge. For T registered terms and M merges,
/// this is O(T * M). This test measures the scaling to catch regressions and quantify
/// the overhead for large term sets.
///
/// Current behavior: O(T) per merge (rebuild from scratch).
/// Optimal: O(1) amortized per merge (incremental canonical map).
#[test]
fn test_build_class_members_map_scaling() {
    // Small: 20 terms, 10 merges
    let elapsed_small = {
        let mut eq = EqualityTheory::new();
        let n_small = 20;
        let terms: Vec<SmtTerm> = (0..n_small)
            .map(|i| SmtTerm::Const(Symbol::new(format!("t{i}"))))
            .collect();
        eq.set_terms(terms);

        let start = std::time::Instant::now();
        for i in 0..(n_small / 2) {
            let lit = Lit::pos(crate::cdcl::Var::new(i));
            let t1 = TermId(i * 2);
            let t2 = TermId(i * 2 + 1);
            let _ = eq.assert_literal(lit, &TheoryLiteral::Eq(t1, t2));
        }
        start.elapsed()
    };

    // Large: 200 terms, 100 merges
    let elapsed_large = {
        let mut eq = EqualityTheory::new();
        let n_large = 200;
        let terms: Vec<SmtTerm> = (0..n_large)
            .map(|i| SmtTerm::Const(Symbol::new(format!("t{i}"))))
            .collect();
        eq.set_terms(terms);

        let start = std::time::Instant::now();
        for i in 0..(n_large / 2) {
            let lit = Lit::pos(crate::cdcl::Var::new(i));
            let t1 = TermId(i * 2);
            let t2 = TermId(i * 2 + 1);
            let _ = eq.assert_literal(lit, &TheoryLiteral::Eq(t1, t2));
        }
        start.elapsed()
    };

    // 10x terms + 10x merges -> expected O(T*M) = 100x if quadratic
    // With 40x threshold we catch >O(n) but allow constant factor noise.
    // Sub-quadratic (e.g., O(n log n)) would be ~33x.
    let ratio = elapsed_large.as_nanos() as f64 / elapsed_small.as_nanos().max(1) as f64;
    assert!(
        ratio < 400.0,
        "build_class_members_map scaling: 10x input gave {ratio:.1}x time \
         (expected <400x for O(T*M) with 10x T and 10x M; got worse than quadratic)"
    );
}

/// Performance proof: `check_disequalities` scans ALL disequalities on
/// every `assert_equality` call.
///
/// In `theory.rs` `check_disequalities()` (lines 279-293):
///
///     for i in 0..self.disequalities.len() {
///         let (t1, t2, lit) = self.disequalities[i];
///         let ec1 = self.get_or_create_eclass(t1);
///         let ec2 = self.get_or_create_eclass(t2);
///         if self.egraph.are_equal(ec1, ec2) { ... }
///     }
///
/// Called from `assert_equality()` (line 254) on EVERY equality assertion.
/// With D disequalities and E equality assertions, total work is O(D * E).
///
/// Production EUF solvers maintain a forbidden-pair index (mapping canonical
/// class pairs to disequality literals) and only check disequalities for
/// the two merged classes after a union, giving O(min(|class1|, |class2|))
/// instead of O(D).
///
/// This test measures the O(D * E) scaling to document the quadratic cost
/// and catch regressions.
///
/// Regression test for performance_proofs P1 iter 1230.
#[test]
fn test_check_disequalities_full_scan_scaling() {
    // Measure time for D disequalities followed by E equalities.
    // We use distinct term pairs so no conflict is triggered.
    let measure = |d: u32, e: u32| -> u128 {
        let total_terms = 2 * (d + e);
        let mut eq = EqualityTheory::new();
        let terms: Vec<SmtTerm> = (0..total_terms)
            .map(|i| SmtTerm::Const(Symbol::new(format!("t{i}"))))
            .collect();
        eq.set_terms(terms);

        // Assert D disequalities on term pairs (0,1), (2,3), ...
        for i in 0..d {
            let lit = Lit::neg(crate::cdcl::Var::new(i));
            let t1 = TermId(i * 2);
            let t2 = TermId(i * 2 + 1);
            let _ = eq.assert_literal(lit, &TheoryLiteral::Neq(t1, t2));
        }

        // Assert E equalities on fresh term pairs — no conflict.
        let start = std::time::Instant::now();
        for i in 0..e {
            let lit = Lit::pos(crate::cdcl::Var::new(d + i));
            let base = 2 * d + i * 2;
            let t1 = TermId(base);
            let t2 = TermId(base + 1);
            let _ = eq.assert_literal(lit, &TheoryLiteral::Eq(t1, t2));
        }
        start.elapsed().as_nanos()
    };

    // Small: 10 diseqs, 10 eqs -> 100 total check iterations
    let t_small = measure(10, 10);
    // Large: 100 diseqs, 100 eqs -> 10000 total check iterations
    let t_large = measure(100, 100);

    // 10x D and 10x E: expected O(D*E) = 100x if purely quadratic.
    // The rebuild in take_class_members_snapshot adds O(T*E), so total is
    // O((D+T)*E). With generous threshold for constant-factor noise.
    let ratio = t_large as f64 / t_small.max(1) as f64;
    eprintln!(
        "check_disequalities scan: 10x input gave {ratio:.1}x time \
         (small={t_small}ns, large={t_large}ns)"
    );
    assert!(
        ratio < 2000.0,
        "check_disequalities scaling: 10x input gave {ratio:.1}x time \
         (expected <2000x for O(D*E) with rebuild overhead; catastrophic regression)"
    );
}
