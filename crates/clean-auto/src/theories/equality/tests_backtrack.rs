// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn new_backtrack_fixture() -> (EqualityTheory, TermId, TermId, TermId, TermId, TermId) {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),                // 0
        SmtTerm::Const(Symbol::new("b")),                // 1
        SmtTerm::Const(Symbol::new("c")),                // 2
        SmtTerm::App(Symbol::new("f"), vec![TermId(0)]), // 3: f(a)
        SmtTerm::App(Symbol::new("f"), vec![TermId(1)]), // 4: f(b)
    ];
    eq.set_terms(terms);

    (eq, TermId(0), TermId(1), TermId(2), TermId(3), TermId(4))
}

fn seed_level0_congruence(
    eq: &mut EqualityTheory,
    a: TermId,
    b: TermId,
    fa: TermId,
    fb: TermId,
) -> usize {
    let _ec_fa = eq.get_or_create_eclass(fa);
    let _ec_fb = eq.get_or_create_eclass(fb);
    let lit = Lit::pos(crate::cdcl::Var::new(0));
    assert!(matches!(
        eq.assert_literal(lit, &TheoryLiteral::Eq(a, b)),
        TheoryCheckResult::Consistent
    ));
    assert!(eq.are_equal(a, b));
    assert!(eq.are_equal(fa, fb), "congruence: f(a) = f(b)");

    let level0_eclass_count = eq.term_to_eclass.len();
    assert!(
        level0_eclass_count >= 4,
        "should have entries for a, b, f(a), f(b)"
    );
    level0_eclass_count
}

fn assert_term_to_eclass_entries_are_canonical(eq: &EqualityTheory) {
    for (&term_id, &eclass_id) in &eq.term_to_eclass {
        let canonical = eq.egraph().find_const(eclass_id);
        let double_find = eq.egraph().find_const(canonical);
        assert_eq!(
            canonical.id(),
            double_find.id(),
            "term_to_eclass entry for TermId({}) has non-idempotent find: \
             EClassId {} -> canonical {} -> double-find {}",
            term_id.raw(),
            eclass_id.id(),
            canonical.id(),
            double_find.id()
        );
    }
}

fn assert_backtrack_trails_cleared(eq: &EqualityTheory, iter: usize) {
    assert_eq!(
        eq.equality_trail.len(),
        1,
        "equality_trail should have 1 level after backtrack (iter {iter})"
    );
    assert_eq!(
        eq.diseq_trail.len(),
        1,
        "diseq_trail should have 1 entry after backtrack (iter {iter})"
    );
    assert_eq!(
        eq.egraph_trail.len(),
        0,
        "egraph_trail should be empty after backtrack to 0 (iter {iter})"
    );
    assert_eq!(
        eq.term_to_eclass_trail.len(),
        0,
        "term_to_eclass_trail should be empty after backtrack to 0 (iter {iter})"
    );
    assert_eq!(
        eq.proof_trace_len_trail.len(),
        0,
        "proof_trace_len_trail should be empty after backtrack to 0 (iter {iter})"
    );
    assert_eq!(
        eq.term_to_hypothesis_trail.len(),
        0,
        "term_to_hypothesis_trail should be empty after backtrack to 0 (iter {iter})"
    );
}

/// Verify that term_to_eclass is properly cleared and rebuilt during
/// backtrack, preventing stale EClassId references (#2310).
///
/// After backtrack(0), the E-graph is rebuilt from scratch. Any
/// term_to_eclass entries from higher levels must be gone, and surviving
/// level-0 entries must reference valid EClassIds in the new E-graph.
#[test]
fn test_term_to_eclass_cleared_on_backtrack() {
    let (mut eq, a, b, c, fa, fb) = new_backtrack_fixture();
    let level0_eclass_count = seed_level0_congruence(&mut eq, a, b, fa, fb);

    // Push to level 1
    eq.push();

    // Level 1: assert b = c (adds c to term_to_eclass)
    let lit2 = Lit::pos(crate::cdcl::Var::new(1));
    assert!(matches!(
        eq.assert_literal(lit2, &TheoryLiteral::Eq(b, c)),
        TheoryCheckResult::Consistent
    ));
    assert!(eq.are_equal(a, c), "transitivity via level-1 assertion");

    let level1_eclass_count = eq.term_to_eclass.len();
    assert!(
        level1_eclass_count > level0_eclass_count,
        "level 1 should have added c to term_to_eclass"
    );

    // Backtrack to level 0
    eq.backtrack(0);

    // term_to_eclass should be rebuilt - stale level-1 entries gone
    // After rebuild, only terms referenced by level-0 equalities are present
    // (a, b, and their subterms from get_or_create_eclass during replay)
    assert!(
        !eq.are_equal(a, c),
        "a = c should not hold after backtrack to level 0"
    );

    // Verify the rebuilt term_to_eclass has valid EClassIds
    // by checking that level-0 equalities still work correctly
    assert!(
        eq.are_equal(a, b),
        "a = b (level 0) should survive backtrack"
    );
    assert_term_to_eclass_entries_are_canonical(&eq);
}

/// Verify that repeated push/backtrack cycles don't leak memory in
/// term_to_eclass, equality_trail, or disequalities.
///
/// Simulates the DPLL(T) pattern: push -> assert -> backtrack(0) -> repeat.
#[test]
fn test_equality_push_backtrack_no_memory_growth() {
    let (mut eq, a, b, c, _fa, _fb) = new_backtrack_fixture();

    // Level 0: base assertion
    let lit0 = Lit::pos(crate::cdcl::Var::new(0));
    assert!(matches!(
        eq.assert_literal(lit0, &TheoryLiteral::Eq(a, b)),
        TheoryCheckResult::Consistent
    ));

    // Simulate 100 DPLL(T) iterations: push -> assert at level 1 -> backtrack(0)
    for i in 0..100 {
        eq.push();

        // Assert b = c at level 1
        let lit = Lit::pos(crate::cdcl::Var::new(1));
        assert!(matches!(
            eq.assert_literal(lit, &TheoryLiteral::Eq(b, c)),
            TheoryCheckResult::Consistent
        ));

        eq.backtrack(0);
        assert_backtrack_trails_cleared(&eq, i);
    }

    // a = b should still hold
    assert!(eq.are_equal(a, b));
    // a = c should NOT hold
    assert!(!eq.are_equal(a, c));
}

/// Regression test for #2318: term_to_hypothesis is saved/restored by push/backtrack.
///
/// Before the fix, `term_to_hypothesis` retained stale mappings from retracted
/// levels. If different hypotheses are registered for the same term pair at
/// different decision levels, the wrong hypothesis could be used after backtrack.
#[test]
fn test_term_to_hypothesis_restored_on_backtrack() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let hyp_level0 = clean_kernel::FVarId::new(100);
    let hyp_level1 = clean_kernel::FVarId::new(200);

    // Level 0: register hypothesis for (a, b)
    eq.register_hypothesis(a, b, hyp_level0);
    assert_eq!(
        eq.term_to_hypothesis.get(&(a, b)).copied(),
        Some(hyp_level0),
        "level 0 hypothesis should be registered"
    );

    // Push to level 1
    eq.push();

    // Level 1: overwrite hypothesis for same term pair
    eq.register_hypothesis(a, b, hyp_level1);
    assert_eq!(
        eq.term_to_hypothesis.get(&(a, b)).copied(),
        Some(hyp_level1),
        "level 1 hypothesis should overwrite"
    );

    // Backtrack to level 0
    eq.backtrack(0);

    // term_to_hypothesis should be restored to level 0 state
    assert_eq!(
        eq.term_to_hypothesis.get(&(a, b)).copied(),
        Some(hyp_level0),
        "hypothesis should be restored to level 0 value after backtrack"
    );
}

/// Regression for #2386: reusable snapshots must track the latest restored
/// level-1 state, not the first branch that previously occupied that level.
#[test]
fn test_backtrack_reuses_updated_level_snapshot_after_rebranch() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
        SmtTerm::Const(Symbol::new("c")),
        SmtTerm::Const(Symbol::new("d")),
        SmtTerm::Const(Symbol::new("e")),
        SmtTerm::Const(Symbol::new("f")),
        SmtTerm::Const(Symbol::new("g")),
        SmtTerm::Const(Symbol::new("h")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let c = TermId(2);
    let d = TermId(3);
    let e = TermId(4);
    let f = TermId(5);
    let g = TermId(6);
    let h = TermId(7);

    eq.push();
    let ab = Lit::pos(crate::cdcl::Var::new(0));
    assert!(matches!(
        eq.assert_literal(ab, &TheoryLiteral::Eq(a, b)),
        TheoryCheckResult::Consistent
    ));
    assert!(eq.are_equal(a, b), "level 1 should contain a = b");

    eq.push();
    let cd = Lit::pos(crate::cdcl::Var::new(1));
    assert!(matches!(
        eq.assert_literal(cd, &TheoryLiteral::Eq(c, d)),
        TheoryCheckResult::Consistent
    ));
    assert!(eq.are_equal(c, d), "level 2 should contain c = d");

    eq.backtrack(1);
    assert!(
        eq.are_equal(a, b),
        "a = b should survive backtrack to level 1"
    );
    assert!(
        !eq.are_equal(c, d),
        "level-2 equality must disappear after backtrack"
    );

    let ef = Lit::pos(crate::cdcl::Var::new(2));
    assert!(matches!(
        eq.assert_literal(ef, &TheoryLiteral::Eq(e, f)),
        TheoryCheckResult::Consistent
    ));
    assert!(eq.are_equal(e, f), "restored level 1 should accept e = f");

    eq.push();
    let gh = Lit::pos(crate::cdcl::Var::new(3));
    assert!(matches!(
        eq.assert_literal(gh, &TheoryLiteral::Eq(g, h)),
        TheoryCheckResult::Consistent
    ));
    assert!(
        eq.are_equal(g, h),
        "second level-2 branch should contain g = h"
    );

    eq.backtrack(1);
    assert!(
        eq.are_equal(a, b),
        "original level-1 equality should still hold"
    );
    assert!(
        eq.are_equal(e, f),
        "backtrack after rebranch must keep the updated level-1 equality"
    );
    assert!(
        !eq.are_equal(c, d),
        "first level-2 branch must stay retracted after the second backtrack"
    );
    assert!(
        !eq.are_equal(g, h),
        "latest level-2 equality must be removed by the second backtrack"
    );
}

/// Soundness invariant: EqualityTheory snapshot trail lengths must stay
/// in sync at all points during push/backtrack sequences. The `if let
/// Some(snapshot)` pattern in backtrack() (solver_impl.rs:43-54) silently
/// skips state restoration when a trail entry is missing. This test verifies
/// the structural invariant that prevents that silent failure path from
/// ever being reachable.
///
/// All four rollback trails (egraph, term_to_eclass, proof-trace checkpoints,
/// term_to_hypothesis) must have the same length at every point. The
/// equality_trail and diseq_trail must always be one longer (they include
/// a level-0 entry).
#[test]
fn test_equality_trail_length_invariant_across_push_backtrack() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
        SmtTerm::Const(Symbol::new("c")),
        SmtTerm::Const(Symbol::new("d")),
    ];
    eq.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);
    let c = TermId(2);
    let d = TermId(3);

    fn assert_snapshot_trails_in_sync(eq: &EqualityTheory, expected_level: usize, ctx: &str) {
        // All four rollback trails must have the same length
        let egraph_len = eq.egraph_trail.len();
        assert_eq!(
            egraph_len, expected_level,
            "egraph_trail length mismatch at {ctx}"
        );
        assert_eq!(
            eq.term_to_eclass_trail.len(),
            egraph_len,
            "term_to_eclass_trail out of sync with egraph_trail at {ctx}"
        );
        assert_eq!(
            eq.proof_trace_len_trail.len(),
            egraph_len,
            "proof_trace_len_trail out of sync with egraph_trail at {ctx}"
        );
        assert_eq!(
            eq.term_to_hypothesis_trail.len(),
            egraph_len,
            "term_to_hypothesis_trail out of sync with egraph_trail at {ctx}"
        );
        // equality_trail and diseq_trail always have one extra (level 0)
        assert_eq!(
            eq.equality_trail.len(),
            egraph_len + 1,
            "equality_trail length mismatch at {ctx}"
        );
        assert_eq!(
            eq.diseq_trail.len(),
            egraph_len + 1,
            "diseq_trail length mismatch at {ctx}"
        );
    }

    assert_snapshot_trails_in_sync(&eq, 0, "initial state (level 0)");

    eq.push();
    assert_snapshot_trails_in_sync(&eq, 1, "after push to level 1");

    let lit0 = Lit::pos(crate::cdcl::Var::new(0));
    let _ = eq.assert_literal(lit0, &TheoryLiteral::Eq(a, b));
    assert_snapshot_trails_in_sync(&eq, 1, "after assert a=b at level 1");

    eq.push();
    assert_snapshot_trails_in_sync(&eq, 2, "after push to level 2");

    let lit1 = Lit::pos(crate::cdcl::Var::new(1));
    let _ = eq.assert_literal(lit1, &TheoryLiteral::Eq(c, d));
    assert_snapshot_trails_in_sync(&eq, 2, "after assert c=d at level 2");

    eq.backtrack(1);
    assert_snapshot_trails_in_sync(&eq, 1, "after backtrack to level 1");

    // Rebranch: push again from level 1
    eq.push();
    assert_snapshot_trails_in_sync(&eq, 2, "after rebranch push to level 2");

    eq.backtrack(0);
    assert_snapshot_trails_in_sync(&eq, 0, "after backtrack to level 0");
}
