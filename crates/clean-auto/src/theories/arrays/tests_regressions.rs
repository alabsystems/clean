// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn new_row_same_explanation_fixture() -> ArrayTheory {
    let mut theory = ArrayTheory::new();
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("i")), // 1: store index
        SmtTerm::Const(Symbol::new("j")), // 2: select index (distinct from i)
        SmtTerm::Const(Symbol::new("v")), // 3: value
        SmtTerm::Const(Symbol::new("x")), // 4: irrelevant
        SmtTerm::Const(Symbol::new("y")), // 5: irrelevant
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(3)]), // 6
        SmtTerm::App(Symbol::new("select"), vec![TermId(6), TermId(2)]), // 7
    ];
    theory.set_terms(terms);
    theory
}

fn assert_irrelevant_row_same_literals(theory: &mut ArrayTheory) -> Lit {
    let lit_xy = make_lit(10, true);
    let lit_aa = make_lit(11, true);
    let lit_vv = make_lit(12, true);

    let _ = theory.assert_literal(lit_xy, &TheoryLiteral::Eq(TermId(4), TermId(5)));
    let _ = theory.assert_literal(lit_aa, &TheoryLiteral::Eq(TermId(0), TermId(0)));
    let _ = theory.assert_literal(lit_vv, &TheoryLiteral::Eq(TermId(3), TermId(3)));

    lit_xy
}

fn assert_single_literal_row_same_explanation(
    drained: &[(TermId, TermId, Vec<Lit>)],
    trigger: Lit,
    irrelevant: Lit,
) {
    for (_t1, _t2, explanation) in drained {
        assert_eq!(
            explanation.len(),
            1,
            "ROW-same explanation should contain exactly 1 literal (the i=j trigger), \
             got {} lits: {:?} (#2330)",
            explanation.len(),
            explanation,
        );
        assert_eq!(
            explanation[0], trigger,
            "explanation literal should be the triggering i=j literal"
        );
        assert!(
            !explanation.contains(&irrelevant),
            "explanation should NOT contain irrelevant x=y literal"
        );
    }
}

/// Regression test for #2313: pending_equalities cleared on backtrack.
///
/// Before the fix, backtrack truncated equalities/disequalities but left
/// pending_equalities intact, leaking stale propagations across DPLL(T)
/// iterations. The fix clears pending_equalities in backtrack().
#[test]
fn test_pending_equalities_cleared_on_backtrack() {
    let mut theory = ArrayTheory::new();

    // select(store(a, i, v), i) - ROW-same-index applies
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("i")), // 1
        SmtTerm::Const(Symbol::new("v")), // 2
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(2)]), // 3
        SmtTerm::App(Symbol::new("select"), vec![TermId(3), TermId(1)]), // 4
    ];
    theory.set_terms(terms);

    // Push to level 1
    theory.push();

    // Assert i = i (same index). ROW-same-index should trigger, adding
    // (TermId(4), TermId(2)) to pending_equalities (select_result = v).
    let eq_lit = make_lit(0, true);
    let result = theory.assert_literal(eq_lit, &TheoryLiteral::Eq(TermId(1), TermId(1)));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Backtrack to level 0 - pending_equalities should be cleared (#2313)
    theory.backtrack(0);

    assert!(
        theory.pending_equalities.is_empty(),
        "pending_equalities must be empty after backtrack"
    );

    // drain_deduced_equalities should return nothing (no stale leakage)
    let drained = theory.drain_deduced_equalities();
    assert!(
        drained.is_empty(),
        "no stale pending equalities should leak after backtrack"
    );
}

/// #2330: Per-equality explanations are shorter than full assertion set.
///
/// Uses distinct term IDs for store index (i) and select index (j), then
/// asserts 4 literals (3 irrelevant + 1 triggering `i=j` for ROW-same).
/// Verifies the drained explanation contains only the 1 relevant literal.
#[test]
fn test_propagation_explanation_shorter_than_assertion_set() {
    let mut theory = new_row_same_explanation_fixture();
    let lit_xy = assert_irrelevant_row_same_literals(&mut theory);

    // No pending equalities yet - i(1) != j(2) so ROW-same hasn't fired.
    assert!(
        theory.drain_deduced_equalities().is_empty(),
        "no ROW-same before i=j asserted"
    );

    // Assert the relevant equality: i = j (triggers ROW-same).
    let lit_ij = make_lit(13, true);
    let _ = theory.assert_literal(lit_ij, &TheoryLiteral::Eq(TermId(1), TermId(2)));

    // Drain: should get (TermId(7), TermId(3), explanation)
    // select(store(a,i,v), j) = v because i = j
    let drained = theory.drain_deduced_equalities();
    assert!(
        !drained.is_empty(),
        "ROW-same should fire for select(store(a,i,v),j) when i=j asserted"
    );

    assert_single_literal_row_same_explanation(&drained, lit_ij, lit_xy);
}

/// Regression test for #2353: transitive index equality triggers ROW-same.
///
/// Before the fix, are_equal(i, j) returned false when i=j was only
/// known transitively via the E-graph (i=k, k=j). The forwarding in
/// smt.rs:check_theories ensures the array theory sees these deductions.
#[test]
fn test_row_same_transitive_index() {
    use crate::smt::{SmtResult, SmtSolver};
    use crate::theories::equality::EqualityTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArrayTheory::new()));

    // Terms: a, i, k, j, v, store(a, i, v), select(store(a, i, v), j)
    let a = smt.const_term("a");
    let i = smt.const_term("i");
    let k = smt.const_term("k");
    let j = smt.const_term("j");
    let v = smt.const_term("v");
    let store_aiv = smt.app_term("store", vec![a, i, v]);
    let select_j = smt.app_term("select", vec![store_aiv, j]);

    // Assert i = k and k = j (transitive: i = j)
    let _ = smt.assert_eq(i, k);
    let _ = smt.assert_eq(k, j);

    // Assert select(store(a, i, v), j) != v
    // UNSAT: transitively i = j, so ROW-same gives select(store(a,i,v),j) = v
    let _ = smt.assert_neq(select_j, v);

    match smt.solve() {
        SmtResult::Unsat(_) => {} // Expected
        other => {
            panic!("Expected UNSAT (transitive i=k, k=j triggers ROW-same), got {other:?}")
        }
    }
}

#[test]
fn test_row_same_conflicts_follow_select_key_order() {
    let mut theory = ArrayTheory::new();

    let i = TermId(0);
    let j = TermId(1);
    let v_small = TermId(2);
    let v_large = TermId(3);
    let base_small = TermId(4);
    let base_large = TermId(5);
    let store_small = TermId(6);
    let store_large = TermId(7);
    let result_small = TermId(8);
    let result_large = TermId(9);

    theory.selects.insert((store_large, j), result_large);
    theory.selects.insert((store_small, j), result_small);
    theory.stores.insert(store_large, (base_large, i, v_large));
    theory.stores.insert(store_small, (base_small, i, v_small));

    let large_result_diseq = make_lit(0, false);
    let small_result_diseq = make_lit(1, false);
    let index_eq = make_lit(2, true);

    let result = theory.assert_literal(
        large_result_diseq,
        &TheoryLiteral::Neq(result_large, v_large),
    );
    assert!(matches!(result, TheoryCheckResult::Consistent));

    let result = theory.assert_literal(
        small_result_diseq,
        &TheoryLiteral::Neq(result_small, v_small),
    );
    assert!(matches!(result, TheoryCheckResult::Consistent));

    match theory.assert_literal(index_eq, &TheoryLiteral::Eq(i, j)) {
        TheoryCheckResult::Conflict(lits) => {
            assert_eq!(
                lits,
                vec![index_eq, small_result_diseq],
                "ROW-same should surface the lexicographically first select/store conflict"
            );
        }
        other => panic!("Expected ROW-same conflict, got {other:?}"),
    }
}

#[test]
fn test_row_diff_conflicts_follow_select_key_order() {
    let mut theory = ArrayTheory::new();

    let i = TermId(0);
    let j = TermId(1);
    let v_small = TermId(2);
    let v_large = TermId(3);
    let base_small = TermId(4);
    let base_large = TermId(5);
    let store_small = TermId(6);
    let store_large = TermId(7);
    let result_small = TermId(8);
    let result_large = TermId(9);
    let base_select_small = TermId(10);
    let base_select_large = TermId(11);

    theory.selects.insert((store_large, j), result_large);
    theory.selects.insert((base_large, j), base_select_large);
    theory.selects.insert((store_small, j), result_small);
    theory.selects.insert((base_small, j), base_select_small);
    theory.stores.insert(store_large, (base_large, i, v_large));
    theory.stores.insert(store_small, (base_small, i, v_small));

    let large_result_diseq = make_lit(0, false);
    let small_result_diseq = make_lit(1, false);
    let index_diseq = make_lit(2, false);

    let result = theory.assert_literal(
        large_result_diseq,
        &TheoryLiteral::Neq(result_large, base_select_large),
    );
    assert!(matches!(result, TheoryCheckResult::Consistent));

    let result = theory.assert_literal(
        small_result_diseq,
        &TheoryLiteral::Neq(result_small, base_select_small),
    );
    assert!(matches!(result, TheoryCheckResult::Consistent));

    match theory.assert_literal(index_diseq, &TheoryLiteral::Neq(i, j)) {
        TheoryCheckResult::Conflict(lits) => {
            assert_eq!(
                lits,
                vec![index_diseq, small_result_diseq],
                "ROW-diff should surface the lexicographically first select/store conflict"
            );
        }
        other => panic!("Expected ROW-diff conflict, got {other:?}"),
    }
}

/// Regression test for #2389: build_row_same_conflict must never return empty Conflict.
///
/// When select and store share the same index TermId, `are_equal` returns true
/// via structural equality (`t1 == t2`), but `eq_index` has no entry for that
/// pair because no explicit equality assertion was made. Before #2389, this
/// meant the eq_key lookup in `build_row_same_conflict` would miss, and if the
/// diseq lookup also missed, an empty `Conflict(vec![])` would be returned -
/// telling CDCL there is an unconditional contradiction (unsound).
///
/// This test verifies that even when the index equality is structural (same
/// TermId), the conflict clause is non-empty: the diseq literal for
/// `select_result != store_value` is always present.
#[test]
fn test_row_same_structural_equality_conflict_nonempty() {
    let mut theory = ArrayTheory::new();

    // select(store(a, i, v), i) - same TermId(1) for both store index and select index
    // No explicit equality assertion needed: are_equal(1, 1) = true by t1 == t2
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("i")), // 1
        SmtTerm::Const(Symbol::new("v")), // 2
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(2)]), // 3
        SmtTerm::App(Symbol::new("select"), vec![TermId(3), TermId(1)]), // 4
    ];
    theory.set_terms(terms);

    // Assert select_result(4) != store_value(2). This + structural i==i triggers
    // build_row_same_conflict. The eq_index lookup for (1,1) will miss (no assertion),
    // but the diseq_index lookup for (2,4) should hit.
    let neq_lit = make_lit(0, false);
    let result = theory.assert_literal(neq_lit, &TheoryLiteral::Neq(TermId(4), TermId(2)));

    match result {
        TheoryCheckResult::Conflict(lits) => {
            assert!(
                !lits.is_empty(),
                "#2389: conflict clause must be non-empty (got empty Conflict)"
            );
            // Should contain exactly the diseq literal
            assert!(
                lits.contains(&neq_lit),
                "conflict should contain the disequality literal"
            );
        }
        TheoryCheckResult::Consistent => {
            // The guard in #2389 could cause this if BOTH lookups miss.
            // In this test, the diseq lookup should succeed, so Conflict is expected.
            panic!("Expected Conflict with diseq literal, got Consistent");
        }
        other => panic!("Unexpected result: {other:?}"),
    }
}

/// Regression test for #2389: build_row_diff_conflict guard against empty Conflict.
///
/// Exercises the ROW-diff path: select(store(a, i, v), j) with i != j.
/// Verifies the conflict clause includes both the index disequality and
/// the result disequality literals.
#[test]
fn test_row_diff_conflict_nonempty() {
    let mut theory = ArrayTheory::new();

    // select(store(a, i, v), j) with i != j and select(a, j)
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("i")), // 1
        SmtTerm::Const(Symbol::new("j")), // 2
        SmtTerm::Const(Symbol::new("v")), // 3
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(3)]), // 4: store(a,i,v)
        SmtTerm::App(Symbol::new("select"), vec![TermId(4), TermId(2)]), // 5: select(store(a,i,v), j)
        SmtTerm::App(Symbol::new("select"), vec![TermId(0), TermId(2)]), // 6: select(a, j)
    ];
    theory.set_terms(terms);

    // Assert i != j (triggers ROW-diff)
    let diseq_idx_lit = make_lit(0, false);
    let result = theory.assert_literal(diseq_idx_lit, &TheoryLiteral::Neq(TermId(1), TermId(2)));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Assert select(store(a,i,v), j)(5) != select(a, j)(6) - conflicts with ROW-diff axiom
    let diseq_res_lit = make_lit(1, false);
    let result = theory.assert_literal(diseq_res_lit, &TheoryLiteral::Neq(TermId(5), TermId(6)));

    match result {
        TheoryCheckResult::Conflict(lits) => {
            assert!(!lits.is_empty(), "#2389: conflict clause must be non-empty");
            assert!(
                lits.contains(&diseq_idx_lit),
                "conflict should contain the index disequality literal"
            );
            assert!(
                lits.contains(&diseq_res_lit),
                "conflict should contain the result disequality literal"
            );
        }
        other => panic!("Expected Conflict, got {other:?}"),
    }
}
