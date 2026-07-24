// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_array_theory_basic() {
    let mut theory = ArrayTheory::new();

    // Create terms: a, i, v
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")), // 0: array a
        SmtTerm::Const(Symbol::new("i")), // 1: index i
        SmtTerm::Const(Symbol::new("v")), // 2: value v
    ];
    theory.set_terms(terms);

    let stats = theory.stats();
    assert_eq!(stats.num_selects, 0);
    assert_eq!(stats.num_stores, 0);
}

#[test]
fn test_array_select_store_analysis() {
    let mut theory = ArrayTheory::new();

    // Terms: a, i, v, store(a, i, v), select(store(a, i, v), i)
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("i")), // 1
        SmtTerm::Const(Symbol::new("v")), // 2
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(2)]), // 3: store(a, i, v)
        SmtTerm::App(Symbol::new("select"), vec![TermId(3), TermId(1)]), // 4: select(store(a, i, v), i)
    ];
    theory.set_terms(terms);

    let stats = theory.stats();
    assert_eq!(stats.num_stores, 1, "Should detect 1 store operation");
    assert_eq!(stats.num_selects, 1, "Should detect 1 select operation");
}

#[test]
fn test_row_same_index_consistency() {
    let mut theory = ArrayTheory::new();

    // Terms for: select(store(a, i, v), i) should equal v
    // 0: a, 1: i, 2: v, 3: store(a,i,v), 4: select(store(a,i,v), i)
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("i")), // 1
        SmtTerm::Const(Symbol::new("v")), // 2
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(2)]), // 3
        SmtTerm::App(Symbol::new("select"), vec![TermId(3), TermId(1)]), // 4
    ];
    theory.set_terms(terms);

    // Assert i = i (reflexive, already true) - the select uses the same index as store
    // The theory should recognize that select result (4) should equal v (2)

    // Check that no conflict occurs initially
    let result = theory.check();
    assert!(matches!(result, TheoryCheckResult::Consistent));
}

#[test]
fn test_row_same_index_conflict() {
    let mut theory = ArrayTheory::new();

    // select(store(a, i, v), i) != v should cause conflict
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("i")), // 1
        SmtTerm::Const(Symbol::new("v")), // 2
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(2)]), // 3
        SmtTerm::App(Symbol::new("select"), vec![TermId(3), TermId(1)]), // 4
    ];
    theory.set_terms(terms);

    let i = TermId(1);
    let v = TermId(2);
    let select_result = TermId(4);

    // Assert that the indices are equal (they're the same term, so trivially true)
    // In this case, we need to assert i = i explicitly for the theory to track it
    let eq_lit = make_lit(0, true);
    let result = theory.assert_literal(eq_lit, &TheoryLiteral::Eq(i, i));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // Now assert select(store(a,i,v), i) != v - this should conflict
    let neq_lit = make_lit(1, false);
    let result = theory.assert_literal(neq_lit, &TheoryLiteral::Neq(select_result, v));

    // The ROW-same axiom says select(store(a,i,v), i) = v
    // So asserting they're not equal should cause a conflict
    assert!(
        matches!(result, TheoryCheckResult::Conflict(_)),
        "ROW-same axiom violation should cause conflict"
    );
}

#[test]
fn test_row_diff_index() {
    let mut theory = ArrayTheory::new();

    // Test: select(store(a, i, v), j) = select(a, j) when i != j
    let terms = vec![
        SmtTerm::Const(Symbol::new("a")), // 0: array a
        SmtTerm::Const(Symbol::new("i")), // 1: index i
        SmtTerm::Const(Symbol::new("j")), // 2: index j
        SmtTerm::Const(Symbol::new("v")), // 3: value v
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(3)]), // 4: store(a, i, v)
        SmtTerm::App(Symbol::new("select"), vec![TermId(4), TermId(2)]), // 5: select(store(a,i,v), j)
        SmtTerm::App(Symbol::new("select"), vec![TermId(0), TermId(2)]), // 6: select(a, j)
    ];
    theory.set_terms(terms);

    let i = TermId(1);
    let j = TermId(2);
    let select_store = TermId(5);
    let select_base = TermId(6);

    // Assert i != j
    let diseq_lit = make_lit(0, false);
    let result = theory.assert_literal(diseq_lit, &TheoryLiteral::Neq(i, j));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    // At this point, ROW-diff axiom should imply select_store = select_base
    // Check that asserting select_store != select_base causes conflict
    let neq_lit = make_lit(1, false);
    let result = theory.assert_literal(neq_lit, &TheoryLiteral::Neq(select_store, select_base));

    assert!(
        matches!(result, TheoryCheckResult::Conflict(_)),
        "ROW-diff axiom violation should cause conflict"
    );
}

#[test]
fn test_backtrack() {
    let mut theory = ArrayTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ];
    theory.set_terms(terms);

    let a = TermId(0);
    let b = TermId(1);

    // Level 0: assert a = b
    let eq_lit = make_lit(0, true);
    let result = theory.assert_literal(eq_lit, &TheoryLiteral::Eq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert_eq!(theory.equalities.len(), 1);

    // Push to level 1
    theory.push();

    // Level 1: assert a != b (would conflict but we're testing backtrack)
    let neq_lit = make_lit(1, false);
    // Note: This doesn't actually conflict because are_equal uses simple lookup
    let result = theory.assert_literal(neq_lit, &TheoryLiteral::Neq(a, b));
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert_eq!(theory.disequalities.len(), 1);

    // Backtrack to level 0
    theory.backtrack(0);

    // Disequality should be removed
    assert_eq!(theory.disequalities.len(), 0);
    // Equality should remain
    assert_eq!(theory.equalities.len(), 1);
}

#[test]
fn test_multiple_stores() {
    let mut theory = ArrayTheory::new();

    // a1 = store(a0, i, v1)
    // a2 = store(a1, j, v2)
    // select(a2, i) when i != j should equal v1 (from first store)
    let terms = vec![
        SmtTerm::Const(Symbol::new("a0")), // 0
        SmtTerm::Const(Symbol::new("i")),  // 1
        SmtTerm::Const(Symbol::new("j")),  // 2
        SmtTerm::Const(Symbol::new("v1")), // 3
        SmtTerm::Const(Symbol::new("v2")), // 4
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(3)]), // 5: store(a0, i, v1)
        SmtTerm::App(Symbol::new("store"), vec![TermId(5), TermId(2), TermId(4)]), // 6: store(a1, j, v2)
        SmtTerm::App(Symbol::new("select"), vec![TermId(6), TermId(1)]), // 7: select(a2, i)
        SmtTerm::App(Symbol::new("select"), vec![TermId(5), TermId(1)]), // 8: select(a1, i)
    ];
    theory.set_terms(terms);

    let stats = theory.stats();
    assert_eq!(stats.num_stores, 2);
    assert_eq!(stats.num_selects, 2);
}

#[test]
fn test_stats() {
    let mut theory = ArrayTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("i")),
        SmtTerm::Const(Symbol::new("v")),
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(2)]),
        SmtTerm::App(Symbol::new("select"), vec![TermId(3), TermId(1)]),
    ];
    theory.set_terms(terms);

    let stats = theory.stats();
    assert_eq!(stats.num_stores, 1);
    assert_eq!(stats.num_selects, 1);
    assert_eq!(stats.num_equalities, 0);
    assert_eq!(stats.num_disequalities, 0);
}

#[test]
fn test_smt_integration() {
    use crate::smt::{SmtResult, SmtSolver};

    let mut smt = SmtSolver::new();

    // Add array theory
    smt.add_theory(Box::new(ArrayTheory::new()));

    // Create array terms: a, i, v, store(a, i, v)
    let a = smt.const_term("a");
    let i = smt.const_term("i");
    let v = smt.const_term("v");
    let store_aiv = smt.app_term("store", vec![a, i, v]);
    let _select = smt.app_term("select", vec![store_aiv, i]);

    // This should be satisfiable - just declaring the terms
    match smt.solve() {
        SmtResult::Sat(_) => {}
        other => panic!("Expected SAT, got {other:?}"),
    }
}

#[test]
fn test_smt_with_equality_integration() {
    use crate::smt::{SmtResult, SmtSolver};
    use crate::theories::equality::EqualityTheory;

    let mut smt = SmtSolver::new();

    // Add both equality and array theories
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArrayTheory::new()));

    // Create terms
    let a = smt.const_term("a");
    let i = smt.const_term("i");
    let j = smt.const_term("j");
    let v = smt.const_term("v");

    // store(a, i, v)
    let store_aiv = smt.app_term("store", vec![a, i, v]);

    // select(store(a, i, v), j)
    let _select_j = smt.app_term("select", vec![store_aiv, j]);

    // select(a, j)
    let _select_base = smt.app_term("select", vec![a, j]);

    // Assert i != j (different indices)
    let _ = smt.assert_neq(i, j);

    // With i != j, the array theory should allow consistency
    // (ROW-diff axiom would be applicable but not violated)
    match smt.solve() {
        SmtResult::Sat(_) => {}
        other => panic!("Expected SAT, got {other:?}"),
    }
}
