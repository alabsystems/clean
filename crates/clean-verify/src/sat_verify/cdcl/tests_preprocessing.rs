// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for CNF preprocessing verification.

use super::preprocessing::*;
use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// subsumption_elimination
// ---------------------------------------------------------------------------

#[test]
fn test_subsumption_elimination_proper_subset_removes_superset() {
    // {1, 2} subsumes {1, 2, 3}
    let clauses = vec![vec![1, 2], vec![1, 2, 3]];
    let result = subsumption_elimination(&clauses);
    assert_eq!(result, vec![vec![1, 2]]);
}

#[test]
fn test_subsumption_elimination_identical_clauses_deduplicates() {
    let clauses = vec![vec![1, 2], vec![1, 2]];
    let result = subsumption_elimination(&clauses);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0], vec![1, 2]);
}

#[test]
fn test_subsumption_elimination_no_subsumption() {
    let clauses = vec![vec![1, 2], vec![3, 4]];
    let result = subsumption_elimination(&clauses);
    assert_eq!(result.len(), 2);
}

#[test]
fn test_subsumption_elimination_empty_clause_subsumes_all() {
    // The empty clause (always false) is a subset of every clause.
    let clauses = vec![vec![], vec![1, 2, 3]];
    let result = subsumption_elimination(&clauses);
    assert_eq!(result, vec![Vec::<i32>::new()]);
}

#[test]
fn test_subsumption_elimination_empty_input() {
    let clauses: Vec<Vec<i32>> = vec![];
    let result = subsumption_elimination(&clauses);
    assert!(result.is_empty());
}

#[test]
fn test_subsumption_elimination_single_literal_subsumes() {
    // {1} subsumes {1, 2} and {1, 3} but not {2, 3}
    let clauses = vec![vec![1], vec![1, 2], vec![1, 3], vec![2, 3]];
    let result = subsumption_elimination(&clauses);
    assert_eq!(result.len(), 2);
    assert!(result.contains(&vec![1]));
    assert!(result.contains(&vec![2, 3]));
}

#[test]
fn test_subsumption_elimination_chain() {
    // {1} subsumes {1, 2} which subsumes {1, 2, 3}
    let clauses = vec![vec![1, 2, 3], vec![1, 2], vec![1]];
    let result = subsumption_elimination(&clauses);
    assert_eq!(result, vec![vec![1]]);
}

// ---------------------------------------------------------------------------
// pure_literal_elimination
// ---------------------------------------------------------------------------

#[test]
fn test_pure_literal_elimination_all_pure() {
    // x1 appears only positive, x2 appears only negative
    let clauses = vec![vec![1, -2], vec![1], vec![-2]];
    let (reduced, pures) = pure_literal_elimination(&clauses, 2);
    // Both are pure, so all clauses are removed.
    assert!(reduced.is_empty());
    assert!(pures.contains(&1));
    assert!(pures.contains(&-2));
}

#[test]
fn test_pure_literal_elimination_none_pure() {
    // Both x1 and x2 appear in both polarities
    let clauses = vec![vec![1, 2], vec![-1, -2]];
    let (reduced, pures) = pure_literal_elimination(&clauses, 2);
    assert!(pures.is_empty());
    assert_eq!(reduced.len(), 2);
}

#[test]
fn test_pure_literal_elimination_mixed() {
    // x1 is pure (positive only), x2 appears both ways
    let clauses = vec![vec![1, 2], vec![1, -2], vec![2, -2]];
    let (reduced, pures) = pure_literal_elimination(&clauses, 2);
    assert_eq!(pures, vec![1]);
    // Clauses containing literal 1 are removed: first two clauses gone.
    assert_eq!(reduced.len(), 1);
    assert_eq!(reduced[0], vec![2, -2]);
}

#[test]
fn test_pure_literal_elimination_empty_input() {
    let clauses: Vec<Vec<i32>> = vec![];
    let (reduced, pures) = pure_literal_elimination(&clauses, 3);
    assert!(reduced.is_empty());
    assert!(pures.is_empty());
}

#[test]
fn test_pure_literal_elimination_preserves_equisat() {
    // (1 v 2) ^ (-1 v 3) ^ (3) -- var 2 is pure positive
    let original = vec![vec![1, 2], vec![-1, 3], vec![3]];
    let (reduced, _) = pure_literal_elimination(&original, 3);
    assert!(verify_preprocessing_equisat(&original, &reduced, 3));
}

// ---------------------------------------------------------------------------
// failed_literal_probe
// ---------------------------------------------------------------------------

#[test]
fn test_failed_literal_probe_finds_conflict() {
    // Clauses: (-1 v 2), (-1 v -2). Assuming 1 forces 2 then conflict with clause 2.
    let clauses = vec![vec![-1, 2], vec![-1, -2]];
    let result = failed_literal_probe(&clauses, 1);
    assert_eq!(result, Some(-1));
}

#[test]
fn test_failed_literal_probe_no_conflict() {
    // Clauses: (1 v 2), (-1 v 2). Assuming 1 satisfies clause 1, forces 2, no conflict.
    let clauses = vec![vec![1, 2], vec![-1, 2]];
    let result = failed_literal_probe(&clauses, 1);
    assert_eq!(result, None);
}

#[test]
fn test_failed_literal_probe_unit_propagation_chain() {
    // (-1 v 2), (-2 v 3), (-3 v -3): assuming 1 -> 2 -> 3 -> conflict in (-3 v -3)
    // Actually (-3 v -3) is just {-3}; forcing 3 conflicts.
    let clauses = vec![vec![-1, 2], vec![-2, 3], vec![-3]];
    let result = failed_literal_probe(&clauses, 1);
    assert_eq!(result, Some(-1));
}

#[test]
fn test_failed_literal_probe_empty_clauses() {
    let clauses: Vec<Vec<i32>> = vec![];
    let result = failed_literal_probe(&clauses, 1);
    assert_eq!(result, None);
}

// ---------------------------------------------------------------------------
// self_subsumption_elimination
// ---------------------------------------------------------------------------

#[test]
fn test_self_subsumption_basic() {
    // C = {a, b, p} = {1, 2, 3}, D = {a, ~p} = {1, -3}
    // Resolvent on pivot 3: {1, 2}. This is subset of C \ {3} = {1, 2}.
    // So C is strengthened to {1, 2}.
    let clauses = vec![vec![1, 2, 3], vec![1, -3]];
    let result = self_subsumption_elimination(&clauses);
    assert!(result.contains(&vec![1, 2]));
    assert!(result.contains(&vec![1, -3]));
}

#[test]
fn test_self_subsumption_no_strengthening() {
    // No self-subsumption possible
    let clauses = vec![vec![1, 2], vec![3, 4]];
    let result = self_subsumption_elimination(&clauses);
    assert_eq!(result.len(), 2);
}

#[test]
fn test_self_subsumption_preserves_equisat() {
    let original = vec![vec![1, 2, 3], vec![1, -3]];
    let preprocessed = self_subsumption_elimination(&original);
    assert!(verify_preprocessing_equisat(&original, &preprocessed, 3));
}

// ---------------------------------------------------------------------------
// verify_preprocessing_equisat
// ---------------------------------------------------------------------------

#[test]
fn test_equisat_both_sat() {
    let orig = vec![vec![1, 2]];
    let prep = vec![vec![1]];
    // Both are satisfiable
    assert!(verify_preprocessing_equisat(&orig, &prep, 2));
}

#[test]
fn test_equisat_both_unsat() {
    let orig = vec![vec![1], vec![-1]];
    let prep = vec![vec![2], vec![-2]];
    // Both are unsatisfiable
    assert!(verify_preprocessing_equisat(&orig, &prep, 2));
}

#[test]
fn test_equisat_mismatch_detected() {
    let orig = vec![vec![1]]; // SAT
    let prep = vec![vec![1], vec![-1]]; // UNSAT
    assert!(!verify_preprocessing_equisat(&orig, &prep, 1));
}

#[test]
fn test_equisat_empty_both() {
    let orig: Vec<Vec<i32>> = vec![];
    let prep: Vec<Vec<i32>> = vec![];
    assert!(verify_preprocessing_equisat(&orig, &prep, 0));
}

#[test]
fn test_equisat_empty_clause_is_unsat() {
    // A formula containing the empty clause is UNSAT.
    let orig = vec![vec![]];
    let prep = vec![vec![1], vec![-1]];
    assert!(verify_preprocessing_equisat(&orig, &prep, 1));
}

// ---------------------------------------------------------------------------
// count_literals
// ---------------------------------------------------------------------------

#[test]
fn test_count_literals_basic() {
    let clauses = vec![vec![1, 2, 3], vec![4, 5]];
    assert_eq!(count_literals(&clauses), 5);
}

#[test]
fn test_count_literals_empty() {
    let clauses: Vec<Vec<i32>> = vec![];
    assert_eq!(count_literals(&clauses), 0);
}

#[test]
fn test_count_literals_with_empty_clause() {
    let clauses = vec![vec![], vec![1]];
    assert_eq!(count_literals(&clauses), 1);
}

// ---------------------------------------------------------------------------
// preprocessing_stats
// ---------------------------------------------------------------------------

#[test]
fn test_preprocessing_stats_basic() {
    let original = vec![vec![1, 2, 3], vec![1, 2], vec![4, 5]];
    let preprocessed = vec![vec![1, 2], vec![4, 5]];
    let stats = preprocessing_stats(&original, &preprocessed);
    assert_eq!(stats.original_clauses, 3);
    assert_eq!(stats.preprocessed_clauses, 2);
    assert_eq!(stats.original_literals, 7);
    assert_eq!(stats.preprocessed_literals, 4);
    assert_eq!(stats.clauses_removed, 1);
    assert_eq!(stats.literals_removed, 3);
}

#[test]
fn test_preprocessing_stats_no_reduction() {
    let clauses = vec![vec![1, 2]];
    let stats = preprocessing_stats(&clauses, &clauses);
    assert_eq!(stats.clauses_removed, 0);
    assert_eq!(stats.literals_removed, 0);
}

#[test]
fn test_preprocessing_stats_full_reduction() {
    let original = vec![vec![1, 2], vec![3]];
    let preprocessed: Vec<Vec<i32>> = vec![];
    let stats = preprocessing_stats(&original, &preprocessed);
    assert_eq!(stats.clauses_removed, 2);
    assert_eq!(stats.literals_removed, 3);
}

// ---------------------------------------------------------------------------
// proof status constants
// ---------------------------------------------------------------------------

#[test]
fn test_proof_status_constants() {
    assert_eq!(S11_SUBSUMPTION_PRESERVES_SAT, ProofStatus::DerivedPending);
    assert_eq!(S12_PURE_LITERAL_PRESERVES_SAT, ProofStatus::DerivedPending);
}

// ---------------------------------------------------------------------------
// integration: subsumption + equisat check
// ---------------------------------------------------------------------------

#[test]
fn test_subsumption_preserves_equisat() {
    let original = vec![vec![1, 2], vec![1, 2, 3], vec![-1, -2]];
    let preprocessed = subsumption_elimination(&original);
    assert!(verify_preprocessing_equisat(&original, &preprocessed, 3));
}

#[test]
fn test_pure_literal_then_subsumption() {
    // x3 is pure positive
    let original = vec![vec![1, 3], vec![-1, 2], vec![-2, 3]];
    let (after_pure, _) = pure_literal_elimination(&original, 3);
    let after_sub = subsumption_elimination(&after_pure);
    assert!(verify_preprocessing_equisat(&original, &after_sub, 3));
}

#[test]
fn test_full_pipeline_small_unsat() {
    // UNSAT instance: (1) ^ (-1)
    let original = vec![vec![1], vec![-1]];
    let preprocessed = subsumption_elimination(&original);
    let (reduced, _) = pure_literal_elimination(&preprocessed, 1);
    // Still UNSAT
    assert!(verify_preprocessing_equisat(&original, &reduced, 1));
}
