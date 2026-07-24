// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dedicated tests for `resolution.rs`: resolve_clauses, ResolutionProof, ResolutionStep.

use super::resolution::*;
use super::*;

// ============================================================
// 1. resolve_clauses — basic resolution
// ============================================================

#[test]
fn test_resolve_clauses_basic_positive_pivot() {
    // (1 v 2) resolve (-1 v 3) on pivot 1 => (2 v 3)
    let r = resolve_clauses(&[1, 2], &[-1, 3], 1).unwrap();
    assert_eq!(r, vec![2, 3]);
}

#[test]
fn test_resolve_clauses_unit_to_empty() {
    // (1) resolve (-1) on pivot 1 => empty clause
    let r = resolve_clauses(&[1], &[-1], 1).unwrap();
    assert!(r.is_empty());
}

#[test]
fn test_resolve_clauses_deduplication() {
    // (1 v 2) resolve (-1 v 2) on 1 => (2) — duplicate 2 removed
    let r = resolve_clauses(&[1, 2], &[-1, 2], 1).unwrap();
    assert_eq!(r, vec![2]);
}

#[test]
fn test_resolve_clauses_tautology_result() {
    // (1 v 2) resolve (-1 v -2) on 1 => (2 v -2) — tautological resolvent is fine
    let r = resolve_clauses(&[1, 2], &[-1, -2], 1).unwrap();
    assert_eq!(r, vec![2, -2]);
}

#[test]
fn test_resolve_clauses_large_clauses() {
    // (1 v 2 v 3 v 4 v 5) resolve (-1 v 6 v 7 v 8) on 1
    let r = resolve_clauses(&[1, 2, 3, 4, 5], &[-1, 6, 7, 8], 1).unwrap();
    assert_eq!(r, vec![2, 3, 4, 5, 6, 7, 8]);
}

#[test]
fn test_resolve_clauses_reversed_polarity() {
    // (-1 v 2) resolve (1 v 3) on pivot 1 — negative in c1, positive in c2
    let r = resolve_clauses(&[-1, 2], &[1, 3], 1).unwrap();
    assert_eq!(r, vec![2, 3]);
}

#[test]
fn test_resolve_clauses_negative_pivot_value() {
    // pivot=-1: should find -1 in one clause and 1 in the other
    // (1 v 2) and (-1 v 3), pivot=-1
    let r = resolve_clauses(&[1, 2], &[-1, 3], -1).unwrap();
    assert_eq!(r, vec![2, 3]);
}

#[test]
fn test_resolve_clauses_missing_pivot_error() {
    // Neither clause contains pivot variable 5
    let r = resolve_clauses(&[1, 2], &[3, 4], 5);
    assert!(r.is_err());
}

#[test]
fn test_resolve_clauses_same_polarity_error() {
    // Both clauses have +1, neither has -1
    let r = resolve_clauses(&[1, 2], &[1, 3], 1);
    assert!(r.is_err());
}

#[test]
fn test_resolve_clauses_both_negative_error() {
    // Both clauses have -1, neither has +1
    let r = resolve_clauses(&[-1, 2], &[-1, 3], 1);
    assert!(r.is_err());
}

#[test]
fn test_resolve_clauses_sort_order() {
    // Resolvent should be sorted by (var, negative-last)
    // (3 v 1) resolve (-3 v 2) on 3 => sorted: [1, 2]
    let r = resolve_clauses(&[3, 1], &[-3, 2], 3).unwrap();
    assert_eq!(r, vec![1, 2]);
}

#[test]
fn test_resolve_clauses_sort_order_mixed_polarity() {
    // (1 v -2 v 3) resolve (-1 v 2 v -3) on 1 => {-2, 3, 2, -3}
    // sorted by (var, neg-last): [2, -2, 3, -3]
    let r = resolve_clauses(&[1, -2, 3], &[-1, 2, -3], 1).unwrap();
    assert_eq!(r, vec![2, -2, 3, -3]);
}

#[test]
fn test_resolve_clauses_multiple_same_var_removed() {
    // If c1 has both +v and -v of the pivot var, all are removed
    // (1 v -1 v 2) resolve (-1 v 3) on 1 — both 1 and -1 in c1 removed
    let r = resolve_clauses(&[1, -1, 2], &[-1, 3], 1).unwrap();
    // c1 minus var 1: [2], c2 minus var 1: [3] => [2, 3]
    assert_eq!(r, vec![2, 3]);
}

#[test]
fn test_resolve_clauses_single_lit_different_vars() {
    // (2) resolve (-2) on 2 => empty
    let r = resolve_clauses(&[2], &[-2], 2).unwrap();
    assert!(r.is_empty());
}

#[test]
fn test_resolve_clauses_high_variable_numbers() {
    // (100 v 200) resolve (-100 v 300) on 100
    let r = resolve_clauses(&[100, 200], &[-100, 300], 100).unwrap();
    assert_eq!(r, vec![200, 300]);
}

#[test]
fn test_resolve_clauses_pivot_only_in_one_clause_error() {
    // c1 has pivot, c2 does not have negation of pivot
    let r = resolve_clauses(&[1, 2], &[3, 4], 1);
    assert!(r.is_err());
}

#[test]
fn test_resolve_clauses_dedup_from_both_sides() {
    // (1 v 2 v 3) resolve (-1 v 2 v 3) on 1 => (2 v 3) — dedup from both
    let r = resolve_clauses(&[1, 2, 3], &[-1, 2, 3], 1).unwrap();
    assert_eq!(r, vec![2, 3]);
}

// ============================================================
// 2. ResolutionProof construction
// ============================================================

#[test]
fn test_proof_new_is_empty() {
    let proof = ResolutionProof::new();
    assert!(proof.is_empty());
    assert_eq!(proof.len(), 0);
}

#[test]
fn test_proof_add_input_sequential_indices() {
    let mut proof = ResolutionProof::new();
    assert_eq!(proof.add_input(vec![1, 2]), 0);
    assert_eq!(proof.add_input(vec![-1, 3]), 1);
    assert_eq!(proof.add_input(vec![4]), 2);
}

#[test]
fn test_proof_clause_at_returns_correct() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1, 2]);
    proof.add_input(vec![-3, 4]);
    assert_eq!(proof.clause_at(0), Some(&vec![1, 2]));
    assert_eq!(proof.clause_at(1), Some(&vec![-3, 4]));
}

#[test]
fn test_proof_clause_at_out_of_bounds() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]);
    assert_eq!(proof.clause_at(1), None);
    assert_eq!(proof.clause_at(100), None);
}

#[test]
fn test_proof_clause_at_empty_proof() {
    let proof = ResolutionProof::new();
    assert_eq!(proof.clause_at(0), None);
}

#[test]
fn test_proof_len_tracks_all_steps() {
    let mut proof = ResolutionProof::new();
    assert_eq!(proof.len(), 0);
    proof.add_input(vec![1]);
    assert_eq!(proof.len(), 1);
    proof.add_input(vec![-1]);
    assert_eq!(proof.len(), 2);
    proof.add_resolve(0, 1, 1).unwrap();
    assert_eq!(proof.len(), 3);
}

#[test]
fn test_proof_is_empty_false_after_input() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]);
    assert!(!proof.is_empty());
}

#[test]
fn test_proof_default_equals_new() {
    let a = ResolutionProof::new();
    let b = ResolutionProof::default();
    assert_eq!(a.len(), b.len());
    assert!(a.is_empty());
    assert!(b.is_empty());
}

#[test]
fn test_proof_add_input_empty_clause() {
    let mut proof = ResolutionProof::new();
    let idx = proof.add_input(vec![]);
    assert_eq!(proof.clause_at(idx), Some(&vec![]));
}

#[test]
fn test_proof_multiple_inputs_len() {
    let mut proof = ResolutionProof::new();
    for i in 1..=10 {
        proof.add_input(vec![i]);
    }
    assert_eq!(proof.len(), 10);
}

// ============================================================
// 3. ResolutionProof::add_resolve
// ============================================================

#[test]
fn test_add_resolve_valid_returns_ok() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1, 2]);
    proof.add_input(vec![-1, 3]);
    let result = proof.add_resolve(0, 1, 1);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 2);
}

#[test]
fn test_add_resolve_invalid_left_index() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]);
    assert!(proof.add_resolve(5, 0, 1).is_err());
}

#[test]
fn test_add_resolve_invalid_right_index() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]);
    assert!(proof.add_resolve(0, 5, 1).is_err());
}

#[test]
fn test_add_resolve_both_invalid_indices() {
    let mut proof = ResolutionProof::new();
    assert!(proof.add_resolve(0, 1, 1).is_err());
}

#[test]
fn test_add_resolve_stores_correct_resolvent() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1, 2]);
    proof.add_input(vec![-1, 3]);
    let idx = proof.add_resolve(0, 1, 1).unwrap();
    assert_eq!(proof.clause_at(idx), Some(&vec![2, 3]));
}

#[test]
fn test_add_resolve_chain() {
    // Chain: (1 v 2), (-1 v 3), (-3 v 4)
    // Step 1: resolve 0,1 on 1 => (2 v 3)
    // Step 2: resolve 2,2 on 3 => (2 v 4)
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1, 2]); // idx 0
    proof.add_input(vec![-1, 3]); // idx 1
    proof.add_input(vec![-3, 4]); // idx 2
    let r1 = proof.add_resolve(0, 1, 1).unwrap(); // idx 3: (2, 3)
    assert_eq!(proof.clause_at(r1), Some(&vec![2, 3]));
    let r2 = proof.add_resolve(r1, 2, 3).unwrap(); // idx 4: (2, 4)
    assert_eq!(proof.clause_at(r2), Some(&vec![2, 4]));
}

#[test]
fn test_add_resolve_with_derived_clauses() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]); // idx 0
    proof.add_input(vec![-1, 2]); // idx 1
    proof.add_input(vec![-2]); // idx 2
    let r1 = proof.add_resolve(0, 1, 1).unwrap(); // idx 3: (2)
    let r2 = proof.add_resolve(r1, 2, 2).unwrap(); // idx 4: ()
    assert_eq!(proof.clause_at(r2), Some(&vec![]));
}

#[test]
fn test_add_resolve_pivot_mismatch_error() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1, 2]);
    proof.add_input(vec![3, 4]);
    assert!(proof.add_resolve(0, 1, 1).is_err());
}

#[test]
fn test_add_resolve_index_at_boundary() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]);
    proof.add_input(vec![-1]);
    // len is 2, so index 2 is out of bounds
    assert!(proof.add_resolve(0, 2, 1).is_err());
    // but index 1 is valid
    assert!(proof.add_resolve(0, 1, 1).is_ok());
}

// ============================================================
// 4. ResolutionProof::verify
// ============================================================

#[test]
fn test_verify_simple_refutation() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]);
    proof.add_input(vec![-1]);
    proof.add_resolve(0, 1, 1).unwrap();
    assert!(proof.verify());
}

#[test]
fn test_verify_two_step_refutation() {
    // (1 v 2), (-1 v 2), (-2)
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1, 2]); // 0
    proof.add_input(vec![-1, 2]); // 1
    proof.add_input(vec![-2]); // 2
    let r1 = proof.add_resolve(0, 1, 1).unwrap(); // 3: (2)
    proof.add_resolve(r1, 2, 2).unwrap(); // 4: ()
    assert!(proof.verify());
}

#[test]
fn test_verify_non_refutation_single_clause() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1, 2]);
    assert!(!proof.verify());
}

#[test]
fn test_verify_empty_proof() {
    let proof = ResolutionProof::new();
    assert!(!proof.verify());
}

#[test]
fn test_verify_non_empty_final_clause() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1, 2]);
    proof.add_input(vec![-1, 3]);
    proof.add_resolve(0, 1, 1).unwrap(); // (2, 3) — not empty
    assert!(!proof.verify());
}

#[test]
fn test_verify_three_variable_chain() {
    // (1), (-1 v 2), (-2 v 3), (-3)
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]); // 0
    proof.add_input(vec![-1, 2]); // 1
    proof.add_input(vec![-2, 3]); // 2
    proof.add_input(vec![-3]); // 3
    let r1 = proof.add_resolve(0, 1, 1).unwrap(); // 4: (2)
    let r2 = proof.add_resolve(r1, 2, 2).unwrap(); // 5: (3)
    proof.add_resolve(r2, 3, 3).unwrap(); // 6: ()
    assert!(proof.verify());
}

#[test]
fn test_verify_five_clause_refutation() {
    // (1 v 2), (-1 v 3), (-2 v 3), (-3 v 4), (-4)
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1, 2]); // 0
    proof.add_input(vec![-1, 3]); // 1
    proof.add_input(vec![-2, 3]); // 2
    proof.add_input(vec![-3, 4]); // 3
    proof.add_input(vec![-4]); // 4
    let r1 = proof.add_resolve(0, 1, 1).unwrap(); // 5: (2, 3)
    let r2 = proof.add_resolve(r1, 2, 2).unwrap(); // 6: (3)
    let r3 = proof.add_resolve(r2, 3, 3).unwrap(); // 7: (4)
    proof.add_resolve(r3, 4, 4).unwrap(); // 8: ()
    assert!(proof.verify());
}

#[test]
fn test_verify_input_empty_clause_immediate() {
    // An input empty clause means the proof already has contradiction
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![]);
    assert!(proof.verify());
}

#[test]
fn test_verify_after_non_empty_then_empty() {
    // Only the LAST clause matters for verify()
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1, 2]); // 0: non-empty
    proof.add_input(vec![1]); // 1: non-empty
    proof.add_input(vec![-1]); // 2: non-empty
    proof.add_resolve(1, 2, 1).unwrap(); // 3: empty
    assert!(proof.verify());
}

#[test]
fn test_verify_false_when_last_step_not_empty() {
    // Build a valid resolution but add another input after
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]);
    proof.add_input(vec![-1]);
    proof.add_resolve(0, 1, 1).unwrap(); // empty
                                         // Now add another input — last clause is no longer empty
    proof.add_input(vec![5, 6]);
    assert!(!proof.verify());
}

#[test]
fn test_verify_diamond_refutation() {
    // (1 v 2), (-1 v 2), (1 v -2), (-1 v -2)
    // Resolve 0,1 on 1 => (2), resolve 2,3 on 1 => (-2), then resolve on 2
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1, 2]); // 0
    proof.add_input(vec![-1, 2]); // 1
    proof.add_input(vec![1, -2]); // 2
    proof.add_input(vec![-1, -2]); // 3
    let r1 = proof.add_resolve(0, 1, 1).unwrap(); // 4: (2)
    let r2 = proof.add_resolve(2, 3, 1).unwrap(); // 5: (-2)
    proof.add_resolve(r1, r2, 2).unwrap(); // 6: ()
    assert!(proof.verify());
}

// ============================================================
// 5. ResolutionStep trait derives
// ============================================================

#[test]
fn test_step_debug_input() {
    let step = ResolutionStep::Input(vec![1, 2, 3]);
    let dbg = format!("{:?}", step);
    assert!(dbg.contains("Input"));
}

#[test]
fn test_step_debug_resolve() {
    let step = ResolutionStep::Resolve {
        left: 0,
        right: 1,
        pivot: 3,
    };
    let dbg = format!("{:?}", step);
    assert!(dbg.contains("Resolve"));
    assert!(dbg.contains("pivot"));
}

#[test]
fn test_step_clone() {
    let step = ResolutionStep::Input(vec![1, -2]);
    let cloned = step.clone();
    assert_eq!(step, cloned);
}

#[test]
fn test_step_eq_input_variants() {
    let a = ResolutionStep::Input(vec![1, 2]);
    let b = ResolutionStep::Input(vec![1, 2]);
    let c = ResolutionStep::Input(vec![1, 3]);
    assert_eq!(a, b);
    assert_ne!(a, c);
}

#[test]
fn test_step_eq_resolve_variants() {
    let a = ResolutionStep::Resolve {
        left: 0,
        right: 1,
        pivot: 2,
    };
    let b = ResolutionStep::Resolve {
        left: 0,
        right: 1,
        pivot: 2,
    };
    let c = ResolutionStep::Resolve {
        left: 0,
        right: 1,
        pivot: 3,
    };
    assert_eq!(a, b);
    assert_ne!(a, c);
}

#[test]
fn test_step_ne_different_variants() {
    let input = ResolutionStep::Input(vec![1]);
    let resolve = ResolutionStep::Resolve {
        left: 0,
        right: 1,
        pivot: 1,
    };
    assert_ne!(input, resolve);
}

// ============================================================
// 6. Edge cases
// ============================================================

#[test]
fn test_resolve_clauses_empty_first_clause() {
    // Empty c1 cannot contain the pivot
    let r = resolve_clauses(&[], &[-1, 2], 1);
    assert!(r.is_err());
}

#[test]
fn test_resolve_clauses_empty_both_clauses() {
    let r = resolve_clauses(&[], &[], 1);
    assert!(r.is_err());
}

#[test]
fn test_resolve_clauses_pivot_zero_error() {
    // var_of(0) would be 0, and literal 0 is unusual in DIMACS
    // Neither clause can contain literal 0 meaningfully
    let r = resolve_clauses(&[1, 2], &[-1, 3], 0);
    assert!(r.is_err());
}

#[test]
fn test_proof_long_chain() {
    // Build chain: (1), (-1 v 2), (-2 v 3), ..., (-9 v 10), (-10)
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]); // 0
    for i in 1..=9 {
        proof.add_input(vec![-(i as i32), (i + 1) as i32]);
    }
    proof.add_input(vec![-10]); // 10
                                // Chain resolve: step 0 with step 1 on var 1, then result with step 2 on var 2, etc.
    let mut prev = 0;
    for i in 1..=10 {
        prev = proof.add_resolve(prev, i, i as i32).unwrap();
    }
    assert!(proof.verify());
    assert_eq!(proof.len(), 21); // 11 inputs + 10 resolves
}

#[test]
fn test_resolve_clauses_preserves_non_pivot_literals() {
    // (1 v 2 v 3 v 4) resolve (-1 v 5 v 6 v 7) on 1
    // All non-pivot literals preserved
    let r = resolve_clauses(&[1, 2, 3, 4], &[-1, 5, 6, 7], 1).unwrap();
    assert_eq!(r, vec![2, 3, 4, 5, 6, 7]);
}

#[test]
fn test_proof_clone_independence() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]);
    proof.add_input(vec![-1]);
    let mut cloned = proof.clone();
    cloned.add_resolve(0, 1, 1).unwrap();
    // Original is unaffected
    assert_eq!(proof.len(), 2);
    assert_eq!(cloned.len(), 3);
    assert!(cloned.verify());
    assert!(!proof.verify());
}
