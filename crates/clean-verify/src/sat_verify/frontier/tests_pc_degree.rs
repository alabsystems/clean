// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Polynomial Calculus degree bounds (pc_degree module).

use super::pc_degree::*;
use super::polynomial_calculus::{clause_to_polynomial, GF2Polynomial};

// ---------------------------------------------------------------------------
// resolution_to_pc: basic translation
// ---------------------------------------------------------------------------

#[test]
fn test_resolution_to_pc_single_clause_no_steps() {
    let clauses = vec![vec![1]];
    let derivation = resolution_to_pc(&clauses, &[]);
    assert_eq!(derivation.len(), 1);
    assert_eq!(derivation[0], clause_to_polynomial(&[1]));
}

#[test]
fn test_resolution_to_pc_two_clauses_no_steps() {
    let clauses = vec![vec![1, 2], vec![-1, 3]];
    let derivation = resolution_to_pc(&clauses, &[]);
    assert_eq!(derivation.len(), 2);
    assert_eq!(derivation[0], clause_to_polynomial(&[1, 2]));
    assert_eq!(derivation[1], clause_to_polynomial(&[-1, 3]));
}

#[test]
fn test_resolution_to_pc_empty_clauses_no_steps() {
    let clauses: Vec<Vec<i32>> = vec![];
    let derivation = resolution_to_pc(&clauses, &[]);
    assert!(derivation.is_empty());
}

#[test]
fn test_resolution_to_pc_unit_contradiction() {
    // {x1} and {-x1} resolved on variable 1 produce empty clause.
    let clauses = vec![vec![1], vec![-1]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    assert_eq!(derivation.len(), 3);
    assert!(
        derivation[2].is_one(),
        "empty resolvent should be GF2 constant 1"
    );
}

#[test]
fn test_resolution_to_pc_invalid_index_produces_zero() {
    let clauses = vec![vec![1]];
    let derivation = resolution_to_pc(&clauses, &[(0, 5, 1)]);
    assert_eq!(derivation.len(), 2);
    assert!(
        derivation[1].is_zero(),
        "invalid index should produce zero sentinel"
    );
}

#[test]
fn test_resolution_to_pc_invalid_pivot_produces_zero() {
    // Both clauses have positive literal 1; pivot 1 is not complementary.
    let clauses = vec![vec![1], vec![1]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    assert_eq!(derivation.len(), 3);
    assert!(
        derivation[2].is_zero(),
        "non-complementary pivot should produce zero"
    );
}

#[test]
fn test_resolution_to_pc_pivot_absent_produces_zero() {
    // Pivot variable 3 does not appear in either clause.
    let clauses = vec![vec![1], vec![-1]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 3)]);
    assert_eq!(derivation.len(), 3);
    assert!(derivation[2].is_zero());
}

#[test]
fn test_resolution_to_pc_three_clauses_one_step() {
    // Resolve clause 0 and clause 1 on variable 1.
    let clauses = vec![vec![1, 2], vec![-1, 3], vec![4]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    assert_eq!(derivation.len(), 4);
    // Resolvent is [2, 3].
    assert_eq!(derivation[3], clause_to_polynomial(&[2, 3]));
}

#[test]
fn test_resolution_to_pc_multi_step_proof() {
    // c0=[1,2], c1=[-1,3], c2=[-2,-3]
    // Step 0: resolve c0,c1 on 1 -> [2,3] (index 3)
    // Step 1: resolve 3,c2 on 2 -> [3,-3]... but let's do on 3:
    // resolve [2,3] with [-2,-3] on 2 -> [3,-3]
    let clauses = vec![vec![1, 2], vec![-1, 3], vec![-2, -3]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1), (3, 2, 2)]);
    assert_eq!(derivation.len(), 5);
    // First derived: [2,3], second derived: [3,-3]
    assert_eq!(derivation[3], clause_to_polynomial(&[2, 3]));
    assert_eq!(derivation[4], clause_to_polynomial(&[-3, 3]));
}

#[test]
fn test_resolution_to_pc_pivot_sign_ignored() {
    // Pivot -1 should work the same as pivot 1 (abs value used).
    let clauses = vec![vec![1], vec![-1]];
    let d1 = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    let d2 = resolution_to_pc(&clauses, &[(0, 1, -1)]);
    assert_eq!(d1.len(), d2.len());
    assert_eq!(d1[2], d2[2]);
}

#[test]
fn test_resolution_to_pc_derived_index_used_in_later_step() {
    // c0=[1], c1=[-1,2], c2=[-2]
    // Step 0: resolve c0,c1 on 1 -> [2] (index 3)
    // Step 1: resolve 3,c2 on 2 -> empty (index 4)
    let clauses = vec![vec![1], vec![-1, 2], vec![-2]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1), (3, 2, 2)]);
    assert_eq!(derivation.len(), 5);
    assert_eq!(derivation[3], clause_to_polynomial(&[2]));
    assert!(derivation[4].is_one(), "empty resolvent is contradiction");
}

#[test]
fn test_resolution_to_pc_non_empty_resolvent_polynomial() {
    // [1,2] resolved with [-1,3] on 1 yields [2,3].
    let clauses = vec![vec![1, 2], vec![-1, 3]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    let expected = clause_to_polynomial(&[2, 3]);
    assert_eq!(derivation[2], expected);
}

// ---------------------------------------------------------------------------
// Resolution correctness
// ---------------------------------------------------------------------------

#[test]
fn test_resolve_two_lits_complementary() {
    // [1,2] and [-1,3] on 1 -> resolvent polynomial matches [2,3].
    let clauses = vec![vec![1, 2], vec![-1, 3]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    assert_eq!(derivation[2], clause_to_polynomial(&[2, 3]));
}

#[test]
fn test_resolve_unit_clauses_contradiction() {
    let clauses = vec![vec![1], vec![-1]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    assert!(derivation[2].is_one());
}

#[test]
fn test_resolve_produces_tautology() {
    // [1,2] and [-1,-2] on 1 -> [2,-2] (tautological resolvent).
    let clauses = vec![vec![1, 2], vec![-1, -2]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    assert_eq!(derivation.len(), 3);
    assert_eq!(derivation[2], clause_to_polynomial(&[-2, 2]));
}

#[test]
fn test_resolve_large_clauses() {
    // [1,2,3] and [-1,4,5] on 1 -> [2,3,4,5].
    let clauses = vec![vec![1, 2, 3], vec![-1, 4, 5]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    assert_eq!(derivation[2], clause_to_polynomial(&[2, 3, 4, 5]));
}

#[test]
fn test_resolve_chain_three_steps() {
    // c0=[1], c1=[-1,2], c2=[-2]
    // Step 0: resolve c0,c1 on 1 -> [2]
    // Step 1: resolve derived[3],c2 on 2 -> empty
    let clauses = vec![vec![1], vec![-1, 2], vec![-2]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1), (3, 2, 2)]);
    assert!(derivation[4].is_one());
}

#[test]
fn test_resolve_deduplicates_shared_literal() {
    // [1,2] and [-1,2] on 1 -> [2] (not [2,2]).
    let clauses = vec![vec![1, 2], vec![-1, 2]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    // [2] as a clause encodes to (1-x1), degree 1, 2 terms.
    let expected = clause_to_polynomial(&[2]);
    assert_eq!(derivation[2], expected);
}

#[test]
fn test_resolve_reversed_polarity_order() {
    // c0=[-1], c1=[1,2]. Resolve on 1; c0 has -1, c1 has +1.
    let clauses = vec![vec![-1], vec![1, 2]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    assert_eq!(derivation[2], clause_to_polynomial(&[2]));
}

#[test]
fn test_resolve_both_negative_pivot_fails() {
    // Both clauses have -1; no complementary pair.
    let clauses = vec![vec![-1], vec![-1, 2]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    assert!(derivation[2].is_zero(), "both-negative pivot is invalid");
}

// ---------------------------------------------------------------------------
// pc_proof_degree
// ---------------------------------------------------------------------------

#[test]
fn test_pc_proof_degree_empty_derivation() {
    let derivation: Vec<GF2Polynomial> = vec![];
    assert_eq!(pc_proof_degree(&derivation), 0);
}

#[test]
fn test_pc_proof_degree_single_constant() {
    assert_eq!(pc_proof_degree(&[GF2Polynomial::one()]), 0);
}

#[test]
fn test_pc_proof_degree_single_variable() {
    assert_eq!(pc_proof_degree(&[GF2Polynomial::var(0)]), 1);
}

#[test]
fn test_pc_proof_degree_mixed() {
    let polys = vec![
        GF2Polynomial::one(),
        GF2Polynomial::var(0),
        GF2Polynomial::monomial(&[0, 1, 2]),
        GF2Polynomial::monomial(&[3, 4]),
    ];
    assert_eq!(pc_proof_degree(&polys), 3);
}

#[test]
fn test_pc_proof_degree_clause_length_k() {
    // A clause of length k has polynomial degree k.
    let p = clause_to_polynomial(&[1, 2, 3, 4]);
    assert_eq!(pc_proof_degree(&[p]), 4);
}

#[test]
fn test_pc_proof_degree_resolution_bounded() {
    // Resolving [1,2] and [-1,3] on 1: initial max degree=2, resolvent [2,3]=degree 2.
    let clauses = vec![vec![1, 2], vec![-1, 3]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    assert_eq!(pc_proof_degree(&derivation), 2);
}

#[test]
fn test_pc_proof_degree_high_monomial() {
    let big = GF2Polynomial::monomial(&[0, 1, 2, 3, 4, 5, 6]);
    assert_eq!(pc_proof_degree(&[big]), 7);
}

#[test]
fn test_pc_proof_degree_zero_polynomial() {
    assert_eq!(pc_proof_degree(&[GF2Polynomial::zero()]), 0);
}

// ---------------------------------------------------------------------------
// verify_pc_degree_bound
// ---------------------------------------------------------------------------

#[test]
fn test_verify_bound_equals_max_degree() {
    let clauses = vec![vec![1, 2]];
    let derivation = resolution_to_pc(&clauses, &[]);
    // Clause [1,2] has degree 2.
    assert!(verify_pc_degree_bound(&clauses, &derivation, 2));
}

#[test]
fn test_verify_bound_exceeds_max_degree() {
    let clauses = vec![vec![1, 2]];
    let derivation = resolution_to_pc(&clauses, &[]);
    assert!(verify_pc_degree_bound(&clauses, &derivation, 5));
}

#[test]
fn test_verify_bound_below_max_degree() {
    let clauses = vec![vec![1, 2, 3]];
    let derivation = resolution_to_pc(&clauses, &[]);
    // Degree 3, bound 2 should fail.
    assert!(!verify_pc_degree_bound(&clauses, &derivation, 2));
}

#[test]
fn test_verify_bound_zero_with_constants_only() {
    let clauses: Vec<Vec<i32>> = vec![];
    let derivation = vec![GF2Polynomial::one()];
    // Constant polynomial has degree 0.
    assert!(verify_pc_degree_bound(&clauses, &derivation, 0));
}

#[test]
fn test_verify_bound_zero_with_variable_fails() {
    let clauses: Vec<Vec<i32>> = vec![];
    let derivation = vec![GF2Polynomial::var(0)];
    assert!(!verify_pc_degree_bound(&clauses, &derivation, 0));
}

#[test]
fn test_verify_bound_checks_initial_clauses() {
    // Large clause violates bound even if derivation is fine.
    let clauses = vec![vec![1, 2, 3, 4]]; // degree 4
    let derivation = vec![GF2Polynomial::var(0)]; // degree 1
    assert!(!verify_pc_degree_bound(&clauses, &derivation, 3));
}

#[test]
fn test_verify_bound_derivation_violates() {
    // Clauses are fine but derivation has a high-degree polynomial.
    let clauses = vec![vec![1]]; // degree 1
    let derivation = vec![GF2Polynomial::monomial(&[0, 1, 2, 3])]; // degree 4
    assert!(!verify_pc_degree_bound(&clauses, &derivation, 3));
}

#[test]
fn test_verify_bound_exact_match() {
    let clauses = vec![vec![1, 2]];
    let derivation = vec![clause_to_polynomial(&[1, 2])];
    // Exact match at degree 2.
    assert!(verify_pc_degree_bound(&clauses, &derivation, 2));
    assert!(!verify_pc_degree_bound(&clauses, &derivation, 1));
}

#[test]
fn test_verify_bound_empty_clause_and_derivation() {
    let clauses: Vec<Vec<i32>> = vec![];
    let derivation: Vec<GF2Polynomial> = vec![];
    assert!(verify_pc_degree_bound(&clauses, &derivation, 0));
}

#[test]
fn test_verify_bound_multiple_clauses_mixed() {
    let clauses = vec![vec![1], vec![1, 2, 3]]; // degrees 1 and 3
    let derivation = vec![GF2Polynomial::var(0)]; // degree 1
    assert!(verify_pc_degree_bound(&clauses, &derivation, 3));
    assert!(!verify_pc_degree_bound(&clauses, &derivation, 2));
}

// ---------------------------------------------------------------------------
// Integration: resolution-to-PC + degree + verification
// ---------------------------------------------------------------------------

#[test]
fn test_integration_unit_refutation_degree() {
    // {x1}, {-x1} -> resolve to contradiction. Degree = 1.
    let clauses = vec![vec![1], vec![-1]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    let deg = pc_proof_degree(&derivation);
    assert_eq!(deg, 1);
    assert!(verify_pc_degree_bound(&clauses, &derivation, 1));
    assert!(verify_pc_degree_bound(&clauses, &derivation, 2));
}

#[test]
fn test_integration_chain_refutation_degree() {
    // c0=[1], c1=[-1,2], c2=[-2]
    // Step 0: resolve 0,1 on 1 -> [2]
    // Step 1: resolve 3,2 on 2 -> empty
    let clauses = vec![vec![1], vec![-1, 2], vec![-2]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1), (3, 2, 2)]);
    let deg = pc_proof_degree(&derivation);
    // Max initial degree: clause [-1,2] has degree 2. Derived [2] has degree 1.
    assert_eq!(deg, 2);
    assert!(verify_pc_degree_bound(&clauses, &derivation, 2));
    assert!(!verify_pc_degree_bound(&clauses, &derivation, 1));
}

#[test]
fn test_integration_php_like_two_pigeons_one_hole() {
    // PHP(2,1): {x1}, {x2}, {-x1,-x2}
    // Resolve c0,c2 on 1 -> {-x2} (index 3)
    // Resolve c1,3 on 2 -> empty (index 4)
    let clauses = vec![vec![1], vec![2], vec![-1, -2]];
    let derivation = resolution_to_pc(&clauses, &[(0, 2, 1), (1, 3, 2)]);
    let deg = pc_proof_degree(&derivation);
    assert_eq!(deg, 2); // clause [-1,-2] has degree 2
    assert!(derivation.last().unwrap().is_one());
    assert!(verify_pc_degree_bound(&clauses, &derivation, 2));
}

#[test]
fn test_integration_three_variable_chain() {
    // c0=[1,2], c1=[-2,3], c2=[-1], c3=[-3]
    // Step 0: resolve c0,c1 on 2 -> [1,3] (index 4)
    // Step 1: resolve 4,c2 on 1 -> [3] (index 5)
    // Step 2: resolve 5,c3 on 3 -> empty (index 6)
    let clauses = vec![vec![1, 2], vec![-2, 3], vec![-1], vec![-3]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 2), (4, 2, 1), (5, 3, 3)]);
    assert!(derivation.last().unwrap().is_one());
    let deg = pc_proof_degree(&derivation);
    assert_eq!(deg, 2);
    assert!(verify_pc_degree_bound(&clauses, &derivation, 2));
}

#[test]
fn test_integration_degree_verified_against_manual() {
    // Verify that resolution_to_pc output polynomials match manual encoding.
    let clauses = vec![vec![1, -2], vec![-1, 2]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    // Resolvent: remove +1 from c0 and -1 from c1 -> [-2, 2].
    // clause_to_polynomial([-2,2]) = x1 * (1+x1) = x1 + x1^2 = x1 + x1 = 0 in GF(2)
    // So the resolvent polynomial should be zero (tautological clause).
    assert!(derivation[2].is_zero());
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_edge_empty_clause_in_input() {
    // An empty clause [] encodes as GF2Polynomial::one() (product of zero factors = 1).
    let clauses = vec![vec![]];
    let derivation = resolution_to_pc(&clauses, &[]);
    assert!(derivation[0].is_one());
}

#[test]
fn test_edge_single_literal_clauses() {
    let clauses = vec![vec![5], vec![-5]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 5)]);
    assert!(derivation[2].is_one());
}

#[test]
fn test_edge_many_resolution_steps() {
    // Build a chain: c0=[1], c1=[-1,2], c2=[-2,3], c3=[-3,4], c4=[-4]
    // Resolve sequentially.
    let clauses = vec![vec![1], vec![-1, 2], vec![-2, 3], vec![-3, 4], vec![-4]];
    let steps = vec![
        (0, 1, 1), // -> [2], index 5
        (5, 2, 2), // -> [3], index 6
        (6, 3, 3), // -> [4], index 7
        (7, 4, 4), // -> [], index 8
    ];
    let derivation = resolution_to_pc(&clauses, &steps);
    assert_eq!(derivation.len(), 9);
    assert!(
        derivation[8].is_one(),
        "final resolvent should be contradiction"
    );
}

#[test]
fn test_edge_pivot_variable_large_number() {
    // Variables can be large DIMACS indices.
    let clauses = vec![vec![100], vec![-100]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 100)]);
    assert!(derivation[2].is_one());
}

#[test]
fn test_edge_both_indices_same_clause() {
    // Resolving a clause with itself: pivot must be complementary in
    // the same clause, which is impossible for a well-formed clause.
    let clauses = vec![vec![1, 2]];
    let derivation = resolution_to_pc(&clauses, &[(0, 0, 1)]);
    // c0 has +1 but not -1, so resolve_clauses returns None -> zero sentinel.
    assert!(derivation[1].is_zero());
}

#[test]
fn test_edge_degree_bound_zero_empty_input() {
    let clauses: Vec<Vec<i32>> = vec![];
    let derivation: Vec<GF2Polynomial> = vec![];
    assert!(verify_pc_degree_bound(&clauses, &derivation, 0));
}
