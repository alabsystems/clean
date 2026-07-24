// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended tests for Polynomial Calculus degree bounds, resolution
//! simulation, polynomial evaluation, and clause round-tripping.

use super::pc_degree::{pc_proof_degree, resolution_to_pc, verify_pc_degree_bound};
use super::polynomial_calculus::{
    clause_to_polynomial, evaluate_polynomial, polynomial_degree, polynomial_to_clause,
    GF2Polynomial,
};

// ---------------------------------------------------------------------------
// polynomial_degree (free function)
// ---------------------------------------------------------------------------

#[test]
fn test_polynomial_degree_zero() {
    let zero = GF2Polynomial::zero();
    assert_eq!(polynomial_degree(&zero), 0);
}

#[test]
fn test_polynomial_degree_constant() {
    let one = GF2Polynomial::one();
    assert_eq!(polynomial_degree(&one), 0);
}

#[test]
fn test_polynomial_degree_single_var() {
    let x = GF2Polynomial::var(3);
    assert_eq!(polynomial_degree(&x), 1);
}

#[test]
fn test_polynomial_degree_monomial() {
    let m = GF2Polynomial::monomial(&[0, 1, 2, 3]);
    assert_eq!(polynomial_degree(&m), 4);
}

#[test]
fn test_polynomial_degree_sum_of_monomials() {
    // x0*x1*x2 + x3 has degree 3.
    let high = GF2Polynomial::monomial(&[0, 1, 2]);
    let low = GF2Polynomial::var(3);
    let poly = high.add(&low);
    assert_eq!(polynomial_degree(&poly), 3);
}

// ---------------------------------------------------------------------------
// evaluate_polynomial (slice-based)
// ---------------------------------------------------------------------------

#[test]
fn test_evaluate_polynomial_zero() {
    let zero = GF2Polynomial::zero();
    assert!(!evaluate_polynomial(&zero, &[true, true]));
}

#[test]
fn test_evaluate_polynomial_one() {
    let one = GF2Polynomial::one();
    assert!(evaluate_polynomial(&one, &[]));
    assert!(evaluate_polynomial(&one, &[false, false]));
}

#[test]
fn test_evaluate_polynomial_single_var_true() {
    let x0 = GF2Polynomial::var(0);
    assert!(evaluate_polynomial(&x0, &[true]));
}

#[test]
fn test_evaluate_polynomial_single_var_false() {
    let x0 = GF2Polynomial::var(0);
    assert!(!evaluate_polynomial(&x0, &[false]));
}

#[test]
fn test_evaluate_polynomial_xor_expression() {
    // p = x0 + x1 (XOR).
    let p = GF2Polynomial::var(0).add(&GF2Polynomial::var(1));
    assert!(!evaluate_polynomial(&p, &[false, false]));
    assert!(evaluate_polynomial(&p, &[true, false]));
    assert!(evaluate_polynomial(&p, &[false, true]));
    assert!(!evaluate_polynomial(&p, &[true, true]));
}

#[test]
fn test_evaluate_polynomial_and_expression() {
    // p = x0 * x1 (AND).
    let p = GF2Polynomial::monomial(&[0, 1]);
    assert!(!evaluate_polynomial(&p, &[false, false]));
    assert!(!evaluate_polynomial(&p, &[true, false]));
    assert!(!evaluate_polynomial(&p, &[false, true]));
    assert!(evaluate_polynomial(&p, &[true, true]));
}

#[test]
fn test_evaluate_polynomial_missing_vars_are_false() {
    // Variable index beyond slice length treated as false.
    let x5 = GF2Polynomial::var(5);
    assert!(!evaluate_polynomial(&x5, &[true, true]));
}

#[test]
fn test_evaluate_polynomial_complex() {
    // p = x0*x1 + x0 + 1
    let p = GF2Polynomial::monomial(&[0, 1])
        .add(&GF2Polynomial::var(0))
        .add(&GF2Polynomial::one());
    // (0,0): 0 + 0 + 1 = 1
    assert!(evaluate_polynomial(&p, &[false, false]));
    // (1,0): 0 + 1 + 1 = 0
    assert!(!evaluate_polynomial(&p, &[true, false]));
    // (0,1): 0 + 0 + 1 = 1
    assert!(evaluate_polynomial(&p, &[false, true]));
    // (1,1): 1 + 1 + 1 = 1
    assert!(evaluate_polynomial(&p, &[true, true]));
}

// ---------------------------------------------------------------------------
// clause_to_polynomial + polynomial_to_clause round-trip
// ---------------------------------------------------------------------------

#[test]
fn test_clause_roundtrip_single_positive() {
    let clause = vec![1];
    let poly = clause_to_polynomial(&clause);
    let recovered = polynomial_to_clause(&poly).expect("should recover clause");
    assert_eq!(recovered, vec![1]);
}

#[test]
fn test_clause_roundtrip_single_negative() {
    let clause = vec![-1];
    let poly = clause_to_polynomial(&clause);
    let recovered = polynomial_to_clause(&poly).expect("should recover clause");
    assert_eq!(recovered, vec![-1]);
}

#[test]
fn test_clause_roundtrip_two_literals() {
    let clause = vec![1, -2];
    let poly = clause_to_polynomial(&clause);
    let recovered = polynomial_to_clause(&poly).expect("should recover clause");
    // Sorted by absolute value.
    assert_eq!(recovered, vec![1, -2]);
}

#[test]
fn test_clause_roundtrip_three_literals() {
    let clause = vec![-3, 1, 2];
    let poly = clause_to_polynomial(&clause);
    let recovered = polynomial_to_clause(&poly).expect("should recover clause");
    assert_eq!(recovered, vec![1, 2, -3]);
}

#[test]
fn test_polynomial_to_clause_zero_is_empty() {
    let zero = GF2Polynomial::zero();
    let recovered = polynomial_to_clause(&zero).expect("zero poly = empty clause");
    assert!(recovered.is_empty());
}

#[test]
fn test_polynomial_to_clause_constant_one_fails() {
    // Constant 1 is not a clause (the empty clause would be zero).
    let one = GF2Polynomial::one();
    assert!(polynomial_to_clause(&one).is_none());
}

#[test]
fn test_polynomial_to_clause_non_clause_polynomial() {
    // x0 + x1 is XOR, not a clause product.
    let p = GF2Polynomial::var(0).add(&GF2Polynomial::var(1));
    assert!(polynomial_to_clause(&p).is_none());
}

// ---------------------------------------------------------------------------
// resolution_to_pc
// ---------------------------------------------------------------------------

#[test]
fn test_resolution_to_pc_no_steps() {
    let clauses = vec![vec![1], vec![-1]];
    let derivation = resolution_to_pc(&clauses, &[]);
    assert_eq!(derivation.len(), 2);
    assert_eq!(derivation[0], clause_to_polynomial(&[1]));
    assert_eq!(derivation[1], clause_to_polynomial(&[-1]));
}

#[test]
fn test_resolution_to_pc_simple_refutation() {
    // Clauses: {x}, {-x}. Resolve on x to get empty clause.
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![(0, 1, 1)];
    let derivation = resolution_to_pc(&clauses, &steps);

    assert_eq!(derivation.len(), 3);
    // The resolvent: (1 + x0) + x0 = 1 (contradiction).
    assert!(
        derivation[2].is_one(),
        "resolvent of x and -x should be constant 1"
    );
}

#[test]
fn test_resolution_to_pc_two_step_chain() {
    // Clauses: {x, y}, {-x}, {-y}
    // Step 1: resolve clause 0 and clause 1 on x -> {y}
    // Step 2: resolve result (idx 3) and clause 2 on y -> {}
    let clauses = vec![vec![1, 2], vec![-1], vec![-2]];
    let steps = vec![(0, 1, 1), (3, 2, 2)];
    let derivation = resolution_to_pc(&clauses, &steps);

    assert_eq!(derivation.len(), 5);
    // Final resolvent should be constant 1 (contradiction in GF(2)).
    assert!(
        derivation[4].is_one(),
        "two-step resolution should derive contradiction"
    );
}

#[test]
fn test_resolution_to_pc_preserves_initial_clauses() {
    let clauses = vec![vec![1, 2], vec![-1, 3]];
    let derivation = resolution_to_pc(&clauses, &[]);
    assert_eq!(derivation[0], clause_to_polynomial(&[1, 2]));
    assert_eq!(derivation[1], clause_to_polynomial(&[-1, 3]));
}

#[test]
fn test_resolution_to_pc_invalid_index_gives_zero() {
    let clauses = vec![vec![1]];
    let steps = vec![(0, 5, 1)]; // index 5 out of bounds
    let derivation = resolution_to_pc(&clauses, &steps);
    assert!(derivation[1].is_zero());
}

// ---------------------------------------------------------------------------
// pc_proof_degree
// ---------------------------------------------------------------------------

#[test]
fn test_pc_proof_degree_empty() {
    assert_eq!(pc_proof_degree(&[]), 0);
}

#[test]
fn test_pc_proof_degree_single_constant() {
    let derivation = vec![GF2Polynomial::one()];
    assert_eq!(pc_proof_degree(&derivation), 0);
}

#[test]
fn test_pc_proof_degree_mixed() {
    let d = vec![
        GF2Polynomial::var(0),               // degree 1
        GF2Polynomial::monomial(&[0, 1]),    // degree 2
        GF2Polynomial::monomial(&[0, 1, 2]), // degree 3
        GF2Polynomial::one(),                // degree 0
    ];
    assert_eq!(pc_proof_degree(&d), 3);
}

#[test]
fn test_pc_proof_degree_resolution_refutation() {
    let clauses = vec![vec![1], vec![-1]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    // Clause degrees: (1+x0) = degree 1, x0 = degree 1, resolvent 1 = degree 0.
    assert_eq!(pc_proof_degree(&derivation), 1);
}

// ---------------------------------------------------------------------------
// verify_pc_degree_bound
// ---------------------------------------------------------------------------

#[test]
fn test_verify_pc_degree_bound_passes() {
    let clauses = vec![vec![1], vec![-1]];
    let derivation = resolution_to_pc(&clauses, &[(0, 1, 1)]);
    assert!(verify_pc_degree_bound(&clauses, &derivation, 1));
    assert!(verify_pc_degree_bound(&clauses, &derivation, 5));
}

#[test]
fn test_verify_pc_degree_bound_fails_derivation() {
    // Derivation contains degree-3 polynomial but bound is 2.
    let clauses = vec![vec![1]];
    let derivation = vec![
        clause_to_polynomial(&[1]),
        GF2Polynomial::monomial(&[0, 1, 2]),
    ];
    assert!(!verify_pc_degree_bound(&clauses, &derivation, 2));
}

#[test]
fn test_verify_pc_degree_bound_fails_clause() {
    // Clause itself exceeds the bound.
    let clauses = vec![vec![1, 2, 3]]; // degree 3 polynomial
    let derivation = vec![clause_to_polynomial(&[1, 2, 3])];
    assert!(!verify_pc_degree_bound(&clauses, &derivation, 2));
    assert!(verify_pc_degree_bound(&clauses, &derivation, 3));
}

#[test]
fn test_verify_pc_degree_bound_empty() {
    assert!(verify_pc_degree_bound(&[], &[], 0));
}

#[test]
fn test_verify_pc_degree_bound_zero_bound() {
    // Only constant polynomials allowed.
    let clauses: Vec<Vec<i32>> = vec![];
    let derivation = vec![GF2Polynomial::one()];
    assert!(verify_pc_degree_bound(&clauses, &derivation, 0));

    let derivation_with_var = vec![GF2Polynomial::var(0)];
    assert!(!verify_pc_degree_bound(&clauses, &derivation_with_var, 0));
}

// ---------------------------------------------------------------------------
// Integration: resolution proof through full pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_resolution_pipeline_php_2_1() {
    // PHP(2,1): 2 pigeons, 1 hole. UNSAT.
    // Clauses (DIMACS): {1}, {2}, {-1, -2}
    // Resolution: resolve clause 0 and 2 on var 1 -> {-2} (idx 3)
    //             resolve idx 3 and clause 1 on var 2 -> {} (idx 4)
    let clauses = vec![vec![1], vec![2], vec![-1, -2]];
    let steps = vec![(0, 2, 1), (3, 1, 2)];

    let derivation = resolution_to_pc(&clauses, &steps);

    // The final polynomial should be the contradiction (constant 1).
    assert!(
        derivation.last().expect("non-empty derivation").is_one(),
        "PHP(2,1) resolution should derive contradiction in GF(2)"
    );

    // Max degree in derivation should be 2 (from the at-most-one clause).
    assert_eq!(pc_proof_degree(&derivation), 2);

    // Degree bound of 2 should pass.
    assert!(verify_pc_degree_bound(&clauses, &derivation, 2));

    // Degree bound of 1 should fail (clause {-1,-2} has degree 2).
    assert!(!verify_pc_degree_bound(&clauses, &derivation, 1));
}

#[test]
fn test_evaluate_clause_polynomial_semantics() {
    // Clause (x1 OR -x2): satisfied iff x1=true OR x2=false.
    // Polynomial = (1+x0)*x1. It equals 0 exactly when clause satisfied.
    let poly = clause_to_polynomial(&[1, -2]);

    // x1=false, x2=false -> clause satisfied (via -x2) -> poly = 0
    assert!(!evaluate_polynomial(&poly, &[false, false]));
    // x1=true, x2=false -> clause satisfied -> poly = 0
    assert!(!evaluate_polynomial(&poly, &[true, false]));
    // x1=true, x2=true -> clause satisfied (via x1) -> poly = 0
    assert!(!evaluate_polynomial(&poly, &[true, true]));
    // x1=false, x2=true -> clause NOT satisfied -> poly = 1
    assert!(evaluate_polynomial(&poly, &[false, true]));
}
