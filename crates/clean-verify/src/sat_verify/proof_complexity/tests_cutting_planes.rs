// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dedicated tests for the Cutting Planes proof system module.
//!
//! Covers: CpInequality (construction, evaluate, is_trivially_valid),
//! CpStep variants, CuttingPlanesProof (add_input, add, multiply, divide,
//! saturate, inequality_at, len, is_empty, verify, Default).

use super::cutting_planes::*;

// ===== CpInequality::new =====

#[test]
fn test_cp_inequality_new_basic() {
    let ineq = CpInequality::new(vec![1, 2, 3], 5);
    assert_eq!(ineq.coeffs, vec![1, 2, 3]);
    assert_eq!(ineq.rhs, 5);
}

#[test]
fn test_cp_inequality_new_empty_coeffs() {
    let ineq = CpInequality::new(vec![], 0);
    assert!(ineq.coeffs.is_empty());
    assert_eq!(ineq.rhs, 0);
}

#[test]
fn test_cp_inequality_new_negative_coeffs() {
    let ineq = CpInequality::new(vec![-3, -1, 2], -5);
    assert_eq!(ineq.coeffs, vec![-3, -1, 2]);
    assert_eq!(ineq.rhs, -5);
}

#[test]
fn test_cp_inequality_new_single_variable() {
    let ineq = CpInequality::new(vec![7], 3);
    assert_eq!(ineq.coeffs.len(), 1);
    assert_eq!(ineq.coeffs[0], 7);
}

// ===== CpInequality::evaluate =====

#[test]
fn test_evaluate_all_true_satisfies() {
    // 1*x0 + 2*x1 >= 3 with x0=1, x1=1 => 3 >= 3
    let ineq = CpInequality::new(vec![1, 2], 3);
    assert!(ineq.evaluate(&[true, true]));
}

#[test]
fn test_evaluate_all_false_zero_sum() {
    // 1*x0 + 2*x1 >= 0 with all false => 0 >= 0
    let ineq = CpInequality::new(vec![1, 2], 0);
    assert!(ineq.evaluate(&[false, false]));
}

#[test]
fn test_evaluate_all_false_positive_rhs() {
    // 1*x0 + 2*x1 >= 1 with all false => 0 >= 1 fails
    let ineq = CpInequality::new(vec![1, 2], 1);
    assert!(!ineq.evaluate(&[false, false]));
}

#[test]
fn test_evaluate_negative_coefficients() {
    // -1*x0 + 3*x1 >= 2 with x0=true, x1=true => -1 + 3 = 2 >= 2
    let ineq = CpInequality::new(vec![-1, 3], 2);
    assert!(ineq.evaluate(&[true, true]));
}

#[test]
fn test_evaluate_negative_coefficients_fail() {
    // -1*x0 + 3*x1 >= 3 with x0=true, x1=true => 2 >= 3 fails
    let ineq = CpInequality::new(vec![-1, 3], 3);
    assert!(!ineq.evaluate(&[true, true]));
}

#[test]
fn test_evaluate_assignment_shorter_than_coeffs() {
    // 1*x0 + 2*x1 + 3*x2 >= 1 with assignment=[true]
    // Missing vars treated as false: 1 + 0 + 0 = 1 >= 1
    let ineq = CpInequality::new(vec![1, 2, 3], 1);
    assert!(ineq.evaluate(&[true]));
}

#[test]
fn test_evaluate_assignment_longer_than_coeffs() {
    // 1*x0 >= 1 with assignment=[true, true, true]
    // Extra assignment entries are irrelevant (no coefficients)
    let ineq = CpInequality::new(vec![1], 1);
    assert!(ineq.evaluate(&[true, true, true]));
}

#[test]
fn test_evaluate_empty_coeffs_zero_rhs() {
    // 0 >= 0 is always satisfied
    let ineq = CpInequality::new(vec![], 0);
    assert!(ineq.evaluate(&[]));
    assert!(ineq.evaluate(&[true, false]));
}

#[test]
fn test_evaluate_empty_coeffs_positive_rhs() {
    // 0 >= 1 is never satisfied
    let ineq = CpInequality::new(vec![], 1);
    assert!(!ineq.evaluate(&[]));
    assert!(!ineq.evaluate(&[true]));
}

#[test]
fn test_evaluate_empty_coeffs_negative_rhs() {
    // 0 >= -1 is always satisfied
    let ineq = CpInequality::new(vec![], -1);
    assert!(ineq.evaluate(&[]));
}

#[test]
fn test_evaluate_exact_boundary() {
    // 5*x0 >= 5 with x0=true => 5 >= 5 (exact equality, should pass)
    let ineq = CpInequality::new(vec![5], 5);
    assert!(ineq.evaluate(&[true]));
}

#[test]
fn test_evaluate_just_below_boundary() {
    // 4*x0 >= 5 with x0=true => 4 >= 5 fails
    let ineq = CpInequality::new(vec![4], 5);
    assert!(!ineq.evaluate(&[true]));
}

// ===== CpInequality::is_trivially_valid =====

#[test]
fn test_trivially_valid_rhs_zero() {
    let ineq = CpInequality::new(vec![1, -2, 3], 0);
    assert!(ineq.is_trivially_valid());
}

#[test]
fn test_trivially_valid_rhs_negative() {
    let ineq = CpInequality::new(vec![-5, -10], -100);
    assert!(ineq.is_trivially_valid());
}

#[test]
fn test_trivially_valid_sum_equals_rhs() {
    // 1 + 2 = 3 >= 3
    let ineq = CpInequality::new(vec![1, 2], 3);
    assert!(ineq.is_trivially_valid());
}

#[test]
fn test_trivially_valid_sum_exceeds_rhs() {
    // 2 + 3 = 5 >= 4
    let ineq = CpInequality::new(vec![2, 3], 4);
    assert!(ineq.is_trivially_valid());
}

#[test]
fn test_not_trivially_valid_sum_less_than_rhs() {
    // 1 + 2 = 3, but rhs = 4
    let ineq = CpInequality::new(vec![1, 2], 4);
    assert!(!ineq.is_trivially_valid());
}

#[test]
fn test_not_trivially_valid_negative_coeff_with_positive_rhs() {
    // -1 + 5 = 4 >= 3, but has negative coefficient => not trivially valid
    let ineq = CpInequality::new(vec![-1, 5], 3);
    assert!(!ineq.is_trivially_valid());
}

#[test]
fn test_trivially_valid_empty_coeffs_zero_rhs() {
    let ineq = CpInequality::new(vec![], 0);
    assert!(ineq.is_trivially_valid());
}

#[test]
fn test_trivially_valid_all_zero_coeffs_zero_rhs() {
    let ineq = CpInequality::new(vec![0, 0, 0], 0);
    assert!(ineq.is_trivially_valid());
}

// ===== CpInequality: Clone, PartialEq, Eq =====

#[test]
fn test_cp_inequality_clone_and_eq() {
    let a = CpInequality::new(vec![1, 2, 3], 6);
    let b = a.clone();
    assert_eq!(a, b);
}

#[test]
fn test_cp_inequality_not_equal_different_coeffs() {
    let a = CpInequality::new(vec![1, 2], 3);
    let b = CpInequality::new(vec![1, 3], 3);
    assert_ne!(a, b);
}

#[test]
fn test_cp_inequality_not_equal_different_rhs() {
    let a = CpInequality::new(vec![1, 2], 3);
    let b = CpInequality::new(vec![1, 2], 4);
    assert_ne!(a, b);
}

// ===== CuttingPlanesProof::new / Default =====

#[test]
fn test_proof_new_is_empty() {
    let proof = CuttingPlanesProof::new();
    assert!(proof.is_empty());
    assert_eq!(proof.len(), 0);
}

#[test]
fn test_proof_default_is_empty() {
    let proof = CuttingPlanesProof::default();
    assert!(proof.is_empty());
    assert_eq!(proof.len(), 0);
}

#[test]
fn test_proof_new_does_not_verify() {
    let proof = CuttingPlanesProof::new();
    assert!(!proof.verify());
}

// ===== CuttingPlanesProof::add_input =====

#[test]
fn test_add_input_returns_index_zero() {
    let mut proof = CuttingPlanesProof::new();
    let idx = proof.add_input(CpInequality::new(vec![1], 1));
    assert_eq!(idx, 0);
}

#[test]
fn test_add_input_increments_index() {
    let mut proof = CuttingPlanesProof::new();
    let i0 = proof.add_input(CpInequality::new(vec![1], 1));
    let i1 = proof.add_input(CpInequality::new(vec![2], 2));
    let i2 = proof.add_input(CpInequality::new(vec![3], 3));
    assert_eq!(i0, 0);
    assert_eq!(i1, 1);
    assert_eq!(i2, 2);
    assert_eq!(proof.len(), 3);
}

#[test]
fn test_add_input_stores_inequality() {
    let mut proof = CuttingPlanesProof::new();
    let ineq = CpInequality::new(vec![10, 20], 15);
    let idx = proof.add_input(ineq.clone());
    assert_eq!(proof.inequality_at(idx), Some(&ineq));
}

#[test]
fn test_add_input_not_empty() {
    let mut proof = CuttingPlanesProof::new();
    proof.add_input(CpInequality::new(vec![1], 1));
    assert!(!proof.is_empty());
}

// ===== CuttingPlanesProof::add =====

#[test]
fn test_add_basic() {
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1, 0], 1));
    let b = proof.add_input(CpInequality::new(vec![0, 2], 3));
    let c = proof.add(a, b).unwrap();
    let ineq = proof.inequality_at(c).unwrap();
    assert_eq!(ineq.coeffs, vec![1, 2]);
    assert_eq!(ineq.rhs, 4);
}

#[test]
fn test_add_different_length_coeffs() {
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1], 1));
    let b = proof.add_input(CpInequality::new(vec![0, 2, 3], 5));
    let c = proof.add(a, b).unwrap();
    let ineq = proof.inequality_at(c).unwrap();
    assert_eq!(ineq.coeffs, vec![1, 2, 3]);
    assert_eq!(ineq.rhs, 6);
}

#[test]
fn test_add_cancellation() {
    // x >= 1 and -x >= -1 => add => 0 >= 0
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1], 1));
    let b = proof.add_input(CpInequality::new(vec![-1], -1));
    let c = proof.add(a, b).unwrap();
    let ineq = proof.inequality_at(c).unwrap();
    assert_eq!(ineq.coeffs, vec![0]);
    assert_eq!(ineq.rhs, 0);
}

#[test]
fn test_add_self_doubles() {
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![3, 5], 4));
    let c = proof.add(a, a).unwrap();
    let ineq = proof.inequality_at(c).unwrap();
    assert_eq!(ineq.coeffs, vec![6, 10]);
    assert_eq!(ineq.rhs, 8);
}

#[test]
fn test_add_invalid_left_index() {
    let mut proof = CuttingPlanesProof::new();
    proof.add_input(CpInequality::new(vec![1], 1));
    assert!(proof.add(99, 0).is_err());
}

#[test]
fn test_add_invalid_right_index() {
    let mut proof = CuttingPlanesProof::new();
    proof.add_input(CpInequality::new(vec![1], 1));
    assert!(proof.add(0, 99).is_err());
}

#[test]
fn test_add_both_indices_invalid() {
    let proof = CuttingPlanesProof::new();
    assert!(proof.clone().add(0, 1).is_err());
}

// ===== CuttingPlanesProof::multiply =====

#[test]
fn test_multiply_by_one_identity() {
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![3, 7], 5));
    let b = proof.multiply(a, 1).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![3, 7]);
    assert_eq!(ineq.rhs, 5);
}

#[test]
fn test_multiply_by_large_scalar() {
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1, 2], 3));
    let b = proof.multiply(a, 100).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![100, 200]);
    assert_eq!(ineq.rhs, 300);
}

#[test]
fn test_multiply_zero_scalar_fails() {
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1], 1));
    assert!(proof.multiply(a, 0).is_err());
}

#[test]
fn test_multiply_negative_scalar_fails() {
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1], 1));
    assert!(proof.multiply(a, -5).is_err());
}

#[test]
fn test_multiply_invalid_index_fails() {
    let mut proof = CuttingPlanesProof::new();
    assert!(proof.multiply(0, 2).is_err());
}

#[test]
fn test_multiply_negative_coefficients() {
    // -2*x >= -3, multiply by 2 => -4*x >= -6
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![-2], -3));
    let b = proof.multiply(a, 2).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![-4]);
    assert_eq!(ineq.rhs, -6);
}

// ===== CuttingPlanesProof::divide =====

#[test]
fn test_divide_exact() {
    // 4*x + 6*y >= 10, divide by 2 => 2*x + 3*y >= 5
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![4, 6], 10));
    let b = proof.divide(a, 2).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![2, 3]);
    assert_eq!(ineq.rhs, 5);
}

#[test]
fn test_divide_ceiling_on_rhs() {
    // 2*x + 3*y >= 5, divide by 2 => ceil(2/2)*x + ceil(3/2)*y >= ceil(5/2)
    // => 1*x + 2*y >= 3
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![2, 3], 5));
    let b = proof.divide(a, 2).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![1, 2]);
    assert_eq!(ineq.rhs, 3);
}

#[test]
fn test_divide_by_one_identity() {
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![5, 7], 11));
    let b = proof.divide(a, 1).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![5, 7]);
    assert_eq!(ineq.rhs, 11);
}

#[test]
fn test_divide_zero_divisor_fails() {
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1], 1));
    assert!(proof.divide(a, 0).is_err());
}

#[test]
fn test_divide_negative_divisor_fails() {
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1], 1));
    assert!(proof.divide(a, -3).is_err());
}

#[test]
fn test_divide_invalid_index_fails() {
    let mut proof = CuttingPlanesProof::new();
    assert!(proof.divide(0, 2).is_err());
}

#[test]
fn test_divide_negative_coefficients_ceiling() {
    // -3*x >= -5, divide by 2 => ceil(-3/2)*x >= ceil(-5/2)
    // For negative: ceil(-3/2) = -3/2 = -1 (rounds toward +inf)
    // ceil(-5/2) = -5/2 = -2
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![-3], -5));
    let b = proof.divide(a, 2).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![-1]);
    assert_eq!(ineq.rhs, -2);
}

#[test]
fn test_divide_large_divisor() {
    // 1*x >= 1, divide by 100 => ceil(1/100) = 1, ceil(1/100) = 1
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1], 1));
    let b = proof.divide(a, 100).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![1]);
    assert_eq!(ineq.rhs, 1);
}

#[test]
fn test_divide_all_zero_coefficients() {
    // 0*x + 0*y >= 0, divide by 3 => 0*x + 0*y >= 0
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![0, 0], 0));
    let b = proof.divide(a, 3).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![0, 0]);
    assert_eq!(ineq.rhs, 0);
}

// ===== CuttingPlanesProof::saturate =====

#[test]
fn test_saturate_caps_at_rhs() {
    // 10*x + 3*y + 1*z >= 3
    // Saturate: min(10, 3)=3, min(3, 3)=3, min(1, 3)=1 (but also max(.,0))
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![10, 3, 1], 3));
    let b = proof.saturate(a).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![3, 3, 1]);
    assert_eq!(ineq.rhs, 3);
}

#[test]
fn test_saturate_clamps_negative_to_zero() {
    // -5*x + 10*y >= 3
    // Saturate: max(min(-5, 3), 0) = 0, max(min(10, 3), 0) = 3
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![-5, 10], 3));
    let b = proof.saturate(a).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![0, 3]);
    assert_eq!(ineq.rhs, 3);
}

#[test]
fn test_saturate_all_below_rhs_unchanged() {
    // 1*x + 2*y >= 5, both coefficients < 5
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1, 2], 5));
    let b = proof.saturate(a).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![1, 2]);
    assert_eq!(ineq.rhs, 5);
}

#[test]
fn test_saturate_negative_rhs_all_zeroed() {
    // 5*x + 3*y >= -2
    // Saturate: min(5, -2) = -2, max(-2, 0) = 0; min(3, -2) = -2, max(-2, 0) = 0
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![5, 3], -2));
    let b = proof.saturate(a).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![0, 0]);
    assert_eq!(ineq.rhs, -2);
}

#[test]
fn test_saturate_zero_rhs_all_zeroed() {
    // 5*x + 3*y >= 0, saturate => min(5,0)=0, min(3,0)=0 then max(.,0)=0
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![5, 3], 0));
    let b = proof.saturate(a).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![0, 0]);
    assert_eq!(ineq.rhs, 0);
}

#[test]
fn test_saturate_invalid_index_fails() {
    let mut proof = CuttingPlanesProof::new();
    assert!(proof.saturate(0).is_err());
}

// ===== CuttingPlanesProof::inequality_at =====

#[test]
fn test_inequality_at_valid_index() {
    let mut proof = CuttingPlanesProof::new();
    let ineq = CpInequality::new(vec![42], 7);
    let idx = proof.add_input(ineq.clone());
    assert_eq!(proof.inequality_at(idx), Some(&ineq));
}

#[test]
fn test_inequality_at_invalid_index_returns_none() {
    let proof = CuttingPlanesProof::new();
    assert_eq!(proof.inequality_at(0), None);
    assert_eq!(proof.inequality_at(100), None);
}

// ===== CuttingPlanesProof::len / is_empty =====

#[test]
fn test_len_after_mixed_operations() {
    let mut proof = CuttingPlanesProof::new();
    assert_eq!(proof.len(), 0);
    let a = proof.add_input(CpInequality::new(vec![1], 1));
    assert_eq!(proof.len(), 1);
    let b = proof.add_input(CpInequality::new(vec![2], 2));
    assert_eq!(proof.len(), 2);
    let _c = proof.add(a, b).unwrap();
    assert_eq!(proof.len(), 3);
    let _d = proof.multiply(a, 3).unwrap();
    assert_eq!(proof.len(), 4);
    let _e = proof.divide(b, 2).unwrap();
    assert_eq!(proof.len(), 5);
    let _f = proof.saturate(a).unwrap();
    assert_eq!(proof.len(), 6);
}

// ===== CuttingPlanesProof::verify =====

#[test]
fn test_verify_empty_proof() {
    let proof = CuttingPlanesProof::new();
    assert!(!proof.verify());
}

#[test]
fn test_verify_single_input_not_contradiction() {
    let mut proof = CuttingPlanesProof::new();
    proof.add_input(CpInequality::new(vec![1, 2], 3));
    assert!(!proof.verify());
}

#[test]
fn test_verify_contradiction_zero_ge_one() {
    // 0 >= 1 is a contradiction
    let mut proof = CuttingPlanesProof::new();
    proof.add_input(CpInequality::new(vec![0], 1));
    assert!(proof.verify());
}

#[test]
fn test_verify_not_contradiction_zero_ge_zero() {
    // 0 >= 0 is not a contradiction
    let mut proof = CuttingPlanesProof::new();
    proof.add_input(CpInequality::new(vec![0], 0));
    assert!(!proof.verify());
}

#[test]
fn test_verify_not_contradiction_zero_ge_negative() {
    // 0 >= -1 is not a contradiction (rhs <= 0)
    let mut proof = CuttingPlanesProof::new();
    proof.add_input(CpInequality::new(vec![0], -1));
    assert!(!proof.verify());
}

#[test]
fn test_verify_nonzero_coefficients_not_contradiction() {
    // 1 >= 1 has nonzero coefficient, not 0 >= c form
    let mut proof = CuttingPlanesProof::new();
    proof.add_input(CpInequality::new(vec![1], 1));
    assert!(!proof.verify());
}

#[test]
fn test_verify_derived_contradiction() {
    // x >= 1 and -x >= 0 => 0 >= 1
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1], 1));
    let b = proof.add_input(CpInequality::new(vec![-1], 0));
    let _c = proof.add(a, b).unwrap();
    assert!(proof.verify());
}

#[test]
fn test_verify_checks_last_step_only() {
    // Even if intermediate step is a contradiction, verify checks the last step.
    let mut proof = CuttingPlanesProof::new();
    // Step 0: contradiction 0 >= 1
    proof.add_input(CpInequality::new(vec![0], 1));
    // Step 1: non-contradiction input
    proof.add_input(CpInequality::new(vec![1], 1));
    // Last step is step 1, which is NOT a contradiction
    assert!(!proof.verify());
}

#[test]
fn test_verify_multiple_zero_coefficients() {
    // 0*x + 0*y + 0*z >= 2 is a contradiction
    let mut proof = CuttingPlanesProof::new();
    proof.add_input(CpInequality::new(vec![0, 0, 0], 2));
    assert!(proof.verify());
}

#[test]
fn test_verify_empty_coeffs_positive_rhs() {
    // no vars, rhs > 0 => 0 >= rhs contradiction
    let mut proof = CuttingPlanesProof::new();
    proof.add_input(CpInequality::new(vec![], 5));
    assert!(proof.verify());
}

// ===== CpStep enum variants =====

#[test]
fn test_cp_step_input_debug() {
    let step = CpStep::Input(CpInequality::new(vec![1], 1));
    let dbg = format!("{step:?}");
    assert!(dbg.contains("Input"));
}

#[test]
fn test_cp_step_add_debug() {
    let step = CpStep::Add(0, 1);
    let dbg = format!("{step:?}");
    assert!(dbg.contains("Add"));
}

#[test]
fn test_cp_step_multiply_debug() {
    let step = CpStep::Multiply(0, 5);
    let dbg = format!("{step:?}");
    assert!(dbg.contains("Multiply"));
}

#[test]
fn test_cp_step_divide_debug() {
    let step = CpStep::Divide(0, 3);
    let dbg = format!("{step:?}");
    assert!(dbg.contains("Divide"));
}

#[test]
fn test_cp_step_saturate_debug() {
    let step = CpStep::Saturate(0);
    let dbg = format!("{step:?}");
    assert!(dbg.contains("Saturate"));
}

#[test]
fn test_cp_step_clone_eq() {
    let a = CpStep::Add(1, 2);
    let b = a.clone();
    assert_eq!(a, b);
}

// ===== Composite proofs / integration =====

#[test]
fn test_multiply_then_add_contradiction() {
    // x >= 1, -2x >= -1
    // multiply first by 2: 2x >= 2
    // add: 2x + (-2x) >= 2 + (-1) => 0 >= 1
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1], 1));
    let b = proof.add_input(CpInequality::new(vec![-2], -1));
    let c = proof.multiply(a, 2).unwrap();
    let d = proof.add(c, b).unwrap();
    let ineq = proof.inequality_at(d).unwrap();
    assert_eq!(ineq.coeffs, vec![0]);
    assert_eq!(ineq.rhs, 1);
    assert!(proof.verify());
}

#[test]
fn test_divide_then_saturate() {
    // 6*x + 9*y >= 7, divide by 3 => ceil(6/3)=2, ceil(9/3)=3, ceil(7/3)=3
    // saturate: min(2,3)=2, min(3,3)=3 (both non-negative)
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![6, 9], 7));
    let b = proof.divide(a, 3).unwrap();
    let ineq_div = proof.inequality_at(b).unwrap();
    assert_eq!(ineq_div.coeffs, vec![2, 3]);
    assert_eq!(ineq_div.rhs, 3);
    let c = proof.saturate(b).unwrap();
    let ineq_sat = proof.inequality_at(c).unwrap();
    assert_eq!(ineq_sat.coeffs, vec![2, 3]);
    assert_eq!(ineq_sat.rhs, 3);
}

#[test]
fn test_chain_add_three_inequalities() {
    // a: x >= 1, b: y >= 1, c: -x - y >= -1
    // add(a, b) => x + y >= 2
    // add(result, c) => 0 >= 1
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1, 0], 1));
    let b = proof.add_input(CpInequality::new(vec![0, 1], 1));
    let c = proof.add_input(CpInequality::new(vec![-1, -1], -1));
    let d = proof.add(a, b).unwrap();
    let e = proof.add(d, c).unwrap();
    let ineq = proof.inequality_at(e).unwrap();
    assert_eq!(ineq.coeffs, vec![0, 0]);
    assert_eq!(ineq.rhs, 1);
    assert!(proof.verify());
}

#[test]
fn test_saturate_strengthens_inequality() {
    // 100*x + 1*y >= 2, saturate => 2*x + 1*y >= 2
    // Saturated version is strictly stronger (fewer satisfying assignments possible)
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![100, 1], 2));
    let b = proof.saturate(a).unwrap();
    let ineq = proof.inequality_at(b).unwrap();
    assert_eq!(ineq.coeffs, vec![2, 1]);
    assert_eq!(ineq.rhs, 2);
    // x=false, y=true: original 0+1=1 < 2 (fails both), not demonstrative.
    // x=true, y=false: original 100 >= 2 (pass), saturated 2 >= 2 (pass)
    // Soundness: saturated is at least as strong for 0/1 variables
    assert!(ineq.evaluate(&[true, false]));
}

#[test]
fn test_full_proof_php_2_1_manual() {
    // PHP(2,1): 2 pigeons, 1 hole
    // x1 >= 1 (pigeon 1 must go in hole 1)
    // x2 >= 1 (pigeon 2 must go in hole 1)
    // -x1 - x2 >= -1 (hole 1 holds at most 1 pigeon)
    // Sum: 0 >= 1
    let mut proof = CuttingPlanesProof::new();
    let s0 = proof.add_input(CpInequality::new(vec![1, 0], 1));
    let s1 = proof.add_input(CpInequality::new(vec![0, 1], 1));
    let s2 = proof.add_input(CpInequality::new(vec![-1, -1], -1));
    let s3 = proof.add(s0, s1).unwrap();
    let s4 = proof.add(s3, s2).unwrap();
    let final_ineq = proof.inequality_at(s4).unwrap();
    assert_eq!(final_ineq.coeffs, vec![0, 0]);
    assert_eq!(final_ineq.rhs, 1);
    assert!(proof.verify());
    assert_eq!(proof.len(), 5);
}

#[test]
fn test_proof_clone_preserves_state() {
    let mut proof = CuttingPlanesProof::new();
    let a = proof.add_input(CpInequality::new(vec![1], 1));
    let b = proof.add_input(CpInequality::new(vec![-1], 0));
    let _c = proof.add(a, b).unwrap();
    let cloned = proof.clone();
    assert_eq!(cloned.len(), proof.len());
    assert!(cloned.verify());
    assert_eq!(
        cloned.inequality_at(2).unwrap(),
        proof.inequality_at(2).unwrap()
    );
}

#[test]
fn test_error_message_contains_index() {
    let proof = CuttingPlanesProof::new();
    let err = proof.clone().add(5, 0).unwrap_err();
    assert!(err.contains("5"), "error should mention invalid index 5");
}

#[test]
fn test_multiply_error_message_contains_scalar() {
    let mut proof = CuttingPlanesProof::new();
    proof.add_input(CpInequality::new(vec![1], 1));
    let err = proof.multiply(0, -7).unwrap_err();
    assert!(err.contains("-7"), "error should mention invalid scalar -7");
}

#[test]
fn test_divide_error_message_contains_divisor() {
    let mut proof = CuttingPlanesProof::new();
    proof.add_input(CpInequality::new(vec![1], 1));
    let err = proof.divide(0, -2).unwrap_err();
    assert!(
        err.contains("-2"),
        "error should mention invalid divisor -2"
    );
}
