// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for constructive proof witnesses (proofs.rs).
//! Covers T01-T08 with concrete zonotope inputs.

use super::concrete::ConcreteZonotope;
use super::proofs::*;
use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// T01: Interval hull soundness
// ---------------------------------------------------------------------------

#[test]
fn test_t01_basic_1d() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let w = verify_t01_interval_hull_sound(&z, &[0.5]);
    assert!(w.verified, "center + 0.5*gen should be in hull");
    assert_eq!(w.proof_status, ProofStatus::DerivedPending);
}

#[test]
fn test_t01_extreme_coefficients() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    // Extremes: eps = [1, -1] -> point = [2, 1]
    let w = verify_t01_interval_hull_sound(&z, &[1.0, -1.0]);
    assert!(w.verified, "extreme point should be in hull");
}

#[test]
fn test_t01_zero_generators() {
    let z = ConcreteZonotope::new(vec![5.0], vec![]);
    let w = verify_t01_interval_hull_sound(&z, &[]);
    assert!(w.verified, "point zonotope should be in its own hull");
}

#[test]
fn test_t01_many_generators() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![1.0, 0.5], vec![0.3, -0.7], vec![-0.2, 0.4]],
    );
    let w = verify_t01_interval_hull_sound(&z, &[0.5, -0.3, 0.8]);
    assert!(w.verified);
}

// ---------------------------------------------------------------------------
// T02: Linear transform exactness
// ---------------------------------------------------------------------------

#[test]
fn test_t02_identity_transform() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let w_mat: Vec<&[f64]> = vec![&[1.0, 0.0], &[0.0, 1.0]];
    let bias = vec![0.0, 0.0];
    let w = verify_t02_linear_transform_exact(&z, &w_mat, &bias, &[0.5, -0.3]);
    assert!(w.verified, "identity transform should preserve membership");
    assert_eq!(w.proof_status, ProofStatus::DerivedPending);
}

#[test]
fn test_t02_scaling_and_bias() {
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![2.0]]);
    let w_mat: Vec<&[f64]> = vec![&[3.0]];
    let bias = vec![1.0];
    let w = verify_t02_linear_transform_exact(&z, &w_mat, &bias, &[0.5]);
    assert!(w.verified, "3*x + 1 should be in transformed zonotope");
}

#[test]
fn test_t02_dimension_expansion() {
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![1.0]]);
    let w_mat: Vec<&[f64]> = vec![&[1.0], &[2.0]];
    let bias = vec![0.0, 0.0];
    let w = verify_t02_linear_transform_exact(&z, &w_mat, &bias, &[0.5]);
    assert!(w.verified);
}

// ---------------------------------------------------------------------------
// T03: ReLU overapproximation soundness
// ---------------------------------------------------------------------------

#[test]
fn test_t03_always_active() {
    let z = ConcreteZonotope::new(vec![5.0], vec![vec![1.0]]);
    let w = verify_t03_relu_overapprox_sound(&z, &[0.5]);
    assert!(w.verified, "relu of positive region should be sound");
    assert_eq!(w.proof_status, ProofStatus::DerivedPending);
}

#[test]
fn test_t03_always_inactive() {
    let z = ConcreteZonotope::new(vec![-5.0], vec![vec![1.0]]);
    let w = verify_t03_relu_overapprox_sound(&z, &[0.5]);
    assert!(w.verified, "relu of negative region should be sound");
}

#[test]
fn test_t03_crossing() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![2.0]]);
    let w = verify_t03_relu_overapprox_sound(&z, &[0.5]);
    assert!(w.verified, "relu of crossing region should be sound");
}

#[test]
fn test_t03_crossing_negative_point() {
    // When x < 0, relu(x) = 0 should be in the overapproximation.
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![2.0]]);
    let w = verify_t03_relu_overapprox_sound(&z, &[-0.8]);
    assert!(w.verified, "relu(negative point) = 0 should be in hull");
}

#[test]
fn test_t03_2d_mixed() {
    // dim 0: crossing [-1, 3], dim 1: always active [1, 5]
    let z = ConcreteZonotope::new(vec![1.0, 3.0], vec![vec![2.0, 2.0]]);
    let w = verify_t03_relu_overapprox_sound(&z, &[0.5]);
    assert!(w.verified);
}

// ---------------------------------------------------------------------------
// T04: Lambda-relaxation tightness
// ---------------------------------------------------------------------------

#[test]
fn test_t04_symmetric_crossing() {
    let w = verify_t04_relu_lambda_relaxation_tight(-1.0, 1.0);
    assert!(
        w.verified,
        "symmetric crossing should have valid relaxation"
    );
    assert_eq!(w.proof_status, ProofStatus::DerivedPending);
}

#[test]
fn test_t04_asymmetric_crossing() {
    let w = verify_t04_relu_lambda_relaxation_tight(-2.0, 4.0);
    assert!(
        w.verified,
        "asymmetric crossing should have valid relaxation"
    );
}

#[test]
fn test_t04_non_crossing_vacuous() {
    // Not a crossing interval -> vacuously true.
    let w = verify_t04_relu_lambda_relaxation_tight(1.0, 5.0);
    assert!(w.verified, "non-crossing is vacuously true");
}

#[test]
fn test_t04_narrow_crossing() {
    let w = verify_t04_relu_lambda_relaxation_tight(-0.01, 0.01);
    assert!(w.verified, "narrow crossing should work");
}

// ---------------------------------------------------------------------------
// T05: ReLU always-active exactness
// ---------------------------------------------------------------------------

#[test]
fn test_t05_all_positive() {
    let z = ConcreteZonotope::new(vec![5.0, 3.0], vec![vec![1.0, 0.5]]);
    let w = verify_t05_relu_always_active_exact(&z);
    assert!(w.verified, "all-positive zonotope should be identity");
    assert_eq!(w.proof_status, ProofStatus::DerivedPending);
}

#[test]
fn test_t05_edge_at_zero() {
    // Lower bound exactly 0 -> still always active.
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![1.0]]);
    let w = verify_t05_relu_always_active_exact(&z);
    assert!(w.verified, "lower=0 is still always active");
}

#[test]
fn test_t05_vacuous_when_crossing() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![2.0]]);
    let w = verify_t05_relu_always_active_exact(&z);
    assert!(w.verified, "crossing case is vacuously true for T05");
}

// ---------------------------------------------------------------------------
// T06: ReLU always-inactive exactness
// ---------------------------------------------------------------------------

#[test]
fn test_t06_all_negative() {
    let z = ConcreteZonotope::new(vec![-5.0, -3.0], vec![vec![1.0, 1.0]]);
    let w = verify_t06_relu_always_inactive_exact(&z);
    assert!(w.verified, "all-negative should be zeroed");
    assert_eq!(w.proof_status, ProofStatus::DerivedPending);
}

#[test]
fn test_t06_edge_at_zero() {
    // Upper bound exactly 0 -> still always inactive.
    let z = ConcreteZonotope::new(vec![-1.0], vec![vec![1.0]]);
    let w = verify_t06_relu_always_inactive_exact(&z);
    assert!(w.verified);
}

#[test]
fn test_t06_vacuous_when_positive() {
    let z = ConcreteZonotope::new(vec![5.0], vec![vec![1.0]]);
    let w = verify_t06_relu_always_inactive_exact(&z);
    assert!(w.verified, "positive case is vacuously true for T06");
}

// ---------------------------------------------------------------------------
// T07: Affine+ReLU composition soundness
// ---------------------------------------------------------------------------

#[test]
fn test_t07_basic_composition() {
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![2.0]]);
    let w_mat: Vec<&[f64]> = vec![&[1.0]];
    let bias = vec![0.0];
    let w = verify_t07_affine_relu_composition_sound(&z, &w_mat, &bias, &[0.5]);
    assert!(w.verified);
    assert_eq!(w.proof_status, ProofStatus::DerivedPending);
}

#[test]
fn test_t07_scaling_then_relu() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let w_mat: Vec<&[f64]> = vec![&[2.0]];
    let bias = vec![-1.0];
    // Affine: 2*x - 1, hull [-3, 1], crossing
    let w = verify_t07_affine_relu_composition_sound(&z, &w_mat, &bias, &[0.5]);
    assert!(w.verified);
}

// ---------------------------------------------------------------------------
// T08: Minkowski sum soundness
// ---------------------------------------------------------------------------

#[test]
fn test_t08_basic_sum() {
    let z1 = ConcreteZonotope::new(vec![1.0], vec![vec![1.0]]);
    let z2 = ConcreteZonotope::new(vec![2.0], vec![vec![0.5]]);
    let w = verify_t08_minkowski_sum_sound(&z1, &z2, &[0.5], &[-0.3]);
    assert!(w.verified, "sum of points should be in Minkowski sum");
    assert_eq!(w.proof_status, ProofStatus::DerivedPending);
}

#[test]
fn test_t08_2d_sum() {
    let z1 = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0]]);
    let z2 = ConcreteZonotope::new(vec![3.0, 4.0], vec![vec![0.0, 1.0]]);
    let w = verify_t08_minkowski_sum_sound(&z1, &z2, &[0.5], &[-0.5]);
    assert!(w.verified);
}

#[test]
fn test_t08_extreme_coefficients() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let w = verify_t08_minkowski_sum_sound(&z1, &z2, &[1.0], &[1.0]);
    assert!(w.verified, "extremes should still be in hull");
}

// ---------------------------------------------------------------------------
// Summary
// ---------------------------------------------------------------------------

#[test]
fn test_all_proved() {
    let statuses = proof_statuses();
    assert_eq!(statuses.len(), 8);
    for (id, desc, status) in &statuses {
        assert_eq!(
            *status,
            ProofStatus::DerivedPending,
            "theorem {id} ({desc}) should be DerivedPending"
        );
    }
}
