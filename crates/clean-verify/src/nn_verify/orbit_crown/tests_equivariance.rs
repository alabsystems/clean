// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for weight equivariance verification.

use super::equivariance::*;
use super::symmetry::*;

// ---------------------------------------------------------------------------
// Circulant matrices are equivariant under TranslationGroup
// ---------------------------------------------------------------------------

/// Build a circulant matrix from its first row.
///
/// A circulant matrix C has C[i][j] = first_row[(j - i) mod n].
/// Circulant matrices commute with cyclic shifts.
fn circulant_matrix(first_row: &[f64]) -> Vec<Vec<f64>> {
    let n = first_row.len();
    let mut mat = vec![vec![0.0; n]; n];
    for i in 0..n {
        for j in 0..n {
            mat[i][j] = first_row[(j + n - i) % n];
        }
    }
    mat
}

#[test]
fn test_circulant_is_equivariant() {
    let w = circulant_matrix(&[1.0, 2.0, 3.0, 4.0]);
    let group = TranslationGroup::new(4);
    let result = verify_equivariance(&w, &group, 1e-10).expect("circulant should be equivariant");
    assert!(
        result.is_equivariant,
        "circulant matrix commutes with cyclic shifts, error = {:.2e}",
        result.max_commutator_norm
    );
    assert!(
        result.max_commutator_norm < 1e-12,
        "commutator norm should be near zero for exact circulant"
    );
}

#[test]
fn test_random_matrix_not_equivariant() {
    // A non-circulant matrix should NOT commute with cyclic shifts
    let w = vec![
        vec![1.0, 0.0, 0.0],
        vec![0.0, 2.0, 0.0],
        vec![0.0, 0.0, 3.0],
    ];
    let group = TranslationGroup::new(3);
    let result = verify_equivariance(&w, &group, 1e-10)
        .expect("should return result even if not equivariant");
    assert!(
        !result.is_equivariant,
        "diagonal matrix with distinct entries is not circulant"
    );
    assert!(
        result.max_commutator_norm > 0.1,
        "commutator norm should be significant for non-equivariant matrix"
    );
}

#[test]
fn test_scalar_matrix_is_equivariant() {
    // Scalar matrix (alpha * I) commutes with everything
    let n = 5;
    let alpha = 3.7;
    let w: Vec<Vec<f64>> = (0..n)
        .map(|i| {
            let mut row = vec![0.0; n];
            row[i] = alpha;
            row
        })
        .collect();
    let group = TranslationGroup::new(n);
    let result = verify_equivariance(&w, &group, 1e-10).expect("scalar matrix should pass");
    assert!(
        result.is_equivariant,
        "scalar matrix commutes with all permutations"
    );
}

// ---------------------------------------------------------------------------
// Permutation-equivariant matrices
// ---------------------------------------------------------------------------

#[test]
fn test_s3_equivariant_matrix() {
    // A matrix equivariant under S_3 must be of the form a*I + b*J
    // where J is the all-ones matrix.
    let a = 2.0;
    let b = 0.5;
    let w = vec![vec![a + b, b, b], vec![b, a + b, b], vec![b, b, a + b]];

    let cycle = GroupElement::new(vec![1, 2, 0]);
    let swap = GroupElement::new(vec![1, 0, 2]);
    let group = PermutationGroup::new(3, vec![cycle, swap]);

    let result = verify_equivariance(&w, &group, 1e-10).expect("aI + bJ should be S_3-equivariant");
    assert!(
        result.is_equivariant,
        "aI + bJ commutes with all permutations, error = {:.2e}",
        result.max_commutator_norm
    );
}

#[test]
fn test_non_s3_equivariant() {
    // Non-symmetric matrix
    let w = vec![
        vec![1.0, 2.0, 3.0],
        vec![4.0, 5.0, 6.0],
        vec![7.0, 8.0, 9.0],
    ];

    let cycle = GroupElement::new(vec![1, 2, 0]);
    let swap = GroupElement::new(vec![1, 0, 2]);
    let group = PermutationGroup::new(3, vec![cycle, swap]);

    let result = verify_equivariance(&w, &group, 1e-10)
        .expect("should return result for non-equivariant matrix");
    assert!(!result.is_equivariant);
}

// ---------------------------------------------------------------------------
// Dimension mismatch detection
// ---------------------------------------------------------------------------

#[test]
fn test_dimension_mismatch_rows() {
    let w = vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.0, 0.0]];
    let group = TranslationGroup::new(2);
    let result = verify_equivariance(&w, &group, 1e-10);
    assert!(
        matches!(result, Err(EquivarianceError::DimensionMismatch { .. })),
        "should detect row count mismatch"
    );
}

#[test]
fn test_dimension_mismatch_cols() {
    let w = vec![vec![1.0, 0.0, 0.0], vec![0.0, 1.0, 0.0]];
    let group = TranslationGroup::new(2);
    let result = verify_equivariance(&w, &group, 1e-10);
    assert!(
        matches!(result, Err(EquivarianceError::DimensionMismatch { .. })),
        "should detect column count mismatch"
    );
}

// ---------------------------------------------------------------------------
// Tolerance behavior
// ---------------------------------------------------------------------------

#[test]
fn test_approximate_equivariance() {
    // Start with a circulant and add small noise
    let mut w = circulant_matrix(&[1.0, 0.5, 0.25]);
    w[0][1] += 1e-6; // small perturbation

    let group = TranslationGroup::new(3);

    // Tight tolerance: should fail
    let result_tight = verify_equivariance(&w, &group, 1e-8).expect("should return result");
    assert!(
        !result_tight.is_equivariant,
        "tight tolerance should fail for perturbed circulant"
    );

    // Loose tolerance: should pass
    let result_loose = verify_equivariance(&w, &group, 1e-4).expect("should return result");
    assert!(
        result_loose.is_equivariant,
        "loose tolerance should pass for nearly-circulant"
    );
}

#[test]
fn test_per_generator_norms_reported() {
    let w = circulant_matrix(&[1.0, 2.0, 3.0]);
    let group = TranslationGroup::new(3);
    let result = verify_equivariance(&w, &group, 1e-10).expect("circulant should pass");
    assert_eq!(
        result.generator_norms.len(),
        1,
        "TranslationGroup has 1 generator"
    );
}

#[test]
fn test_equivariance_error_display() {
    let err = EquivarianceError::NotEquivariant {
        generator_index: 0,
        commutator_norm: 1.5,
        tolerance: 1e-6,
    };
    let msg = err.to_string();
    assert!(
        msg.contains("generator 0"),
        "should mention generator index"
    );
    assert!(msg.contains("1.5"), "should mention the norm");
}
