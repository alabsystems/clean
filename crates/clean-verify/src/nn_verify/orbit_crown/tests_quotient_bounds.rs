// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for orbit-quotiented CROWN bound computation.

use super::equivariance::EquivarianceError;
use super::quotient_bounds::*;
use super::symmetry::*;
use crate::nn_verify::ibp_crown::{CrownBound, Interval};

// ---------------------------------------------------------------------------
// Helper: build a circulant matrix
// ---------------------------------------------------------------------------

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

/// Compute full IBP bounds for comparison: W+ * u + W- * l (upper), W+ * l + W- * u (lower).
fn full_ibp_bounds(
    w: &[Vec<f64>],
    bias: &[f64],
    input_bounds: &[Interval],
) -> (Vec<f64>, Vec<f64>) {
    let n = w.len();
    let mut lower = vec![0.0; n];
    let mut upper = vec![0.0; n];
    for i in 0..n {
        lower[i] = bias[i];
        upper[i] = bias[i];
        for (j, &w_ij) in w[i].iter().enumerate() {
            if w_ij >= 0.0 {
                lower[i] += w_ij * input_bounds[j].lower;
                upper[i] += w_ij * input_bounds[j].upper;
            } else {
                lower[i] += w_ij * input_bounds[j].upper;
                upper[i] += w_ij * input_bounds[j].lower;
            }
        }
    }
    (lower, upper)
}

// ---------------------------------------------------------------------------
// Orbit-CROWN correctness: quotient bounds match full bounds for equivariant W
// ---------------------------------------------------------------------------

#[test]
fn test_orbit_crown_circulant_soundness() {
    let w = circulant_matrix(&[1.0, -0.5, 0.25, 0.1]);
    let bias = vec![0.0; 4];
    let input_bounds = vec![
        Interval::new(-1.0, 1.0),
        Interval::new(-1.0, 1.0),
        Interval::new(-1.0, 1.0),
        Interval::new(-1.0, 1.0),
    ];
    let group = TranslationGroup::new(4);

    let result = orbit_crown_bounds(&w, &bias, &input_bounds, &group, 1e-10)
        .expect("circulant should be equivariant");

    // For a circulant matrix with symmetric input bounds, all outputs
    // should have the same bounds
    let (full_lower, full_upper) = full_ibp_bounds(&w, &bias, &input_bounds);

    // All full bounds should be equal (circulant + symmetric inputs)
    for i in 1..4 {
        assert!(
            (full_lower[i] - full_lower[0]).abs() < 1e-10,
            "full lower bounds should be equal for circulant"
        );
        assert!(
            (full_upper[i] - full_upper[0]).abs() < 1e-10,
            "full upper bounds should be equal for circulant"
        );
    }

    // Orbit bounds should match full bounds
    for i in 0..4 {
        assert!(
            (result.bounds.full_lower[i] - full_lower[i]).abs() < 1e-10,
            "orbit lower[{i}] should match full IBP lower"
        );
        assert!(
            (result.bounds.full_upper[i] - full_upper[i]).abs() < 1e-10,
            "orbit upper[{i}] should match full IBP upper"
        );
    }
}

#[test]
fn test_orbit_crown_reduction_factor() {
    let w = circulant_matrix(&[1.0, 0.5, 0.25]);
    let bias = vec![0.0; 3];
    let input_bounds = vec![Interval::new(-1.0, 1.0); 3];
    let group = TranslationGroup::new(3);

    let result =
        orbit_crown_bounds(&w, &bias, &input_bounds, &group, 1e-10).expect("should succeed");

    assert!(
        (result.reduction_factor - 3.0).abs() < 1e-10,
        "Z_3 on R^3 should give 3x reduction, got {:.1}",
        result.reduction_factor
    );
    assert!(result.equivariance_verified);
}

#[test]
fn test_orbit_crown_partial_symmetry() {
    // Z_2 (swap 0,1) on R^3: orbits are {0,1} and {2}
    let swap = GroupElement::new(vec![1, 0, 2]);
    let group = PermutationGroup::new(3, vec![swap]);

    // Build a matrix equivariant under this Z_2:
    // W must satisfy P*W = W*P where P swaps rows/cols 0 and 1
    // This means W[0][0]=W[1][1], W[0][1]=W[1][0], W[0][2]=W[1][2], W[2][0]=W[2][1]
    let w = vec![
        vec![2.0, 1.0, 0.5],
        vec![1.0, 2.0, 0.5],
        vec![0.3, 0.3, 1.0],
    ];
    let bias = vec![0.0; 3];
    let input_bounds = vec![
        Interval::new(-1.0, 1.0),
        Interval::new(-1.0, 1.0),
        Interval::new(-2.0, 2.0),
    ];

    let result = orbit_crown_bounds(&w, &bias, &input_bounds, &group, 1e-10)
        .expect("should succeed for Z_2-equivariant matrix");

    assert_eq!(
        result.bounds.orbits.len(),
        2,
        "Z_2 on R^3 with swap(0,1) has 2 orbits"
    );
    assert!(
        (result.reduction_factor - 1.5).abs() < 1e-10,
        "3 dims / 2 orbits = 1.5x reduction"
    );

    // Bounds at positions 0 and 1 should be equal (same orbit)
    assert!(
        (result.bounds.full_lower[0] - result.bounds.full_lower[1]).abs() < 1e-10,
        "positions in same orbit should have same lower bound"
    );
    assert!(
        (result.bounds.full_upper[0] - result.bounds.full_upper[1]).abs() < 1e-10,
        "positions in same orbit should have same upper bound"
    );
}

// ---------------------------------------------------------------------------
// Non-equivariant rejection
// ---------------------------------------------------------------------------

#[test]
fn test_orbit_crown_rejects_non_equivariant() {
    let w = vec![
        vec![1.0, 0.0, 0.0],
        vec![0.0, 2.0, 0.0],
        vec![0.0, 0.0, 3.0],
    ];
    let bias = vec![0.0; 3];
    let input_bounds = vec![Interval::new(-1.0, 1.0); 3];
    let group = TranslationGroup::new(3);

    let result = orbit_crown_bounds(&w, &bias, &input_bounds, &group, 1e-10);
    assert!(
        matches!(result, Err(EquivarianceError::NotEquivariant { .. })),
        "should reject non-equivariant matrix"
    );
}

// ---------------------------------------------------------------------------
// Quotient CROWN bound from existing full CROWN bound
// ---------------------------------------------------------------------------

#[test]
fn test_quotient_crown_bound_from_full() {
    let crown = CrownBound {
        lower_coeffs: vec![vec![1.0, 0.0, 0.0]; 3],
        upper_coeffs: vec![vec![0.0, 1.0, 0.0]; 3],
        lower_bias: vec![-1.0, -1.0, -2.0],
        upper_bias: vec![1.0, 1.0, 3.0],
    };

    let swap = GroupElement::new(vec![1, 0, 2]);
    let group = PermutationGroup::new(3, vec![swap]);

    let qb = quotient_crown_bound(&crown, &group);

    // Orbits: {0,1} and {2}
    assert_eq!(qb.orbits.len(), 2);

    // Representative of {0,1} is 0, so rep_lower[0] = lower_bias[0] = -1.0
    assert!((qb.representative_lower[0] - (-1.0)).abs() < 1e-10);
    assert!((qb.representative_upper[0] - 1.0).abs() < 1e-10);

    // Both positions 0 and 1 should get the same bounds
    assert!((qb.full_lower[0] - qb.full_lower[1]).abs() < 1e-10);
    assert!((qb.full_upper[0] - qb.full_upper[1]).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// Soundness: orbit bounds contain full IBP bounds
// ---------------------------------------------------------------------------

#[test]
fn test_orbit_bounds_sound_vs_full_ibp() {
    // For an equivariant matrix, orbit bounds should equal full IBP bounds
    // (not merely contain them), because the symmetry is exact.
    let w = circulant_matrix(&[2.0, -1.0, 0.5]);
    let bias = vec![0.1, 0.1, 0.1];
    let input_bounds = vec![
        Interval::new(-0.5, 0.5),
        Interval::new(-0.5, 0.5),
        Interval::new(-0.5, 0.5),
    ];
    let group = TranslationGroup::new(3);

    let result =
        orbit_crown_bounds(&w, &bias, &input_bounds, &group, 1e-10).expect("should succeed");
    let (full_lower, full_upper) = full_ibp_bounds(&w, &bias, &input_bounds);

    for i in 0..3 {
        // Orbit bounds should be sound (contain the true output range)
        assert!(
            result.bounds.full_lower[i] <= full_lower[i] + 1e-10,
            "orbit lower[{i}] must be <= full IBP lower"
        );
        assert!(
            result.bounds.full_upper[i] >= full_upper[i] - 1e-10,
            "orbit upper[{i}] must be >= full IBP upper"
        );
    }
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_orbit_crown_dim_1() {
    // Trivial case: 1D, no symmetry
    let w = vec![vec![2.0]];
    let bias = vec![0.5];
    let input_bounds = vec![Interval::new(-1.0, 1.0)];
    let group = TranslationGroup::new(1);

    let result =
        orbit_crown_bounds(&w, &bias, &input_bounds, &group, 1e-10).expect("should succeed for 1D");

    assert_eq!(result.bounds.orbits.len(), 1);
    assert!((result.bounds.full_lower[0] - (-1.5)).abs() < 1e-10);
    assert!((result.bounds.full_upper[0] - 2.5).abs() < 1e-10);
}

#[test]
fn test_orbit_crown_with_bias() {
    let w = circulant_matrix(&[1.0, 0.0]);
    let bias = vec![0.5, 0.5]; // equal biases (equivariant)
    let input_bounds = vec![Interval::new(-1.0, 2.0), Interval::new(-1.0, 2.0)];
    let group = TranslationGroup::new(2);

    let result =
        orbit_crown_bounds(&w, &bias, &input_bounds, &group, 1e-10).expect("should succeed");

    // W is identity (circulant of [1, 0]), so output = input + bias
    // lower = -1.0 + 0.5 = -0.5, upper = 2.0 + 0.5 = 2.5
    assert!((result.bounds.full_lower[0] - (-0.5)).abs() < 1e-10);
    assert!((result.bounds.full_upper[0] - 2.5).abs() < 1e-10);
}
