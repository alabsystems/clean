// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C004: CROWN through LayerNorm degenerates to IBP.
//!
//! Exercises the core degeneration result across multiple configurations:
//! - Varying dimension (2, 3, 4, 8)
//! - Varying epsilon (small, medium, large input perturbation)
//! - Varying gamma/beta (uniform, non-uniform, with zeros)
//! - Jacobian structure (non-diagonal for generic inputs)
//! - Edge cases (point intervals, very large perturbations)

use super::crown::CrownBound;
use super::crown_layernorm_degeneration::{
    approx_eq, crown_backward_through_layernorm, evaluate_layernorm, ibp_through_layernorm,
    matrix_is_diagonal, midpoint, CrownLayerNormDegenerationSpec, LayerNormJacobian,
};

const EPS: f64 = 1e-5;

// ===========================================================================
// LayerNorm Jacobian tests
// ===========================================================================

#[test]
fn test_jacobian_dimension_2_uniform() {
    let x = vec![1.0, 3.0];
    let gamma = vec![1.0, 1.0];
    let jac = LayerNormJacobian::compute(&x, &gamma, EPS);
    assert_eq!(jac.dim(), 2);
    assert_eq!(jac.matrix.len(), 2);
    assert_eq!(jac.matrix[0].len(), 2);
}

#[test]
fn test_jacobian_non_diagonal_generic_input() {
    let x = vec![1.0, 3.0, 5.0];
    let gamma = vec![1.0, 1.0, 1.0];
    let jac = LayerNormJacobian::compute(&x, &gamma, EPS);

    assert!(!jac.is_diagonal(1e-10));
    assert!(jac.off_diagonal_nonzero_count(1e-10) > 0);
    assert!(jac.off_diagonal_l1_norm() > 1e-3);
}

#[test]
fn test_jacobian_row_sum_near_zero() {
    // The LayerNorm Jacobian has the property that each row sums to
    // approximately zero (because mean subtraction kills the all-ones direction).
    let x = vec![2.0, 4.0, 6.0];
    let gamma = vec![1.0, 1.0, 1.0];
    let jac = LayerNormJacobian::compute(&x, &gamma, EPS);

    for i in 0..3 {
        let row_sum: f64 = jac.matrix[i].iter().sum();
        assert!(
            row_sum.abs() < 1e-6,
            "row {} sum = {} (expected ~0)",
            i,
            row_sum,
        );
    }
}

#[test]
fn test_jacobian_gamma_scaling() {
    let x = vec![1.0, 3.0, 5.0];
    let gamma1 = vec![1.0, 1.0, 1.0];
    let gamma2 = vec![2.0, 2.0, 2.0];
    let jac1 = LayerNormJacobian::compute(&x, &gamma1, EPS);
    let jac2 = LayerNormJacobian::compute(&x, &gamma2, EPS);

    for i in 0..3 {
        for j in 0..3 {
            let ratio = if jac1.matrix[i][j].abs() > 1e-15 {
                jac2.matrix[i][j] / jac1.matrix[i][j]
            } else {
                2.0
            };
            assert!(
                (ratio - 2.0).abs() < 1e-6,
                "gamma scaling: J2[{i}][{j}]/J1[{i}][{j}] = {ratio}, expected 2.0",
            );
        }
    }
}

#[test]
fn test_jacobian_non_uniform_gamma() {
    let x = vec![1.0, 3.0, 5.0];
    let gamma_uniform = vec![1.0, 1.0, 1.0];
    let gamma_mixed = vec![1.0, 2.0, 3.0];
    let jac_u = LayerNormJacobian::compute(&x, &gamma_uniform, EPS);
    let jac_m = LayerNormJacobian::compute(&x, &gamma_mixed, EPS);

    for i in 0..3 {
        let scale = gamma_mixed[i] / gamma_uniform[i];
        for j in 0..3 {
            let expected = jac_u.matrix[i][j] * scale;
            assert!(
                (jac_m.matrix[i][j] - expected).abs() < 1e-10,
                "non-uniform gamma: J_m[{i}][{j}] = {}, expected {}",
                jac_m.matrix[i][j],
                expected,
            );
        }
    }
}

#[test]
fn test_jacobian_equal_inputs() {
    // When all inputs are equal, variance -> eps, z_i -> 0
    let x = vec![5.0, 5.0, 5.0];
    let gamma = vec![1.0, 1.0, 1.0];
    let jac = LayerNormJacobian::compute(&x, &gamma, EPS);

    let inv_sqrt_eps = 1.0 / EPS.sqrt();
    let inv_n = 1.0 / 3.0;

    for i in 0..3 {
        for j in 0..3 {
            let delta_ij = if i == j { 1.0 } else { 0.0 };
            let expected = inv_sqrt_eps * (delta_ij - inv_n);
            assert!(
                (jac.matrix[i][j] - expected).abs() < 1e-2,
                "equal inputs: J[{i}][{j}] = {}, expected {expected}",
                jac.matrix[i][j],
            );
        }
    }
}

#[test]
fn test_jacobian_stores_reference_point() {
    let x = vec![1.0, 2.0, 3.0];
    let gamma = vec![1.0, 1.0, 1.0];
    let jac = LayerNormJacobian::compute(&x, &gamma, EPS);
    assert_eq!(jac.reference_point, x);
}

#[test]
fn test_jacobian_stores_statistics() {
    let x = vec![1.0, 3.0, 5.0];
    let gamma = vec![1.0, 1.0, 1.0];
    let jac = LayerNormJacobian::compute(&x, &gamma, EPS);

    // mean = (1+3+5)/3 = 3.0
    assert!(approx_eq(jac.mean, 3.0, 1e-10));
    // variance = ((1-3)^2 + (3-3)^2 + (5-3)^2) / 3 = (4+0+4)/3 ≈ 2.667
    assert!(approx_eq(jac.variance, 8.0 / 3.0, 1e-10));
    assert!(jac.sigma > 0.0);
}

// ===========================================================================
// evaluate_layernorm tests
// ===========================================================================

#[test]
fn test_evaluate_layernorm_basic() {
    let x = vec![1.0, 3.0, 5.0];
    let gamma = vec![1.0, 1.0, 1.0];
    let beta = vec![0.0, 0.0, 0.0];
    let output = evaluate_layernorm(&x, &gamma, &beta, EPS);

    assert_eq!(output.len(), 3);
    // Mean = 3.0, so centered = [-2, 0, 2]
    // Variance = 8/3, sigma = sqrt(8/3 + eps)
    // Normalized ≈ [-2/sigma, 0, 2/sigma]
    assert!(output[0] < 0.0); // below mean
    assert!(approx_eq(output[1], 0.0, 1e-6)); // at mean
    assert!(output[2] > 0.0); // above mean
                              // With unit gamma, zero beta, output should sum to ~0
    let sum: f64 = output.iter().sum();
    assert!(sum.abs() < 1e-6, "output sum = {sum}, expected ~0");
}

#[test]
fn test_evaluate_layernorm_beta_shift() {
    let x = vec![1.0, 3.0, 5.0];
    let gamma = vec![1.0, 1.0, 1.0];
    let beta0 = vec![0.0, 0.0, 0.0];
    let beta1 = vec![10.0, 10.0, 10.0];
    let out0 = evaluate_layernorm(&x, &gamma, &beta0, EPS);
    let out1 = evaluate_layernorm(&x, &gamma, &beta1, EPS);

    for i in 0..3 {
        assert!(approx_eq(out1[i] - out0[i], 10.0, 1e-6));
    }
}

// ===========================================================================
// CROWN backward through LayerNorm
// ===========================================================================

#[test]
fn test_crown_backward_returns_correct_dimension() {
    let n = 3;
    let gamma = vec![1.0; n];
    let beta = vec![0.0; n];
    let lo = vec![0.0; n];
    let hi = vec![1.0; n];
    let bound = CrownBound::identity(n);

    let result = crown_backward_through_layernorm(&gamma, &beta, EPS, &lo, &hi, &bound);
    assert_eq!(result.num_outputs(), n);
}

#[test]
fn test_crown_backward_produces_diagonal_effective_bound() {
    // The key C004 result: the effective bound after degeneration has
    // zero off-diagonal coefficients (all info is in the bias).
    let n = 3;
    let gamma = vec![1.0, 2.0, 0.5];
    let beta = vec![0.1, -0.2, 0.3];
    let lo = vec![-1.0, 0.0, 1.0];
    let hi = vec![1.0, 2.0, 3.0];
    let bound = CrownBound::identity(n);

    let result = crown_backward_through_layernorm(&gamma, &beta, EPS, &lo, &hi, &bound);

    // All coefficients should be zero (degenerated to pure bias bounds)
    assert!(
        matrix_is_diagonal(&result.lower_coeffs, 1e-10),
        "expected diagonal lower coeffs after degeneration",
    );
    assert!(
        matrix_is_diagonal(&result.upper_coeffs, 1e-10),
        "expected diagonal upper coeffs after degeneration",
    );
}

// ===========================================================================
// IBP through LayerNorm
// ===========================================================================

#[test]
fn test_ibp_returns_correct_dimension() {
    let n = 3;
    let gamma = vec![1.0; n];
    let beta = vec![0.0; n];
    let lo = vec![0.0; n];
    let hi = vec![1.0; n];

    let bounds = ibp_through_layernorm(&lo, &hi, &gamma, &beta, EPS);
    assert_eq!(bounds.len(), n);
}

#[test]
fn test_ibp_lower_le_upper() {
    let _n = 4;
    let gamma = vec![1.0, 2.0, 0.5, 3.0];
    let beta = vec![0.1, -0.1, 0.0, 0.5];
    let lo = vec![-1.0, 0.0, 1.0, 2.0];
    let hi = vec![1.0, 2.0, 3.0, 4.0];

    let bounds = ibp_through_layernorm(&lo, &hi, &gamma, &beta, EPS);
    for (i, iv) in bounds.iter().enumerate() {
        assert!(
            iv.lower <= iv.upper + 1e-6,
            "element {i}: lower {} > upper {}",
            iv.lower,
            iv.upper,
        );
    }
}

// ===========================================================================
// C004 degeneration verification
// ===========================================================================

#[test]
fn test_degeneration_dim2_uniform_gamma() {
    let spec = CrownLayerNormDegenerationSpec::new();
    let result = spec.verify_degeneration(&[1.0, 1.0], &[0.0, 0.0], EPS, &[0.0, 0.0], &[1.0, 1.0]);
    assert!(result.is_ok(), "dim2: {}", result.unwrap_err());
}

#[test]
fn test_degeneration_dim3_non_uniform_gamma() {
    let spec = CrownLayerNormDegenerationSpec::new();
    let result = spec.verify_degeneration(
        &[1.0, 2.0, 0.5],
        &[0.1, -0.2, 0.3],
        EPS,
        &[-1.0, 0.0, 1.0],
        &[1.0, 2.0, 3.0],
    );
    assert!(result.is_ok(), "dim3: {}", result.unwrap_err());
}

#[test]
fn test_degeneration_dim4_large_perturbation() {
    let spec = CrownLayerNormDegenerationSpec::new();
    let result = spec.verify_degeneration(
        &[1.0; 4],
        &[0.0; 4],
        EPS,
        &[-10.0, -10.0, -10.0, -10.0],
        &[10.0, 10.0, 10.0, 10.0],
    );
    assert!(result.is_ok(), "dim4 large: {}", result.unwrap_err());
}

#[test]
fn test_degeneration_dim4_small_perturbation() {
    let spec = CrownLayerNormDegenerationSpec::new();
    let center = [5.0, 3.0, -1.0, 2.0];
    let eps_val = 0.001;
    let lo: Vec<f64> = center.iter().map(|c| c - eps_val).collect();
    let hi: Vec<f64> = center.iter().map(|c| c + eps_val).collect();
    let result = spec.verify_degeneration(&[1.0; 4], &[0.0; 4], EPS, &lo, &hi);
    assert!(result.is_ok(), "dim4 small: {}", result.unwrap_err());
}

#[test]
fn test_degeneration_dim8_varied_gamma_beta() {
    let spec = CrownLayerNormDegenerationSpec::new();
    let gamma = vec![0.5, 1.0, 1.5, 2.0, 0.3, 0.7, 1.2, 0.9];
    let beta = vec![0.0, 0.1, -0.1, 0.5, -0.5, 0.2, -0.3, 0.0];
    let lo = vec![0.0, 1.0, 2.0, 3.0, -1.0, -2.0, 0.5, 1.5];
    let hi = vec![1.0, 2.0, 3.0, 4.0, 0.0, -1.0, 1.5, 2.5];

    let result = spec.verify_degeneration(&gamma, &beta, EPS, &lo, &hi);
    assert!(result.is_ok(), "dim8: {}", result.unwrap_err());
}

#[test]
fn test_degeneration_point_intervals() {
    let spec = CrownLayerNormDegenerationSpec::new();
    let result = spec.verify_degeneration(
        &[1.0, 2.0, 3.0],
        &[0.1, 0.2, 0.3],
        EPS,
        &[1.0, 2.0, 3.0],
        &[1.0, 2.0, 3.0],
    );
    assert!(result.is_ok(), "point intervals: {}", result.unwrap_err());
}

#[test]
fn test_degeneration_asymmetric_intervals() {
    let spec = CrownLayerNormDegenerationSpec::new();
    let result = spec.verify_degeneration(
        &[1.0, 1.0, 1.0],
        &[0.0, 0.0, 0.0],
        EPS,
        &[-5.0, 2.9, 2.9],
        &[5.0, 3.1, 3.1],
    );
    assert!(result.is_ok(), "asymmetric: {}", result.unwrap_err());
}

// ===========================================================================
// Jacobian structure verification
// ===========================================================================

#[test]
fn test_spec_verify_jacobian_structure_passes() {
    let spec = CrownLayerNormDegenerationSpec::new();
    let result =
        spec.verify_jacobian_structure(&[1.0, 1.0, 1.0], &[0.0, 1.0, 2.0], &[1.0, 2.0, 3.0], EPS);
    assert!(
        result.is_ok(),
        "jacobian structure: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_spec_verify_jacobian_structure_dim1_rejected() {
    let spec = CrownLayerNormDegenerationSpec::new();
    let result = spec.verify_jacobian_structure(&[1.0], &[0.0], &[1.0], EPS);
    assert!(result.is_err(), "dim=1 should be rejected");
}

// ===========================================================================
// Diagonal effective verification
// ===========================================================================

#[test]
fn test_spec_verify_diagonal_effective_passes() {
    let spec = CrownLayerNormDegenerationSpec::new();
    let result = spec.verify_diagonal_effective(
        &[1.0, 2.0, 0.5],
        &[0.1, -0.2, 0.3],
        EPS,
        &[-1.0, 0.0, 1.0],
        &[1.0, 2.0, 3.0],
    );
    assert!(
        result.is_ok(),
        "diagonal effective: {}",
        result.unwrap_err()
    );
}

// ===========================================================================
// Utility function tests
// ===========================================================================

#[test]
fn test_midpoint_basic() {
    let lo = vec![0.0, 2.0, -4.0];
    let hi = vec![2.0, 6.0, 0.0];
    let mid = midpoint(&lo, &hi);
    assert!(approx_eq(mid[0], 1.0, 1e-10));
    assert!(approx_eq(mid[1], 4.0, 1e-10));
    assert!(approx_eq(mid[2], -2.0, 1e-10));
}

#[test]
fn test_matrix_is_diagonal_true() {
    let m = vec![vec![1.0, 0.0], vec![0.0, 2.0]];
    assert!(matrix_is_diagonal(&m, 1e-10));
}

#[test]
fn test_matrix_is_diagonal_false() {
    let m = vec![vec![1.0, 0.5], vec![0.0, 2.0]];
    assert!(!matrix_is_diagonal(&m, 1e-10));
}

#[test]
fn test_approx_eq_basic() {
    assert!(approx_eq(1.0, 1.0, 1e-10));
    assert!(approx_eq(1.0, 1.0 + 1e-11, 1e-10));
    assert!(!approx_eq(1.0, 2.0, 1e-10));
}

// ===========================================================================
// Combined: dense Jacobian + degenerate bounds (the C004 paradox)
// ===========================================================================

#[test]
fn test_jacobian_is_dense_but_bounds_are_ibp() {
    let spec = CrownLayerNormDegenerationSpec::new();

    // Step 1: Verify Jacobian IS dense
    let jac_result =
        spec.verify_jacobian_structure(&[1.0, 1.0, 1.0], &[0.5, 2.5, 6.5], &[1.5, 3.5, 7.5], EPS);
    assert!(jac_result.is_ok(), "Jacobian should be dense");

    // Step 2: But CROWN still equals IBP
    let degen_result = spec.verify_degeneration(
        &[1.0, 1.0, 1.0],
        &[0.0, 0.0, 0.0],
        EPS,
        &[0.5, 2.5, 6.5],
        &[1.5, 3.5, 7.5],
    );
    assert!(
        degen_result.is_ok(),
        "degeneration: {}",
        degen_result.unwrap_err(),
    );
}
