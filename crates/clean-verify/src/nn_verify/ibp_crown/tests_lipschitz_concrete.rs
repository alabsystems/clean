// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for concrete Lipschitz verification (lipschitz_concrete module).
//!
//! Covers power iteration convergence, per-layer constants, network-level
//! composition (T30/T32), residual bounds (T33), and submultiplicativity
//! with concrete matrix products.

use super::lipschitz_concrete::*;

// ---------------------------------------------------------------------------
// Power iteration
// ---------------------------------------------------------------------------

#[test]
fn test_power_iteration_identity_2x2() {
    // Identity matrix: singular values are all 1.0.
    let row0: &[f64] = &[1.0, 0.0];
    let row1: &[f64] = &[0.0, 1.0];
    let matrix: &[&[f64]] = &[row0, row1];
    let sigma = power_iteration(matrix, 50);
    assert!(
        (sigma - 1.0).abs() < 1e-6,
        "identity singular value should be 1.0, got {sigma}"
    );
}

#[test]
fn test_power_iteration_scaling_matrix() {
    // [[2,0],[0,3]]: singular values are 2 and 3, max = 3.
    let row0: &[f64] = &[2.0, 0.0];
    let row1: &[f64] = &[0.0, 3.0];
    let matrix: &[&[f64]] = &[row0, row1];
    let sigma = power_iteration(matrix, 50);
    assert!(
        (sigma - 3.0).abs() < 1e-6,
        "max singular value of diag(2,3) should be 3.0, got {sigma}"
    );
}

#[test]
fn test_power_iteration_rectangular() {
    // [[1, 2], [3, 4], [5, 6]]: 3x2 matrix.
    // W^T W = [[35, 44], [44, 56]], eigenvalues ~90.73 and ~0.27.
    // Max singular value = sqrt(90.73) ~ 9.526.
    let row0: &[f64] = &[1.0, 2.0];
    let row1: &[f64] = &[3.0, 4.0];
    let row2: &[f64] = &[5.0, 6.0];
    let matrix: &[&[f64]] = &[row0, row1, row2];
    let sigma = power_iteration(matrix, 100);
    // Known max singular value of [[1,2],[3,4],[5,6]]: sqrt(90.7345...) ~ 9.5257
    assert!(
        (sigma - 9.526).abs() < 0.01,
        "max singular value should be ~9.526, got {sigma}"
    );
}

#[test]
fn test_power_iteration_symmetric_positive_definite() {
    // Symmetric PD: [[4, 2], [2, 3]].
    // char poly: λ² - 7λ + 8, eigenvalues: (7 ± sqrt(17))/2 ≈ 5.561, 1.439.
    // For a symmetric matrix, singular values = eigenvalues.
    let row0: &[f64] = &[4.0, 2.0];
    let row1: &[f64] = &[2.0, 3.0];
    let matrix: &[&[f64]] = &[row0, row1];
    let sigma = power_iteration(matrix, 100);
    let expected = (7.0 + 17.0_f64.sqrt()) / 2.0;
    assert!(
        (sigma - expected).abs() < 1e-6,
        "SPD singular value should be {expected}, got {sigma}"
    );
}

#[test]
fn test_power_iteration_zero_matrix() {
    let row0: &[f64] = &[0.0, 0.0];
    let row1: &[f64] = &[0.0, 0.0];
    let matrix: &[&[f64]] = &[row0, row1];
    let sigma = power_iteration(matrix, 50);
    assert!(
        sigma < 1e-10,
        "zero matrix should have sigma ~0, got {sigma}"
    );
}

#[test]
fn test_power_iteration_empty_matrix() {
    let matrix: &[&[f64]] = &[];
    let sigma = power_iteration(matrix, 50);
    assert!(
        (sigma - 0.0).abs() < 1e-10,
        "empty matrix sigma should be 0"
    );
}

#[test]
fn test_power_iteration_single_element() {
    let row0: &[f64] = &[7.0];
    let matrix: &[&[f64]] = &[row0];
    let sigma = power_iteration(matrix, 50);
    assert!(
        (sigma - 7.0).abs() < 1e-6,
        "1x1 matrix [[7]] should have sigma=7, got {sigma}"
    );
}

#[test]
fn test_power_iteration_convergence_improves_with_iterations() {
    // More iterations should give a more accurate answer.
    let row0: &[f64] = &[1.0, 2.0];
    let row1: &[f64] = &[3.0, 4.0];
    let matrix: &[&[f64]] = &[row0, row1];
    // Exact: eigenvalues of A^T A = [[10,14],[14,20]].
    // Trace=30, det=200-196=4. eigenvalues = (30 +/- sqrt(900-16))/2
    // lambda_1 = 29.866..., sigma_max = sqrt(29.866) ~ 5.465
    let sigma_5 = power_iteration(matrix, 5);
    let sigma_50 = power_iteration(matrix, 50);
    let exact = 29.866_f64.sqrt();
    assert!(
        (sigma_50 - exact).abs() <= (sigma_5 - exact).abs() + 1e-10,
        "50 iterations should be at least as accurate as 5"
    );
}

// ---------------------------------------------------------------------------
// Per-layer Lipschitz constants
// ---------------------------------------------------------------------------

#[test]
fn test_compute_layer_lipschitz_identity() {
    let row0: &[f64] = &[1.0, 0.0];
    let row1: &[f64] = &[0.0, 1.0];
    let weight: &[&[f64]] = &[row0, row1];
    let lip = compute_layer_lipschitz(weight, 50);
    assert!(
        (lip - 1.0).abs() < 1e-6,
        "identity Lipschitz constant should be 1.0, got {lip}"
    );
}

#[test]
fn test_compute_layer_lipschitz_scaling() {
    let row0: &[f64] = &[2.0, 0.0];
    let row1: &[f64] = &[0.0, 3.0];
    let weight: &[&[f64]] = &[row0, row1];
    let lip = compute_layer_lipschitz(weight, 50);
    assert!(
        (lip - 3.0).abs() < 1e-6,
        "diag(2,3) Lipschitz constant should be 3.0, got {lip}"
    );
}

#[test]
fn test_compute_relu_lipschitz_is_one() {
    assert!(
        (compute_relu_lipschitz() - 1.0).abs() < f64::EPSILON,
        "ReLU Lipschitz constant must be exactly 1.0"
    );
}

// ---------------------------------------------------------------------------
// Network-level Lipschitz (T32 + T30)
// ---------------------------------------------------------------------------

#[test]
fn test_compute_network_lipschitz_single_linear() {
    let layers = vec![LayerSpec::Linear(vec![vec![2.0, 0.0], vec![0.0, 3.0]])];
    let lip = compute_network_lipschitz(&layers, 50);
    assert!(
        (lip - 3.0).abs() < 1e-6,
        "single linear layer should have lip=3.0, got {lip}"
    );
}

#[test]
fn test_compute_network_lipschitz_linear_relu_linear() {
    // Network: Linear(diag(2,2)) -> ReLU -> Linear(diag(3,3))
    // Lip = 2 * 1 * 3 = 6
    let layers = vec![
        LayerSpec::Linear(vec![vec![2.0, 0.0], vec![0.0, 2.0]]),
        LayerSpec::Relu,
        LayerSpec::Linear(vec![vec![3.0, 0.0], vec![0.0, 3.0]]),
    ];
    let lip = compute_network_lipschitz(&layers, 50);
    assert!(
        (lip - 6.0).abs() < 1e-4,
        "3-layer network lip should be 6.0, got {lip}"
    );
}

#[test]
fn test_compute_network_lipschitz_three_layer_product() {
    // Linear(5*I) -> ReLU -> Linear(2*I) -> ReLU -> Linear(3*I)
    // Product: 5 * 1 * 2 * 1 * 3 = 30
    let eye = |s: f64| vec![vec![s, 0.0], vec![0.0, s]];
    let layers = vec![
        LayerSpec::Linear(eye(5.0)),
        LayerSpec::Relu,
        LayerSpec::Linear(eye(2.0)),
        LayerSpec::Relu,
        LayerSpec::Linear(eye(3.0)),
    ];
    let lip = compute_network_lipschitz(&layers, 50);
    assert!(
        (lip - 30.0).abs() < 1e-3,
        "5-layer network lip should be 30.0, got {lip}"
    );
}

#[test]
fn test_compute_network_lipschitz_empty_network() {
    // Empty layer list: product of zero items = 1.0 (multiplicative identity).
    let layers: Vec<LayerSpec> = vec![];
    let lip = compute_network_lipschitz(&layers, 50);
    assert!(
        (lip - 1.0).abs() < 1e-10,
        "empty network lip should be 1.0 (multiplicative identity), got {lip}"
    );
}

#[test]
fn test_compute_network_lipschitz_relu_only() {
    let layers = vec![LayerSpec::Relu, LayerSpec::Relu, LayerSpec::Relu];
    let lip = compute_network_lipschitz(&layers, 50);
    assert!(
        (lip - 1.0).abs() < 1e-10,
        "relu-only network lip should be 1.0, got {lip}"
    );
}

// ---------------------------------------------------------------------------
// Residual Lipschitz (T33)
// ---------------------------------------------------------------------------

#[test]
fn test_compute_residual_lipschitz_basic() {
    // y = x + f(x) with L_attn=2, L_ffn=3: 1 + 2 + 3 = 6
    let lip = compute_residual_lipschitz(2.0, 3.0);
    assert!(
        (lip - 6.0).abs() < 1e-10,
        "residual lip should be 6.0, got {lip}"
    );
}

#[test]
fn test_compute_residual_lipschitz_zero_branches() {
    // Both branches have zero Lipschitz: identity, 1 + 0 + 0 = 1
    let lip = compute_residual_lipschitz(0.0, 0.0);
    assert!(
        (lip - 1.0).abs() < 1e-10,
        "residual with zero branches should be 1.0, got {lip}"
    );
}

#[test]
fn test_compute_residual_lipschitz_single_branch() {
    // Only attention active (FFN=0): 1 + L_attn
    let lip = compute_residual_lipschitz(4.5, 0.0);
    assert!(
        (lip - 5.5).abs() < 1e-10,
        "single-branch residual lip should be 5.5, got {lip}"
    );
}

// ---------------------------------------------------------------------------
// T30 concrete verification (submultiplicativity)
// ---------------------------------------------------------------------------

#[test]
fn test_verify_lipschitz_compose_valid() {
    // l1=2, l2=3, composed=5 <= 6: valid
    assert!(verify_lipschitz_compose(2.0, 3.0, 5.0));
}

#[test]
fn test_verify_lipschitz_compose_exact() {
    // l1=2, l2=3, composed=6 = l1*l2: valid (tight bound)
    assert!(verify_lipschitz_compose(2.0, 3.0, 6.0));
}

#[test]
fn test_verify_lipschitz_compose_violation() {
    // l1=2, l2=3, composed=7 > 6: invalid
    assert!(!verify_lipschitz_compose(2.0, 3.0, 7.0));
}

#[test]
fn test_verify_lipschitz_compose_zero() {
    // Zero Lipschitz: composed must also be ~0.
    assert!(verify_lipschitz_compose(0.0, 5.0, 0.0));
    assert!(!verify_lipschitz_compose(0.0, 5.0, 1.0));
}

// ---------------------------------------------------------------------------
// Submultiplicativity with concrete matrix products
// ---------------------------------------------------------------------------

#[test]
fn test_submultiplicativity_diagonal_matrices() {
    // A = diag(2, 3), B = diag(4, 5)
    // sigma(A) = 3, sigma(B) = 5
    // AB = diag(8, 15), sigma(AB) = 15
    // Check: sigma(AB) <= sigma(A) * sigma(B) = 15 <= 15. Tight!
    let a = vec![vec![2.0, 0.0], vec![0.0, 3.0]];
    let b = vec![vec![4.0, 0.0], vec![0.0, 5.0]];
    let ab = mat_mul(&a, &b);

    let refs_a: Vec<&[f64]> = a.iter().map(|r| r.as_slice()).collect();
    let refs_b: Vec<&[f64]> = b.iter().map(|r| r.as_slice()).collect();
    let refs_ab: Vec<&[f64]> = ab.iter().map(|r| r.as_slice()).collect();

    let sigma_a = power_iteration(&refs_a, 100);
    let sigma_b = power_iteration(&refs_b, 100);
    let sigma_ab = power_iteration(&refs_ab, 100);

    assert!(
        sigma_ab <= sigma_a * sigma_b + 1e-6,
        "submultiplicativity violated: sigma(AB)={sigma_ab} > sigma(A)*sigma(B)={}",
        sigma_a * sigma_b
    );
    assert!(
        verify_lipschitz_compose(sigma_a, sigma_b, sigma_ab),
        "verify_lipschitz_compose should accept diagonal product"
    );
}

#[test]
fn test_submultiplicativity_general_matrices() {
    // A = [[1, 2], [3, 4]], B = [[5, 6], [7, 8]]
    // AB = [[19, 22], [43, 50]]
    let a = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
    let b = vec![vec![5.0, 6.0], vec![7.0, 8.0]];
    let ab = mat_mul(&a, &b);

    let refs_a: Vec<&[f64]> = a.iter().map(|r| r.as_slice()).collect();
    let refs_b: Vec<&[f64]> = b.iter().map(|r| r.as_slice()).collect();
    let refs_ab: Vec<&[f64]> = ab.iter().map(|r| r.as_slice()).collect();

    let sigma_a = power_iteration(&refs_a, 100);
    let sigma_b = power_iteration(&refs_b, 100);
    let sigma_ab = power_iteration(&refs_ab, 100);

    assert!(
        sigma_ab <= sigma_a * sigma_b + 1e-6,
        "submultiplicativity: sigma(AB)={sigma_ab} > sigma(A)*sigma(B)={}",
        sigma_a * sigma_b
    );
}

#[test]
fn test_submultiplicativity_rotation_times_scaling() {
    // Rotation by pi/4 (orthogonal, sigma=1) times scaling diag(2,5).
    // sigma(product) should be <= 1 * 5 = 5.
    let c = std::f64::consts::FRAC_1_SQRT_2;
    let rot = vec![vec![c, -c], vec![c, c]];
    let scale = vec![vec![2.0, 0.0], vec![0.0, 5.0]];
    let prod = mat_mul(&rot, &scale);

    let refs_rot: Vec<&[f64]> = rot.iter().map(|r| r.as_slice()).collect();
    let refs_scale: Vec<&[f64]> = scale.iter().map(|r| r.as_slice()).collect();
    let refs_prod: Vec<&[f64]> = prod.iter().map(|r| r.as_slice()).collect();

    let sigma_rot = power_iteration(&refs_rot, 100);
    let sigma_scale = power_iteration(&refs_scale, 100);
    let sigma_prod = power_iteration(&refs_prod, 100);

    assert!(
        (sigma_rot - 1.0).abs() < 1e-6,
        "rotation sigma should be 1.0, got {sigma_rot}"
    );
    assert!(
        (sigma_scale - 5.0).abs() < 1e-6,
        "scaling sigma should be 5.0, got {sigma_scale}"
    );
    assert!(
        sigma_prod <= sigma_rot * sigma_scale + 1e-6,
        "submultiplicativity: sigma(RS)={sigma_prod} > sigma(R)*sigma(S)={}",
        sigma_rot * sigma_scale
    );
    // For orthogonal * diagonal, product sigma should equal max diagonal entry.
    assert!(
        (sigma_prod - 5.0).abs() < 1e-6,
        "rotation * scaling sigma should be 5.0, got {sigma_prod}"
    );
}

// ---------------------------------------------------------------------------
// Integration: spectral norm connects to LayerLipschitz spec
// ---------------------------------------------------------------------------

#[test]
fn test_spectral_norm_matches_spec_compose() {
    use super::lipschitz::{LayerLipschitz, LipschitzComposeSpec, LipschitzSource};

    // Compute concrete constants and verify they compose correctly via spec.
    let w1 = [vec![2.0, 0.0], vec![0.0, 2.0]];
    let w2 = [vec![3.0, 0.0], vec![0.0, 3.0]];
    let refs1: Vec<&[f64]> = w1.iter().map(|r| r.as_slice()).collect();
    let refs2: Vec<&[f64]> = w2.iter().map(|r| r.as_slice()).collect();

    let lip1 = compute_layer_lipschitz(&refs1, 50);
    let lip2 = compute_layer_lipschitz(&refs2, 50);

    let l1 = LayerLipschitz::new(lip1, LipschitzSource::SpectralNorm);
    let l2 = LayerLipschitz::new(lip2, LipschitzSource::SpectralNorm);
    let spec = LipschitzComposeSpec::new();
    let composed = spec.compose(&l1, &l2);

    assert!(
        (composed.constant() - 6.0).abs() < 1e-4,
        "spec compose should yield 6.0, got {}",
        composed.constant()
    );
}

#[test]
fn test_mat_mul_basic() {
    let a = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
    let b = vec![vec![5.0, 6.0], vec![7.0, 8.0]];
    let c = mat_mul(&a, &b);
    assert!((c[0][0] - 19.0).abs() < 1e-10);
    assert!((c[0][1] - 22.0).abs() < 1e-10);
    assert!((c[1][0] - 43.0).abs() < 1e-10);
    assert!((c[1][1] - 50.0).abs() < 1e-10);
}

#[test]
fn test_mat_mul_identity() {
    let a = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let b = vec![vec![3.0, 7.0], vec![2.0, 9.0]];
    let c = mat_mul(&a, &b);
    assert!((c[0][0] - 3.0).abs() < 1e-10);
    assert!((c[0][1] - 7.0).abs() < 1e-10);
    assert!((c[1][0] - 2.0).abs() < 1e-10);
    assert!((c[1][1] - 9.0).abs() < 1e-10);
}
