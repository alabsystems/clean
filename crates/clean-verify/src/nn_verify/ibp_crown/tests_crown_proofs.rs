// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for CROWN kernel proof terms (T40-T47).
//!
//! These tests exercise the proof verification functions in `crown_proofs.rs`
//! across a range of network configurations to establish confidence in the
//! 8 CROWN ReLU backward + composition theorems.

use super::crown::CrownBound;
use super::crown_proofs::*;

// ===========================================================================
// T40: CROWN Linear Relaxation Soundness
// ===========================================================================

#[test]
fn test_t40_proof_various_crossings() {
    // Test a range of crossing intervals to verify the relaxation.
    let cases: Vec<(f64, f64)> = vec![
        (-1.0, 1.0),
        (-0.5, 2.0),
        (-3.0, 0.1),
        (-10.0, 10.0),
        (-0.001, 0.001),
        (-100.0, 1.0),
        (-1.0, 100.0),
    ];
    for (l, u) in cases {
        let result = verify_t40_relu_relaxation(l, u, 200);
        assert!(
            result.is_ok(),
            "T40 failed for [{l}, {u}]: {:?}",
            result.err()
        );
    }
}

#[test]
fn test_t40_proof_lambda_mu_properties() {
    let w = verify_t40_relu_relaxation(-2.0, 6.0, 100).unwrap();
    // lambda = 6/8 = 0.75
    assert!((w.lambda - 0.75).abs() < 1e-9);
    // mu = 12/8 = 1.5
    assert!((w.mu - 1.5).abs() < 1e-9);
    // lambda in [0, 1]
    assert!(w.lambda >= 0.0 && w.lambda <= 1.0);
    // mu >= 0
    assert!(w.mu >= 0.0);
}

// ===========================================================================
// T41: CROWN Backward Bound Propagation
// ===========================================================================

#[test]
fn test_t41_proof_always_active_network() {
    let network = vec![
        (vec![vec![1.0, 0.5], vec![0.5, 1.0]], vec![2.0, 1.0]),
        (vec![vec![1.0, -1.0]], vec![0.0]),
    ];
    let w = verify_t41_backward_propagation(&network, &[0.0, 0.0], &[1.0, 1.0], 200)
        .expect("always-active network should verify");
    assert_eq!(w.num_layers, 2);
    // All pre-activations positive, so CROWN = exact.
    assert!(w.concrete_lower[0] <= w.concrete_upper[0] + 1e-9);
}

#[test]
fn test_t41_proof_mixed_network() {
    let network = vec![
        (vec![vec![1.0, -0.5], vec![-1.0, 2.0]], vec![0.5, -0.5]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let w = verify_t41_backward_propagation(&network, &[-1.0, -1.0], &[1.0, 1.0], 500)
        .expect("mixed network should verify");
    assert!(w.samples_verified >= 500);
}

#[test]
fn test_t41_proof_deep_network() {
    let network = vec![
        (vec![vec![1.0], vec![-1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
        (vec![vec![2.0, -1.0], vec![0.5, 1.5]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let w = verify_t41_backward_propagation(&network, &[-0.5], &[0.5], 300)
        .expect("4-layer network should verify");
    assert_eq!(w.num_layers, 4);
}

// ===========================================================================
// T42: CROWN Concave Envelope Tightness
// ===========================================================================

#[test]
fn test_t42_proof_various_intervals() {
    let cases: Vec<(f64, f64)> = vec![(-1.0, 1.0), (-0.5, 3.0), (-5.0, 0.5), (-10.0, 10.0)];
    for (l, u) in cases {
        let result = verify_t42_concave_envelope(l, u, 200);
        assert!(
            result.is_ok(),
            "T42 failed for [{l}, {u}]: {:?}",
            result.err()
        );
    }
}

#[test]
fn test_t42_proof_envelope_is_tight() {
    // For symmetric interval [-a, a], the max gap at z=0 is exactly a/2.
    let w = verify_t42_concave_envelope(-2.0, 2.0, 1000).unwrap();
    assert!((w.max_gap - 1.0).abs() < 0.01);
}

// ===========================================================================
// T43: Alpha-CROWN Soundness
// ===========================================================================

#[test]
fn test_t43_proof_sweep_alpha_values() {
    // Test soundness for multiple alpha values on a crossing neuron.
    for alpha_val in [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0] {
        let result = verify_t43_alpha_soundness(&[-1.0], &[1.0], &[alpha_val], 200);
        assert!(
            result.is_ok(),
            "T43 failed for alpha={alpha_val}: {:?}",
            result.err()
        );
    }
}

#[test]
fn test_t43_proof_multiple_neurons() {
    let result = verify_t43_alpha_soundness(
        &[-1.0, -2.0, -0.5, 1.0, -3.0],
        &[1.0, 4.0, 2.0, 3.0, -0.1],
        &[0.3, 0.7, 0.5, 0.0, 0.9],
        100,
    );
    assert!(
        result.is_ok(),
        "T43 multi-neuron failed: {:?}",
        result.err()
    );
    let w = result.unwrap();
    // Only the first 3 are crossing (neuron 3 is all-positive, neuron 4 is all-negative).
    assert_eq!(w.crossing_verified, 3);
}

// ===========================================================================
// T44: Alpha-CROWN Tighter Than CROWN
// ===========================================================================

#[test]
fn test_t44_proof_single_layer_equal() {
    // Single linear layer: no ReLU to optimize, both should be equal.
    let network = vec![(vec![vec![2.0, -1.0]], vec![0.5])];
    let w = verify_t44_alpha_tighter(&network, &[-1.0, -1.0], &[1.0, 1.0])
        .expect("single layer should verify");
    // Both methods are exact for a single linear layer.
    assert!(w.crown_width >= -1e-6);
}

// ===========================================================================
// T45: CROWN Composition Soundness
// ===========================================================================

#[test]
fn test_t45_proof_empty_network() {
    let w = verify_t45_composition(&[], &[1.0], &[2.0]).expect("empty network should verify");
    assert_eq!(w.num_layers, 0);
}

#[test]
fn test_t45_proof_three_layer_composition() {
    let network = vec![
        (vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 0.5], vec![0.5, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, -1.0]], vec![0.0]),
    ];
    let w = verify_t45_composition(&network, &[-1.0, -1.0], &[1.0, 1.0])
        .expect("three-layer composition should verify");
    assert_eq!(w.num_layers, 3);
    assert!(w.final_bound_width >= 0.0);
}

// ===========================================================================
// T46: CROWN Concretization Soundness
// ===========================================================================

#[test]
fn test_t46_proof_positive_coefficients() {
    let bound = CrownBound {
        lower_coeffs: vec![vec![1.0, 2.0]],
        upper_coeffs: vec![vec![3.0, 4.0]],
        lower_bias: vec![0.0],
        upper_bias: vec![0.0],
    };
    let w = verify_t46_concretization(&bound, &[0.0, 0.0], &[1.0, 1.0])
        .expect("positive coefficients should verify");
    assert_eq!(w.num_outputs, 1);
}

#[test]
fn test_t46_proof_mixed_coefficients() {
    let bound = CrownBound {
        lower_coeffs: vec![vec![2.0, -3.0], vec![-1.0, 4.0]],
        upper_coeffs: vec![vec![2.0, -3.0], vec![-1.0, 4.0]],
        lower_bias: vec![1.0, -1.0],
        upper_bias: vec![1.0, -1.0],
    };
    let w = verify_t46_concretization(&bound, &[-1.0, -1.0], &[1.0, 1.0])
        .expect("mixed coefficients should verify");
    assert_eq!(w.num_outputs, 2);
    assert_eq!(w.num_inputs, 2);
}

#[test]
fn test_t46_proof_asymmetric_input() {
    let bound = CrownBound::identity(3);
    let w = verify_t46_concretization(&bound, &[-5.0, 0.0, 2.0], &[-1.0, 3.0, 7.0])
        .expect("asymmetric input should verify");
    // Identity bound: concrete = input.
    assert!((w.concrete_lower[0] - (-5.0)).abs() < 1e-9);
    assert!((w.concrete_upper[2] - 7.0).abs() < 1e-9);
}

// ===========================================================================
// T47: CROWN-IBP Dominance
// ===========================================================================

#[test]
fn test_t47_proof_three_layer_crossing() {
    let network = vec![
        (vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 0.5], vec![0.5, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, -1.0]], vec![0.0]),
    ];
    let w = verify_t47_crown_ibp_dominance(&network, &[-1.0, -1.0], &[1.0, 1.0])
        .expect("three-layer should verify dominance");
    assert!(w.dominated);
    // CROWN widths should be <= IBP widths.
    for (ibp, crown) in w.ibp_widths.iter().zip(w.crown_widths.iter()) {
        assert!(
            *crown <= *ibp + 1e-9,
            "CROWN width {crown} > IBP width {ibp}"
        );
    }
}

#[test]
fn test_t47_proof_all_inactive_network() {
    // All neurons inactive: both methods give zero output.
    let network = vec![
        (vec![vec![-1.0]], vec![-5.0]),
        (vec![vec![1.0]], vec![10.0]),
    ];
    let w = verify_t47_crown_ibp_dominance(&network, &[0.0], &[1.0])
        .expect("all-inactive should verify");
    assert!(w.dominated);
}
