// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for CROWN backward bound propagation (T40-T42).
//!
//! Tests verify correctness of backward linear propagation, ReLU relaxation,
//! concretization, and end-to-end CROWN tightness vs IBP.

use super::crown::*;
use super::crown_backward::*;
use super::ibp::{IbpCompositionSpec, IbpLinearSpec, IbpReluSpec, Interval};

const EPS: f64 = 1e-9;

fn approx_eq(a: f64, b: f64) -> bool {
    (a - b).abs() < EPS
}

// ---------------------------------------------------------------------------
// CrownBound identity
// ---------------------------------------------------------------------------

#[test]
fn test_crown_bound_identity_dimensions() {
    let b = CrownBound::identity(3);
    assert_eq!(b.num_outputs(), 3);
    assert_eq!(b.num_inputs(), 3);
    assert_eq!(b.lower_bias.len(), 3);
    assert_eq!(b.upper_bias.len(), 3);
}

#[test]
fn test_crown_bound_identity_values() {
    let b = CrownBound::identity(2);
    // Diagonal is 1, off-diagonal is 0
    assert!(approx_eq(b.lower_coeffs[0][0], 1.0));
    assert!(approx_eq(b.lower_coeffs[0][1], 0.0));
    assert!(approx_eq(b.lower_coeffs[1][0], 0.0));
    assert!(approx_eq(b.lower_coeffs[1][1], 1.0));
    // Same for upper
    assert!(approx_eq(b.upper_coeffs[0][0], 1.0));
    assert!(approx_eq(b.upper_coeffs[1][1], 1.0));
    // Bias is zero
    assert!(approx_eq(b.lower_bias[0], 0.0));
    assert!(approx_eq(b.upper_bias[0], 0.0));
}

// ---------------------------------------------------------------------------
// Single linear layer: CROWN = exact
// ---------------------------------------------------------------------------

#[test]
fn test_crown_single_linear_layer_exact() {
    // y = 2x + 1, x in [0, 1] => y in [1, 3]
    let network = vec![(vec![vec![2.0]], vec![1.0])];
    let result = verify_crown_bounds(&network, &[0.0], &[1.0]);
    assert!(approx_eq(result.lower[0], 1.0));
    assert!(approx_eq(result.upper[0], 3.0));
}

#[test]
fn test_crown_single_linear_multi_output() {
    // W = [[1, -1], [-1, 1]], b = [0, 0], x in [-1,1]^2
    let network = vec![(vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0])];
    let result = verify_crown_bounds(&network, &[-1.0, -1.0], &[1.0, 1.0]);
    // y0 = x0 - x1: min at x0=-1,x1=1 => -2, max at x0=1,x1=-1 => 2
    assert!(approx_eq(result.lower[0], -2.0));
    assert!(approx_eq(result.upper[0], 2.0));
    // y1 = -x0 + x1: same range
    assert!(approx_eq(result.lower[1], -2.0));
    assert!(approx_eq(result.upper[1], 2.0));
}

// ---------------------------------------------------------------------------
// Linear + ReLU (always active): CROWN = exact
// ---------------------------------------------------------------------------

#[test]
fn test_crown_linear_relu_always_active() {
    // Layer 1: y = 2x + 3, x in [1, 2] => pre-act [5, 7], all >= 0
    // ReLU is identity => post-act [5, 7]
    // Layer 2 (output): z = 1*y + 0 => [5, 7]
    let network = vec![(vec![vec![2.0]], vec![3.0]), (vec![vec![1.0]], vec![0.0])];
    let result = verify_crown_bounds(&network, &[1.0], &[2.0]);
    assert!(approx_eq(result.lower[0], 5.0));
    assert!(approx_eq(result.upper[0], 7.0));
}

// ---------------------------------------------------------------------------
// Linear + ReLU (always inactive): CROWN gives zero output
// ---------------------------------------------------------------------------

#[test]
fn test_crown_linear_relu_always_inactive() {
    // Layer 1: y = -2x - 3, x in [0, 1] => pre-act [-5, -3], all <= 0
    // ReLU output = 0
    // Layer 2 (output): z = 1*0 + 0 = 0
    let network = vec![(vec![vec![-2.0]], vec![-3.0]), (vec![vec![1.0]], vec![0.0])];
    let result = verify_crown_bounds(&network, &[0.0], &[1.0]);
    assert!(approx_eq(result.lower[0], 0.0));
    assert!(approx_eq(result.upper[0], 0.0));
}

// ---------------------------------------------------------------------------
// Linear + ReLU (crossing): CROWN bounds tighter than IBP
// ---------------------------------------------------------------------------

#[test]
fn test_crown_linear_relu_crossing_tighter_than_ibp() {
    // Layer 1: y = x, x in [-1, 1] => pre-act [-1, 1], crossing
    // Layer 2 (output): z = y + 0
    //
    // IBP: pre-act [-1, 1] -> ReLU -> [0, 1] -> linear -> [0, 1]
    // CROWN: backward with lambda=1/(1-(-1))=0.5, mu=0.5
    //   Upper: 0.5*x + 0.5 => max at x=1: 1.0, so upper=1.0
    //   Lower: alpha=0 for crossing, so lower=0.0
    // Same as IBP for this simple case (single neuron)
    let network = vec![(vec![vec![1.0]], vec![0.0]), (vec![vec![1.0]], vec![0.0])];
    let result = verify_crown_bounds(&network, &[-1.0], &[1.0]);
    // CROWN should give valid bounds
    assert!(result.lower[0] <= EPS); // true value at x=0 is 0
    assert!(result.upper[0] >= 1.0 - EPS); // true value at x=1 is 1
}

#[test]
fn test_crown_crossing_multi_neuron_tighter() {
    // 2-neuron hidden layer with crossing ReLU.
    // Layer 1: W=[[1],[-1]], b=[0,0], x in [-1,1]
    //   pre-act: [(-1,1), (-1,1)] both crossing
    // Layer 2 (output): W=[[1,1]], b=[0]
    //   IBP: ReLU([(-1,1),(-1,1)]) = [(0,1),(0,1)] => output [0,2]
    //   CROWN should produce bounds at least as tight.
    let network = vec![
        (vec![vec![1.0], vec![-1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let crown_result = verify_crown_bounds(&network, &[-1.0], &[1.0]);

    // IBP bounds
    let ibp_linear = IbpLinearSpec::new();
    let ibp_relu = IbpReluSpec::new();
    let ibp_comp = IbpCompositionSpec::new();
    let input = vec![Interval::new(-1.0, 1.0)];
    let w1 = vec![vec![1.0], vec![-1.0]];
    let b1 = vec![0.0, 0.0];
    let hidden = ibp_comp.compose_linear_relu(&ibp_linear, &ibp_relu, &w1, &b1, &input);
    let w2 = vec![vec![1.0, 1.0]];
    let b2 = vec![0.0];
    let ibp_output = ibp_linear.propagate(&w2, &b2, &hidden);

    // CROWN bounds must be valid (contain true outputs)
    assert!(crown_result.lower[0] <= ibp_output[0].upper + EPS);
    assert!(crown_result.upper[0] >= ibp_output[0].lower - EPS);

    // CROWN bounds should be at least as tight as IBP
    assert!(
        crown_result.lower[0] >= ibp_output[0].lower - EPS,
        "CROWN lower {} should be >= IBP lower {}",
        crown_result.lower[0],
        ibp_output[0].lower
    );
    assert!(
        crown_result.upper[0] <= ibp_output[0].upper + EPS,
        "CROWN upper {} should be <= IBP upper {}",
        crown_result.upper[0],
        ibp_output[0].upper
    );
}

// ---------------------------------------------------------------------------
// 2-layer network: CROWN vs IBP comparison
// ---------------------------------------------------------------------------

#[test]
fn test_crown_two_layer_vs_ibp() {
    // 2-layer network: input -> linear+relu -> linear (output)
    let w1 = vec![vec![1.0, 0.5], vec![-0.5, 1.0]];
    let b1 = vec![0.0, 0.0];
    let w2 = vec![vec![1.0, -1.0]];
    let b2 = vec![0.0];
    let network = vec![(w1.clone(), b1.clone()), (w2.clone(), b2.clone())];
    let input_lower = vec![-1.0, -1.0];
    let input_upper = vec![1.0, 1.0];

    let crown_result = verify_crown_bounds(&network, &input_lower, &input_upper);

    // IBP for comparison
    let ibp_linear = IbpLinearSpec::new();
    let ibp_relu = IbpReluSpec::new();
    let ibp_comp = IbpCompositionSpec::new();
    let input = vec![Interval::new(-1.0, 1.0), Interval::new(-1.0, 1.0)];
    let hidden = ibp_comp.compose_linear_relu(&ibp_linear, &ibp_relu, &w1, &b1, &input);
    let ibp_output = ibp_linear.propagate(&w2, &b2, &hidden);

    // CROWN must be at least as tight
    assert!(
        crown_result.lower[0] >= ibp_output[0].lower - EPS,
        "CROWN lower {} >= IBP lower {}",
        crown_result.lower[0],
        ibp_output[0].lower
    );
    assert!(
        crown_result.upper[0] <= ibp_output[0].upper + EPS,
        "CROWN upper {} <= IBP upper {}",
        crown_result.upper[0],
        ibp_output[0].upper
    );
}

// ---------------------------------------------------------------------------
// Identity weight: CROWN preserves input bounds
// ---------------------------------------------------------------------------

#[test]
fn test_crown_identity_weight_preserves_bounds() {
    // Single linear layer with identity weight, no bias
    let network = vec![(vec![vec![1.0, 0.0], vec![0.0, 1.0]], vec![0.0, 0.0])];
    let result = verify_crown_bounds(&network, &[-3.0, 2.0], &[1.0, 5.0]);
    assert!(approx_eq(result.lower[0], -3.0));
    assert!(approx_eq(result.upper[0], 1.0));
    assert!(approx_eq(result.lower[1], 2.0));
    assert!(approx_eq(result.upper[1], 5.0));
}

// ---------------------------------------------------------------------------
// Negative weights: correct backward propagation
// ---------------------------------------------------------------------------

#[test]
fn test_crown_negative_weights_backward() {
    // y = -2x + 1, x in [0, 1] => y in [-1, 1]
    let network = vec![(vec![vec![-2.0]], vec![1.0])];
    let result = verify_crown_bounds(&network, &[0.0], &[1.0]);
    assert!(approx_eq(result.lower[0], -1.0));
    assert!(approx_eq(result.upper[0], 1.0));
}

#[test]
fn test_crown_all_negative_weights() {
    // W = [[-1, -2]], b = [0], x in [1, 2]^2
    // y = -x0 - 2*x1, min at x0=2,x1=2 => -6, max at x0=1,x1=1 => -3
    let network = vec![(vec![vec![-1.0, -2.0]], vec![0.0])];
    let result = verify_crown_bounds(&network, &[1.0, 1.0], &[2.0, 2.0]);
    assert!(approx_eq(result.lower[0], -6.0));
    assert!(approx_eq(result.upper[0], -3.0));
}

// ---------------------------------------------------------------------------
// Concretization: symbolic -> concrete matches hand calculation
// ---------------------------------------------------------------------------

#[test]
fn test_concretize_positive_coeffs() {
    // lower = 2*x + 1, upper = 3*x + 2, x in [0, 1]
    // concrete_lower = 1 + 2*0 = 1, concrete_upper = 2 + 3*1 = 5
    let bound = CrownBound {
        lower_coeffs: vec![vec![2.0]],
        upper_coeffs: vec![vec![3.0]],
        lower_bias: vec![1.0],
        upper_bias: vec![2.0],
    };
    let (cl, cu) = crown_concretize(&bound, &[0.0], &[1.0]);
    assert!(approx_eq(cl[0], 1.0));
    assert!(approx_eq(cu[0], 5.0));
}

#[test]
fn test_concretize_negative_coeffs() {
    // lower = -2*x + 1, x in [0, 1]
    // concrete_lower = 1 + (-2)*1 = -1 (negative coeff uses upper input)
    let bound = CrownBound {
        lower_coeffs: vec![vec![-2.0]],
        upper_coeffs: vec![vec![-2.0]],
        lower_bias: vec![1.0],
        upper_bias: vec![1.0],
    };
    let (cl, cu) = crown_concretize(&bound, &[0.0], &[1.0]);
    assert!(approx_eq(cl[0], -1.0));
    assert!(approx_eq(cu[0], 1.0));
}

#[test]
fn test_concretize_mixed_coeffs() {
    // lower = 2*x0 - 3*x1 + 1, x0 in [0,1], x1 in [0,1]
    // concrete_lower = 1 + 2*0 + (-3)*1 = -2
    // upper = 2*x0 - 3*x1 + 1
    // concrete_upper = 1 + 2*1 + (-3)*0 = 3
    let bound = CrownBound {
        lower_coeffs: vec![vec![2.0, -3.0]],
        upper_coeffs: vec![vec![2.0, -3.0]],
        lower_bias: vec![1.0],
        upper_bias: vec![1.0],
    };
    let (cl, cu) = crown_concretize(&bound, &[0.0, 0.0], &[1.0, 1.0]);
    assert!(approx_eq(cl[0], -2.0));
    assert!(approx_eq(cu[0], 3.0));
}

#[test]
fn test_concretize_identity_bound() {
    // Identity bound: f(x) = x, x in [-1, 2]
    let bound = CrownBound::identity(1);
    let (cl, cu) = crown_concretize(&bound, &[-1.0], &[2.0]);
    assert!(approx_eq(cl[0], -1.0));
    assert!(approx_eq(cu[0], 2.0));
}

// ---------------------------------------------------------------------------
// crown_linear_backward
// ---------------------------------------------------------------------------

#[test]
fn test_linear_backward_identity_weight() {
    // Backward through identity: coefficients unchanged
    let bound = CrownBound::identity(2);
    let weight = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let bias = vec![0.0, 0.0];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 1.0));
    assert!(approx_eq(result.lower_coeffs[0][1], 0.0));
    assert!(approx_eq(result.lower_coeffs[1][0], 0.0));
    assert!(approx_eq(result.lower_coeffs[1][1], 1.0));
    assert!(approx_eq(result.lower_bias[0], 0.0));
    assert!(approx_eq(result.upper_bias[1], 0.0));
}

#[test]
fn test_linear_backward_scaling() {
    // y = 3*x + 2, backward from identity bound on y
    // Result: coeffs = [[3]], bias = [2]
    let bound = CrownBound::identity(1);
    let weight = vec![vec![3.0]];
    let bias = vec![2.0];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 3.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 3.0));
    assert!(approx_eq(result.lower_bias[0], 2.0));
    assert!(approx_eq(result.upper_bias[0], 2.0));
}

#[test]
fn test_linear_backward_bias_absorption() {
    // Weight = [[1]], bias = [5], identity bound
    // After backward: new bias should be 5
    let bound = CrownBound::identity(1);
    let weight = vec![vec![1.0]];
    let bias = vec![5.0];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert!(approx_eq(result.lower_bias[0], 5.0));
    assert!(approx_eq(result.upper_bias[0], 5.0));
}

// ---------------------------------------------------------------------------
// crown_relu_backward
// ---------------------------------------------------------------------------

#[test]
fn test_relu_backward_always_active() {
    // Pre-act bounds [1, 3]: always active => identity
    let bound = CrownBound::identity(1);
    let result = crown_relu_backward(&[1.0], &[3.0], &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 1.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 1.0));
    assert!(approx_eq(result.lower_bias[0], 0.0));
    assert!(approx_eq(result.upper_bias[0], 0.0));
}

#[test]
fn test_relu_backward_always_inactive() {
    // Pre-act bounds [-3, -1]: always inactive => zero
    let bound = CrownBound::identity(1);
    let result = crown_relu_backward(&[-3.0], &[-1.0], &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 0.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 0.0));
    assert!(approx_eq(result.lower_bias[0], 0.0));
    assert!(approx_eq(result.upper_bias[0], 0.0));
}

#[test]
fn test_relu_backward_crossing() {
    // Pre-act bounds [-1, 1]: crossing
    // lambda = 1/(1-(-1)) = 0.5, mu = 1*1/(1-(-1)) = 0.5
    // Upper coeff (positive): 1.0 * 0.5 = 0.5, bias += 1.0 * 0.5 = 0.5
    // Lower coeff (positive, alpha=0): 0.0
    let bound = CrownBound::identity(1);
    let result = crown_relu_backward(&[-1.0], &[1.0], &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 0.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 0.5));
    assert!(approx_eq(result.lower_bias[0], 0.0));
    assert!(approx_eq(result.upper_bias[0], 0.5));
}

#[test]
fn test_relu_backward_crossing_asymmetric() {
    // Pre-act bounds [-2, 4]: crossing
    // lambda = 4/(4-(-2)) = 4/6 = 2/3
    // mu = 2*4/6 = 4/3
    let bound = CrownBound::identity(1);
    let result = crown_relu_backward(&[-2.0], &[4.0], &bound);
    let lambda = 4.0 / 6.0;
    let mu = 8.0 / 6.0;
    assert!(approx_eq(result.upper_coeffs[0][0], lambda));
    assert!(approx_eq(result.upper_bias[0], mu));
    assert!(approx_eq(result.lower_coeffs[0][0], 0.0));
}

// ---------------------------------------------------------------------------
// Empty / degenerate networks
// ---------------------------------------------------------------------------

#[test]
fn test_crown_empty_network() {
    let result = verify_crown_bounds(&[], &[1.0, 2.0], &[3.0, 4.0]);
    assert!(approx_eq(result.lower[0], 1.0));
    assert!(approx_eq(result.upper[0], 3.0));
    assert!(approx_eq(result.lower[1], 2.0));
    assert!(approx_eq(result.upper[1], 4.0));
}

#[test]
fn test_crown_point_input() {
    // Point input [2, 2], single linear layer
    let network = vec![(vec![vec![3.0]], vec![1.0])];
    let result = verify_crown_bounds(&network, &[2.0], &[2.0]);
    // y = 3*2 + 1 = 7
    assert!(approx_eq(result.lower[0], 7.0));
    assert!(approx_eq(result.upper[0], 7.0));
}

// ---------------------------------------------------------------------------
// Soundness: CROWN bounds contain true outputs for random concrete inputs
// ---------------------------------------------------------------------------

#[test]
fn test_crown_soundness_concrete_samples() {
    // 2-layer network
    let w1 = vec![vec![1.0, -0.5], vec![-1.0, 2.0]];
    let b1 = vec![0.5, -0.5];
    let w2 = vec![vec![1.0, 1.0]];
    let b2 = vec![0.0];
    let network = vec![(w1.clone(), b1.clone()), (w2.clone(), b2.clone())];
    let il = vec![-1.0, -1.0];
    let iu = vec![1.0, 1.0];

    let crown_result = verify_crown_bounds(&network, &il, &iu);

    // Sample concrete inputs and verify they fall within CROWN bounds
    let samples: Vec<[f64; 2]> = vec![
        [0.0, 0.0],
        [-1.0, -1.0],
        [1.0, 1.0],
        [-1.0, 1.0],
        [1.0, -1.0],
        [0.5, -0.5],
    ];

    for sample in &samples {
        // Forward pass
        let h0 = w1[0][0] * sample[0] + w1[0][1] * sample[1] + b1[0];
        let h1 = w1[1][0] * sample[0] + w1[1][1] * sample[1] + b1[1];
        let r0 = h0.max(0.0);
        let r1 = h1.max(0.0);
        let y = w2[0][0] * r0 + w2[0][1] * r1 + b2[0];

        assert!(
            y >= crown_result.lower[0] - EPS,
            "sample {:?}: y={} < crown_lower={}",
            sample,
            y,
            crown_result.lower[0]
        );
        assert!(
            y <= crown_result.upper[0] + EPS,
            "sample {:?}: y={} > crown_upper={}",
            sample,
            y,
            crown_result.upper[0]
        );
    }
}

// ---------------------------------------------------------------------------
// CROWN tightness: should never be looser than IBP
// ---------------------------------------------------------------------------

#[test]
fn test_crown_tightness_vs_ibp_always_active_network() {
    // All pre-activations positive: CROWN = exact = IBP
    let w1 = vec![vec![1.0], vec![0.5]];
    let b1 = vec![2.0, 1.0];
    let w2 = vec![vec![1.0, 1.0]];
    let b2 = vec![0.0];
    let network = vec![(w1.clone(), b1.clone()), (w2.clone(), b2.clone())];

    // x in [0, 1] => pre-act1 in [2, 3], pre-act2 in [1, 1.5], all positive
    let crown_result = verify_crown_bounds(&network, &[0.0], &[1.0]);

    let ibp_linear = IbpLinearSpec::new();
    let ibp_relu = IbpReluSpec::new();
    let ibp_comp = IbpCompositionSpec::new();
    let input = vec![Interval::new(0.0, 1.0)];
    let hidden = ibp_comp.compose_linear_relu(&ibp_linear, &ibp_relu, &w1, &b1, &input);
    let ibp_output = ibp_linear.propagate(&w2, &b2, &hidden);

    // Both should give exact bounds
    assert!(approx_eq(crown_result.lower[0], ibp_output[0].lower));
    assert!(approx_eq(crown_result.upper[0], ibp_output[0].upper));
}

#[test]
fn test_crown_result_valid_ordering() {
    // Verify lower <= upper for all outputs
    let w1 = vec![vec![2.0, -1.0], vec![-1.0, 3.0], vec![0.5, 0.5]];
    let b1 = vec![0.0, 0.0, 0.0];
    let w2 = vec![vec![1.0, -1.0, 0.5], vec![-0.5, 1.0, -1.0]];
    let b2 = vec![1.0, -1.0];
    let network = vec![(w1, b1), (w2, b2)];

    let result = verify_crown_bounds(&network, &[-2.0, -2.0], &[2.0, 2.0]);
    for i in 0..result.lower.len() {
        assert!(
            result.lower[i] <= result.upper[i] + EPS,
            "output {}: lower {} > upper {}",
            i,
            result.lower[i],
            result.upper[i]
        );
    }
}
