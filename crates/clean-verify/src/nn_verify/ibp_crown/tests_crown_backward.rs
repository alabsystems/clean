// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dedicated tests for `crown_backward.rs`: `crown_linear_backward`,
//! `crown_relu_backward`, and `verify_crown_bounds`.

use super::crown::{crown_concretize, CrownBound};
use super::crown_backward::{crown_linear_backward, crown_relu_backward, verify_crown_bounds};

const EPS: f64 = 1e-9;

fn approx_eq(a: f64, b: f64) -> bool {
    (a - b).abs() < EPS
}

// ===========================================================================
// crown_linear_backward — identity weight
// ===========================================================================

#[test]
fn test_linear_backward_identity_2x2_preserves_coeffs() {
    let bound = CrownBound::identity(2);
    let weight = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let bias = vec![0.0, 0.0];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert_eq!(result.num_outputs(), 2);
    assert_eq!(result.num_inputs(), 2);
    for i in 0..2 {
        for j in 0..2 {
            let expected = if i == j { 1.0 } else { 0.0 };
            assert!(approx_eq(result.lower_coeffs[i][j], expected));
            assert!(approx_eq(result.upper_coeffs[i][j], expected));
        }
        assert!(approx_eq(result.lower_bias[i], 0.0));
        assert!(approx_eq(result.upper_bias[i], 0.0));
    }
}

// ===========================================================================
// crown_linear_backward — scalar scaling
// ===========================================================================

#[test]
fn test_linear_backward_scalar_scaling_positive() {
    let bound = CrownBound::identity(1);
    let weight = vec![vec![5.0]];
    let bias = vec![0.0];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 5.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 5.0));
}

#[test]
fn test_linear_backward_scalar_scaling_negative() {
    let bound = CrownBound::identity(1);
    let weight = vec![vec![-3.0]];
    let bias = vec![0.0];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], -3.0));
    assert!(approx_eq(result.upper_coeffs[0][0], -3.0));
}

// ===========================================================================
// crown_linear_backward — bias absorption
// ===========================================================================

#[test]
fn test_linear_backward_bias_absorbed_into_output() {
    let bound = CrownBound::identity(1);
    let weight = vec![vec![1.0]];
    let bias = vec![7.5];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert!(approx_eq(result.lower_bias[0], 7.5));
    assert!(approx_eq(result.upper_bias[0], 7.5));
}

#[test]
fn test_linear_backward_bias_negative() {
    let bound = CrownBound::identity(1);
    let weight = vec![vec![2.0]];
    let bias = vec![-4.0];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert!(approx_eq(result.lower_bias[0], -4.0));
    assert!(approx_eq(result.upper_bias[0], -4.0));
    assert!(approx_eq(result.lower_coeffs[0][0], 2.0));
}

// ===========================================================================
// crown_linear_backward — multi-output matrix product
// ===========================================================================

#[test]
fn test_linear_backward_2x3_matrix_product() {
    // Bound: identity 2x2 (output dim = 2, referencing 2 intermediate neurons)
    // Weight: 2x3 (2 intermediate neurons from 3 inputs)
    // After backward: should have 2x3 coeffs
    let bound = CrownBound::identity(2);
    let weight = vec![vec![1.0, 2.0, 3.0], vec![4.0, 5.0, 6.0]];
    let bias = vec![10.0, 20.0];
    let result = crown_linear_backward(&weight, &bias, &bound);

    assert_eq!(result.num_outputs(), 2);
    assert_eq!(result.num_inputs(), 3);

    // Row 0 of identity * W = row 0 of W
    assert!(approx_eq(result.lower_coeffs[0][0], 1.0));
    assert!(approx_eq(result.lower_coeffs[0][1], 2.0));
    assert!(approx_eq(result.lower_coeffs[0][2], 3.0));
    // Row 1 of identity * W = row 1 of W
    assert!(approx_eq(result.lower_coeffs[1][0], 4.0));
    assert!(approx_eq(result.lower_coeffs[1][1], 5.0));
    assert!(approx_eq(result.lower_coeffs[1][2], 6.0));

    // Bias absorbed from identity: lb[0] = 0 + 1*10 + 0*20 = 10
    assert!(approx_eq(result.lower_bias[0], 10.0));
    assert!(approx_eq(result.lower_bias[1], 20.0));
}

#[test]
fn test_linear_backward_nonidentity_bound_matrix_product() {
    // Bound: 1 output, 2 intermediate, lower_coeffs = [[2, -1]], upper_coeffs = [[1, 3]]
    let bound = CrownBound {
        lower_coeffs: vec![vec![2.0, -1.0]],
        upper_coeffs: vec![vec![1.0, 3.0]],
        lower_bias: vec![0.5],
        upper_bias: vec![-0.5],
    };
    // Weight: 2x2 (2 intermediate from 2 inputs)
    let weight = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let bias = vec![0.0, 0.0];
    let result = crown_linear_backward(&weight, &bias, &bound);

    // With identity weight, coeffs pass through unchanged
    assert!(approx_eq(result.lower_coeffs[0][0], 2.0));
    assert!(approx_eq(result.lower_coeffs[0][1], -1.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 1.0));
    assert!(approx_eq(result.upper_coeffs[0][1], 3.0));
    assert!(approx_eq(result.lower_bias[0], 0.5));
    assert!(approx_eq(result.upper_bias[0], -0.5));
}

#[test]
fn test_linear_backward_general_matrix_product() {
    // Bound: 1 output referencing 2 intermediates, coeffs = [[2, 3]]
    // Weight: 2x2 = [[1, 4], [2, 5]], bias = [0, 0]
    // new_coeffs[0][j] = sum_k coeffs[0][k] * weight[k][j]
    //   j=0: 2*1 + 3*2 = 8
    //   j=1: 2*4 + 3*5 = 23
    let bound = CrownBound {
        lower_coeffs: vec![vec![2.0, 3.0]],
        upper_coeffs: vec![vec![2.0, 3.0]],
        lower_bias: vec![0.0],
        upper_bias: vec![0.0],
    };
    let weight = vec![vec![1.0, 4.0], vec![2.0, 5.0]];
    let bias = vec![0.0, 0.0];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 8.0));
    assert!(approx_eq(result.lower_coeffs[0][1], 23.0));
}

#[test]
fn test_linear_backward_bias_scaled_by_coeffs() {
    // Bound coeffs = [[3]], bias layer = [2]
    // new_bias = 0 + 3 * 2 = 6
    let bound = CrownBound {
        lower_coeffs: vec![vec![3.0]],
        upper_coeffs: vec![vec![-1.0]],
        lower_bias: vec![1.0],
        upper_bias: vec![2.0],
    };
    let weight = vec![vec![1.0]];
    let bias = vec![2.0];
    let result = crown_linear_backward(&weight, &bias, &bound);
    // lower_bias = 1.0 + 3.0 * 2.0 = 7.0
    assert!(approx_eq(result.lower_bias[0], 7.0));
    // upper_bias = 2.0 + (-1.0) * 2.0 = 0.0
    assert!(approx_eq(result.upper_bias[0], 0.0));
}

// ===========================================================================
// crown_linear_backward — zero weight
// ===========================================================================

#[test]
fn test_linear_backward_zero_weight() {
    let bound = CrownBound::identity(1);
    let weight = vec![vec![0.0]];
    let bias = vec![3.0];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 0.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 0.0));
    assert!(approx_eq(result.lower_bias[0], 3.0));
    assert!(approx_eq(result.upper_bias[0], 3.0));
}

// ===========================================================================
// crown_linear_backward — empty weight
// ===========================================================================

#[test]
fn test_linear_backward_empty_weight_zero_in_features() {
    // Weight has rows but each row is empty (0 in_features)
    let bound = CrownBound::identity(1);
    let weight: Vec<Vec<f64>> = vec![vec![]];
    let bias = vec![5.0];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert_eq!(result.num_inputs(), 0);
    assert!(approx_eq(result.lower_bias[0], 5.0));
}

// ===========================================================================
// crown_relu_backward — always active (l >= 0)
// ===========================================================================

#[test]
fn test_relu_backward_always_active_identity_passthrough() {
    let bound = CrownBound::identity(1);
    let result = crown_relu_backward(&[2.0], &[5.0], &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 1.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 1.0));
    assert!(approx_eq(result.lower_bias[0], 0.0));
    assert!(approx_eq(result.upper_bias[0], 0.0));
}

#[test]
fn test_relu_backward_active_at_zero_boundary() {
    // l = 0, u = 1: l >= 0, so always active
    let bound = CrownBound::identity(1);
    let result = crown_relu_backward(&[0.0], &[1.0], &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 1.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 1.0));
}

#[test]
fn test_relu_backward_active_preserves_nonidentity_coeffs() {
    let bound = CrownBound {
        lower_coeffs: vec![vec![3.0]],
        upper_coeffs: vec![vec![-2.0]],
        lower_bias: vec![1.0],
        upper_bias: vec![2.0],
    };
    let result = crown_relu_backward(&[1.0], &[5.0], &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 3.0));
    assert!(approx_eq(result.upper_coeffs[0][0], -2.0));
    assert!(approx_eq(result.lower_bias[0], 1.0));
    assert!(approx_eq(result.upper_bias[0], 2.0));
}

// ===========================================================================
// crown_relu_backward — always inactive (u <= 0)
// ===========================================================================

#[test]
fn test_relu_backward_always_inactive_zeros_coeffs() {
    let bound = CrownBound::identity(1);
    let result = crown_relu_backward(&[-5.0], &[-1.0], &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 0.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 0.0));
    assert!(approx_eq(result.lower_bias[0], 0.0));
    assert!(approx_eq(result.upper_bias[0], 0.0));
}

#[test]
fn test_relu_backward_inactive_at_zero_boundary() {
    // l = -1, u = 0: u <= 0, so always inactive
    let bound = CrownBound::identity(1);
    let result = crown_relu_backward(&[-1.0], &[0.0], &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 0.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 0.0));
}

#[test]
fn test_relu_backward_inactive_zeros_nonidentity_coeffs() {
    let bound = CrownBound {
        lower_coeffs: vec![vec![10.0]],
        upper_coeffs: vec![vec![-7.0]],
        lower_bias: vec![3.0],
        upper_bias: vec![4.0],
    };
    let result = crown_relu_backward(&[-3.0], &[-1.0], &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 0.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 0.0));
    // Bias unchanged (no intercept contribution)
    assert!(approx_eq(result.lower_bias[0], 3.0));
    assert!(approx_eq(result.upper_bias[0], 4.0));
}

// ===========================================================================
// crown_relu_backward — crossing (l < 0 < u)
// ===========================================================================

#[test]
fn test_relu_backward_crossing_symmetric() {
    // l = -1, u = 1 => lambda = 0.5, mu = 0.5
    let bound = CrownBound::identity(1);
    let result = crown_relu_backward(&[-1.0], &[1.0], &bound);
    // Lower coeff positive => alpha=0 => lower_coeff = 0
    assert!(approx_eq(result.lower_coeffs[0][0], 0.0));
    assert!(approx_eq(result.lower_bias[0], 0.0));
    // Upper coeff positive => upper relaxation => 0.5, bias += 0.5
    assert!(approx_eq(result.upper_coeffs[0][0], 0.5));
    assert!(approx_eq(result.upper_bias[0], 0.5));
}

#[test]
fn test_relu_backward_crossing_asymmetric_wide_positive() {
    // l = -1, u = 3 => lambda = 3/4, mu = 3/4
    let bound = CrownBound::identity(1);
    let result = crown_relu_backward(&[-1.0], &[3.0], &bound);
    let lambda = 3.0 / 4.0;
    let mu = 3.0 / 4.0;
    assert!(approx_eq(result.lower_coeffs[0][0], 0.0));
    assert!(approx_eq(result.upper_coeffs[0][0], lambda));
    assert!(approx_eq(result.upper_bias[0], mu));
}

#[test]
fn test_relu_backward_crossing_asymmetric_wide_negative() {
    // l = -4, u = 1 => lambda = 1/5, mu = 4/5
    let bound = CrownBound::identity(1);
    let result = crown_relu_backward(&[-4.0], &[1.0], &bound);
    let lambda = 1.0 / 5.0;
    let mu = 4.0 / 5.0;
    assert!(approx_eq(result.upper_coeffs[0][0], lambda));
    assert!(approx_eq(result.upper_bias[0], mu));
}

#[test]
fn test_relu_backward_crossing_negative_lower_coeff() {
    // Negative lower coeff: wants ReLU large => upper relaxation
    let bound = CrownBound {
        lower_coeffs: vec![vec![-2.0]],
        upper_coeffs: vec![vec![1.0]],
        lower_bias: vec![0.0],
        upper_bias: vec![0.0],
    };
    // l = -1, u = 1 => lambda = 0.5, mu = 0.5
    let result = crown_relu_backward(&[-1.0], &[1.0], &bound);
    // Lower coeff negative => use upper relaxation: -2 * 0.5 = -1.0
    assert!(approx_eq(result.lower_coeffs[0][0], -1.0));
    // Lower bias += -2 * 0.5 = -1.0
    assert!(approx_eq(result.lower_bias[0], -1.0));
    // Upper coeff positive => upper relaxation: 1 * 0.5 = 0.5
    assert!(approx_eq(result.upper_coeffs[0][0], 0.5));
    assert!(approx_eq(result.upper_bias[0], 0.5));
}

#[test]
fn test_relu_backward_crossing_negative_upper_coeff() {
    // Negative upper coeff: wants ReLU small => alpha=0
    let bound = CrownBound {
        lower_coeffs: vec![vec![1.0]],
        upper_coeffs: vec![vec![-3.0]],
        lower_bias: vec![0.0],
        upper_bias: vec![0.0],
    };
    // l = -1, u = 1
    let result = crown_relu_backward(&[-1.0], &[1.0], &bound);
    // Lower coeff positive => alpha=0
    assert!(approx_eq(result.lower_coeffs[0][0], 0.0));
    assert!(approx_eq(result.lower_bias[0], 0.0));
    // Upper coeff negative => alpha=0
    assert!(approx_eq(result.upper_coeffs[0][0], 0.0));
    assert!(approx_eq(result.upper_bias[0], 0.0));
}

#[test]
fn test_relu_backward_crossing_both_negative_coeffs() {
    let bound = CrownBound {
        lower_coeffs: vec![vec![-2.0]],
        upper_coeffs: vec![vec![-3.0]],
        lower_bias: vec![0.0],
        upper_bias: vec![0.0],
    };
    // l = -2, u = 4 => lambda = 4/6 = 2/3, mu = 8/6 = 4/3
    let lambda = 4.0 / 6.0;
    let mu = 8.0 / 6.0;
    let result = crown_relu_backward(&[-2.0], &[4.0], &bound);
    // Lower coeff negative => upper relaxation: -2 * 2/3 = -4/3
    assert!(approx_eq(result.lower_coeffs[0][0], -2.0 * lambda));
    assert!(approx_eq(result.lower_bias[0], -2.0 * mu));
    // Upper coeff negative => alpha=0
    assert!(approx_eq(result.upper_coeffs[0][0], 0.0));
    assert!(approx_eq(result.upper_bias[0], 0.0));
}

// ===========================================================================
// crown_relu_backward — multi-neuron mixed cases
// ===========================================================================

#[test]
fn test_relu_backward_multi_neuron_mixed() {
    // 2 output neurons, 3 intermediate neurons
    // Neuron 0: always active (l=1, u=3)
    // Neuron 1: always inactive (l=-2, u=-1)
    // Neuron 2: crossing (l=-1, u=2) => lambda=2/3, mu=2/3
    let bound = CrownBound {
        lower_coeffs: vec![vec![1.0, 2.0, 3.0], vec![-1.0, -2.0, -3.0]],
        upper_coeffs: vec![vec![1.0, 2.0, 3.0], vec![-1.0, -2.0, -3.0]],
        lower_bias: vec![0.0, 0.0],
        upper_bias: vec![0.0, 0.0],
    };
    let lower = vec![1.0, -2.0, -1.0];
    let upper = vec![3.0, -1.0, 2.0];
    let result = crown_relu_backward(&lower, &upper, &bound);

    let lambda = 2.0 / 3.0;
    let mu = 2.0 / 3.0;

    // Output 0:
    //   Neuron 0 active: coeff unchanged (1.0)
    assert!(approx_eq(result.lower_coeffs[0][0], 1.0));
    //   Neuron 1 inactive: zeroed
    assert!(approx_eq(result.lower_coeffs[0][1], 0.0));
    //   Neuron 2 crossing, lower_coeff=3.0 (positive) => alpha=0
    assert!(approx_eq(result.lower_coeffs[0][2], 0.0));

    // Output 1:
    //   Neuron 0 active: coeff unchanged (-1.0)
    assert!(approx_eq(result.lower_coeffs[1][0], -1.0));
    //   Neuron 1 inactive: zeroed
    assert!(approx_eq(result.lower_coeffs[1][1], 0.0));
    //   Neuron 2 crossing, lower_coeff=-3.0 (negative) => upper relaxation
    assert!(approx_eq(result.lower_coeffs[1][2], -3.0 * lambda));
    assert!(approx_eq(result.lower_bias[1], -3.0 * mu));
}

// ===========================================================================
// crown_relu_backward — zero coefficient edge case
// ===========================================================================

#[test]
fn test_relu_backward_crossing_zero_coeff() {
    // Coeff = 0 => 0 >= 0, so positive branch: alpha=0 for lower, lambda for upper
    // But 0 * anything = 0 anyway
    let bound = CrownBound {
        lower_coeffs: vec![vec![0.0]],
        upper_coeffs: vec![vec![0.0]],
        lower_bias: vec![5.0],
        upper_bias: vec![6.0],
    };
    let result = crown_relu_backward(&[-1.0], &[1.0], &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 0.0));
    assert!(approx_eq(result.upper_coeffs[0][0], 0.0));
    assert!(approx_eq(result.lower_bias[0], 5.0));
    assert!(approx_eq(result.upper_bias[0], 6.0));
}

// ===========================================================================
// verify_crown_bounds — empty network
// ===========================================================================

#[test]
fn test_verify_crown_bounds_empty_network_passthrough() {
    let result = verify_crown_bounds(&[], &[1.0, 2.0, 3.0], &[4.0, 5.0, 6.0]);
    assert_eq!(result.lower, vec![1.0, 2.0, 3.0]);
    assert_eq!(result.upper, vec![4.0, 5.0, 6.0]);
}

#[test]
fn test_verify_crown_bounds_empty_network_single_element() {
    let result = verify_crown_bounds(&[], &[42.0], &[42.0]);
    assert!(approx_eq(result.lower[0], 42.0));
    assert!(approx_eq(result.upper[0], 42.0));
}

// ===========================================================================
// verify_crown_bounds — single linear layer (no ReLU)
// ===========================================================================

#[test]
fn test_verify_crown_single_layer_positive_weight() {
    // y = 3x + 1, x in [0, 2] => y in [1, 7]
    let network = vec![(vec![vec![3.0]], vec![1.0])];
    let result = verify_crown_bounds(&network, &[0.0], &[2.0]);
    assert!(approx_eq(result.lower[0], 1.0));
    assert!(approx_eq(result.upper[0], 7.0));
}

#[test]
fn test_verify_crown_single_layer_negative_weight() {
    // y = -2x + 5, x in [1, 3] => y in [-1, 3]
    let network = vec![(vec![vec![-2.0]], vec![5.0])];
    let result = verify_crown_bounds(&network, &[1.0], &[3.0]);
    assert!(approx_eq(result.lower[0], -1.0));
    assert!(approx_eq(result.upper[0], 3.0));
}

#[test]
fn test_verify_crown_single_layer_multi_io() {
    // W = [[1, -1], [2, 3]], b = [0, 1], x in [0,1]^2
    // y0 = x0 - x1, y1 = 2*x0 + 3*x1 + 1
    let network = vec![(vec![vec![1.0, -1.0], vec![2.0, 3.0]], vec![0.0, 1.0])];
    let result = verify_crown_bounds(&network, &[0.0, 0.0], &[1.0, 1.0]);
    // y0: min=0-1=-1, max=1-0=1
    assert!(approx_eq(result.lower[0], -1.0));
    assert!(approx_eq(result.upper[0], 1.0));
    // y1: min=0+0+1=1, max=2+3+1=6
    assert!(approx_eq(result.lower[1], 1.0));
    assert!(approx_eq(result.upper[1], 6.0));
}

// ===========================================================================
// verify_crown_bounds — point input (interval width = 0)
// ===========================================================================

#[test]
fn test_verify_crown_point_input_single_layer() {
    let network = vec![(vec![vec![2.0, -1.0]], vec![3.0])];
    let result = verify_crown_bounds(&network, &[1.0, 2.0], &[1.0, 2.0]);
    // y = 2*1 + (-1)*2 + 3 = 3
    assert!(approx_eq(result.lower[0], 3.0));
    assert!(approx_eq(result.upper[0], 3.0));
}

#[test]
fn test_verify_crown_point_input_two_layers() {
    // Layer 1: y = 2x + 1, x=1 => y=3. ReLU(3)=3.
    // Layer 2: z = -1*y + 0 = -3.
    let network = vec![(vec![vec![2.0]], vec![1.0]), (vec![vec![-1.0]], vec![0.0])];
    let result = verify_crown_bounds(&network, &[1.0], &[1.0]);
    assert!(approx_eq(result.lower[0], -3.0));
    assert!(approx_eq(result.upper[0], -3.0));
}

// ===========================================================================
// verify_crown_bounds — two-layer with always-active ReLU
// ===========================================================================

#[test]
fn test_verify_crown_two_layer_all_active_exact() {
    // Layer 1: y = x + 5, x in [0,1] => pre-act [5,6], active
    // Layer 2: z = 2y + 0 => [10, 12]
    let network = vec![(vec![vec![1.0]], vec![5.0]), (vec![vec![2.0]], vec![0.0])];
    let result = verify_crown_bounds(&network, &[0.0], &[1.0]);
    assert!(approx_eq(result.lower[0], 10.0));
    assert!(approx_eq(result.upper[0], 12.0));
}

// ===========================================================================
// verify_crown_bounds — two-layer with always-inactive ReLU
// ===========================================================================

#[test]
fn test_verify_crown_two_layer_all_inactive() {
    // Layer 1: y = -x - 5, x in [0,1] => pre-act [-6,-5], inactive
    // ReLU => 0. Layer 2: z = y + 10 => 10
    let network = vec![
        (vec![vec![-1.0]], vec![-5.0]),
        (vec![vec![1.0]], vec![10.0]),
    ];
    let result = verify_crown_bounds(&network, &[0.0], &[1.0]);
    assert!(approx_eq(result.lower[0], 10.0));
    assert!(approx_eq(result.upper[0], 10.0));
}

// ===========================================================================
// verify_crown_bounds — two-layer with crossing ReLU
// ===========================================================================

#[test]
fn test_verify_crown_two_layer_crossing_soundness() {
    // Layer 1: y = x, x in [-1, 1] => pre-act [-1,1], crossing
    // Layer 2: z = y + 0
    let network = vec![(vec![vec![1.0]], vec![0.0]), (vec![vec![1.0]], vec![0.0])];
    let result = verify_crown_bounds(&network, &[-1.0], &[1.0]);
    // True output is max(x, 0) for x in [-1,1], so range [0, 1]
    // CROWN lower should be <= 0 (sound)
    assert!(result.lower[0] <= 0.0 + EPS);
    // CROWN upper should be >= 1 (sound)
    assert!(result.upper[0] >= 1.0 - EPS);
    // Order: lower <= upper
    assert!(result.lower[0] <= result.upper[0] + EPS);
}

// ===========================================================================
// verify_crown_bounds — three-layer deep network
// ===========================================================================

#[test]
fn test_verify_crown_three_layer_soundness() {
    let w1 = vec![vec![1.0, -1.0], vec![-1.0, 1.0]];
    let b1 = vec![0.0, 0.0];
    let w2 = vec![vec![1.0, 0.5], vec![0.5, 1.0]];
    let b2 = vec![0.0, 0.0];
    let w3 = vec![vec![1.0, -1.0]];
    let b3 = vec![0.0];
    let network = vec![
        (w1.clone(), b1.clone()),
        (w2.clone(), b2.clone()),
        (w3.clone(), b3.clone()),
    ];
    let il = vec![-1.0, -1.0];
    let iu = vec![1.0, 1.0];

    let result = verify_crown_bounds(&network, &il, &iu);
    assert!(result.lower[0] <= result.upper[0] + EPS);

    // Verify soundness by sampling concrete inputs
    let samples: Vec<[f64; 2]> = vec![
        [0.0, 0.0],
        [1.0, 1.0],
        [-1.0, -1.0],
        [1.0, -1.0],
        [-1.0, 1.0],
        [0.5, -0.5],
        [-0.3, 0.7],
    ];
    for s in &samples {
        let h0 = (s[0] * w1[0][0] + s[1] * w1[0][1] + b1[0]).max(0.0);
        let h1 = (s[0] * w1[1][0] + s[1] * w1[1][1] + b1[1]).max(0.0);
        let g0 = (h0 * w2[0][0] + h1 * w2[0][1] + b2[0]).max(0.0);
        let g1 = (h0 * w2[1][0] + h1 * w2[1][1] + b2[1]).max(0.0);
        let y = g0 * w3[0][0] + g1 * w3[0][1] + b3[0];
        assert!(
            y >= result.lower[0] - EPS,
            "sample {:?}: y={} < lower={}",
            s,
            y,
            result.lower[0]
        );
        assert!(
            y <= result.upper[0] + EPS,
            "sample {:?}: y={} > upper={}",
            s,
            y,
            result.upper[0]
        );
    }
}

// ===========================================================================
// verify_crown_bounds — result ordering invariant
// ===========================================================================

#[test]
fn test_verify_crown_lower_leq_upper_multi_output() {
    let w1 = vec![vec![2.0, -1.0], vec![-1.0, 3.0], vec![0.5, 0.5]];
    let b1 = vec![0.0, 0.0, 0.0];
    let w2 = vec![vec![1.0, -1.0, 0.5], vec![-0.5, 1.0, -1.0]];
    let b2 = vec![1.0, -1.0];
    let network = vec![(w1, b1), (w2, b2)];
    let result = verify_crown_bounds(&network, &[-2.0, -2.0], &[2.0, 2.0]);
    for i in 0..result.lower.len() {
        assert!(
            result.lower[i] <= result.upper[i] + EPS,
            "output {}: lower={} > upper={}",
            i,
            result.lower[i],
            result.upper[i]
        );
    }
}

// ===========================================================================
// IBP forward phase correctness within verify_crown_bounds
// ===========================================================================

#[test]
fn test_verify_crown_ibp_forward_negative_weight_swaps() {
    // Negative weight should swap lower/upper in IBP forward
    // y = -x, x in [1, 3] => y in [-3, -1]
    // ReLU => [0, 0] (all inactive)
    // Output layer: z = y + 0 => [0, 0]
    let network = vec![(vec![vec![-1.0]], vec![0.0]), (vec![vec![1.0]], vec![0.0])];
    let result = verify_crown_bounds(&network, &[1.0], &[3.0]);
    assert!(approx_eq(result.lower[0], 0.0));
    assert!(approx_eq(result.upper[0], 0.0));
}

// ===========================================================================
// Composition: linear_backward then concretize should match direct eval
// ===========================================================================

#[test]
fn test_linear_backward_then_concretize_matches_direct() {
    // y = 2x + 3, x in [1, 4]
    // Direct: y in [5, 11]
    let bound = CrownBound::identity(1);
    let weight = vec![vec![2.0]];
    let bias = vec![3.0];
    let propagated = crown_linear_backward(&weight, &bias, &bound);
    let (cl, cu) = crown_concretize(&propagated, &[1.0], &[4.0]);
    assert!(approx_eq(cl[0], 5.0));
    assert!(approx_eq(cu[0], 11.0));
}

// ===========================================================================
// Composition: relu_backward then linear_backward then concretize
// ===========================================================================

#[test]
fn test_relu_then_linear_backward_composition() {
    // Layer 1: y = x, x in [0, 2] => pre-act [0, 2], always active
    // Layer 2: z = 3y + 1
    // Expected: z in [1, 7]
    let bound = CrownBound::identity(1);
    // Backward through layer 2
    let b2 = crown_linear_backward(&[vec![3.0]], &[1.0], &bound);
    // Backward through ReLU between layer 1 and 2 (always active)
    let b1 = crown_relu_backward(&[0.0], &[2.0], &b2);
    // Backward through layer 1
    let b0 = crown_linear_backward(&[vec![1.0]], &[0.0], &b1);
    let (cl, cu) = crown_concretize(&b0, &[0.0], &[2.0]);
    assert!(approx_eq(cl[0], 1.0));
    assert!(approx_eq(cu[0], 7.0));
}

// ===========================================================================
// Soundness: CROWN is at least as tight as IBP
// ===========================================================================

#[test]
fn test_crown_at_least_as_tight_as_ibp_crossing_network() {
    use super::ibp::{IbpCompositionSpec, IbpLinearSpec, IbpReluSpec, Interval};

    let w1 = vec![vec![1.0, 0.5], vec![-0.5, 1.0]];
    let b1 = vec![0.0, 0.0];
    let w2 = vec![vec![1.0, -1.0]];
    let b2 = vec![0.0];
    let network = vec![(w1.clone(), b1.clone()), (w2.clone(), b2.clone())];
    let il = vec![-1.0, -1.0];
    let iu = vec![1.0, 1.0];

    let crown = verify_crown_bounds(&network, &il, &iu);

    let ibp_l = IbpLinearSpec::new();
    let ibp_r = IbpReluSpec::new();
    let ibp_c = IbpCompositionSpec::new();
    let input = vec![Interval::new(-1.0, 1.0), Interval::new(-1.0, 1.0)];
    let hidden = ibp_c.compose_linear_relu(&ibp_l, &ibp_r, &w1, &b1, &input);
    let ibp_out = ibp_l.propagate(&w2, &b2, &hidden);

    assert!(
        crown.lower[0] >= ibp_out[0].lower - EPS,
        "CROWN lower {} should >= IBP lower {}",
        crown.lower[0],
        ibp_out[0].lower
    );
    assert!(
        crown.upper[0] <= ibp_out[0].upper + EPS,
        "CROWN upper {} should <= IBP upper {}",
        crown.upper[0],
        ibp_out[0].upper
    );
}

// ===========================================================================
// Larger network: 4-layer soundness via sampling
// ===========================================================================

#[test]
fn test_verify_crown_four_layer_soundness_sampling() {
    let network = vec![
        (vec![vec![1.0], vec![-1.0]], vec![0.0, 0.0]), // 1->2
        (vec![vec![1.0, 1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]), // 2->2
        (vec![vec![2.0, -1.0], vec![0.5, 1.5]], vec![0.0, 0.0]), // 2->2
        (vec![vec![1.0, 1.0]], vec![0.0]),             // 2->1
    ];
    let il = vec![-0.5];
    let iu = vec![0.5];

    let result = verify_crown_bounds(&network, &il, &iu);
    assert!(result.lower[0] <= result.upper[0] + EPS);

    // Sample some inputs and forward-propagate manually
    for &x in &[-0.5, -0.25, 0.0, 0.25, 0.5] {
        let mut v = vec![x];
        for (layer_idx, (w, b)) in network.iter().enumerate() {
            let mut out = vec![0.0; w.len()];
            for r in 0..w.len() {
                let mut s = b[r];
                for (j, val) in v.iter().enumerate() {
                    s += w[r][j] * val;
                }
                out[r] = s;
            }
            if layer_idx < network.len() - 1 {
                for val in &mut out {
                    *val = val.max(0.0);
                }
            }
            v = out;
        }
        assert!(
            v[0] >= result.lower[0] - EPS,
            "x={}: output={} < lower={}",
            x,
            v[0],
            result.lower[0]
        );
        assert!(
            v[0] <= result.upper[0] + EPS,
            "x={}: output={} > upper={}",
            x,
            v[0],
            result.upper[0]
        );
    }
}

// ===========================================================================
// Edge: all-zero weight layer
// ===========================================================================

#[test]
fn test_verify_crown_zero_weight_layer() {
    // Layer 1: W=[[0]], b=[5] => output = [5] always
    let network = vec![(vec![vec![0.0]], vec![5.0])];
    let result = verify_crown_bounds(&network, &[-100.0], &[100.0]);
    assert!(approx_eq(result.lower[0], 5.0));
    assert!(approx_eq(result.upper[0], 5.0));
}

// ===========================================================================
// Edge: very large and very small coefficients
// ===========================================================================

#[test]
fn test_linear_backward_large_coefficients() {
    let bound = CrownBound::identity(1);
    let weight = vec![vec![1e6]];
    let bias = vec![1e6];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 1e6));
    assert!(approx_eq(result.lower_bias[0], 1e6));
}

#[test]
fn test_linear_backward_tiny_coefficients() {
    let bound = CrownBound::identity(1);
    let weight = vec![vec![1e-10]];
    let bias = vec![1e-10];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert!(approx_eq(result.lower_coeffs[0][0], 1e-10));
    assert!(approx_eq(result.lower_bias[0], 1e-10));
}

// ===========================================================================
// Edge: single-element dimension (1x1 network)
// ===========================================================================

#[test]
fn test_verify_crown_1x1_network() {
    let network = vec![(vec![vec![1.0]], vec![0.0])];
    let result = verify_crown_bounds(&network, &[5.0], &[5.0]);
    assert!(approx_eq(result.lower[0], 5.0));
    assert!(approx_eq(result.upper[0], 5.0));
}

// ===========================================================================
// Dimension consistency checks
// ===========================================================================

#[test]
fn test_linear_backward_output_dimensions() {
    // 3 outputs referencing 2 intermediates, weight 2x4 => result has 3 outputs, 4 inputs
    let bound = CrownBound {
        lower_coeffs: vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![1.0, 1.0]],
        upper_coeffs: vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![1.0, 1.0]],
        lower_bias: vec![0.0; 3],
        upper_bias: vec![0.0; 3],
    };
    let weight = vec![vec![1.0, 2.0, 3.0, 4.0], vec![5.0, 6.0, 7.0, 8.0]];
    let bias = vec![0.0, 0.0];
    let result = crown_linear_backward(&weight, &bias, &bound);
    assert_eq!(result.num_outputs(), 3);
    assert_eq!(result.num_inputs(), 4);
}

#[test]
fn test_relu_backward_preserves_dimensions() {
    let bound = CrownBound {
        lower_coeffs: vec![vec![1.0, 2.0, 3.0]; 2],
        upper_coeffs: vec![vec![4.0, 5.0, 6.0]; 2],
        lower_bias: vec![0.0; 2],
        upper_bias: vec![0.0; 2],
    };
    let result = crown_relu_backward(&[1.0, -1.0, -0.5], &[3.0, -0.1, 1.0], &bound);
    assert_eq!(result.num_outputs(), 2);
    assert_eq!(result.lower_coeffs[0].len(), 3);
}

// ===========================================================================
// verify_crown_bounds — wide input interval
// ===========================================================================

#[test]
fn test_verify_crown_wide_input_interval() {
    let network = vec![
        (vec![vec![1.0], vec![-1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let result = verify_crown_bounds(&network, &[-10.0], &[10.0]);
    assert!(result.lower[0] <= result.upper[0] + EPS);
    // f(x) = ReLU(x) + ReLU(-x) = |x|, range [0, 10]
    // CROWN should contain [0, 10]
    assert!(result.lower[0] <= 0.0 + EPS);
    assert!(result.upper[0] >= 10.0 - EPS);
}
