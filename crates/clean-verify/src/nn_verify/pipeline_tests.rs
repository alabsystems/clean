// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the IBP NN verification pipeline.

use super::ibp_crown::Interval;
use super::pipeline::*;

// ---------------------------------------------------------------------------
// Helper constructors
// ---------------------------------------------------------------------------

fn linear_layer(weights: Vec<Vec<f64>>, bias: Vec<f64>) -> Layer {
    Layer {
        weights,
        bias,
        activation: ActivationType::Linear,
    }
}

fn relu_layer(weights: Vec<Vec<f64>>, bias: Vec<f64>) -> Layer {
    Layer {
        weights,
        bias,
        activation: ActivationType::ReLU,
    }
}

fn bounded_property(bounds: Vec<Interval>) -> VerificationProperty {
    VerificationProperty::OutputBounded(bounds)
}

// ---------------------------------------------------------------------------
// 1. Two-layer MLP: Linear(2->3) + ReLU + Linear(3->1)
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_two_layer_mlp_verified() {
    let network = NetworkArchitecture {
        layers: vec![
            relu_layer(
                vec![vec![1.0, 0.5], vec![-0.5, 1.0], vec![0.3, -0.7]],
                vec![0.1, -0.2, 0.0],
            ),
            linear_layer(vec![vec![1.0, 1.0, 1.0]], vec![0.0]),
        ],
    };
    let input_bounds = vec![Interval::new(-1.0, 1.0), Interval::new(-1.0, 1.0)];
    let property = bounded_property(vec![Interval::new(-10.0, 10.0)]);

    let request = VerificationRequest {
        network,
        input_bounds,
        property,
    };
    let result = verify_network(&request).expect("pipeline should succeed");
    assert!(result.verified, "generous bounds should be verified");
    assert_eq!(result.chain.len(), 2, "two layers => two certificates");
    assert_eq!(result.trust, TrustLevel::DerivedPending);
}

#[test]
fn test_pipeline_two_layer_mlp_concrete_containment() {
    let network = NetworkArchitecture {
        layers: vec![
            relu_layer(
                vec![vec![1.0, 0.5], vec![-0.5, 1.0], vec![0.3, -0.7]],
                vec![0.1, -0.2, 0.0],
            ),
            linear_layer(vec![vec![1.0, 1.0, 1.0]], vec![0.0]),
        ],
    };
    let input_bounds = vec![Interval::new(-1.0, 1.0), Interval::new(-1.0, 1.0)];
    let request = VerificationRequest {
        network: network.clone(),
        input_bounds,
        property: bounded_property(vec![Interval::new(-100.0, 100.0)]),
    };
    let result = verify_network(&request).expect("pipeline should succeed");

    // Evaluate at several concrete points; all must fall within IBP bounds.
    let test_points: &[&[f64]] = &[
        &[0.0, 0.0],
        &[1.0, 1.0],
        &[-1.0, -1.0],
        &[1.0, -1.0],
        &[-1.0, 1.0],
        &[0.5, -0.3],
    ];
    for pt in test_points {
        let output = evaluate_network(&network, pt);
        for (val, bound) in output.iter().zip(result.output_bounds.iter()) {
            assert!(
                *val >= bound.lower - f64::EPSILON && *val <= bound.upper + f64::EPSILON,
                "concrete output {val} not in [{}, {}] for input {pt:?}",
                bound.lower,
                bound.upper,
            );
        }
    }
}

// ---------------------------------------------------------------------------
// 2. Identity network: Linear(2->2) with identity weights
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_identity_network_linear() {
    let network = NetworkArchitecture {
        layers: vec![linear_layer(
            vec![vec![1.0, 0.0], vec![0.0, 1.0]],
            vec![0.0, 0.0],
        )],
    };
    let input_bounds = vec![Interval::new(-2.0, 3.0), Interval::new(1.0, 5.0)];
    let request = VerificationRequest {
        network,
        input_bounds: input_bounds.clone(),
        property: bounded_property(input_bounds.clone()),
    };
    let result = verify_network(&request).expect("identity network should succeed");
    assert!(result.verified, "identity network output = input bounds");
    for (out, inp) in result.output_bounds.iter().zip(input_bounds.iter()) {
        assert!((out.lower - inp.lower).abs() < 1e-10);
        assert!((out.upper - inp.upper).abs() < 1e-10);
    }
}

#[test]
fn test_pipeline_identity_network_relu_clips_negative() {
    let network = NetworkArchitecture {
        layers: vec![relu_layer(
            vec![vec![1.0, 0.0], vec![0.0, 1.0]],
            vec![0.0, 0.0],
        )],
    };
    let input_bounds = vec![Interval::new(-2.0, 3.0), Interval::new(1.0, 5.0)];
    let request = VerificationRequest {
        network,
        input_bounds,
        property: bounded_property(vec![Interval::new(0.0, 3.0), Interval::new(1.0, 5.0)]),
    };
    let result = verify_network(&request).expect("identity+relu should succeed");
    assert!(result.verified);
    assert!(
        (result.output_bounds[0].lower).abs() < 1e-10,
        "ReLU clips negative to 0"
    );
    assert!((result.output_bounds[0].upper - 3.0).abs() < 1e-10);
    assert!(
        (result.output_bounds[1].lower - 1.0).abs() < 1e-10,
        "positive region unchanged"
    );
}

// ---------------------------------------------------------------------------
// 3. Negative weights: W+/W- decomposition correctness
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_negative_weights_reverses_bounds() {
    let network = NetworkArchitecture {
        layers: vec![linear_layer(
            vec![vec![-1.0, 0.0], vec![0.0, -1.0]],
            vec![0.0, 0.0],
        )],
    };
    let input_bounds = vec![Interval::new(1.0, 3.0), Interval::new(2.0, 5.0)];
    let request = VerificationRequest {
        network,
        input_bounds,
        property: bounded_property(vec![Interval::new(-3.0, -1.0), Interval::new(-5.0, -2.0)]),
    };
    let result = verify_network(&request).expect("negative weights should succeed");
    assert!(result.verified);
    assert!((result.output_bounds[0].lower - (-3.0)).abs() < 1e-10);
    assert!((result.output_bounds[0].upper - (-1.0)).abs() < 1e-10);
}

#[test]
fn test_pipeline_mixed_negative_weights() {
    // w = [-2, -3], b = 1, input in [0,1]x[0,1]
    // y = -2*x1 - 3*x2 + 1
    // lower: -2*1 + -3*1 + 1 = -4, upper: -2*0 + -3*0 + 1 = 1
    let network = NetworkArchitecture {
        layers: vec![linear_layer(vec![vec![-2.0, -3.0]], vec![1.0])],
    };
    let input_bounds = vec![Interval::new(0.0, 1.0), Interval::new(0.0, 1.0)];
    let request = VerificationRequest {
        network,
        input_bounds,
        property: bounded_property(vec![Interval::new(-4.0, 1.0)]),
    };
    let result = verify_network(&request).expect("mixed negative should succeed");
    assert!(result.verified);
    assert!((result.output_bounds[0].lower - (-4.0)).abs() < 1e-10);
    assert!((result.output_bounds[0].upper - 1.0).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// 4. Certificate chain: 3-layer network
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_three_layer_chain_composition() {
    let network = NetworkArchitecture {
        layers: vec![
            relu_layer(vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
            relu_layer(vec![vec![0.5, 0.5], vec![1.0, -1.0]], vec![0.1, 0.0]),
            linear_layer(vec![vec![1.0, 1.0]], vec![-0.5]),
        ],
    };
    let input_bounds = vec![Interval::new(-1.0, 1.0), Interval::new(-1.0, 1.0)];
    let request = VerificationRequest {
        network,
        input_bounds,
        property: bounded_property(vec![Interval::new(-20.0, 20.0)]),
    };
    let result = verify_network(&request).expect("3-layer chain should succeed");
    assert!(result.verified);
    assert_eq!(result.chain.len(), 3, "3 layers => 3 certificates");
    assert_eq!(result.chain[0].post_activation_bounds.len(), 2);
    assert_eq!(result.chain[1].post_activation_bounds.len(), 2);
    assert_eq!(result.chain[2].post_activation_bounds.len(), 1);

    for cert in &result.chain {
        assert_eq!(
            cert.pre_activation_bounds.len(),
            cert.post_activation_bounds.len(),
            "pre/post activation must have same dimension"
        );
    }
}

#[test]
fn test_pipeline_three_layer_concrete_containment() {
    let network = NetworkArchitecture {
        layers: vec![
            relu_layer(vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
            relu_layer(vec![vec![0.5, 0.5], vec![1.0, -1.0]], vec![0.1, 0.0]),
            linear_layer(vec![vec![1.0, 1.0]], vec![-0.5]),
        ],
    };
    let input_bounds = vec![Interval::new(-1.0, 1.0), Interval::new(-1.0, 1.0)];
    let request = VerificationRequest {
        network: network.clone(),
        input_bounds,
        property: bounded_property(vec![Interval::new(-50.0, 50.0)]),
    };
    let result = verify_network(&request).expect("should succeed");

    for pt in &[
        vec![0.0, 0.0],
        vec![1.0, 1.0],
        vec![-1.0, 1.0],
        vec![0.5, -0.5],
    ] {
        let output = evaluate_network(&network, pt);
        for (val, bound) in output.iter().zip(result.output_bounds.iter()) {
            assert!(
                *val >= bound.lower - f64::EPSILON && *val <= bound.upper + f64::EPSILON,
                "output {val} outside [{}, {}] for input {pt:?}",
                bound.lower,
                bound.upper,
            );
        }
    }
}

// ---------------------------------------------------------------------------
// 5. Mismatch detection
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_mismatch_tight_bounds_not_verified() {
    let network = NetworkArchitecture {
        layers: vec![linear_layer(vec![vec![10.0]], vec![0.0])],
    };
    let input_bounds = vec![Interval::new(-1.0, 1.0)];
    let request = VerificationRequest {
        network,
        input_bounds,
        property: bounded_property(vec![Interval::new(-0.1, 0.1)]),
    };
    let result = verify_network(&request).expect("pipeline returns unverified, not error");
    assert!(!result.verified, "tight bounds should NOT be verified");
}

#[test]
fn test_pipeline_mismatch_property_dimension_error() {
    let network = NetworkArchitecture {
        layers: vec![linear_layer(vec![vec![1.0], vec![2.0]], vec![0.0, 0.0])],
    };
    let input_bounds = vec![Interval::new(0.0, 1.0)];
    let request = VerificationRequest {
        network,
        input_bounds,
        property: bounded_property(vec![Interval::new(-10.0, 10.0)]),
    };
    let err = verify_network(&request).unwrap_err();
    assert!(
        matches!(err, PipelineError::PropertyDimensionMismatch { .. }),
        "expected PropertyDimensionMismatch, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// 6. Single neuron: 1->1 linear + ReLU
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_single_neuron_linear() {
    // y = 2x + 1, x in [0, 3] => y in [1, 7]
    let network = NetworkArchitecture {
        layers: vec![linear_layer(vec![vec![2.0]], vec![1.0])],
    };
    let input_bounds = vec![Interval::new(0.0, 3.0)];
    let request = VerificationRequest {
        network,
        input_bounds,
        property: bounded_property(vec![Interval::new(1.0, 7.0)]),
    };
    let result = verify_network(&request).expect("single neuron should succeed");
    assert!(result.verified);
    assert!((result.output_bounds[0].lower - 1.0).abs() < 1e-10);
    assert!((result.output_bounds[0].upper - 7.0).abs() < 1e-10);
}

#[test]
fn test_pipeline_single_neuron_relu_crossing() {
    // y = ReLU(x - 1), x in [0, 3] => pre: [-1, 2], post: [0, 2]
    let network = NetworkArchitecture {
        layers: vec![relu_layer(vec![vec![1.0]], vec![-1.0])],
    };
    let input_bounds = vec![Interval::new(0.0, 3.0)];
    let request = VerificationRequest {
        network,
        input_bounds,
        property: bounded_property(vec![Interval::new(0.0, 2.0)]),
    };
    let result = verify_network(&request).expect("single neuron relu should succeed");
    assert!(result.verified);
    assert!((result.output_bounds[0].lower).abs() < 1e-10);
    assert!((result.output_bounds[0].upper - 2.0).abs() < 1e-10);
}

#[test]
fn test_pipeline_single_neuron_relu_all_negative() {
    // y = ReLU(-x), x in [1, 3] => pre: [-3, -1], post: [0, 0]
    let network = NetworkArchitecture {
        layers: vec![relu_layer(vec![vec![-1.0]], vec![0.0])],
    };
    let input_bounds = vec![Interval::new(1.0, 3.0)];
    let request = VerificationRequest {
        network,
        input_bounds,
        property: bounded_property(vec![Interval::new(0.0, 0.0)]),
    };
    let result = verify_network(&request).expect("all-negative relu should succeed");
    assert!(result.verified);
    assert!((result.output_bounds[0].lower).abs() < 1e-10);
    assert!((result.output_bounds[0].upper).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// 7. Error cases
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_empty_network_error() {
    let request = VerificationRequest {
        network: NetworkArchitecture { layers: vec![] },
        input_bounds: vec![Interval::new(0.0, 1.0)],
        property: bounded_property(vec![Interval::new(0.0, 1.0)]),
    };
    let err = verify_network(&request).unwrap_err();
    assert!(matches!(err, PipelineError::EmptyNetwork));
}

#[test]
fn test_pipeline_input_dimension_mismatch() {
    let network = NetworkArchitecture {
        layers: vec![linear_layer(vec![vec![1.0, 2.0]], vec![0.0])],
    };
    let request = VerificationRequest {
        network,
        input_bounds: vec![
            Interval::new(0.0, 1.0),
            Interval::new(0.0, 1.0),
            Interval::new(0.0, 1.0),
        ],
        property: bounded_property(vec![Interval::new(-10.0, 10.0)]),
    };
    let err = verify_network(&request).unwrap_err();
    assert!(
        matches!(err, PipelineError::InputBoundsMismatch { .. }),
        "expected InputBoundsMismatch, got {err:?}"
    );
}

#[test]
fn test_pipeline_inter_layer_dimension_mismatch() {
    let network = NetworkArchitecture {
        layers: vec![
            linear_layer(vec![vec![1.0], vec![2.0]], vec![0.0, 0.0]),
            linear_layer(vec![vec![1.0, 2.0, 3.0]], vec![0.0]),
        ],
    };
    let request = VerificationRequest {
        network,
        input_bounds: vec![Interval::new(0.0, 1.0)],
        property: bounded_property(vec![Interval::new(-10.0, 10.0)]),
    };
    let err = verify_network(&request).unwrap_err();
    assert!(
        matches!(err, PipelineError::DimensionMismatch { .. }),
        "expected DimensionMismatch, got {err:?}"
    );
}

#[test]
fn test_pipeline_bias_weight_mismatch() {
    let network = NetworkArchitecture {
        layers: vec![Layer {
            weights: vec![vec![1.0]],
            bias: vec![0.0, 0.0],
            activation: ActivationType::Linear,
        }],
    };
    let request = VerificationRequest {
        network,
        input_bounds: vec![Interval::new(0.0, 1.0)],
        property: bounded_property(vec![Interval::new(-10.0, 10.0)]),
    };
    let err = verify_network(&request).unwrap_err();
    assert!(
        matches!(err, PipelineError::LayerShapeMismatch { .. }),
        "expected LayerShapeMismatch, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// 8. Wider network: 4-dim input, 3 layers
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_wider_network() {
    let network = NetworkArchitecture {
        layers: vec![
            relu_layer(
                vec![
                    vec![1.0, 0.0, 0.5, -0.5],
                    vec![0.0, 1.0, -0.5, 0.5],
                    vec![0.5, -0.5, 1.0, 0.0],
                ],
                vec![0.0, 0.0, 0.0],
            ),
            relu_layer(
                vec![vec![1.0, 1.0, 1.0], vec![-1.0, 1.0, 0.0]],
                vec![0.0, 0.0],
            ),
            linear_layer(vec![vec![1.0, -1.0]], vec![0.0]),
        ],
    };
    let input_bounds = vec![
        Interval::new(-1.0, 1.0),
        Interval::new(-1.0, 1.0),
        Interval::new(0.0, 2.0),
        Interval::new(-0.5, 0.5),
    ];
    let request = VerificationRequest {
        network: network.clone(),
        input_bounds,
        property: bounded_property(vec![Interval::new(-50.0, 50.0)]),
    };
    let result = verify_network(&request).expect("wider network should succeed");
    assert!(result.verified);

    let output = evaluate_network(&network, &[0.0, 0.0, 1.0, 0.0]);
    assert!(
        output[0] >= result.output_bounds[0].lower - f64::EPSILON
            && output[0] <= result.output_bounds[0].upper + f64::EPSILON
    );
}

// ---------------------------------------------------------------------------
// 9. Bias-only network (zero weights)
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_bias_only_network() {
    let network = NetworkArchitecture {
        layers: vec![linear_layer(vec![vec![0.0, 0.0]], vec![5.0])],
    };
    let input_bounds = vec![Interval::new(-100.0, 100.0), Interval::new(-100.0, 100.0)];
    let request = VerificationRequest {
        network,
        input_bounds,
        property: bounded_property(vec![Interval::new(5.0, 5.0)]),
    };
    let result = verify_network(&request).expect("bias-only should succeed");
    assert!(result.verified);
    assert!((result.output_bounds[0].lower - 5.0).abs() < 1e-10);
    assert!((result.output_bounds[0].upper - 5.0).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// 10. evaluate_network helper correctness
// ---------------------------------------------------------------------------

#[test]
fn test_evaluate_network_simple() {
    let network = NetworkArchitecture {
        layers: vec![
            relu_layer(vec![vec![1.0, -1.0]], vec![0.0]),
            linear_layer(vec![vec![2.0]], vec![1.0]),
        ],
    };
    // x = [3, 1]: layer1 pre = 2, relu = 2, layer2 = 5
    let output = evaluate_network(&network, &[3.0, 1.0]);
    assert!((output[0] - 5.0).abs() < 1e-10);

    // x = [1, 3]: layer1 pre = -2, relu = 0, layer2 = 1
    let output = evaluate_network(&network, &[1.0, 3.0]);
    assert!((output[0] - 1.0).abs() < 1e-10);
}
