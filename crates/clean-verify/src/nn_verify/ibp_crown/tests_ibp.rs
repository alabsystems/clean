// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for IBP core specs (T80, T81, T82) and Interval helper.

use super::ibp::*;
use crate::spec::ProofStatus;

// ---- T80: IBP Linear ----

#[test]
fn test_ibp_linear_identity_matrix() {
    let spec = IbpLinearSpec::new();
    let weights = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let bias = vec![0.0, 0.0];
    let input = vec![Interval::new(-1.0, 1.0), Interval::new(2.0, 3.0)];
    let output = spec.propagate(&weights, &bias, &input);
    assert_eq!(output.len(), 2);
    assert!((output[0].lower - (-1.0)).abs() < 1e-10);
    assert!((output[0].upper - 1.0).abs() < 1e-10);
    assert!((output[1].lower - 2.0).abs() < 1e-10);
    assert!((output[1].upper - 3.0).abs() < 1e-10);
}

#[test]
fn test_ibp_linear_negative_weight() {
    let spec = IbpLinearSpec::new();
    let weights = vec![vec![-2.0]];
    let bias = vec![0.0];
    let input = vec![Interval::new(1.0, 3.0)];
    let output = spec.propagate(&weights, &bias, &input);
    assert!((output[0].lower - (-6.0)).abs() < 1e-10);
    assert!((output[0].upper - (-2.0)).abs() < 1e-10);
}

#[test]
fn test_ibp_linear_with_bias() {
    let spec = IbpLinearSpec::new();
    let weights = vec![vec![1.0]];
    let bias = vec![5.0];
    let input = vec![Interval::new(0.0, 1.0)];
    let output = spec.propagate(&weights, &bias, &input);
    assert!((output[0].lower - 5.0).abs() < 1e-10);
    assert!((output[0].upper - 6.0).abs() < 1e-10);
}

#[test]
fn test_ibp_linear_verify_concrete_sound() {
    let spec = IbpLinearSpec::new();
    let weights = vec![vec![2.0, -1.0], vec![-3.0, 4.0]];
    let bias = vec![1.0, -2.0];
    let input_bounds = vec![Interval::new(-1.0, 1.0), Interval::new(0.0, 2.0)];
    spec.verify_concrete(&weights, &bias, &input_bounds, &[0.5, 1.0])
        .expect("concrete point should be within IBP bounds");
}

#[test]
fn test_ibp_linear_verify_concrete_out_of_input_range() {
    let spec = IbpLinearSpec::new();
    let weights = vec![vec![1.0]];
    let bias = vec![0.0];
    let input_bounds = vec![Interval::new(0.0, 1.0)];
    assert!(
        spec.verify_concrete(&weights, &bias, &input_bounds, &[2.0])
            .is_err(),
        "should reject x outside input bounds"
    );
}

#[test]
fn test_ibp_linear_mixed_sign_weights() {
    let spec = IbpLinearSpec::new();
    let weights = vec![vec![3.0, -2.0]];
    let bias = vec![0.0];
    let input = vec![Interval::new(-1.0, 1.0), Interval::new(-1.0, 1.0)];
    let output = spec.propagate(&weights, &bias, &input);
    assert!((output[0].lower - (-5.0)).abs() < 1e-10);
    assert!((output[0].upper - 5.0).abs() < 1e-10);
}

#[test]
fn test_ibp_linear_status() {
    let spec = IbpLinearSpec::new();
    assert_eq!(spec.status(), ProofStatus::DerivedPending);
}

// ---- T81: IBP ReLU ----

#[test]
fn test_ibp_relu_positive_region() {
    let spec = IbpReluSpec::new();
    let input = Interval::new(1.0, 3.0);
    let output = spec.propagate(&input);
    assert!((output.lower - 1.0).abs() < 1e-10);
    assert!((output.upper - 3.0).abs() < 1e-10);
}

#[test]
fn test_ibp_relu_negative_region() {
    let spec = IbpReluSpec::new();
    let input = Interval::new(-3.0, -1.0);
    let output = spec.propagate(&input);
    assert!((output.lower).abs() < 1e-10);
    assert!((output.upper).abs() < 1e-10);
}

#[test]
fn test_ibp_relu_crossing_region() {
    let spec = IbpReluSpec::new();
    let input = Interval::new(-2.0, 3.0);
    let output = spec.propagate(&input);
    assert!((output.lower).abs() < 1e-10);
    assert!((output.upper - 3.0).abs() < 1e-10);
}

#[test]
fn test_ibp_relu_verify_concrete_positive() {
    let spec = IbpReluSpec::new();
    let input = Interval::new(1.0, 5.0);
    spec.verify_concrete(&input, 3.0)
        .expect("ReLU(3.0) = 3.0 should be in [1, 5]");
}

#[test]
fn test_ibp_relu_verify_concrete_crossing() {
    let spec = IbpReluSpec::new();
    let input = Interval::new(-2.0, 4.0);
    spec.verify_concrete(&input, -1.0)
        .expect("ReLU(-1.0) = 0.0 should be in [0, 4]");
    spec.verify_concrete(&input, 2.0)
        .expect("ReLU(2.0) = 2.0 should be in [0, 4]");
}

#[test]
fn test_ibp_relu_vector() {
    let spec = IbpReluSpec::new();
    let inputs = vec![
        Interval::new(1.0, 2.0),
        Interval::new(-3.0, -1.0),
        Interval::new(-1.0, 1.0),
    ];
    let outputs = spec.propagate_vector(&inputs);
    assert_eq!(outputs.len(), 3);
    assert!((outputs[0].lower - 1.0).abs() < 1e-10);
    assert!((outputs[1].upper).abs() < 1e-10);
    assert!((outputs[2].lower).abs() < 1e-10);
    assert!((outputs[2].upper - 1.0).abs() < 1e-10);
}

#[test]
fn test_ibp_relu_status() {
    let spec = IbpReluSpec::new();
    assert_eq!(spec.status(), ProofStatus::DerivedPending);
}

// ---- T82: IBP Composition ----

#[test]
fn test_ibp_composition_two_layer_network() {
    let comp = IbpCompositionSpec::new();
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();

    let w1 = vec![vec![1.0, -1.0], vec![-1.0, 1.0]];
    let b1 = vec![0.0, 0.0];
    let input = vec![Interval::new(-1.0, 1.0), Interval::new(-1.0, 1.0)];
    let hidden = comp.compose_linear_relu(&linear, &relu, &w1, &b1, &input);

    let w2 = vec![vec![1.0, 1.0]];
    let b2 = vec![0.0];
    let output = linear.propagate(&w2, &b2, &hidden);
    assert_eq!(output.len(), 1);
    assert!(output[0].lower <= f64::EPSILON);
}

#[test]
fn test_ibp_composition_chain_validation() {
    let comp = IbpCompositionSpec::new();
    let bounds = vec![
        vec![Interval::new(-1.0, 1.0)],
        vec![Interval::new(0.0, 2.0)],
        vec![Interval::new(-0.5, 1.5)],
    ];
    comp.verify_chain(&bounds).expect("valid chain should pass");
}

#[test]
fn test_ibp_composition_empty_layer_rejected() {
    let comp = IbpCompositionSpec::new();
    let bounds = vec![vec![Interval::new(-1.0, 1.0)], vec![]];
    assert!(comp.verify_chain(&bounds).is_err());
}

#[test]
fn test_ibp_composition_status() {
    let comp = IbpCompositionSpec::new();
    assert_eq!(comp.status(), ProofStatus::DerivedPending);
}

// ---- Interval helper ----

#[test]
fn test_interval_subset() {
    let inner = Interval::new(0.0, 1.0);
    let outer = Interval::new(-1.0, 2.0);
    assert!(inner.is_subset_of(&outer));
    assert!(!outer.is_subset_of(&inner));
}

#[test]
fn test_interval_point() {
    let p = Interval::point(std::f64::consts::PI);
    assert!((p.width()).abs() < 1e-10);
}
