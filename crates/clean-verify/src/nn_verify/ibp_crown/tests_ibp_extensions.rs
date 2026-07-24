// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for batch IBP and multi-input interval analysis extensions.

use super::ibp::Interval;
use super::ibp_extensions::{
    batch_ibp_forward, ibp_forward_single, ibp_sensitivity, multi_input_hull,
    verify_batch_soundness,
};

/// Helper: single-layer identity-like network (1x1 weight = 1.0, bias = 0.0).
fn identity_network() -> (Vec<Vec<Vec<f64>>>, Vec<Vec<f64>>) {
    (vec![vec![vec![1.0]]], vec![vec![0.0]])
}

/// Helper: simple 1-input, 1-output, 2-layer network.
fn two_layer_network() -> (Vec<Vec<Vec<f64>>>, Vec<Vec<f64>>) {
    // Layer 1: 1->2 (weights [[2.0], [-1.0]], bias [0.0, 0.0])
    // Layer 2: 2->1 (weights [[1.0, 1.0]], bias [0.0])
    let weights = vec![vec![vec![2.0], vec![-1.0]], vec![vec![1.0, 1.0]]];
    let biases = vec![vec![0.0, 0.0], vec![0.0]];
    (weights, biases)
}

/// Helper: network with bias.
fn biased_network() -> (Vec<Vec<Vec<f64>>>, Vec<Vec<f64>>) {
    (vec![vec![vec![1.0]]], vec![vec![3.0]])
}

// ---------------------------------------------------------------------------
// batch_ibp_forward tests
// ---------------------------------------------------------------------------

#[test]
fn test_batch_ibp_forward_single_input() {
    let (w, b) = identity_network();
    let inputs = vec![Interval::new(-1.0, 1.0)];
    let results = batch_ibp_forward(&w, &b, &inputs);
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].len(), 1);
    assert!((results[0][0].lower - (-1.0)).abs() < 1e-10);
    assert!((results[0][0].upper - 1.0).abs() < 1e-10);
}

#[test]
fn test_batch_ibp_forward_multiple_inputs() {
    let (w, b) = identity_network();
    let inputs = vec![
        Interval::new(-1.0, 1.0),
        Interval::new(0.0, 2.0),
        Interval::new(-3.0, -1.0),
    ];
    let results = batch_ibp_forward(&w, &b, &inputs);
    assert_eq!(results.len(), 3);
    assert!((results[1][0].lower - 0.0).abs() < 1e-10);
    assert!((results[1][0].upper - 2.0).abs() < 1e-10);
    assert!((results[2][0].lower - (-3.0)).abs() < 1e-10);
    assert!((results[2][0].upper - (-1.0)).abs() < 1e-10);
}

#[test]
fn test_batch_ibp_forward_empty_inputs() {
    let (w, b) = identity_network();
    let results = batch_ibp_forward(&w, &b, &[]);
    assert!(results.is_empty());
}

#[test]
fn test_batch_ibp_forward_wider_interval_gives_wider_output() {
    let (w, b) = identity_network();
    let inputs = vec![Interval::new(-1.0, 1.0), Interval::new(-5.0, 5.0)];
    let results = batch_ibp_forward(&w, &b, &inputs);
    assert!(results[1][0].width() >= results[0][0].width() - f64::EPSILON);
}

#[test]
fn test_batch_ibp_forward_with_bias() {
    let (w, b) = biased_network();
    let inputs = vec![Interval::new(0.0, 1.0)];
    let results = batch_ibp_forward(&w, &b, &inputs);
    // y = 1.0 * x + 3.0, so [0,1] -> [3,4]
    assert!((results[0][0].lower - 3.0).abs() < 1e-10);
    assert!((results[0][0].upper - 4.0).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// ibp_forward_single tests
// ---------------------------------------------------------------------------

#[test]
fn test_ibp_forward_single_identity() {
    let (w, b) = identity_network();
    let input = Interval::new(-2.0, 3.0);
    let output = ibp_forward_single(&w, &b, &input);
    assert_eq!(output.len(), 1);
    assert!((output[0].lower - (-2.0)).abs() < 1e-10);
    assert!((output[0].upper - 3.0).abs() < 1e-10);
}

#[test]
fn test_ibp_forward_single_two_layer() {
    let (w, b) = two_layer_network();
    let input = Interval::new(0.0, 1.0);
    let output = ibp_forward_single(&w, &b, &input);
    // Layer 1: [2*x, -x] with ReLU -> [max(0,2*[0,1]), max(0,-[0,1])]
    //   = [[0, 2], [0, 0]] after ReLU (negative part clamped to 0)
    // Wait: -1 * [0,1] = [-1, 0], ReLU -> [0, 0]
    // Layer 2: [1,1] * [[0,2], [0,0]] + 0 = [0, 2]
    assert_eq!(output.len(), 1);
    assert!((output[0].lower - 0.0).abs() < 1e-10);
    assert!((output[0].upper - 2.0).abs() < 1e-10);
}

#[test]
fn test_ibp_forward_single_negative_input() {
    let (w, b) = two_layer_network();
    let input = Interval::new(-1.0, 0.0);
    let output = ibp_forward_single(&w, &b, &input);
    // Layer 1: [2*[-1,0], -1*[-1,0]] = [[-2,0], [0,1]], ReLU -> [[0,0], [0,1]]
    // Layer 2: [1,1] * [[0,0], [0,1]] = [0, 1]
    assert_eq!(output.len(), 1);
    assert!((output[0].lower - 0.0).abs() < 1e-10);
    assert!((output[0].upper - 1.0).abs() < 1e-10);
}

#[test]
fn test_ibp_forward_single_point_input() {
    let (w, b) = identity_network();
    let input = Interval::point(5.0);
    let output = ibp_forward_single(&w, &b, &input);
    assert_eq!(output.len(), 1);
    assert!((output[0].lower - 5.0).abs() < 1e-10);
    assert!((output[0].upper - 5.0).abs() < 1e-10);
}

#[test]
fn test_ibp_forward_single_empty_network() {
    let output = ibp_forward_single(&[], &[], &Interval::new(0.0, 1.0));
    assert!(output.is_empty());
}

#[test]
fn test_ibp_forward_single_scaling_network() {
    // Scale by 3.0
    let w = vec![vec![vec![3.0]]];
    let b = vec![vec![0.0]];
    let output = ibp_forward_single(&w, &b, &Interval::new(-1.0, 2.0));
    assert!((output[0].lower - (-3.0)).abs() < 1e-10);
    assert!((output[0].upper - 6.0).abs() < 1e-10);
}

#[test]
fn test_ibp_forward_single_negative_weight() {
    // Negate: weight = -1
    let w = vec![vec![vec![-1.0]]];
    let b = vec![vec![0.0]];
    let output = ibp_forward_single(&w, &b, &Interval::new(1.0, 3.0));
    // -1 * [1,3] = [-3, -1]
    assert!((output[0].lower - (-3.0)).abs() < 1e-10);
    assert!((output[0].upper - (-1.0)).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// multi_input_hull tests
// ---------------------------------------------------------------------------

#[test]
fn test_multi_input_hull_single() {
    let hull = multi_input_hull(&[Interval::new(1.0, 3.0)]);
    assert!((hull.lower - 1.0).abs() < 1e-10);
    assert!((hull.upper - 3.0).abs() < 1e-10);
}

#[test]
fn test_multi_input_hull_two_overlapping() {
    let hull = multi_input_hull(&[Interval::new(0.0, 2.0), Interval::new(1.0, 3.0)]);
    assert!((hull.lower - 0.0).abs() < 1e-10);
    assert!((hull.upper - 3.0).abs() < 1e-10);
}

#[test]
fn test_multi_input_hull_two_disjoint() {
    let hull = multi_input_hull(&[Interval::new(-5.0, -3.0), Interval::new(3.0, 5.0)]);
    assert!((hull.lower - (-5.0)).abs() < 1e-10);
    assert!((hull.upper - 5.0).abs() < 1e-10);
}

#[test]
fn test_multi_input_hull_three_intervals() {
    let hull = multi_input_hull(&[
        Interval::new(-1.0, 0.0),
        Interval::new(-3.0, -2.0),
        Interval::new(4.0, 7.0),
    ]);
    assert!((hull.lower - (-3.0)).abs() < 1e-10);
    assert!((hull.upper - 7.0).abs() < 1e-10);
}

#[test]
fn test_multi_input_hull_empty() {
    let hull = multi_input_hull(&[]);
    assert!((hull.lower - 0.0).abs() < 1e-10);
    assert!((hull.upper - 0.0).abs() < 1e-10);
}

#[test]
fn test_multi_input_hull_identical() {
    let hull = multi_input_hull(&[Interval::new(2.0, 5.0), Interval::new(2.0, 5.0)]);
    assert!((hull.lower - 2.0).abs() < 1e-10);
    assert!((hull.upper - 5.0).abs() < 1e-10);
}

#[test]
fn test_multi_input_hull_nested() {
    // One interval contains the other
    let hull = multi_input_hull(&[Interval::new(-10.0, 10.0), Interval::new(-1.0, 1.0)]);
    assert!((hull.lower - (-10.0)).abs() < 1e-10);
    assert!((hull.upper - 10.0).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// verify_batch_soundness tests
// ---------------------------------------------------------------------------

#[test]
fn test_batch_soundness_all_within() {
    let (w, b) = identity_network();
    let input = Interval::new(-1.0, 1.0);
    let samples = vec![vec![0.0], vec![0.5], vec![-0.5]];
    let result = verify_batch_soundness(&w, &b, &input, &samples);
    assert!(result.sound);
    assert_eq!(result.num_samples, 3);
    assert!(result.violations.is_empty());
}

#[test]
fn test_batch_soundness_some_violations() {
    let (w, b) = identity_network();
    let input = Interval::new(-1.0, 1.0);
    // sample [5.0] is outside [-1,1]
    let samples = vec![vec![0.0], vec![5.0], vec![-0.5]];
    let result = verify_batch_soundness(&w, &b, &input, &samples);
    assert!(!result.sound);
    assert_eq!(result.num_samples, 3);
    assert_eq!(result.violations, vec![1]);
}

#[test]
fn test_batch_soundness_all_violations() {
    let (w, b) = identity_network();
    let input = Interval::new(-0.1, 0.1);
    let samples = vec![vec![5.0], vec![-5.0]];
    let result = verify_batch_soundness(&w, &b, &input, &samples);
    assert!(!result.sound);
    assert_eq!(result.violations.len(), 2);
}

#[test]
fn test_batch_soundness_empty_samples() {
    let (w, b) = identity_network();
    let input = Interval::new(-1.0, 1.0);
    let result = verify_batch_soundness(&w, &b, &input, &[]);
    assert!(result.sound);
    assert_eq!(result.num_samples, 0);
}

#[test]
fn test_batch_soundness_boundary_values() {
    let (w, b) = identity_network();
    let input = Interval::new(-1.0, 1.0);
    // Exact boundary values should be within bounds
    let samples = vec![vec![-1.0], vec![1.0]];
    let result = verify_batch_soundness(&w, &b, &input, &samples);
    assert!(result.sound);
}

#[test]
fn test_batch_soundness_with_bias() {
    let (w, b) = biased_network();
    let input = Interval::new(0.0, 1.0);
    // y = x + 3, bounds = [3, 4], sample x=0.5 -> y=3.5 (within)
    let samples = vec![vec![0.5]];
    let result = verify_batch_soundness(&w, &b, &input, &samples);
    assert!(result.sound);
}

// ---------------------------------------------------------------------------
// ibp_sensitivity tests
// ---------------------------------------------------------------------------

#[test]
fn test_sensitivity_identity_network() {
    let (w, b) = identity_network();
    let input = Interval::new(-1.0, 1.0);
    let result = ibp_sensitivity(&w, &b, &input, 0.1);
    assert!((result.input_width - 2.0).abs() < 1e-10);
    // Perturbed: [-1.1, 1.1], width = 2.2
    assert!((result.output_width - 2.2).abs() < 1e-10);
    // Amplification: (2.2 - 2.0) / (2 * 0.1) = 1.0
    assert!((result.amplification - 1.0).abs() < 1e-10);
}

#[test]
fn test_sensitivity_scaling_network() {
    let w = vec![vec![vec![3.0]]];
    let b = vec![vec![0.0]];
    let input = Interval::new(0.0, 1.0);
    let result = ibp_sensitivity(&w, &b, &input, 0.1);
    // Original: [0,3], width=3.0. Perturbed: [-0.3, 3.3], width=3.6
    assert!((result.input_width - 1.0).abs() < 1e-10);
    assert!((result.output_width - 3.6).abs() < 1e-10);
    // Amplification: (3.6 - 3.0) / 0.2 = 3.0
    assert!((result.amplification - 3.0).abs() < 1e-10);
}

#[test]
fn test_sensitivity_zero_epsilon() {
    let (w, b) = identity_network();
    let input = Interval::new(0.0, 1.0);
    let result = ibp_sensitivity(&w, &b, &input, 0.0);
    assert!((result.input_width - 1.0).abs() < 1e-10);
    // With zero epsilon, output width is same as original
    assert!((result.output_width - 1.0).abs() < 1e-10);
}

#[test]
fn test_sensitivity_point_input() {
    let (w, b) = identity_network();
    let input = Interval::point(0.0);
    let result = ibp_sensitivity(&w, &b, &input, 0.5);
    assert!((result.input_width - 0.0).abs() < 1e-10);
    // Perturbed: [-0.5, 0.5], width=1.0
    assert!((result.output_width - 1.0).abs() < 1e-10);
}

#[test]
fn test_sensitivity_two_layer() {
    let (w, b) = two_layer_network();
    let input = Interval::new(0.0, 1.0);
    let result = ibp_sensitivity(&w, &b, &input, 0.1);
    // Just verify structural correctness
    assert!(result.output_width >= 0.0);
    assert!(result.input_width >= 0.0);
}
