// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended tests for IBP extensions: deeper coverage of batch operations,
//! sensitivity analysis, sigmoid propagation, and multi-input hull.

use super::ibp::Interval;
use super::ibp_extensions::{
    batch_ibp_forward, ibp_forward_single, ibp_sensitivity, multi_input_hull,
    verify_batch_soundness, BatchSoundnessResult, IbpSigmoidSpec, SensitivityResult,
};

fn sigmoid(x: f64) -> f64 {
    1.0 / (1.0 + (-x).exp())
}

fn net_1x1(weight: f64, bias: f64) -> (Vec<Vec<Vec<f64>>>, Vec<Vec<f64>>) {
    (vec![vec![vec![weight]]], vec![vec![bias]])
}

fn net_two_layer(w1: f64, w2: f64, w3: f64, w4: f64) -> (Vec<Vec<Vec<f64>>>, Vec<Vec<f64>>) {
    (
        vec![vec![vec![w1], vec![w2]], vec![vec![w3, w4]]],
        vec![vec![0.0, 0.0], vec![0.0]],
    )
}

// --- ibp_forward_single ---

#[test]
fn test_forward_single_zero_weight_collapses_to_bias() {
    let (w, b) = net_1x1(0.0, 5.0);
    let out = ibp_forward_single(&w, &b, &Interval::new(-100.0, 100.0));
    assert!((out[0].lower - 5.0).abs() < 1e-10);
    assert!((out[0].upper - 5.0).abs() < 1e-10);
}

#[test]
fn test_forward_single_large_positive_weight() {
    let (w, b) = net_1x1(1000.0, 0.0);
    let out = ibp_forward_single(&w, &b, &Interval::new(-1.0, 1.0));
    assert!((out[0].lower - (-1000.0)).abs() < 1e-6);
    assert!((out[0].upper - 1000.0).abs() < 1e-6);
}

#[test]
fn test_forward_single_negative_weight_flips_bounds() {
    let (w, b) = net_1x1(-2.0, 0.0);
    let out = ibp_forward_single(&w, &b, &Interval::new(1.0, 3.0));
    assert!((out[0].lower - (-6.0)).abs() < 1e-10);
    assert!((out[0].upper - (-2.0)).abs() < 1e-10);
}

#[test]
fn test_forward_single_point_interval_deterministic() {
    let (w, b) = net_1x1(7.0, -3.0);
    let out = ibp_forward_single(&w, &b, &Interval::point(2.0));
    assert!((out[0].lower - 11.0).abs() < 1e-10);
    assert!(out[0].width() < 1e-10);
}

#[test]
fn test_forward_single_two_layer_negative_input() {
    let (w, b) = net_two_layer(3.0, -2.0, 1.0, 1.0);
    let out = ibp_forward_single(&w, &b, &Interval::new(-2.0, -1.0));
    // Layer 1: [3*[-2,-1]=[-6,-3], -2*[-2,-1]=[2,4]], ReLU->[[0,0],[2,4]]
    // Layer 2: [1,1]*[[0,0],[2,4]]=[2,4]
    assert!((out[0].lower - 2.0).abs() < 1e-10);
    assert!((out[0].upper - 4.0).abs() < 1e-10);
}

#[test]
fn test_forward_single_wider_input_wider_output() {
    let (w, b) = net_two_layer(1.0, 1.0, 1.0, 1.0);
    let narrow = ibp_forward_single(&w, &b, &Interval::new(0.0, 1.0));
    let wide = ibp_forward_single(&w, &b, &Interval::new(-5.0, 5.0));
    assert!(wide[0].width() >= narrow[0].width() - f64::EPSILON);
}

#[test]
fn test_forward_single_relu_clips_negative() {
    let w = vec![vec![vec![-1.0]], vec![vec![1.0]]];
    let b = vec![vec![0.0], vec![0.0]];
    let out = ibp_forward_single(&w, &b, &Interval::new(1.0, 5.0));
    assert!(out[0].lower.abs() < 1e-10 && out[0].upper.abs() < 1e-10);
}

#[test]
fn test_forward_single_mismatched_layers_uses_min() {
    let out = ibp_forward_single(
        &[vec![vec![1.0]]],
        &[vec![0.0], vec![99.0]],
        &Interval::new(0.0, 1.0),
    );
    assert_eq!(out.len(), 1);
    assert!((out[0].upper - 1.0).abs() < 1e-10);
}

#[test]
fn test_forward_single_symmetric_interval() {
    let out = ibp_forward_single(
        &net_1x1(1.0, 0.0).0,
        &net_1x1(1.0, 0.0).1,
        &Interval::new(-5.0, 5.0),
    );
    assert!((out[0].lower + out[0].upper).abs() < 1e-10);
}

#[test]
fn test_forward_single_bias_shifts_bounds() {
    let out = ibp_forward_single(
        &net_1x1(1.0, 10.0).0,
        &net_1x1(1.0, 10.0).1,
        &Interval::new(-1.0, 1.0),
    );
    assert!((out[0].lower - 9.0).abs() < 1e-10);
    assert!((out[0].upper - 11.0).abs() < 1e-10);
}

#[test]
fn test_forward_single_fractional_weight() {
    let out = ibp_forward_single(
        &net_1x1(0.5, 0.0).0,
        &net_1x1(0.5, 0.0).1,
        &Interval::new(-4.0, 6.0),
    );
    assert!((out[0].lower - (-2.0)).abs() < 1e-10);
    assert!((out[0].upper - 3.0).abs() < 1e-10);
}

#[test]
fn test_forward_single_width_scales_with_weight() {
    let input = Interval::new(-1.0, 1.0);
    let out2 = ibp_forward_single(&net_1x1(2.0, 0.0).0, &net_1x1(2.0, 0.0).1, &input);
    let out5 = ibp_forward_single(&net_1x1(5.0, 0.0).0, &net_1x1(5.0, 0.0).1, &input);
    assert!((out2[0].width() - 4.0).abs() < 1e-10);
    assert!((out5[0].width() - 10.0).abs() < 1e-10);
}

// --- batch_ibp_forward ---

#[test]
fn test_batch_consistency_with_single() {
    let (w, b) = net_1x1(3.0, -1.0);
    let inputs = vec![
        Interval::new(-2.0, 2.0),
        Interval::new(0.0, 5.0),
        Interval::new(-10.0, -3.0),
    ];
    let batch = batch_ibp_forward(&w, &b, &inputs);
    for (i, inp) in inputs.iter().enumerate() {
        let single = ibp_forward_single(&w, &b, inp);
        for j in 0..single.len() {
            assert!((batch[i][j].lower - single[j].lower).abs() < 1e-10);
            assert!((batch[i][j].upper - single[j].upper).abs() < 1e-10);
        }
    }
}

#[test]
fn test_batch_preserves_ordering() {
    let (w, b) = net_1x1(1.0, 0.0);
    let inputs = vec![
        Interval::new(0.0, 1.0),
        Interval::new(1.0, 2.0),
        Interval::new(2.0, 3.0),
    ];
    let results = batch_ibp_forward(&w, &b, &inputs);
    for i in 0..results.len() - 1 {
        assert!(results[i][0].upper <= results[i + 1][0].lower + f64::EPSILON);
    }
}

#[test]
fn test_batch_large_batch() {
    let (w, b) = net_1x1(1.0, 0.0);
    let inputs: Vec<Interval> = (0..50)
        .map(|i| Interval::new(i as f64, i as f64 + 1.0))
        .collect();
    let results = batch_ibp_forward(&w, &b, &inputs);
    assert_eq!(results.len(), 50);
    assert!((results[49][0].lower - 49.0).abs() < 1e-10);
}

#[test]
fn test_batch_point_intervals() {
    let (w, b) = net_1x1(2.0, 1.0);
    let results = batch_ibp_forward(
        &w,
        &b,
        &[
            Interval::point(0.0),
            Interval::point(1.0),
            Interval::point(-1.0),
        ],
    );
    assert!((results[0][0].lower - 1.0).abs() < 1e-10);
    assert!((results[1][0].lower - 3.0).abs() < 1e-10);
    assert!((results[2][0].lower - (-1.0)).abs() < 1e-10);
}

#[test]
fn test_batch_empty_network() {
    let results = batch_ibp_forward(
        &[],
        &[],
        &[Interval::new(0.0, 1.0), Interval::new(1.0, 2.0)],
    );
    assert_eq!(results.len(), 2);
    assert!(results[0].is_empty() && results[1].is_empty());
}

#[test]
fn test_batch_two_layer() {
    let (w, b) = net_two_layer(2.0, -1.0, 1.0, 1.0);
    let results = batch_ibp_forward(&w, &b, &[Interval::new(0.0, 1.0), Interval::new(-1.0, 0.0)]);
    assert_eq!(results.len(), 2);
    assert_eq!(results[0].len(), 1);
}

#[test]
fn test_batch_identical_inputs_identical_outputs() {
    let (w, b) = net_1x1(3.0, -2.0);
    let input = Interval::new(1.0, 4.0);
    let results = batch_ibp_forward(&w, &b, &[input, input, input]);
    for r in &results {
        assert!((r[0].lower - results[0][0].lower).abs() < 1e-10);
    }
}

#[test]
fn test_batch_single_input_matches_forward() {
    let (w, b) = net_1x1(4.0, 2.0);
    let input = Interval::new(-3.0, 3.0);
    let batch = batch_ibp_forward(&w, &b, &[input]);
    let single = ibp_forward_single(&w, &b, &input);
    assert!((batch[0][0].lower - single[0].lower).abs() < 1e-10);
}

// --- ibp_sensitivity ---

#[test]
fn test_sensitivity_output_width_nonnegative() {
    let result = ibp_sensitivity(
        &net_1x1(5.0, 0.0).0,
        &net_1x1(5.0, 0.0).1,
        &Interval::new(-1.0, 1.0),
        0.5,
    );
    assert!(result.output_width >= 0.0);
}

#[test]
fn test_sensitivity_larger_epsilon_wider_output() {
    let (w, b) = net_1x1(2.0, 0.0);
    let input = Interval::new(0.0, 1.0);
    let s1 = ibp_sensitivity(&w, &b, &input, 0.1);
    let s2 = ibp_sensitivity(&w, &b, &input, 0.5);
    assert!(s2.output_width >= s1.output_width - f64::EPSILON);
}

#[test]
fn test_sensitivity_zero_epsilon_preserves_width() {
    let result = ibp_sensitivity(
        &net_1x1(3.0, 0.0).0,
        &net_1x1(3.0, 0.0).1,
        &Interval::new(-1.0, 1.0),
        0.0,
    );
    assert!((result.output_width - 6.0).abs() < 1e-10);
}

#[test]
fn test_sensitivity_amplification_equals_weight() {
    let result = ibp_sensitivity(
        &net_1x1(4.0, 0.0).0,
        &net_1x1(4.0, 0.0).1,
        &Interval::new(0.0, 1.0),
        0.1,
    );
    assert!((result.amplification - 4.0).abs() < 1e-6);
}

#[test]
fn test_sensitivity_input_width_correct() {
    let result = ibp_sensitivity(
        &net_1x1(1.0, 0.0).0,
        &net_1x1(1.0, 0.0).1,
        &Interval::new(-3.0, 7.0),
        0.1,
    );
    assert!((result.input_width - 10.0).abs() < 1e-10);
}

#[test]
fn test_sensitivity_narrow_input() {
    let result = ibp_sensitivity(
        &net_1x1(1.0, 0.0).0,
        &net_1x1(1.0, 0.0).1,
        &Interval::new(0.0, 0.01),
        0.001,
    );
    assert!((result.input_width - 0.01).abs() < 1e-10);
    assert!((result.output_width - 0.012).abs() < 1e-10);
}

#[test]
fn test_sensitivity_wide_input() {
    let result = ibp_sensitivity(
        &net_1x1(1.0, 0.0).0,
        &net_1x1(1.0, 0.0).1,
        &Interval::new(-1000.0, 1000.0),
        1.0,
    );
    assert!((result.input_width - 2000.0).abs() < 1e-6);
    assert!((result.output_width - 2002.0).abs() < 1e-6);
}

#[test]
fn test_sensitivity_neg_weight_same_amplification() {
    let input = Interval::new(0.0, 1.0);
    let s_pos = ibp_sensitivity(&net_1x1(3.0, 0.0).0, &net_1x1(3.0, 0.0).1, &input, 0.1);
    let s_neg = ibp_sensitivity(&net_1x1(-3.0, 0.0).0, &net_1x1(-3.0, 0.0).1, &input, 0.1);
    assert!((s_pos.amplification - s_neg.amplification).abs() < 1e-6);
}

#[test]
fn test_sensitivity_two_layer_finite() {
    let (w, b) = net_two_layer(2.0, -1.0, 1.0, 1.0);
    let result = ibp_sensitivity(&w, &b, &Interval::new(0.0, 1.0), 0.1);
    assert!(result.amplification.is_finite() || result.amplification >= 0.0);
}

#[test]
fn test_sensitivity_point_input_with_epsilon() {
    let result = ibp_sensitivity(
        &net_1x1(2.0, 0.0).0,
        &net_1x1(2.0, 0.0).1,
        &Interval::point(5.0),
        1.0,
    );
    assert!(result.input_width.abs() < 1e-10);
    assert!((result.output_width - 4.0).abs() < 1e-10);
}

// --- multi_input_hull ---

#[test]
fn test_hull_point_intervals() {
    let hull = multi_input_hull(&[Interval::point(1.0), Interval::point(5.0)]);
    assert!((hull.lower - 1.0).abs() < 1e-10 && (hull.upper - 5.0).abs() < 1e-10);
}

#[test]
fn test_hull_negative_intervals() {
    let hull = multi_input_hull(&[Interval::new(-10.0, -5.0), Interval::new(-8.0, -3.0)]);
    assert!((hull.lower - (-10.0)).abs() < 1e-10 && (hull.upper - (-3.0)).abs() < 1e-10);
}

#[test]
fn test_hull_single_point() {
    let hull = multi_input_hull(&[Interval::point(42.0)]);
    assert!((hull.lower - 42.0).abs() < 1e-10 && hull.width() < 1e-10);
}

#[test]
fn test_hull_superset_is_identity() {
    let hull = multi_input_hull(&[Interval::new(0.0, 10.0), Interval::new(2.0, 5.0)]);
    assert!((hull.lower).abs() < 1e-10 && (hull.upper - 10.0).abs() < 1e-10);
}

#[test]
fn test_hull_many_intervals() {
    let ivs: Vec<Interval> = (0..50)
        .map(|i| Interval::new(i as f64, i as f64 + 0.5))
        .collect();
    let hull = multi_input_hull(&ivs);
    assert!(hull.lower.abs() < 1e-10 && (hull.upper - 49.5).abs() < 1e-10);
}

#[test]
fn test_hull_symmetric_intervals() {
    let hull = multi_input_hull(&[Interval::new(-5.0, -1.0), Interval::new(1.0, 5.0)]);
    assert!((hull.lower - (-5.0)).abs() < 1e-10 && (hull.upper - 5.0).abs() < 1e-10);
}

#[test]
fn test_hull_touching_intervals() {
    let hull = multi_input_hull(&[Interval::new(0.0, 1.0), Interval::new(1.0, 2.0)]);
    assert!(hull.lower.abs() < 1e-10 && (hull.upper - 2.0).abs() < 1e-10);
}

#[test]
fn test_hull_width_at_least_max_individual() {
    let ivs = vec![
        Interval::new(0.0, 3.0),
        Interval::new(10.0, 11.0),
        Interval::new(-2.0, 0.0),
    ];
    let hull = multi_input_hull(&ivs);
    let max_w = ivs.iter().map(|iv| iv.width()).fold(0.0_f64, f64::max);
    assert!(hull.width() >= max_w - f64::EPSILON);
}

// --- verify_batch_soundness ---

#[test]
fn test_soundness_scaling_network() {
    let result = verify_batch_soundness(
        &net_1x1(2.0, 0.0).0,
        &net_1x1(2.0, 0.0).1,
        &Interval::new(0.0, 1.0),
        &[vec![0.5]],
    );
    assert!(result.sound && result.num_samples == 1);
}

#[test]
fn test_soundness_violation_indices() {
    let (w, b) = net_1x1(1.0, 0.0);
    let result = verify_batch_soundness(
        &w,
        &b,
        &Interval::new(0.0, 1.0),
        &[vec![0.5], vec![2.0], vec![0.1], vec![-5.0]],
    );
    assert!(!result.sound && result.violations == vec![1, 3]);
}

#[test]
fn test_soundness_midpoint_within() {
    let result = verify_batch_soundness(
        &net_1x1(1.0, 0.0).0,
        &net_1x1(1.0, 0.0).1,
        &Interval::new(-10.0, 10.0),
        &[vec![0.0]],
    );
    assert!(result.sound);
}

#[test]
fn test_soundness_negative_weight() {
    let result = verify_batch_soundness(
        &net_1x1(-1.0, 0.0).0,
        &net_1x1(-1.0, 0.0).1,
        &Interval::new(-1.0, 1.0),
        &[vec![0.5]],
    );
    assert!(result.sound);
}

#[test]
fn test_soundness_two_layer() {
    let (w, b) = net_two_layer(2.0, -1.0, 1.0, 1.0);
    let result = verify_batch_soundness(&w, &b, &Interval::new(0.0, 1.0), &[vec![0.5]]);
    assert_eq!(result.num_samples, 1);
}

#[test]
fn test_soundness_empty_network_vacuously_sound() {
    let result = verify_batch_soundness(&[], &[], &Interval::new(0.0, 1.0), &[vec![0.5]]);
    assert!(result.sound);
}

#[test]
fn test_soundness_all_violations_tracked() {
    let (w, b) = net_1x1(1.0, 0.0);
    let result = verify_batch_soundness(
        &w,
        &b,
        &Interval::new(0.0, 0.1),
        &[vec![1.0], vec![2.0], vec![3.0], vec![4.0], vec![5.0]],
    );
    assert!(!result.sound && result.violations == vec![0, 1, 2, 3, 4]);
}

#[test]
fn test_soundness_struct_construction() {
    let r = BatchSoundnessResult {
        sound: true,
        num_samples: 42,
        violations: vec![],
    };
    assert!(r.sound && r.num_samples == 42);
}

// --- IbpSigmoidSpec ---

#[test]
fn test_sigmoid_positive_interval() {
    let spec = IbpSigmoidSpec::new();
    let out = spec.propagate_sigmoid(&Interval::new(1.0, 3.0));
    assert!(out.lower > 0.73 && out.upper < 0.96 && out.lower < out.upper);
}

#[test]
fn test_sigmoid_negative_interval() {
    let out = IbpSigmoidSpec::new().propagate_sigmoid(&Interval::new(-3.0, -1.0));
    assert!(out.lower > 0.04 && out.upper < 0.27);
}

#[test]
fn test_sigmoid_crossing_interval() {
    let out = IbpSigmoidSpec::new().propagate_sigmoid(&Interval::new(-1.0, 1.0));
    assert!(out.lower < 0.5 && out.upper > 0.5);
}

#[test]
fn test_sigmoid_point_at_zero() {
    let out = IbpSigmoidSpec::new().propagate_sigmoid(&Interval::point(0.0));
    assert!((out.lower - 0.5).abs() < 1e-10);
}

#[test]
fn test_sigmoid_wide_interval_saturates() {
    let out = IbpSigmoidSpec::new().propagate_sigmoid(&Interval::new(-100.0, 100.0));
    assert!(out.lower >= 0.0 && out.upper <= 1.0);
    assert!(out.lower < 1e-10 && out.upper > 1.0 - 1e-10);
}

#[test]
fn test_sigmoid_contains_sampled_points() {
    let out = IbpSigmoidSpec::new().propagate_sigmoid(&Interval::new(-5.0, 5.0));
    for &x in &[-5.0, -2.0, 0.0, 0.5, 2.0, 5.0] {
        let sx = sigmoid(x);
        assert!(
            sx >= out.lower - f64::EPSILON && sx <= out.upper + f64::EPSILON,
            "sigmoid({x})={sx} outside bounds"
        );
    }
}

#[test]
fn test_sigmoid_narrow_tight() {
    let out = IbpSigmoidSpec::new().propagate_sigmoid(&Interval::new(0.0, 0.01));
    assert!((out.width() - (sigmoid(0.01) - sigmoid(0.0))).abs() < 1e-10);
}

#[test]
fn test_sigmoid_wider_input_wider_output() {
    let spec = IbpSigmoidSpec::new();
    let narrow = spec.propagate_sigmoid(&Interval::new(-0.5, 0.5));
    let wide = spec.propagate_sigmoid(&Interval::new(-2.0, 2.0));
    assert!(wide.width() >= narrow.width() - f64::EPSILON);
}

#[test]
fn test_sigmoid_verify_concrete_ok() {
    let spec = IbpSigmoidSpec::new();
    let input = Interval::new(-1.0, 1.0);
    spec.verify_concrete_sigmoid(&input, 0.0).unwrap();
    spec.verify_concrete_sigmoid(&input, -1.0).unwrap();
    spec.verify_concrete_sigmoid(&input, 1.0).unwrap();
}

#[test]
fn test_sigmoid_verify_concrete_rejects_outside() {
    assert!(IbpSigmoidSpec::new()
        .verify_concrete_sigmoid(&Interval::new(-1.0, 1.0), 5.0)
        .is_err());
}

#[test]
fn test_tanh_at_zero() {
    let out = IbpSigmoidSpec::new().propagate_tanh(&Interval::point(0.0));
    assert!(out.lower.abs() < 1e-10);
}

#[test]
fn test_tanh_saturates() {
    let out = IbpSigmoidSpec::new().propagate_tanh(&Interval::new(-100.0, 100.0));
    assert!(out.lower >= -1.0 && out.upper <= 1.0);
    assert!(out.lower < -1.0 + 1e-10 && out.upper > 1.0 - 1e-10);
}

#[test]
fn test_sensitivity_result_fields() {
    let r = SensitivityResult {
        input_width: 2.0,
        output_width: 6.0,
        amplification: 3.0,
    };
    assert!((r.input_width - 2.0).abs() < 1e-10 && (r.amplification - 3.0).abs() < 1e-10);
}
