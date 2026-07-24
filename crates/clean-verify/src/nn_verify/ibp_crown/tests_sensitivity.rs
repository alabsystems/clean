// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for IBP batch sensitivity analysis.

use super::ibp::Interval;
use super::sensitivity::{
    bound_width_statistics, composition_sensitivity, identify_critical_neurons, input_sensitivity,
    layer_amplification_factor, relu_tightness_ratio, BoundWidthStats,
};

const EPS: f64 = 1e-10;

fn approx_eq(a: f64, b: f64) -> bool {
    (a - b).abs() < EPS
}

// ---- input_sensitivity ----

#[test]
fn test_input_sensitivity_identity_matrix() {
    // Identity: each output depends on exactly one input.
    let weights = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let bounds = vec![Interval::new(0.0, 2.0), Interval::new(1.0, 4.0)];
    let sens = input_sensitivity(&weights, &bounds);
    assert!(approx_eq(sens[0], 2.0)); // |1|*2 + |0|*3
    assert!(approx_eq(sens[1], 3.0)); // |0|*2 + |1|*3
}

#[test]
fn test_input_sensitivity_scaling_matrix() {
    // Diagonal with scaling factors.
    let weights = vec![vec![3.0, 0.0], vec![0.0, 5.0]];
    let bounds = vec![Interval::new(0.0, 1.0), Interval::new(0.0, 1.0)];
    let sens = input_sensitivity(&weights, &bounds);
    assert!(approx_eq(sens[0], 3.0));
    assert!(approx_eq(sens[1], 5.0));
}

#[test]
fn test_input_sensitivity_mixed_signs() {
    // Negative weights still contribute via absolute value.
    let weights = vec![vec![-2.0, 3.0]];
    let bounds = vec![Interval::new(0.0, 1.0), Interval::new(0.0, 2.0)];
    let sens = input_sensitivity(&weights, &bounds);
    // |-2|*1 + |3|*2 = 2 + 6 = 8
    assert!(approx_eq(sens[0], 8.0));
}

#[test]
fn test_input_sensitivity_zero_width_inputs() {
    // Point intervals contribute zero sensitivity.
    let weights = vec![vec![5.0, 10.0]];
    let bounds = vec![Interval::point(1.0), Interval::point(2.0)];
    let sens = input_sensitivity(&weights, &bounds);
    assert!(approx_eq(sens[0], 0.0));
}

#[test]
fn test_input_sensitivity_empty_weights() {
    let weights: Vec<Vec<f64>> = vec![];
    let bounds = vec![Interval::new(0.0, 1.0)];
    let sens = input_sensitivity(&weights, &bounds);
    assert!(sens.is_empty());
}

// ---- layer_amplification_factor ----

#[test]
fn test_amplification_identity() {
    let weights = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    assert!(approx_eq(layer_amplification_factor(&weights), 1.0));
}

#[test]
fn test_amplification_scaling() {
    let weights = vec![vec![3.0, 0.0], vec![0.0, 5.0]];
    assert!(approx_eq(layer_amplification_factor(&weights), 5.0));
}

#[test]
fn test_amplification_orthogonal() {
    // Rotation matrix: each row has L1 norm = |cos| + |sin|.
    // For 45 degrees: [0.707, 0.707] -> L1 norm ~ 1.414
    let c = std::f64::consts::FRAC_1_SQRT_2;
    let weights = vec![vec![c, -c], vec![c, c]];
    let factor = layer_amplification_factor(&weights);
    assert!(approx_eq(factor, 2.0 * c)); // ~1.4142
}

#[test]
fn test_amplification_negative_weights() {
    let weights = vec![vec![-3.0, -2.0]];
    assert!(approx_eq(layer_amplification_factor(&weights), 5.0));
}

#[test]
fn test_amplification_empty() {
    let weights: Vec<Vec<f64>> = vec![];
    assert!(approx_eq(layer_amplification_factor(&weights), 0.0));
}

// ---- relu_tightness_ratio ----

#[test]
fn test_relu_tightness_all_positive() {
    let bounds = vec![
        Interval::new(1.0, 2.0),
        Interval::new(0.0, 5.0),
        Interval::new(3.0, 4.0),
    ];
    assert!(approx_eq(relu_tightness_ratio(&bounds), 1.0));
}

#[test]
fn test_relu_tightness_all_negative() {
    let bounds = vec![Interval::new(-5.0, -1.0), Interval::new(-3.0, 0.0)];
    assert!(approx_eq(relu_tightness_ratio(&bounds), 1.0));
}

#[test]
fn test_relu_tightness_all_crossing() {
    let bounds = vec![Interval::new(-1.0, 1.0), Interval::new(-2.0, 3.0)];
    assert!(approx_eq(relu_tightness_ratio(&bounds), 0.0));
}

#[test]
fn test_relu_tightness_mixed() {
    let bounds = vec![
        Interval::new(1.0, 2.0),   // positive (tight)
        Interval::new(-1.0, 1.0),  // crossing
        Interval::new(-3.0, -1.0), // negative (tight)
        Interval::new(-0.5, 0.5),  // crossing
    ];
    assert!(approx_eq(relu_tightness_ratio(&bounds), 0.5));
}

#[test]
fn test_relu_tightness_empty() {
    assert!(approx_eq(relu_tightness_ratio(&[]), 1.0));
}

// ---- composition_sensitivity ----

#[test]
fn test_composition_single_layer() {
    assert!(approx_eq(composition_sensitivity(&[3.0]), 3.0));
}

#[test]
fn test_composition_chain() {
    assert!(approx_eq(composition_sensitivity(&[2.0, 3.0, 4.0]), 24.0));
}

#[test]
fn test_composition_identity() {
    // Product of 1s = 1.
    assert!(approx_eq(composition_sensitivity(&[1.0, 1.0, 1.0]), 1.0));
}

#[test]
fn test_composition_empty() {
    // Empty product = 1.0 (identity element for multiplication).
    assert!(approx_eq(composition_sensitivity(&[]), 1.0));
}

#[test]
fn test_composition_with_zero() {
    // A zero layer kills all sensitivity.
    assert!(approx_eq(composition_sensitivity(&[5.0, 0.0, 3.0]), 0.0));
}

#[test]
fn test_composition_fractional() {
    // Sub-unitary layers reduce sensitivity.
    let result = composition_sensitivity(&[0.5, 0.5]);
    assert!(approx_eq(result, 0.25));
}

// ---- identify_critical_neurons ----

#[test]
fn test_critical_neurons_none() {
    // All positive — no crossing neurons.
    let bounds = vec![Interval::new(1.0, 2.0), Interval::new(0.5, 3.0)];
    let critical = identify_critical_neurons(&bounds, 0.0);
    assert!(critical.is_empty());
}

#[test]
fn test_critical_neurons_all_crossing() {
    let bounds = vec![
        Interval::new(-1.0, 2.0), // width 3.0
        Interval::new(-2.0, 1.0), // width 3.0
    ];
    let critical = identify_critical_neurons(&bounds, 0.0);
    assert_eq!(critical, vec![0, 1]);
}

#[test]
fn test_critical_neurons_threshold_filters() {
    let bounds = vec![
        Interval::new(-0.1, 0.1), // width 0.2 — below threshold
        Interval::new(-1.0, 2.0), // width 3.0 — above threshold
        Interval::new(-0.5, 0.5), // width 1.0 — at threshold (not above)
    ];
    let critical = identify_critical_neurons(&bounds, 1.0);
    assert_eq!(critical, vec![1]);
}

#[test]
fn test_critical_neurons_empty_bounds() {
    let critical = identify_critical_neurons(&[], 0.0);
    assert!(critical.is_empty());
}

#[test]
fn test_critical_neurons_negative_only_excluded() {
    // Negative-only neurons are tight, not critical.
    let bounds = vec![
        Interval::new(-5.0, -1.0),
        Interval::new(-0.5, 0.5), // crossing, width 1.0
    ];
    let critical = identify_critical_neurons(&bounds, 0.0);
    assert_eq!(critical, vec![1]);
}

// ---- bound_width_statistics ----

#[test]
fn test_width_stats_uniform() {
    let bounds = vec![
        Interval::new(0.0, 2.0),
        Interval::new(1.0, 3.0),
        Interval::new(5.0, 7.0),
    ];
    let stats = bound_width_statistics(&bounds).unwrap();
    assert!(approx_eq(stats.min, 2.0));
    assert!(approx_eq(stats.max, 2.0));
    assert!(approx_eq(stats.mean, 2.0));
    assert!(approx_eq(stats.median, 2.0));
    assert_eq!(stats.count, 3);
}

#[test]
fn test_width_stats_varied() {
    let bounds = vec![
        Interval::new(0.0, 1.0), // width 1
        Interval::new(0.0, 3.0), // width 3
        Interval::new(0.0, 5.0), // width 5
        Interval::new(0.0, 7.0), // width 7
    ];
    let stats = bound_width_statistics(&bounds).unwrap();
    assert!(approx_eq(stats.min, 1.0));
    assert!(approx_eq(stats.max, 7.0));
    assert!(approx_eq(stats.mean, 4.0));
    // Even count: median = (3+5)/2 = 4
    assert!(approx_eq(stats.median, 4.0));
    assert_eq!(stats.count, 4);
}

#[test]
fn test_width_stats_single() {
    let bounds = vec![Interval::new(1.0, 4.0)];
    let stats = bound_width_statistics(&bounds).unwrap();
    assert!(approx_eq(stats.min, 3.0));
    assert!(approx_eq(stats.max, 3.0));
    assert!(approx_eq(stats.mean, 3.0));
    assert!(approx_eq(stats.median, 3.0));
    assert_eq!(stats.count, 1);
}

#[test]
fn test_width_stats_empty() {
    assert!(bound_width_statistics(&[]).is_none());
}

#[test]
fn test_width_stats_point_intervals() {
    let bounds = vec![Interval::point(1.0), Interval::point(2.0)];
    let stats = bound_width_statistics(&bounds).unwrap();
    assert!(approx_eq(stats.min, 0.0));
    assert!(approx_eq(stats.max, 0.0));
    assert!(approx_eq(stats.mean, 0.0));
    assert!(approx_eq(stats.median, 0.0));
    assert_eq!(stats.count, 2);
}

#[test]
fn test_width_stats_odd_count_median() {
    // Odd count: median is the middle element.
    let bounds = vec![
        Interval::new(0.0, 1.0),  // width 1
        Interval::new(0.0, 10.0), // width 10
        Interval::new(0.0, 3.0),  // width 3
    ];
    let stats = bound_width_statistics(&bounds).unwrap();
    assert!(approx_eq(stats.median, 3.0));
}

// ---- BoundWidthStats ----

#[test]
fn test_bound_width_stats_debug_impl() {
    let stats = BoundWidthStats {
        min: 1.0,
        max: 5.0,
        mean: 3.0,
        median: 3.0,
        count: 3,
    };
    let debug = format!("{stats:?}");
    assert!(debug.contains("BoundWidthStats"));
    assert!(debug.contains("min"));
}

#[test]
fn test_bound_width_stats_clone() {
    let stats = BoundWidthStats {
        min: 1.0,
        max: 5.0,
        mean: 3.0,
        median: 3.0,
        count: 3,
    };
    let cloned = stats;
    assert!(approx_eq(cloned.min, stats.min));
    assert_eq!(cloned.count, stats.count);
}
