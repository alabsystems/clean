// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for ReLU stability analysis.

use super::stability::*;
use crate::nn_verify::ibp_crown::Interval;

// ---------------------------------------------------------------------------
// Neuron classification
// ---------------------------------------------------------------------------

#[test]
fn test_classify_neuron_stably_active() {
    let bounds = Interval::new(0.5, 2.0);
    assert_eq!(classify_neuron(bounds), NeuronStability::StablyActive);
    assert!(classify_neuron(bounds).is_stable());
}

#[test]
fn test_classify_neuron_stably_inactive() {
    let bounds = Interval::new(-3.0, -0.1);
    assert_eq!(classify_neuron(bounds), NeuronStability::StablyInactive);
    assert!(classify_neuron(bounds).is_stable());
}

#[test]
fn test_classify_neuron_unstable_crossing() {
    let bounds = Interval::new(-1.0, 1.0);
    assert_eq!(classify_neuron(bounds), NeuronStability::Unstable);
    assert!(!classify_neuron(bounds).is_stable());
}

#[test]
fn test_classify_neuron_boundary_at_zero_lower() {
    // l = 0.0 is NOT stably active (strict inequality)
    let bounds = Interval::new(0.0, 1.0);
    assert_eq!(classify_neuron(bounds), NeuronStability::Unstable);
}

#[test]
fn test_classify_neuron_boundary_at_zero_upper() {
    // u = 0.0 is NOT stably inactive (strict inequality)
    let bounds = Interval::new(-1.0, 0.0);
    assert_eq!(classify_neuron(bounds), NeuronStability::Unstable);
}

#[test]
fn test_classify_neuron_point_interval_positive() {
    let bounds = Interval::new(1.0, 1.0);
    assert_eq!(classify_neuron(bounds), NeuronStability::StablyActive);
}

#[test]
fn test_classify_neuron_point_interval_negative() {
    let bounds = Interval::new(-1.0, -1.0);
    assert_eq!(classify_neuron(bounds), NeuronStability::StablyInactive);
}

#[test]
fn test_classify_neuron_point_at_zero() {
    let bounds = Interval::new(0.0, 0.0);
    assert_eq!(classify_neuron(bounds), NeuronStability::Unstable);
}

// ---------------------------------------------------------------------------
// Exact ReLU output
// ---------------------------------------------------------------------------

#[test]
fn test_exact_relu_output_stably_active() {
    let bounds = Interval::new(1.0, 3.0);
    let out = exact_relu_output(bounds).expect("stably active should be exact");
    assert!((out.lower - 1.0).abs() < f64::EPSILON);
    assert!((out.upper - 3.0).abs() < f64::EPSILON);
}

#[test]
fn test_exact_relu_output_stably_inactive() {
    let bounds = Interval::new(-5.0, -0.5);
    let out = exact_relu_output(bounds).expect("stably inactive should be exact");
    assert!((out.lower).abs() < f64::EPSILON);
    assert!((out.upper).abs() < f64::EPSILON);
}

#[test]
fn test_exact_relu_output_unstable_returns_none() {
    let bounds = Interval::new(-1.0, 1.0);
    assert!(exact_relu_output(bounds).is_none());
}

// ---------------------------------------------------------------------------
// Relaxation gap
// ---------------------------------------------------------------------------

#[test]
fn test_neuron_relaxation_gap_stable_is_zero() {
    assert!((neuron_relaxation_gap(Interval::new(1.0, 2.0))).abs() < f64::EPSILON);
    assert!((neuron_relaxation_gap(Interval::new(-3.0, -1.0))).abs() < f64::EPSILON);
}

#[test]
fn test_neuron_relaxation_gap_symmetric_crossing() {
    // [l, u] = [-1, 1], gap = 1*1 / (2*2) = 0.25
    let gap = neuron_relaxation_gap(Interval::new(-1.0, 1.0));
    assert!((gap - 0.25).abs() < 1e-10, "gap = {gap}, expected 0.25");
}

#[test]
fn test_neuron_relaxation_gap_asymmetric_crossing() {
    // [l, u] = [-2, 1], gap = 2*1 / (2*3) = 1/3
    let gap = neuron_relaxation_gap(Interval::new(-2.0, 1.0));
    let expected = 2.0 / 6.0;
    assert!(
        (gap - expected).abs() < 1e-10,
        "gap = {gap}, expected {expected}"
    );
}

#[test]
fn test_relaxation_gap_ratio_all_stable() {
    let bounds = vec![
        Interval::new(1.0, 2.0),
        Interval::new(0.5, 3.0),
        Interval::new(-3.0, -1.0),
    ];
    let ratio = relaxation_gap_ratio(&bounds);
    assert!(
        ratio.abs() < f64::EPSILON,
        "all stable should have 0 gap ratio"
    );
}

#[test]
fn test_relaxation_gap_ratio_all_unstable() {
    let bounds = vec![Interval::new(-1.0, 1.0), Interval::new(-1.0, 1.0)];
    let ratio = relaxation_gap_ratio(&bounds);
    // Each neuron: gap = 0.25, width = 1.0 (output range [0,1])
    // total gap = 0.5, total width = 2.0, ratio = 0.25
    assert!(
        (ratio - 0.25).abs() < 1e-10,
        "ratio = {ratio}, expected 0.25"
    );
}

// ---------------------------------------------------------------------------
// Layer analysis
// ---------------------------------------------------------------------------

#[test]
fn test_analyze_layer_stability_mixed() {
    let bounds = vec![
        Interval::new(1.0, 2.0),   // active
        Interval::new(-3.0, -0.5), // inactive
        Interval::new(-1.0, 1.0),  // unstable
        Interval::new(0.1, 5.0),   // active
    ];
    let classes = analyze_layer_stability(&bounds);
    assert_eq!(classes[0], NeuronStability::StablyActive);
    assert_eq!(classes[1], NeuronStability::StablyInactive);
    assert_eq!(classes[2], NeuronStability::Unstable);
    assert_eq!(classes[3], NeuronStability::StablyActive);
}

// ---------------------------------------------------------------------------
// Network-level analysis
// ---------------------------------------------------------------------------

#[test]
fn test_network_stability_all_stable() {
    let layers = vec![
        vec![Interval::new(1.0, 2.0), Interval::new(0.5, 1.5)],
        vec![Interval::new(-3.0, -1.0), Interval::new(-2.0, -0.5)],
    ];
    let report = analyze_network_stability(&layers);
    assert_eq!(report.total_neurons, 4);
    assert_eq!(report.stably_active, 2);
    assert_eq!(report.stably_inactive, 2);
    assert_eq!(report.unstable, 0);
    assert!(report.is_exact, "all stable should be exact");
    assert!((report.stability_ratio - 1.0).abs() < f64::EPSILON);
    assert!(report.total_relaxation_gap.abs() < f64::EPSILON);
}

#[test]
fn test_network_stability_mixed() {
    let layers = vec![
        vec![
            Interval::new(1.0, 2.0),  // active
            Interval::new(-1.0, 1.0), // unstable
        ],
        vec![
            Interval::new(-3.0, -0.5), // inactive
            Interval::new(-0.5, 0.5),  // unstable
            Interval::new(2.0, 4.0),   // active
        ],
    ];
    let report = analyze_network_stability(&layers);
    assert_eq!(report.total_neurons, 5);
    assert_eq!(report.stably_active, 2);
    assert_eq!(report.stably_inactive, 1);
    assert_eq!(report.unstable, 2);
    assert!(!report.is_exact);
    assert!((report.stability_ratio - 0.6).abs() < 1e-10);
    assert!(report.total_relaxation_gap > 0.0);
}

#[test]
fn test_network_stability_per_layer_counts() {
    let layers = vec![
        vec![Interval::new(1.0, 2.0), Interval::new(-1.0, 1.0)],
        vec![Interval::new(-3.0, -0.5)],
    ];
    let report = analyze_network_stability(&layers);
    assert_eq!(report.per_layer.len(), 2);
    assert_eq!(report.per_layer[0], (1, 0, 1)); // 1 active, 0 inactive, 1 unstable
    assert_eq!(report.per_layer[1], (0, 1, 0)); // 0 active, 1 inactive, 0 unstable
}

#[test]
fn test_network_stability_empty() {
    let layers: Vec<Vec<Interval>> = vec![];
    let report = analyze_network_stability(&layers);
    assert_eq!(report.total_neurons, 0);
    assert!(report.is_exact);
    assert!((report.stability_ratio - 1.0).abs() < f64::EPSILON);
}

// ---------------------------------------------------------------------------
// StabilityAnalyzer builder pattern
// ---------------------------------------------------------------------------

#[test]
fn test_stability_analyzer_incremental() {
    let mut analyzer = StabilityAnalyzer::new();
    analyzer.add_layer(vec![Interval::new(1.0, 2.0), Interval::new(-1.0, 1.0)]);
    analyzer.add_layer(vec![Interval::new(-3.0, -0.5)]);

    let report = analyzer.analyze();
    assert_eq!(report.total_neurons, 3);
    assert_eq!(report.stably_active, 1);
    assert_eq!(report.stably_inactive, 1);
    assert_eq!(report.unstable, 1);
}

// ---------------------------------------------------------------------------
// Concrete network: ACAS Xu-like 6-50-50-50-50-50-5 with known bounds
// ---------------------------------------------------------------------------

#[test]
fn test_acas_xu_like_network_stability() {
    // Simulated ACAS Xu-like network with 5 hidden layers of 50 neurons each.
    // In practice, many neurons are stable for small perturbation radii.
    let mut layers = Vec::new();

    // Layer 1: mostly positive pre-activations (after input normalization)
    let layer1: Vec<Interval> = (0..50)
        .map(|i| {
            if i < 40 {
                Interval::new(0.1 + (i as f64) * 0.05, 1.0 + (i as f64) * 0.1)
            } else {
                Interval::new(-0.5, 0.3) // 10 unstable
            }
        })
        .collect();
    layers.push(layer1);

    // Layer 2-5: similar pattern
    for _ in 1..5 {
        let layer: Vec<Interval> = (0..50)
            .map(|i| {
                if i < 35 {
                    Interval::new(0.05 + (i as f64) * 0.02, 0.5 + (i as f64) * 0.05)
                } else if i < 45 {
                    Interval::new(-2.0, -0.1) // stably inactive
                } else {
                    Interval::new(-0.3, 0.3) // unstable
                }
            })
            .collect();
        layers.push(layer);
    }

    let report = analyze_network_stability(&layers);
    assert_eq!(report.total_neurons, 250); // 5 layers * 50 neurons
                                           // Layer 1: 40 active + 10 unstable
                                           // Layers 2-5: 35 active + 10 inactive + 5 unstable each = 4 * (35+10+5)
    let expected_active = 40 + 4 * 35; // 180
    let expected_inactive = 4 * 10; // 40
    let expected_unstable = 10 + 4 * 5; // 30
    assert_eq!(report.stably_active, expected_active);
    assert_eq!(report.stably_inactive, expected_inactive);
    assert_eq!(report.unstable, expected_unstable);
    assert!(!report.is_exact);
    // Stability ratio = 220/250 = 0.88
    assert!(
        (report.stability_ratio - 0.88).abs() < 1e-10,
        "stability_ratio = {}, expected 0.88",
        report.stability_ratio
    );
}

// ---------------------------------------------------------------------------
// Relaxation gap monotonicity: wider crossing intervals have larger gaps
// ---------------------------------------------------------------------------

#[test]
fn test_relaxation_gap_increases_with_crossing_width() {
    let narrow = neuron_relaxation_gap(Interval::new(-0.1, 0.1));
    let medium = neuron_relaxation_gap(Interval::new(-1.0, 1.0));
    let wide = neuron_relaxation_gap(Interval::new(-10.0, 10.0));
    assert!(narrow < medium, "narrow={narrow} < medium={medium}");
    assert!(medium < wide, "medium={medium} < wide={wide}");
}
