// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for CROWN vs IBP tightness analysis.
//!
//! Validates that CROWN produces bounds at least as tight as IBP, with
//! strictly tighter bounds when crossing ReLU neurons are present.

use super::ibp::Interval;
use super::tightness::*;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn single_linear_layer(weights: Vec<Vec<f64>>, bias: Vec<f64>) -> Vec<(Vec<Vec<f64>>, Vec<f64>)> {
    vec![(weights, bias)]
}

fn two_layer_network(
    w1: Vec<Vec<f64>>,
    b1: Vec<f64>,
    w2: Vec<Vec<f64>>,
    b2: Vec<f64>,
) -> Vec<(Vec<Vec<f64>>, Vec<f64>)> {
    vec![(w1, b1), (w2, b2)]
}

fn three_layer_network(
    w1: Vec<Vec<f64>>,
    b1: Vec<f64>,
    w2: Vec<Vec<f64>>,
    b2: Vec<f64>,
    w3: Vec<Vec<f64>>,
    b3: Vec<f64>,
) -> Vec<(Vec<Vec<f64>>, Vec<f64>)> {
    vec![(w1, b1), (w2, b2), (w3, b3)]
}

// ---------------------------------------------------------------------------
// 1. Single linear layer: IBP = CROWN (both exact for linear)
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_single_linear_layer_ibp_equals_crown() {
    let layers = single_linear_layer(vec![vec![2.0, -1.0], vec![1.0, 3.0]], vec![0.5, -0.5]);
    let report = compare_ibp_crown(&layers, &[-1.0, 0.0], &[1.0, 2.0]);

    assert_eq!(
        report.total_crossing, 0,
        "linear-only network has no crossing neurons"
    );

    for (ibp, crown) in report.output_ibp.iter().zip(report.output_crown.iter()) {
        assert!(
            (ibp.width() - crown.width()).abs() < 1e-10,
            "single linear layer: IBP width {:.6} != CROWN width {:.6}",
            ibp.width(),
            crown.width()
        );
    }

    assert!(
        (report.overall_ratio - 1.0).abs() < 1e-10,
        "ratio should be 1.0 for linear-only, got {:.6}",
        report.overall_ratio
    );
}

// ---------------------------------------------------------------------------
// 2. Linear + always-active ReLU: IBP = CROWN (both exact)
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_always_active_relu_ibp_equals_crown() {
    let layers = two_layer_network(
        vec![vec![1.0, 0.5], vec![0.5, 1.0]],
        vec![1.0, 2.0],
        vec![vec![1.0, 1.0]],
        vec![0.0],
    );
    let report = compare_ibp_crown(&layers, &[1.0, 1.0], &[3.0, 3.0]);

    assert_eq!(
        report.total_crossing, 0,
        "all neurons should be always active"
    );

    for (ibp, crown) in report.output_ibp.iter().zip(report.output_crown.iter()) {
        assert!(
            (ibp.width() - crown.width()).abs() < 1e-8,
            "always-active: IBP width {:.6} != CROWN width {:.6}",
            ibp.width(),
            crown.width()
        );
    }

    assert!(verify_crown_tighter_than_ibp(&report));
}

// ---------------------------------------------------------------------------
// 3. Linear + crossing ReLU: CROWN strictly tighter than IBP
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_crossing_relu_crown_strictly_tighter() {
    // Two hidden neurons with crossing pre-activations plus a second hidden
    // layer to amplify the correlation advantage of CROWN.
    let layers = three_layer_network(
        vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
        vec![0.0, 0.0],
        vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
        vec![0.0, 0.0],
        vec![vec![1.0, 1.0]],
        vec![0.0],
    );
    let report = compare_ibp_crown(&layers, &[-1.0, -1.0], &[1.0, 1.0]);

    assert!(report.total_crossing > 0, "should have crossing neurons");

    let crown_width = report.output_crown[0].width();
    let ibp_width = report.output_ibp[0].width();
    assert!(
        crown_width < ibp_width - 1e-10,
        "CROWN width {:.6} should be < IBP width {:.6} with crossing neurons",
        crown_width,
        ibp_width
    );

    assert!(report.overall_ratio < 1.0, "ratio should be < 1.0");
    assert!(verify_crown_tighter_than_ibp(&report));
}

// ---------------------------------------------------------------------------
// 4. 2-layer network: measure tightness gap
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_two_layer_gap_measurement() {
    let layers = two_layer_network(
        vec![vec![2.0, -1.0], vec![-1.0, 2.0], vec![1.0, 1.0]],
        vec![0.0, 0.0, -1.0],
        vec![vec![1.0, -0.5, 1.0]],
        vec![0.0],
    );
    let report = compare_ibp_crown(&layers, &[-0.5, -0.5], &[0.5, 0.5]);

    assert!(report.total_crossing > 0);
    assert!(verify_crown_tighter_than_ibp(&report));

    assert_eq!(report.layers.len(), 2);
    assert_eq!(report.layers[0].layer_index, 0);
    assert_eq!(report.layers[1].layer_index, 1);
}

// ---------------------------------------------------------------------------
// 5. 3-layer network: gap grows with depth
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_three_layer_gap_grows_with_depth() {
    let w_hidden = vec![vec![1.0, -1.0], vec![-1.0, 1.0]];
    let b_hidden = vec![0.0, 0.0];
    let w_out = vec![vec![1.0, 1.0]];
    let b_out = vec![0.0];

    let input_lower = [-1.0, -1.0];
    let input_upper = [1.0, 1.0];

    let layers_2 = two_layer_network(
        w_hidden.clone(),
        b_hidden.clone(),
        w_out.clone(),
        b_out.clone(),
    );
    let report_2 = compare_ibp_crown(&layers_2, &input_lower, &input_upper);

    let layers_3 = three_layer_network(
        w_hidden.clone(),
        b_hidden.clone(),
        w_hidden.clone(),
        b_hidden.clone(),
        w_out.clone(),
        b_out.clone(),
    );
    let report_3 = compare_ibp_crown(&layers_3, &input_lower, &input_upper);

    // Deeper network: IBP accumulates more over-approximation, so ratio should
    // be no worse (smaller or equal = CROWN advantage at least as large).
    assert!(
        report_3.overall_ratio <= report_2.overall_ratio + 1e-8,
        "3-layer ratio {:.6} should be <= 2-layer ratio {:.6}",
        report_3.overall_ratio,
        report_2.overall_ratio
    );

    assert!(verify_crown_tighter_than_ibp(&report_2));
    assert!(verify_crown_tighter_than_ibp(&report_3));
}

// ---------------------------------------------------------------------------
// 6. Network with large crossing region: maximum CROWN advantage
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_large_crossing_region_max_advantage() {
    // Every hidden neuron crosses zero with large pre-activation range.
    // 3 layers to amplify the gap.
    let layers = three_layer_network(
        vec![vec![5.0, -5.0], vec![-5.0, 5.0]],
        vec![0.0, 0.0],
        vec![vec![3.0, -3.0], vec![-3.0, 3.0]],
        vec![0.0, 0.0],
        vec![vec![1.0, 1.0]],
        vec![0.0],
    );
    let report = compare_ibp_crown(&layers, &[-1.0, -1.0], &[1.0, 1.0]);

    assert!(report.total_crossing >= 2);

    assert!(
        report.overall_ratio < 0.99,
        "large crossing region should give significant CROWN advantage, got ratio {:.4}",
        report.overall_ratio
    );
    assert!(verify_crown_tighter_than_ibp(&report));
}

// ---------------------------------------------------------------------------
// 7. Network with no crossing neurons: IBP = CROWN
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_no_crossing_ibp_equals_crown() {
    let layers = two_layer_network(
        vec![vec![1.0, 1.0], vec![2.0, 0.5]],
        vec![0.0, 0.0],
        vec![vec![1.0, 1.0]],
        vec![0.0],
    );
    let report = compare_ibp_crown(&layers, &[1.0, 1.0], &[2.0, 2.0]);

    assert_eq!(report.total_crossing, 0);

    for (ibp, crown) in report.output_ibp.iter().zip(report.output_crown.iter()) {
        assert!(
            (ibp.width() - crown.width()).abs() < 1e-8,
            "no crossing: IBP width {:.6} should equal CROWN width {:.6}",
            ibp.width(),
            crown.width()
        );
    }
}

// ---------------------------------------------------------------------------
// 8. Monte Carlo ground truth inside both IBP and CROWN bounds
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_monte_carlo_bounds_within_ibp_and_crown() {
    let layers = two_layer_network(
        vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
        vec![0.0, 0.0],
        vec![vec![1.0, 1.0]],
        vec![0.0],
    );
    let input_lower = [-1.0, -1.0];
    let input_upper = [1.0, 1.0];

    let (mc_lower, mc_upper) = best_possible_bounds(&layers, &input_lower, &input_upper, 10_000);
    let report = compare_ibp_crown(&layers, &input_lower, &input_upper);

    for j in 0..report.output_ibp.len() {
        assert!(
            mc_lower[j] >= report.output_crown[j].lower - 1e-8,
            "MC lower {:.6} should be >= CROWN lower {:.6}",
            mc_lower[j],
            report.output_crown[j].lower
        );
        assert!(
            mc_upper[j] <= report.output_crown[j].upper + 1e-8,
            "MC upper {:.6} should be <= CROWN upper {:.6}",
            mc_upper[j],
            report.output_crown[j].upper
        );
        assert!(
            mc_lower[j] >= report.output_ibp[j].lower - 1e-8,
            "MC lower {:.6} should be >= IBP lower {:.6}",
            mc_lower[j],
            report.output_ibp[j].lower
        );
        assert!(
            mc_upper[j] <= report.output_ibp[j].upper + 1e-8,
            "MC upper {:.6} should be <= IBP upper {:.6}",
            mc_upper[j],
            report.output_ibp[j].upper
        );
    }
}

// ---------------------------------------------------------------------------
// 9. Report structure validation
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_report_structure() {
    let layers = two_layer_network(
        vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
        vec![0.0, 0.0],
        vec![vec![1.0, 1.0]],
        vec![0.0],
    );
    let report = compare_ibp_crown(&layers, &[-1.0, -1.0], &[1.0, 1.0]);

    assert_eq!(report.layers.len(), 2);
    assert_eq!(report.output_ibp.len(), 1);
    assert_eq!(report.output_crown.len(), 1);
    assert!(report.overall_ratio > 0.0 && report.overall_ratio <= 1.0 + 1e-10);

    // Hidden layer: 2 neurons.
    assert_eq!(report.layers[0].ibp_widths.len(), 2);
    assert_eq!(report.layers[0].activations.len(), 2);

    // Output layer: 1 neuron.
    assert_eq!(report.layers[1].ibp_widths.len(), 1);
    assert_eq!(report.layers[1].crown_widths.len(), 1);
}

// ---------------------------------------------------------------------------
// 10. Wide network (many neurons): tightness at scale
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_wide_network() {
    let dim = 10;
    let mut w1 = Vec::with_capacity(dim);
    let mut b1 = Vec::with_capacity(dim);
    for i in 0..dim {
        let mut row = vec![0.0; dim];
        row[i] = if i % 2 == 0 { 1.0 } else { -1.0 };
        if i + 1 < dim {
            row[i + 1] = if i % 2 == 0 { -0.5 } else { 0.5 };
        }
        w1.push(row);
        b1.push(0.0);
    }
    let w2 = vec![vec![1.0; dim]];
    let b2 = vec![0.0];

    let layers = two_layer_network(w1, b1, w2, b2);
    let input_lower = vec![-1.0; dim];
    let input_upper = vec![1.0; dim];

    let report = compare_ibp_crown(&layers, &input_lower, &input_upper);

    assert!(
        report.total_crossing > 0,
        "wide network should have crossing neurons"
    );
    assert!(verify_crown_tighter_than_ibp(&report));
    assert_eq!(report.layers[0].ibp_widths.len(), dim);
}

// ---------------------------------------------------------------------------
// 11. eval_network: identity
// ---------------------------------------------------------------------------

#[test]
fn test_eval_network_identity() {
    let layers = single_linear_layer(vec![vec![1.0, 0.0], vec![0.0, 1.0]], vec![0.0, 0.0]);
    let result = eval_network(&layers, &[3.0, 7.0]);
    assert!((result[0] - 3.0).abs() < 1e-10);
    assert!((result[1] - 7.0).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// 12. eval_network: ReLU clips negatives
// ---------------------------------------------------------------------------

#[test]
fn test_eval_network_relu_clips_negative() {
    let layers = two_layer_network(
        vec![vec![1.0], vec![-1.0]],
        vec![0.0, 0.0],
        vec![vec![1.0, 1.0]],
        vec![0.0],
    );
    // [2.0] -> pre: [2, -2] -> post-relu: [2, 0] -> output: 2
    let result = eval_network(&layers, &[2.0]);
    assert!((result[0] - 2.0).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// 13. Monte Carlo on linear network finds exact bounds
// ---------------------------------------------------------------------------

#[test]
fn test_monte_carlo_tight_on_linear() {
    let layers = single_linear_layer(vec![vec![2.0]], vec![1.0]);
    let (mc_lower, mc_upper) = best_possible_bounds(&layers, &[0.0], &[1.0], 1000);

    // True: 2*[0,1] + 1 = [1, 3]
    assert!(
        (mc_lower[0] - 1.0).abs() < 0.05,
        "MC lower should be near 1.0"
    );
    assert!(
        (mc_upper[0] - 3.0).abs() < 0.05,
        "MC upper should be near 3.0"
    );
}

// ---------------------------------------------------------------------------
// 14. verify_crown_tighter_than_ibp returns true for crossing case
// ---------------------------------------------------------------------------

#[test]
fn test_verify_crown_tighter_returns_true() {
    let layers = two_layer_network(
        vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
        vec![0.0, 0.0],
        vec![vec![1.0, 1.0]],
        vec![0.0],
    );
    let report = compare_ibp_crown(&layers, &[-1.0, -1.0], &[1.0, 1.0]);
    assert!(verify_crown_tighter_than_ibp(&report));
}

// ---------------------------------------------------------------------------
// 15. LayerTightness::crossing_count
// ---------------------------------------------------------------------------

#[test]
fn test_layer_tightness_crossing_count() {
    let lt = LayerTightness {
        layer_index: 0,
        ibp_widths: vec![1.0, 2.0, 3.0],
        crown_widths: vec![1.0, 1.5, 2.5],
        ratios: vec![1.0, 0.75, 0.833],
        activations: vec![
            ActivationStatus::AlwaysActive,
            ActivationStatus::Crossing,
            ActivationStatus::Crossing,
        ],
    };
    assert_eq!(lt.crossing_count(), 2);
}

// ---------------------------------------------------------------------------
// 16. LayerTightness::mean_ratio
// ---------------------------------------------------------------------------

#[test]
fn test_layer_tightness_mean_ratio() {
    let lt = LayerTightness {
        layer_index: 0,
        ibp_widths: vec![2.0, 4.0],
        crown_widths: vec![1.0, 2.0],
        ratios: vec![0.5, 0.5],
        activations: vec![ActivationStatus::Crossing, ActivationStatus::Crossing],
    };
    assert!((lt.mean_ratio() - 0.5).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// 17. LayerTightness::min_ratio
// ---------------------------------------------------------------------------

#[test]
fn test_layer_tightness_min_ratio() {
    let lt = LayerTightness {
        layer_index: 0,
        ibp_widths: vec![2.0, 4.0],
        crown_widths: vec![1.0, 3.0],
        ratios: vec![0.5, 0.75],
        activations: vec![ActivationStatus::Crossing, ActivationStatus::Crossing],
    };
    assert!((lt.min_ratio() - 0.5).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// 18. Activation status classification via network
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_activation_classification() {
    let layers = two_layer_network(
        vec![
            vec![1.0],  // [1,2] + 0 = [1,2] -> always active
            vec![-1.0], // [-2,-1] + 0 = [-2,-1] -> always inactive
            vec![1.0],  // [1,2] - 1.5 = [-0.5, 0.5] -> crossing
        ],
        vec![0.0, 0.0, -1.5],
        vec![vec![1.0, 1.0, 1.0]],
        vec![0.0],
    );
    let report = compare_ibp_crown(&layers, &[1.0], &[2.0]);

    let acts = &report.layers[0].activations;
    assert_eq!(acts[0], ActivationStatus::AlwaysActive);
    assert_eq!(acts[1], ActivationStatus::AlwaysInactive);
    assert_eq!(acts[2], ActivationStatus::Crossing);
}

// ---------------------------------------------------------------------------
// 19. Point input: both methods return zero-width bounds
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_point_input_exact() {
    let layers = two_layer_network(
        vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
        vec![0.0, 0.0],
        vec![vec![1.0, 1.0]],
        vec![0.0],
    );
    let report = compare_ibp_crown(&layers, &[0.5, -0.3], &[0.5, -0.3]);

    for (ibp, crown) in report.output_ibp.iter().zip(report.output_crown.iter()) {
        assert!(
            ibp.width() < 1e-10,
            "point input should give zero-width IBP"
        );
        assert!(
            crown.width() < 1e-10,
            "point input should give zero-width CROWN"
        );
    }
}

// ---------------------------------------------------------------------------
// 20. Crossing from bias (positive weights but negative bias)
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_crossing_from_bias() {
    let layers = two_layer_network(
        vec![vec![1.0, 1.0]],
        vec![-1.5], // sum in [0,2] - 1.5 = [-1.5, 0.5] crosses zero
        vec![vec![2.0]],
        vec![0.0],
    );
    let report = compare_ibp_crown(&layers, &[0.0, 0.0], &[1.0, 1.0]);

    assert!(report.total_crossing > 0, "bias should create crossing");
    assert!(verify_crown_tighter_than_ibp(&report));
}

// ---------------------------------------------------------------------------
// 21. CROWN soundness via sampling on 3-layer network
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_crown_soundness_via_sampling() {
    let layers = three_layer_network(
        vec![vec![1.0, -0.5], vec![-0.5, 1.0]],
        vec![0.0, 0.0],
        vec![vec![0.8, -0.3], vec![-0.3, 0.8]],
        vec![-0.2, 0.1],
        vec![vec![1.0, 1.0]],
        vec![0.0],
    );
    let input_lower = [-1.0, -1.0];
    let input_upper = [1.0, 1.0];

    let report = compare_ibp_crown(&layers, &input_lower, &input_upper);
    let (mc_lower, mc_upper) = best_possible_bounds(&layers, &input_lower, &input_upper, 5000);

    for j in 0..report.output_crown.len() {
        assert!(
            mc_lower[j] >= report.output_crown[j].lower - 1e-8,
            "CROWN must be sound: MC lower {:.6} < CROWN lower {:.6}",
            mc_lower[j],
            report.output_crown[j].lower
        );
        assert!(
            mc_upper[j] <= report.output_crown[j].upper + 1e-8,
            "CROWN must be sound: MC upper {:.6} > CROWN upper {:.6}",
            mc_upper[j],
            report.output_crown[j].upper
        );
    }
}

// ---------------------------------------------------------------------------
// 22. Multi-output network
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_multi_output() {
    let layers = two_layer_network(
        vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
        vec![0.0, 0.0],
        vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![1.0, 1.0]],
        vec![0.0, 0.0, 0.0],
    );
    let report = compare_ibp_crown(&layers, &[-1.0, -1.0], &[1.0, 1.0]);

    assert_eq!(report.output_ibp.len(), 3);
    assert_eq!(report.output_crown.len(), 3);
    assert!(verify_crown_tighter_than_ibp(&report));
}

// ---------------------------------------------------------------------------
// 23. Always-inactive ReLU: both give zero output
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_always_inactive_relu() {
    let layers = two_layer_network(
        vec![vec![-1.0, -1.0]],
        vec![-5.0],
        vec![vec![1.0]],
        vec![0.0],
    );
    let report = compare_ibp_crown(&layers, &[1.0, 1.0], &[2.0, 2.0]);

    assert_eq!(
        report.layers[0].activations[0],
        ActivationStatus::AlwaysInactive
    );
    assert!(report.output_ibp[0].width() < 1e-10);
    assert!(report.output_crown[0].width() < 1e-10);
}

// ---------------------------------------------------------------------------
// 24. 4-layer deep network tightness
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_four_layer_network() {
    let layers = vec![
        (vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, -0.5], vec![-0.5, 1.0]], vec![0.0, 0.0]),
        (vec![vec![0.8, 0.2], vec![0.2, 0.8]], vec![-0.3, -0.3]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let report = compare_ibp_crown(&layers, &[-1.0, -1.0], &[1.0, 1.0]);

    assert!(report.total_crossing > 0);
    assert!(verify_crown_tighter_than_ibp(&report));
    assert_eq!(report.layers.len(), 4);
}

// ---------------------------------------------------------------------------
// 25. Monte Carlo corner coverage finds exact bounds on linear network
// ---------------------------------------------------------------------------

#[test]
fn test_monte_carlo_corners_find_exact_for_linear() {
    let layers = single_linear_layer(vec![vec![3.0, -2.0]], vec![1.0]);
    let (mc_lower, mc_upper) = best_possible_bounds(&layers, &[0.0, 0.0], &[1.0, 1.0], 100);

    // True: 3*x0 - 2*x1 + 1. Min at (0,1)=-1, max at (1,0)=4.
    assert!(
        (mc_lower[0] - (-1.0)).abs() < 1e-10,
        "corners find exact lower"
    );
    assert!(
        (mc_upper[0] - 4.0).abs() < 1e-10,
        "corners find exact upper"
    );
}

// ---------------------------------------------------------------------------
// 26. Asymmetric input region
// ---------------------------------------------------------------------------

#[test]
fn test_tightness_asymmetric_input() {
    let layers = two_layer_network(
        vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
        vec![0.0, 0.0],
        vec![vec![1.0, 1.0]],
        vec![0.0],
    );
    let report = compare_ibp_crown(&layers, &[-2.0, -0.5], &[2.0, 0.5]);

    assert!(verify_crown_tighter_than_ibp(&report));
    assert!(report.total_crossing > 0);
}

// ===========================================================================
// Tests for new tightness analysis functions
// ===========================================================================

// ---------------------------------------------------------------------------
// compute_tightness_gap
// ---------------------------------------------------------------------------

#[test]
fn test_compute_gap_crown_tighter() {
    let ibp = Interval::new(-2.0, 2.0); // width 4
    let crown = Interval::new(-1.0, 1.0); // width 2
    let gap = compute_tightness_gap(&ibp, &crown);
    assert!((gap.absolute - 2.0).abs() < 1e-12);
    assert!((gap.relative - 0.5).abs() < 1e-12);
    assert!((gap.ibp_width - 4.0).abs() < 1e-12);
    assert!((gap.crown_width - 2.0).abs() < 1e-12);
}

#[test]
fn test_compute_gap_equal_bounds() {
    let iv = Interval::new(1.0, 3.0);
    let gap = compute_tightness_gap(&iv, &iv);
    assert!(gap.absolute.abs() < 1e-12);
    assert!(gap.relative.abs() < 1e-12);
}

#[test]
fn test_compute_gap_point_intervals() {
    let p = Interval::point(5.0);
    let gap = compute_tightness_gap(&p, &p);
    assert!(gap.absolute.abs() < 1e-12);
    assert!((gap.relative).abs() < 1e-12);
}

#[test]
fn test_compute_gap_crown_much_tighter() {
    let ibp = Interval::new(0.0, 10.0);
    let crown = Interval::new(4.0, 5.0);
    let gap = compute_tightness_gap(&ibp, &crown);
    assert!((gap.absolute - 9.0).abs() < 1e-12);
    assert!((gap.relative - 0.9).abs() < 1e-12);
}

#[test]
fn test_compute_gap_ibp_point_crown_wider_nan() {
    let ibp = Interval::point(3.0);
    let crown = Interval::new(2.0, 4.0);
    let gap = compute_tightness_gap(&ibp, &crown);
    assert!(gap.relative.is_nan());
}

#[test]
fn test_compute_gap_crown_wider_negative_relative() {
    let ibp = Interval::new(0.0, 1.0);
    let crown = Interval::new(-1.0, 2.0);
    let gap = compute_tightness_gap(&ibp, &crown);
    assert!((gap.absolute - (-2.0)).abs() < 1e-12);
    assert!(gap.relative < 0.0);
}

// ---------------------------------------------------------------------------
// crossing_neuron_ratio
// ---------------------------------------------------------------------------

#[test]
fn test_crossing_ratio_all_positive() {
    let bounds = vec![Interval::new(1.0, 5.0), Interval::new(0.0, 3.0)];
    assert!(crossing_neuron_ratio(&bounds).abs() < 1e-12);
}

#[test]
fn test_crossing_ratio_all_negative() {
    let bounds = vec![Interval::new(-5.0, -1.0), Interval::new(-3.0, 0.0)];
    assert!(crossing_neuron_ratio(&bounds).abs() < 1e-12);
}

#[test]
fn test_crossing_ratio_all_crossing() {
    let bounds = vec![Interval::new(-1.0, 1.0), Interval::new(-5.0, 0.5)];
    assert!((crossing_neuron_ratio(&bounds) - 1.0).abs() < 1e-12);
}

#[test]
fn test_crossing_ratio_mixed() {
    let bounds = vec![
        Interval::new(-1.0, 1.0),  // crossing
        Interval::new(0.0, 5.0),   // not crossing (lower == 0)
        Interval::new(-3.0, -1.0), // not crossing
        Interval::new(-2.0, 3.0),  // crossing
    ];
    assert!((crossing_neuron_ratio(&bounds) - 0.5).abs() < 1e-12);
}

#[test]
fn test_crossing_ratio_empty() {
    assert!(crossing_neuron_ratio(&[]).abs() < 1e-12);
}

#[test]
fn test_crossing_ratio_single_crossing() {
    assert!((crossing_neuron_ratio(&[Interval::new(-1.0, 1.0)]) - 1.0).abs() < 1e-12);
}

#[test]
fn test_crossing_ratio_boundary_zero_lower() {
    // lower == 0 means NOT crossing (lower < 0 required)
    assert!(crossing_neuron_ratio(&[Interval::new(0.0, 1.0)]).abs() < 1e-12);
}

// ---------------------------------------------------------------------------
// bound_width_statistics
// ---------------------------------------------------------------------------

#[test]
fn test_width_stats_empty_input() {
    let s = bound_width_statistics(&[]);
    assert_eq!(s.count, 0);
    assert!(s.min.abs() < 1e-12);
    assert!(s.max.abs() < 1e-12);
}

#[test]
fn test_width_stats_single() {
    let s = bound_width_statistics(&[Interval::new(1.0, 4.0)]);
    assert_eq!(s.count, 1);
    assert!((s.min - 3.0).abs() < 1e-12);
    assert!((s.max - 3.0).abs() < 1e-12);
    assert!((s.mean - 3.0).abs() < 1e-12);
    assert!((s.median - 3.0).abs() < 1e-12);
}

#[test]
fn test_width_stats_uniform() {
    let bounds = vec![Interval::new(0.0, 2.0), Interval::new(1.0, 3.0)];
    let s = bound_width_statistics(&bounds);
    assert_eq!(s.count, 2);
    assert!((s.min - 2.0).abs() < 1e-12);
    assert!((s.max - 2.0).abs() < 1e-12);
    assert!((s.mean - 2.0).abs() < 1e-12);
}

#[test]
fn test_width_stats_varied_even() {
    let bounds = vec![
        Interval::new(0.0, 1.0), // width 1
        Interval::new(0.0, 3.0), // width 3
        Interval::new(0.0, 5.0), // width 5
        Interval::new(0.0, 7.0), // width 7
    ];
    let s = bound_width_statistics(&bounds);
    assert!((s.min - 1.0).abs() < 1e-12);
    assert!((s.max - 7.0).abs() < 1e-12);
    assert!((s.mean - 4.0).abs() < 1e-12);
    assert!((s.median - 4.0).abs() < 1e-12); // (3+5)/2
}

#[test]
fn test_width_stats_varied_odd() {
    let bounds = vec![
        Interval::new(0.0, 10.0), // width 10
        Interval::new(0.0, 2.0),  // width 2
        Interval::new(0.0, 6.0),  // width 6
    ];
    let s = bound_width_statistics(&bounds);
    assert!((s.median - 6.0).abs() < 1e-12); // sorted: [2,6,10], middle=6
}

#[test]
fn test_width_stats_point_intervals() {
    let bounds = vec![Interval::point(1.0), Interval::point(9.0)];
    let s = bound_width_statistics(&bounds);
    assert!(s.min.abs() < 1e-12);
    assert!(s.max.abs() < 1e-12);
    assert!(s.mean.abs() < 1e-12);
}

// ---------------------------------------------------------------------------
// verify_crown_tighter (per-interval version)
// ---------------------------------------------------------------------------

#[test]
fn test_crown_tighter_contained() {
    assert!(verify_crown_tighter(
        &Interval::new(-3.0, 5.0),
        &Interval::new(-1.0, 3.0),
    ));
}

#[test]
fn test_crown_tighter_equal() {
    let iv = Interval::new(-2.0, 2.0);
    assert!(verify_crown_tighter(&iv, &iv));
}

#[test]
fn test_crown_tighter_fails_lower() {
    assert!(!verify_crown_tighter(
        &Interval::new(0.0, 5.0),
        &Interval::new(-1.0, 4.0),
    ));
}

#[test]
fn test_crown_tighter_fails_upper() {
    assert!(!verify_crown_tighter(
        &Interval::new(0.0, 5.0),
        &Interval::new(1.0, 6.0),
    ));
}

#[test]
fn test_crown_tighter_point_in_wider() {
    assert!(verify_crown_tighter(
        &Interval::new(-10.0, 10.0),
        &Interval::point(0.0),
    ));
}

// ---------------------------------------------------------------------------
// layer_tightness_profile
// ---------------------------------------------------------------------------

#[test]
fn test_layer_profile_basic_gaps() {
    let ibp = vec![Interval::new(-2.0, 2.0), Interval::new(1.0, 5.0)];
    let crown = vec![Interval::new(-1.0, 1.0), Interval::new(2.0, 4.0)];
    let profile = layer_tightness_profile(&ibp, &crown);
    assert_eq!(profile.gaps.len(), 2);
    assert!((profile.crossing_ratio - 0.5).abs() < 1e-12);
    assert!((profile.mean_width - 4.0).abs() < 1e-12);
    for gap in &profile.gaps {
        assert!((gap.absolute - 2.0).abs() < 1e-12);
        assert!((gap.relative - 0.5).abs() < 1e-12);
    }
}

#[test]
fn test_layer_profile_empty_inputs() {
    let profile = layer_tightness_profile(&[], &[]);
    assert!(profile.gaps.is_empty());
    assert!(profile.crossing_ratio.abs() < 1e-12);
    assert!(profile.mean_width.abs() < 1e-12);
}

#[test]
fn test_layer_profile_all_crossing() {
    let ibp = vec![Interval::new(-3.0, 3.0), Interval::new(-1.0, 2.0)];
    let crown = vec![Interval::new(-1.0, 1.0), Interval::new(-0.5, 1.0)];
    let profile = layer_tightness_profile(&ibp, &crown);
    assert!((profile.crossing_ratio - 1.0).abs() < 1e-12);
}

// ---------------------------------------------------------------------------
// tightness_improvement_chain
// ---------------------------------------------------------------------------

fn make_test_profile(relative_gaps: &[f64]) -> LayerProfile {
    let gaps = relative_gaps
        .iter()
        .map(|&r| TightnessGap {
            absolute: r * 10.0,
            relative: r,
            ibp_width: 10.0,
            crown_width: 10.0 * (1.0 - r),
        })
        .collect();
    LayerProfile {
        gaps,
        crossing_ratio: 0.5,
        mean_width: 4.0,
    }
}

#[test]
fn test_chain_empty() {
    assert!(tightness_improvement_chain(&[]).is_empty());
}

#[test]
fn test_chain_single_layer() {
    assert!(tightness_improvement_chain(&[make_test_profile(&[0.5])]).is_empty());
}

#[test]
fn test_chain_constant_gap() {
    let profiles = vec![make_test_profile(&[0.5]), make_test_profile(&[0.5])];
    let chain = tightness_improvement_chain(&profiles);
    assert_eq!(chain.len(), 1);
    assert!((chain[0] - 1.0).abs() < 1e-12);
}

#[test]
fn test_chain_increasing_gap() {
    let profiles = vec![
        make_test_profile(&[0.2]),
        make_test_profile(&[0.4]),
        make_test_profile(&[0.8]),
    ];
    let chain = tightness_improvement_chain(&profiles);
    assert_eq!(chain.len(), 2);
    assert!((chain[0] - 2.0).abs() < 1e-12);
    assert!((chain[1] - 2.0).abs() < 1e-12);
}

#[test]
fn test_chain_zero_to_nonzero_infinity() {
    let profiles = vec![make_test_profile(&[0.0]), make_test_profile(&[0.5])];
    let chain = tightness_improvement_chain(&profiles);
    assert!(chain[0].is_infinite());
}

#[test]
fn test_chain_zero_to_zero_is_one() {
    let profiles = vec![make_test_profile(&[0.0]), make_test_profile(&[0.0])];
    let chain = tightness_improvement_chain(&profiles);
    assert!((chain[0] - 1.0).abs() < 1e-12);
}

#[test]
fn test_chain_multi_neuron_mean() {
    let profiles = vec![
        make_test_profile(&[0.1, 0.2, 0.3]), // mean = 0.2
        make_test_profile(&[0.3, 0.4, 0.5]), // mean = 0.4
    ];
    let chain = tightness_improvement_chain(&profiles);
    assert!((chain[0] - 2.0).abs() < 1e-12);
}

// ---------------------------------------------------------------------------
// Integration: layer_profile + improvement_chain
// ---------------------------------------------------------------------------

#[test]
fn test_profile_then_chain_integration() {
    let ibp_0 = vec![Interval::new(-4.0, 4.0), Interval::new(-2.0, 2.0)];
    let crown_0 = vec![Interval::new(-2.0, 2.0), Interval::new(-1.0, 1.0)];
    let p0 = layer_tightness_profile(&ibp_0, &crown_0);

    let ibp_1 = vec![Interval::new(-8.0, 8.0), Interval::new(-4.0, 4.0)];
    let crown_1 = vec![Interval::new(-2.0, 2.0), Interval::new(-1.0, 1.0)];
    let p1 = layer_tightness_profile(&ibp_1, &crown_1);

    let chain = tightness_improvement_chain(&[p0, p1]);
    assert_eq!(chain.len(), 1);
    // p0 mean_relative = 0.5, p1 mean_relative = 0.75 => ratio = 1.5
    assert!((chain[0] - 1.5).abs() < 1e-12);
}
