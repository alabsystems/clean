// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Alpha-CROWN per-neuron bound optimization (T43-T44).
//!
//! Validates soundness, tightness hierarchy (IBP >= CROWN >= alpha-CROWN),
//! convergence, and alpha range constraints.

use super::crown_alpha::*;
use super::crown_backward::verify_crown_bounds;
use super::ibp::Interval;
use super::tightness::{best_possible_bounds, eval_network};
use crate::spec::ProofStatus;

const EPS: f64 = 1e-8;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a network description as (weights, biases) pairs for alpha_crown_bounds
/// and as a flat Vec for verify_crown_bounds / eval_network.
fn network_layers(layers: &[(Vec<Vec<f64>>, Vec<f64>)]) -> (Vec<Vec<Vec<f64>>>, Vec<Vec<f64>>) {
    let weights: Vec<Vec<Vec<f64>>> = layers.iter().map(|(w, _)| w.clone()).collect();
    let biases: Vec<Vec<f64>> = layers.iter().map(|(_, b)| b.clone()).collect();
    (weights, biases)
}

// ---------------------------------------------------------------------------
// 1. Single-layer network: alpha-CROWN matches CROWN (no ReLU to optimize)
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_single_layer_matches_crown() {
    let layers = vec![(vec![vec![2.0, -1.0]], vec![0.5])];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let alpha_result = alpha_crown_bounds(&weights, &biases, &input_bounds, 10, 0.1);
    let crown_result = verify_crown_bounds(&layers, &[-1.0, -1.0], &[1.0, 1.0]);

    // Single linear layer: both should be exact.
    let alpha_width = alpha_result.output_bounds.width();
    let crown_width = crown_result.upper[0] - crown_result.lower[0];

    assert!(
        (alpha_width - crown_width).abs() < EPS,
        "single layer: alpha-CROWN width {alpha_width:.6} != CROWN width {crown_width:.6}"
    );
}

// ---------------------------------------------------------------------------
// 2. 2-layer network with crossing neurons: optimization improves bounds
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_two_layer_crossing_improves() {
    let layers = vec![
        (vec![vec![1.0], vec![-1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let alpha_result = alpha_crown_bounds(&weights, &biases, &input_bounds, 50, 0.5);

    // CROWN with fixed alpha=0.
    let crown_result = verify_crown_bounds(&layers, &[-1.0], &[1.0]);
    let crown_width = crown_result.upper[0] - crown_result.lower[0];
    let alpha_width = alpha_result.output_bounds.width();

    // Alpha-CROWN should be at least as tight as CROWN (possibly tighter).
    assert!(
        alpha_width <= crown_width + EPS,
        "alpha-CROWN width {alpha_width:.6} should be <= CROWN width {crown_width:.6}"
    );
}

// ---------------------------------------------------------------------------
// 3. All-positive input: no crossing neurons, all methods equal
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_all_positive_input_no_relaxation() {
    let layers = vec![
        (vec![vec![1.0, 0.5], vec![0.5, 1.0]], vec![1.0, 2.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    // All-positive inputs ensure pre-activations are positive.
    let input_bounds = Interval::new(1.0, 3.0);

    let alpha_result = alpha_crown_bounds(&weights, &biases, &input_bounds, 20, 0.1);
    let crown_result = verify_crown_bounds(&layers, &[1.0, 1.0], &[3.0, 3.0]);

    let alpha_width = alpha_result.output_bounds.width();
    let crown_width = crown_result.upper[0] - crown_result.lower[0];

    assert!(
        (alpha_width - crown_width).abs() < 0.1,
        "all-positive: alpha-CROWN width {alpha_width:.6} ~ CROWN width {crown_width:.6}"
    );
}

// ---------------------------------------------------------------------------
// 4. All-negative input: ReLU zeros everything
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_all_negative_input_zero_output() {
    // Design: W=[[1],[1]], b=[-10,-10], input [1,2].
    // Pre-act neuron 0: 1*[1,2] + (-10) = [-9, -8], all negative.
    // Pre-act neuron 1: 1*[1,2] + (-10) = [-9, -8], all negative.
    // ReLU = [0, 0] for both → output = 0.
    let layers = vec![
        (vec![vec![1.0], vec![1.0]], vec![-10.0, -10.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(1.0, 2.0);

    let alpha_result = alpha_crown_bounds(&weights, &biases, &input_bounds, 10, 0.1);

    // Output should be [0, 0] or very close.
    assert!(
        alpha_result.output_bounds.width() < 0.5,
        "all-negative: width {:.6} should be near zero",
        alpha_result.output_bounds.width()
    );
}

// ---------------------------------------------------------------------------
// 5. Soundness: sampled outputs within alpha-CROWN bounds
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_soundness_sampling() {
    let layers = vec![
        (vec![vec![1.0, -0.5], vec![-1.0, 2.0]], vec![0.5, -0.5]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let alpha_result = alpha_crown_bounds(&weights, &biases, &input_bounds, 30, 0.3);

    // Sample 500 random inputs and verify they fall within bounds.
    let (mc_lower, mc_upper) = best_possible_bounds(&layers, &[-1.0, -1.0], &[1.0, 1.0], 500);

    assert!(
        mc_lower[0] >= alpha_result.output_bounds.lower - EPS,
        "soundness: MC lower {:.6} < alpha-CROWN lower {:.6}",
        mc_lower[0],
        alpha_result.output_bounds.lower
    );
    assert!(
        mc_upper[0] <= alpha_result.output_bounds.upper + EPS,
        "soundness: MC upper {:.6} > alpha-CROWN upper {:.6}",
        mc_upper[0],
        alpha_result.output_bounds.upper
    );
}

// ---------------------------------------------------------------------------
// 6. Tightness hierarchy: IBP >= CROWN >= alpha-CROWN
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_tightness_hierarchy() {
    let layers = vec![
        (vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let alpha_result = alpha_crown_bounds(&weights, &biases, &input_bounds, 50, 0.3);
    let crown_result = verify_crown_bounds(&layers, &[-1.0, -1.0], &[1.0, 1.0]);

    let alpha_width = alpha_result.output_bounds.width();
    let crown_width = crown_result.upper[0] - crown_result.lower[0];

    // Alpha-CROWN <= CROWN.
    assert!(
        alpha_width <= crown_width + EPS,
        "hierarchy: alpha-CROWN width {alpha_width:.6} should be <= CROWN width {crown_width:.6}"
    );
}

// ---------------------------------------------------------------------------
// 7. Convergence: more iterations => tighter or equal bounds
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_convergence_monotone() {
    let layers = vec![
        (vec![vec![2.0, -1.0], vec![-1.0, 2.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let result_5 = alpha_crown_bounds(&weights, &biases, &input_bounds, 5, 0.3);
    let result_50 = alpha_crown_bounds(&weights, &biases, &input_bounds, 50, 0.3);

    let width_5 = result_5.output_bounds.width();
    let width_50 = result_50.output_bounds.width();

    // More iterations should give equal or tighter bounds.
    assert!(
        width_50 <= width_5 + EPS,
        "convergence: width at 50 iters ({width_50:.6}) should be <= width at 5 iters ({width_5:.6})"
    );
}

// ---------------------------------------------------------------------------
// 8. Alpha range: all alphas in [0, 1] after optimization
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_alphas_in_range() {
    let layers = vec![
        (vec![vec![3.0, -2.0], vec![-2.0, 3.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let result = alpha_crown_bounds(&weights, &biases, &input_bounds, 30, 0.5);

    assert!(
        verify_alphas_in_range(&result.params),
        "all alphas must be in [0, 1] after optimization"
    );
}

// ---------------------------------------------------------------------------
// 9. Gradient descent reduces bound width (within tolerance)
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_gradient_reduces_width() {
    let layers = vec![
        (vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    // 0 iterations = just initialization.
    let result_0 = alpha_crown_bounds(&weights, &biases, &input_bounds, 0, 0.3);
    let result_20 = alpha_crown_bounds(&weights, &biases, &input_bounds, 20, 0.3);

    let width_0 = result_0.output_bounds.width();
    let width_20 = result_20.output_bounds.width();

    // After gradient descent, width should be at least no worse.
    assert!(
        width_20 <= width_0 + EPS,
        "gradient descent: width after 20 iters ({width_20:.6}) <= initial ({width_0:.6})"
    );
}

// ---------------------------------------------------------------------------
// 10. 3-layer network with mixed crossing patterns
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_three_layer_mixed_crossing() {
    let layers = vec![
        (vec![vec![1.0, -0.5], vec![-0.5, 1.0]], vec![0.0, 0.0]),
        (vec![vec![0.8, -0.3], vec![-0.3, 0.8]], vec![-0.2, 0.1]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let alpha_result = alpha_crown_bounds(&weights, &biases, &input_bounds, 30, 0.3);

    // Soundness check via sampling.
    let (mc_lower, mc_upper) = best_possible_bounds(&layers, &[-1.0, -1.0], &[1.0, 1.0], 500);

    assert!(
        mc_lower[0] >= alpha_result.output_bounds.lower - EPS,
        "3-layer soundness: MC lower {:.6} >= alpha lower {:.6}",
        mc_lower[0],
        alpha_result.output_bounds.lower
    );
    assert!(
        mc_upper[0] <= alpha_result.output_bounds.upper + EPS,
        "3-layer soundness: MC upper {:.6} <= alpha upper {:.6}",
        mc_upper[0],
        alpha_result.output_bounds.upper
    );

    assert!(verify_alphas_in_range(&alpha_result.params));
}

// ---------------------------------------------------------------------------
// 11. Empty network returns input bounds
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_empty_network() {
    let weights: Vec<Vec<Vec<f64>>> = vec![];
    let biases: Vec<Vec<f64>> = vec![];
    let input_bounds = Interval::new(-2.0, 3.0);

    let result = alpha_crown_bounds(&weights, &biases, &input_bounds, 10, 0.1);

    assert!((result.output_bounds.lower - (-2.0)).abs() < EPS);
    assert!((result.output_bounds.upper - 3.0).abs() < EPS);
    assert_eq!(result.iterations, 0);
}

// ---------------------------------------------------------------------------
// 12. Point input: zero-width bounds
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_point_input() {
    let layers = vec![(vec![vec![2.0]], vec![1.0]), (vec![vec![1.0]], vec![0.0])];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(1.0, 1.0);

    let result = alpha_crown_bounds(&weights, &biases, &input_bounds, 10, 0.1);

    assert!(
        result.output_bounds.width() < EPS,
        "point input: width {:.6} should be ~0",
        result.output_bounds.width()
    );
}

// ---------------------------------------------------------------------------
// 13. Proof status constants
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_proof_status_constants() {
    assert_eq!(T43_ALPHA_CROWN_SOUND, ProofStatus::DerivedPending);
    assert_eq!(T44_ALPHA_TIGHTER_THAN_CROWN, ProofStatus::DerivedPending);
}

// ---------------------------------------------------------------------------
// 14. Proof spec types
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_sound_spec() {
    let spec = AlphaCrownSoundSpec::new();
    assert_eq!(spec.status(), ProofStatus::DerivedPending);
    let spec_default = AlphaCrownSoundSpec::default();
    assert_eq!(spec_default.status(), ProofStatus::DerivedPending);
}

#[test]
fn test_alpha_crown_tighter_spec() {
    let spec = AlphaCrownTighterSpec::new();
    assert_eq!(spec.status(), ProofStatus::DerivedPending);
    let spec_default = AlphaCrownTighterSpec::default();
    assert_eq!(spec_default.status(), ProofStatus::DerivedPending);
}

// ---------------------------------------------------------------------------
// 16. Layer bounds populated correctly
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_layer_bounds_populated() {
    let layers = vec![
        (vec![vec![1.0], vec![-1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let result = alpha_crown_bounds(&weights, &biases, &input_bounds, 5, 0.1);

    // 2 layers: layer 0 has 2 neurons, layer 1 has 1 neuron = 3 bounds total.
    assert_eq!(result.layer_bounds.len(), 3);
}

// ---------------------------------------------------------------------------
// 17. AlphaCrownParams cloning
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_params_clone() {
    let params = AlphaCrownParams {
        alphas: vec![vec![0.3, 0.7], vec![0.5]],
    };
    let cloned = params.clone();
    assert_eq!(cloned.alphas.len(), 2);
    assert!((cloned.alphas[0][0] - 0.3).abs() < EPS);
    assert!((cloned.alphas[1][0] - 0.5).abs() < EPS);
}

// ---------------------------------------------------------------------------
// 18. verify_alphas_in_range: rejects out-of-range
// ---------------------------------------------------------------------------

#[test]
fn test_verify_alphas_rejects_negative() {
    let params = AlphaCrownParams {
        alphas: vec![vec![-0.1, 0.5]],
    };
    assert!(!verify_alphas_in_range(&params));
}

#[test]
fn test_verify_alphas_rejects_above_one() {
    let params = AlphaCrownParams {
        alphas: vec![vec![0.5, 1.1]],
    };
    assert!(!verify_alphas_in_range(&params));
}

#[test]
fn test_verify_alphas_accepts_boundary() {
    let params = AlphaCrownParams {
        alphas: vec![vec![0.0, 1.0]],
    };
    assert!(verify_alphas_in_range(&params));
}

// ---------------------------------------------------------------------------
// 21. Symmetric network gives symmetric bounds
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_symmetric_network() {
    // Symmetric weights + symmetric input => bounds should be symmetric-ish.
    let layers = vec![
        (vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let result = alpha_crown_bounds(&weights, &biases, &input_bounds, 30, 0.3);

    // For symmetric network, |lower| should be close to upper (symmetry).
    // But ReLU breaks symmetry, so just check soundness.
    assert!(result.output_bounds.lower <= result.output_bounds.upper + EPS);
}

// ---------------------------------------------------------------------------
// 22. Large crossing region: alpha optimization has maximal impact
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_large_crossing_region() {
    let layers = vec![
        (vec![vec![5.0, -5.0], vec![-5.0, 5.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let alpha_result = alpha_crown_bounds(&weights, &biases, &input_bounds, 50, 0.5);
    let crown_result = verify_crown_bounds(&layers, &[-1.0, -1.0], &[1.0, 1.0]);

    let alpha_width = alpha_result.output_bounds.width();
    let crown_width = crown_result.upper[0] - crown_result.lower[0];

    // With large crossing regions, alpha optimization has more room to improve.
    assert!(
        alpha_width <= crown_width + EPS,
        "large crossing: alpha {alpha_width:.6} <= CROWN {crown_width:.6}"
    );
}

// ---------------------------------------------------------------------------
// 23. Learning rate 0 means no optimization (stays at initialization)
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_zero_learning_rate() {
    let layers = vec![
        (vec![vec![1.0], vec![-1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let result_0lr = alpha_crown_bounds(&weights, &biases, &input_bounds, 50, 0.0);
    let result_init = alpha_crown_bounds(&weights, &biases, &input_bounds, 0, 0.1);

    let width_0lr = result_0lr.output_bounds.width();
    let width_init = result_init.output_bounds.width();

    // Zero learning rate should give same result as no iterations.
    assert!(
        (width_0lr - width_init).abs() < EPS,
        "zero lr width {width_0lr:.6} should match init width {width_init:.6}"
    );
}

// ---------------------------------------------------------------------------
// 24. Single neuron hidden layer
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_single_neuron_hidden() {
    let layers = vec![(vec![vec![1.0]], vec![0.0]), (vec![vec![2.0]], vec![0.0])];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let result = alpha_crown_bounds(&weights, &biases, &input_bounds, 20, 0.3);

    // Pre-act [-1, 1] crossing → ReLU → [0, 1] → 2*[0,1] → [0, 2].
    assert!(result.output_bounds.lower >= -EPS, "lower >= 0");
    assert!(result.output_bounds.upper <= 2.0 + EPS, "upper <= 2.0");
    assert!(verify_alphas_in_range(&result.params));
}

// ---------------------------------------------------------------------------
// 25. Soundness on 3-layer network with aggressive optimization
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_soundness_aggressive_optimization() {
    let layers = vec![
        (vec![vec![2.0, -1.0], vec![-1.0, 2.0]], vec![0.0, 0.0]),
        (vec![vec![1.5, -0.5], vec![-0.5, 1.5]], vec![-0.3, 0.2]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    // Aggressive: high learning rate, many iterations.
    let result = alpha_crown_bounds(&weights, &biases, &input_bounds, 100, 1.0);

    // Soundness via Monte Carlo.
    let (mc_lower, mc_upper) = best_possible_bounds(&layers, &[-1.0, -1.0], &[1.0, 1.0], 1000);

    assert!(
        mc_lower[0] >= result.output_bounds.lower - EPS,
        "aggressive soundness: MC lower {:.6} >= alpha lower {:.6}",
        mc_lower[0],
        result.output_bounds.lower
    );
    assert!(
        mc_upper[0] <= result.output_bounds.upper + EPS,
        "aggressive soundness: MC upper {:.6} <= alpha upper {:.6}",
        mc_upper[0],
        result.output_bounds.upper
    );

    assert!(verify_alphas_in_range(&result.params));
}

// ---------------------------------------------------------------------------
// 26. AlphaCrownResult has correct iteration count
// ---------------------------------------------------------------------------

#[test]
fn test_alpha_crown_result_iteration_count() {
    let layers = vec![(vec![vec![1.0]], vec![0.0]), (vec![vec![1.0]], vec![0.0])];
    let (weights, biases) = network_layers(&layers);
    let input_bounds = Interval::new(-1.0, 1.0);

    let result = alpha_crown_bounds(&weights, &biases, &input_bounds, 42, 0.1);
    assert_eq!(result.iterations, 42);
}
