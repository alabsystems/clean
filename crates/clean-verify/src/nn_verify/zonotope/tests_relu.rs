// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for zonotope ReLU overapproximation (T03-T07).

use super::affine_relu::{compare_zonotope_ibp, zonotope_affine_relu, zonotope_forward_pass};
use super::concrete::ConcreteZonotope;
use super::relu::{
    classify_relu, verify_relu_soundness, verify_relu_tightness, zonotope_relu, ReluCase,
};

const EPS: f64 = 1e-9;

// ---------------------------------------------------------------------------
// T05: Always-active case (lower >= 0) -- ReLU is identity
// ---------------------------------------------------------------------------

#[test]
fn test_relu_always_active_identity() {
    // Zonotope centered at 5.0 with generator +-1.0 -> hull [4, 6], all positive.
    let z = ConcreteZonotope::new(vec![5.0], vec![vec![1.0]]);
    let result = zonotope_relu(&z);
    assert!((result.center[0] - 5.0).abs() < EPS);
    assert_eq!(result.generators.len(), 1);
    assert!((result.generators[0][0] - 1.0).abs() < EPS);
}

#[test]
fn test_relu_always_active_2d() {
    // Both dims positive: center [3, 2], gen [1, 0.5] -> hull [2,4] x [1.5,2.5]
    let z = ConcreteZonotope::new(vec![3.0, 2.0], vec![vec![1.0, 0.5]]);
    let result = zonotope_relu(&z);
    assert!((result.center[0] - 3.0).abs() < EPS);
    assert!((result.center[1] - 2.0).abs() < EPS);
    assert!((result.generators[0][0] - 1.0).abs() < EPS);
    assert!((result.generators[0][1] - 0.5).abs() < EPS);
    // No new generators added (no crossing dims).
    assert_eq!(result.num_generators(), 1);
}

#[test]
fn test_relu_always_active_exact_tightness() {
    let z = ConcreteZonotope::new(vec![5.0], vec![vec![1.0]]);
    let ratio = verify_relu_tightness(&z);
    // Always-active: ReLU is identity, hull width unchanged => ratio = 1.0
    assert!((ratio - 1.0).abs() < EPS);
}

// ---------------------------------------------------------------------------
// T06: Always-inactive case (upper <= 0) -- ReLU zeros everything
// ---------------------------------------------------------------------------

#[test]
fn test_relu_always_inactive_zeros() {
    // Zonotope centered at -5.0 with gen +-1.0 -> hull [-6, -4], all negative.
    let z = ConcreteZonotope::new(vec![-5.0], vec![vec![1.0]]);
    let result = zonotope_relu(&z);
    assert!(result.center[0].abs() < EPS);
    // All generators zeroed in this dimension.
    for gvec in &result.generators {
        assert!(gvec[0].abs() < EPS);
    }
}

#[test]
fn test_relu_always_inactive_2d() {
    // Both dims negative.
    let z = ConcreteZonotope::new(vec![-3.0, -5.0], vec![vec![1.0, 2.0]]);
    let result = zonotope_relu(&z);
    assert!(result.center[0].abs() < EPS);
    assert!(result.center[1].abs() < EPS);
}

// ---------------------------------------------------------------------------
// T03: Crossing case -- lambda-relaxation
// ---------------------------------------------------------------------------

#[test]
fn test_relu_crossing_lambda_computation() {
    // hull = [-2, 4]: lambda = 4/(4-(-2)) = 4/6 = 2/3
    // mu = (1-2/3)*4/2 = (1/3)*2 = 2/3
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![3.0]]);
    let (lo, hi) = z.to_interval();
    assert!((lo[0] - (-2.0)).abs() < EPS);
    assert!((hi[0] - 4.0).abs() < EPS);

    let result = zonotope_relu(&z);
    let lambda = 4.0 / 6.0;
    let mu = (1.0 - lambda) * 4.0 / 2.0;

    // new center = lambda * 1.0 + mu = 2/3 + 2/3 = 4/3
    assert!((result.center[0] - (lambda * 1.0 + mu)).abs() < EPS);

    // existing generator scaled by lambda
    assert!((result.generators[0][0] - lambda * 3.0).abs() < EPS);

    // new error generator with magnitude mu
    assert_eq!(result.num_generators(), 2);
    assert!((result.generators[1][0] - mu).abs() < EPS);
}

#[test]
fn test_relu_crossing_symmetric_interval() {
    // hull = [-1, 1]: lambda = 1/2, mu = (1/2)*1/2 = 1/4
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let result = zonotope_relu(&z);

    let lambda = 0.5;
    let mu = 0.25;
    assert!((result.center[0] - mu).abs() < EPS);
    assert!((result.generators[0][0] - lambda * 1.0).abs() < EPS);
    assert!((result.generators[1][0] - mu).abs() < EPS);
}

#[test]
fn test_relu_crossing_hull_contains_zero_and_positive() {
    // After ReLU crossing, the interval hull may extend below 0
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![3.0]]);
    let result = zonotope_relu(&z);
    let (_lo, _hi) = result.to_interval();
    // The interval hull is an overapproximation of the zonotope.
}

// ---------------------------------------------------------------------------
// T03: Soundness via sampling
// ---------------------------------------------------------------------------

#[test]
fn test_relu_soundness_1d_crossing() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![2.0]]);
    assert!(verify_relu_soundness(&z, 100));
}

#[test]
fn test_relu_soundness_1d_always_active() {
    let z = ConcreteZonotope::new(vec![5.0], vec![vec![1.0]]);
    assert!(verify_relu_soundness(&z, 50));
}

#[test]
fn test_relu_soundness_1d_always_inactive() {
    let z = ConcreteZonotope::new(vec![-5.0], vec![vec![1.0]]);
    assert!(verify_relu_soundness(&z, 50));
}

#[test]
fn test_relu_soundness_2d_mixed() {
    // dim 0: crossing [-1, 3], dim 1: always active [1, 5]
    let z = ConcreteZonotope::new(vec![1.0, 3.0], vec![vec![2.0, 2.0]]);
    assert!(verify_relu_soundness(&z, 100));
}

#[test]
fn test_relu_soundness_2d_both_crossing() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    assert!(verify_relu_soundness(&z, 100));
}

#[test]
fn test_relu_soundness_3d() {
    // dim 0: crossing, dim 1: always active, dim 2: always inactive
    let z = ConcreteZonotope::new(
        vec![0.0, 5.0, -5.0],
        vec![vec![2.0, 1.0, 1.0], vec![1.0, 0.5, 0.5]],
    );
    assert!(verify_relu_soundness(&z, 200));
}

// ---------------------------------------------------------------------------
// Multi-dimensional zonotopes
// ---------------------------------------------------------------------------

#[test]
fn test_relu_2d_mixed_cases() {
    // dim 0: always active [2, 4], dim 1: always inactive [-4, -2]
    let z = ConcreteZonotope::new(vec![3.0, -3.0], vec![vec![1.0, 1.0]]);
    let result = zonotope_relu(&z);
    // dim 0 unchanged
    assert!((result.center[0] - 3.0).abs() < EPS);
    // dim 1 zeroed
    assert!(result.center[1].abs() < EPS);
    // No crossing dimensions, so no new generators.
    assert_eq!(result.num_generators(), 1);
}

#[test]
fn test_relu_3d_one_crossing() {
    // dim 0: crossing [-1, 3], dim 1: active [2, 4], dim 2: inactive [-4, -2]
    let z = ConcreteZonotope::new(vec![1.0, 3.0, -3.0], vec![vec![2.0, 1.0, 1.0]]);
    let result = zonotope_relu(&z);
    // Exactly 1 crossing dimension -> 1 new error generator
    assert_eq!(result.num_generators(), 2);
    // The new generator should be nonzero only in dim 0.
    assert!(result.generators[1][0].abs() > EPS);
    assert!(result.generators[1][1].abs() < EPS);
    assert!(result.generators[1][2].abs() < EPS);
}

// ---------------------------------------------------------------------------
// T04: Tightness analysis
// ---------------------------------------------------------------------------

#[test]
fn test_relu_tightness_always_inactive() {
    // All negative -> hull width goes to 0
    let z = ConcreteZonotope::new(vec![-5.0], vec![vec![1.0]]);
    let ratio = verify_relu_tightness(&z);
    // Width before = 2, width after = 0 => ratio = 0
    assert!(ratio.abs() < EPS);
}

#[test]
fn test_relu_tightness_crossing_value() {
    // Verify exact ratio for symmetric crossing.
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let ratio = verify_relu_tightness(&z);
    // hull before: [-1, 1], width = 2
    // After ReLU: center = 0.25, gens = [0.5, 0.25]
    // hull after: [0.25 - 0.5 - 0.25, 0.25 + 0.5 + 0.25] = [-0.5, 1.0]
    // width after = 1.5, ratio = 1.5 / 2.0 = 0.75
    assert!((ratio - 0.75).abs() < EPS);
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_relu_zero_width_zonotope() {
    // Point zonotope at 0: hull [0, 0]. lower >= 0, so always active.
    let z = ConcreteZonotope::new(vec![0.0], vec![]);
    let result = zonotope_relu(&z);
    assert!(result.center[0].abs() < EPS);
    assert_eq!(result.num_generators(), 0);
}

#[test]
fn test_relu_point_positive() {
    let z = ConcreteZonotope::new(vec![3.0], vec![]);
    let result = zonotope_relu(&z);
    assert!((result.center[0] - 3.0).abs() < EPS);
}

#[test]
fn test_relu_point_negative() {
    let z = ConcreteZonotope::new(vec![-3.0], vec![]);
    let result = zonotope_relu(&z);
    assert!(result.center[0].abs() < EPS);
}

#[test]
fn test_relu_single_generator_crossing() {
    let z = ConcreteZonotope::new(vec![0.5], vec![vec![1.0]]);
    // hull = [-0.5, 1.5]: crossing
    let result = zonotope_relu(&z);
    assert!(verify_relu_soundness(&z, 50));
    assert_eq!(result.num_generators(), 2);
}

// ---------------------------------------------------------------------------
// classify_relu unit tests
// ---------------------------------------------------------------------------

#[test]
fn test_classify_relu_active() {
    assert_eq!(classify_relu(0.0, 1.0), ReluCase::AlwaysActive);
    assert_eq!(classify_relu(1.0, 5.0), ReluCase::AlwaysActive);
}

#[test]
fn test_classify_relu_inactive() {
    assert_eq!(classify_relu(-5.0, -1.0), ReluCase::AlwaysInactive);
    assert_eq!(classify_relu(-3.0, 0.0), ReluCase::AlwaysInactive);
}

#[test]
fn test_classify_relu_crossing() {
    assert_eq!(classify_relu(-1.0, 1.0), ReluCase::Crossing);
    assert_eq!(classify_relu(-0.001, 0.001), ReluCase::Crossing);
}

// ---------------------------------------------------------------------------
// T07: Affine + ReLU composition
// ---------------------------------------------------------------------------

#[test]
fn test_affine_relu_identity_weight() {
    let z = ConcreteZonotope::new(vec![1.0, -1.0], vec![vec![0.5, 0.5]]);
    let weight = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let bias = vec![0.0, 0.0];
    let result = zonotope_affine_relu(&z, &weight, &bias);
    // Same as plain ReLU on z.
    let plain = zonotope_relu(&z);
    assert_eq!(result.center, plain.center);
    assert_eq!(result.generators.len(), plain.generators.len());
}

#[test]
fn test_affine_relu_with_bias_shift() {
    // Shift all values positive with bias -> all active -> ReLU is identity.
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let weight = vec![vec![1.0]];
    let bias = vec![10.0];
    let result = zonotope_affine_relu(&z, &weight, &bias);
    // After affine: center=10, gen=[1], hull=[9,11] -> all active
    assert!((result.center[0] - 10.0).abs() < EPS);
    assert_eq!(result.num_generators(), 1);
    assert!((result.generators[0][0] - 1.0).abs() < EPS);
}

#[test]
fn test_affine_relu_negative_weight_flips_sign() {
    // z has positive hull [1, 3]. After W=-1, hull becomes [-3, -1] -> inactive.
    let z = ConcreteZonotope::new(vec![2.0], vec![vec![1.0]]);
    let weight = vec![vec![-1.0]];
    let bias = vec![0.0];
    let result = zonotope_affine_relu(&z, &weight, &bias);
    // After affine: center=-2, gen=[-1], hull=[-3,-1] -> inactive -> zeros
    assert!(result.center[0].abs() < EPS);
}

// ---------------------------------------------------------------------------
// Forward pass through multi-layer network
// ---------------------------------------------------------------------------

#[test]
fn test_forward_pass_2_layers() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let layers = vec![
        // Layer 1: 2->2
        (vec![vec![1.0, 1.0], vec![1.0, -1.0]], vec![0.0, 0.0]),
        // Layer 2: 2->1
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let result = zonotope_forward_pass(&z, &layers);
    assert_eq!(result.dim(), 1);
    let (lo, hi) = result.to_interval();
    assert!(hi[0] > lo[0], "output should have nonzero width");
}

#[test]
fn test_forward_pass_single_layer() {
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![2.0]]);
    let layers = vec![(vec![vec![1.0]], vec![0.0])];
    let result = zonotope_forward_pass(&z, &layers);
    let plain = zonotope_affine_relu(&z, &[vec![1.0]], &[0.0]);
    assert_eq!(result.center, plain.center);
}

#[test]
fn test_forward_pass_empty_layers() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![0.5, 0.5]]);
    let result = zonotope_forward_pass(&z, &[]);
    assert_eq!(result.center, z.center);
    assert_eq!(result.generators, z.generators);
}

// ---------------------------------------------------------------------------
// Zonotope tighter than IBP
// ---------------------------------------------------------------------------

#[test]
fn test_zonotope_tighter_than_ibp_crossing() {
    // Correlated input: both dims move together. Zonotope tracks this
    // correlation; IBP does not.
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![1.0, 1.0]], // single shared generator
    );
    let layers = vec![(vec![vec![1.0, -1.0]], vec![0.0])];
    let (zono_w, ibp_w) = compare_zonotope_ibp(&z, &layers);
    // Zonotope should be at least as tight as IBP.
    assert!(
        zono_w <= ibp_w + EPS,
        "zonotope width {} should be <= IBP width {}",
        zono_w,
        ibp_w
    );
}

#[test]
fn test_zonotope_vs_ibp_identity_network() {
    // Identity network with all-positive input -> both methods exact.
    let z = ConcreteZonotope::new(vec![5.0], vec![vec![1.0]]);
    let layers = vec![(vec![vec![1.0]], vec![0.0])];
    let (zono_w, ibp_w) = compare_zonotope_ibp(&z, &layers);
    assert!((zono_w - ibp_w).abs() < EPS);
}

#[test]
fn test_zonotope_vs_ibp_2_layer_network() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.5], vec![0.5, 1.0]]);
    let layers = vec![
        (vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (zono_w, ibp_w) = compare_zonotope_ibp(&z, &layers);
    assert!(
        zono_w <= ibp_w + EPS,
        "zonotope width {} should be <= IBP width {}",
        zono_w,
        ibp_w
    );
}
