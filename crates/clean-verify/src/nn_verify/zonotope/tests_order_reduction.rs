// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for zonotope order reduction strategies: magnitude, PCA, Girard,
//! soundness verification, error bounds, and edge cases.

use super::concrete::ConcreteZonotope;
use super::order_reduction::{
    reduce_by_magnitude, reduce_by_pca, reduce_girard, reduction_error_bound,
    verify_reduction_soundness,
};

const EPS: f64 = 1e-9;

fn approx_eq(a: f64, b: f64) -> bool {
    (a - b).abs() < EPS
}

/// Compute interval hull half-widths for a zonotope.
fn hull_half_widths(z: &ConcreteZonotope) -> Vec<f64> {
    let d = z.dim();
    (0..d)
        .map(|j| z.generators.iter().map(|g| g[j].abs()).sum())
        .collect()
}

// ---------------------------------------------------------------------------
// reduce_by_magnitude — basic behavior
// ---------------------------------------------------------------------------

#[test]
fn test_magnitude_basic_reduction() {
    let z = ConcreteZonotope::new(
        vec![1.0, 2.0],
        vec![
            vec![3.0, 0.0], // mag 3
            vec![0.0, 2.0], // mag 2
            vec![0.5, 0.5], // mag ~0.707
            vec![0.1, 0.1], // mag ~0.141
        ],
    );
    let reduced = reduce_by_magnitude(&z, 2);
    // Kept the 2 largest, merged the rest into one -> 3 generators total.
    assert_eq!(reduced.num_generators(), 3);
    assert_eq!(reduced.center, z.center);
}

#[test]
fn test_magnitude_preserves_hull() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![
            vec![3.0, 0.0],
            vec![0.0, 2.0],
            vec![0.5, 0.5],
            vec![-0.3, 0.1],
        ],
    );
    let reduced = reduce_by_magnitude(&z, 2);

    // Interval hull should be identical (magnitude merge preserves T12).
    let orig_hw = hull_half_widths(&z);
    let reduced_hw = hull_half_widths(&reduced);
    for j in 0..2 {
        assert!(
            approx_eq(orig_hw[j], reduced_hw[j]),
            "dim {j}: orig={}, reduced={}",
            orig_hw[j],
            reduced_hw[j]
        );
    }
}

#[test]
fn test_magnitude_identity_when_under_limit() {
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![2.0], vec![3.0]]);
    let reduced = reduce_by_magnitude(&z, 5);
    assert_eq!(reduced.num_generators(), 2);
    assert_eq!(reduced.generators, z.generators);
}

#[test]
fn test_magnitude_identity_at_exact_limit() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let reduced = reduce_by_magnitude(&z, 2);
    assert_eq!(reduced.num_generators(), 2);
}

#[test]
fn test_magnitude_empty_generators() {
    let z = ConcreteZonotope::new(vec![5.0, 6.0], vec![]);
    let reduced = reduce_by_magnitude(&z, 3);
    assert!(reduced.generators.is_empty());
    assert_eq!(reduced.center, vec![5.0, 6.0]);
}

#[test]
fn test_magnitude_single_generator() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![3.0, 4.0]]);
    let reduced = reduce_by_magnitude(&z, 0);
    // One generator merged into one hull generator.
    assert_eq!(reduced.num_generators(), 1);
    assert!(approx_eq(reduced.generators[0][0], 3.0));
    assert!(approx_eq(reduced.generators[0][1], 4.0));
}

#[test]
fn test_magnitude_equal_magnitudes() {
    // All generators same L2 norm -> stable sort preserves order.
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![
            vec![1.0, 1.0],  // mag sqrt(2)
            vec![1.0, -1.0], // mag sqrt(2)
            vec![-1.0, 1.0], // mag sqrt(2)
        ],
    );
    let reduced = reduce_by_magnitude(&z, 2);
    assert_eq!(reduced.num_generators(), 3); // 2 kept + 1 merged
}

#[test]
fn test_magnitude_soundness_sampling() {
    let z = ConcreteZonotope::new(
        vec![1.0, -2.0, 3.0],
        vec![
            vec![2.0, 0.0, 1.0],
            vec![0.0, 1.5, 0.0],
            vec![0.5, 0.5, 0.5],
            vec![0.1, -0.2, 0.3],
            vec![-0.4, 0.0, 0.1],
        ],
    );
    for target in 0..=5 {
        let reduced = reduce_by_magnitude(&z, target);
        assert!(
            verify_reduction_soundness(&z, &reduced),
            "magnitude reduction to {target} should be sound"
        );
    }
}

// ---------------------------------------------------------------------------
// reduce_by_pca
// ---------------------------------------------------------------------------

#[test]
fn test_pca_basic_reduction() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![10.0, 0.0], vec![0.0, 0.1], vec![0.5, 0.5]],
    );
    let reduced = reduce_by_pca(&z, 1);
    assert_eq!(reduced.num_generators(), 1);
    assert_eq!(reduced.center, z.center);
    // Dominant direction should be close to x-axis.
    let x_mag = reduced.generators[0][0].abs();
    let y_mag = reduced.generators[0][1].abs();
    assert!(
        x_mag > y_mag * 5.0,
        "PCA should pick x-direction: x={x_mag}, y={y_mag}"
    );
}

#[test]
fn test_pca_two_components() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![5.0, 0.0], vec![0.0, 3.0], vec![0.1, 0.1]],
    );
    let reduced = reduce_by_pca(&z, 2);
    assert_eq!(reduced.num_generators(), 2);
}

#[test]
fn test_pca_empty_zonotope() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![]);
    let reduced = reduce_by_pca(&z, 5);
    assert!(reduced.generators.is_empty());
}

#[test]
fn test_pca_target_zero() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0], vec![2.0]]);
    let reduced = reduce_by_pca(&z, 0);
    assert!(reduced.generators.is_empty());
}

#[test]
fn test_pca_preserves_center() {
    let z = ConcreteZonotope::new(vec![7.5, -3.2], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let reduced = reduce_by_pca(&z, 1);
    assert_eq!(reduced.center, vec![7.5, -3.2]);
}

#[test]
fn test_pca_captures_variance() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![5.0, 0.0], vec![0.0, 3.0]]);
    let reduced = reduce_by_pca(&z, 2);
    // Total variance: 25 + 9 = 34.
    let total_var: f64 = reduced
        .generators
        .iter()
        .map(|g| g.iter().map(|x| x * x).sum::<f64>())
        .sum();
    assert!(
        total_var > 30.0,
        "PCA should capture most variance, got {total_var}"
    );
}

// ---------------------------------------------------------------------------
// reduce_girard
// ---------------------------------------------------------------------------

#[test]
fn test_girard_basic_reduction() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![
            vec![3.0, 0.0], // L1=3
            vec![0.0, 2.0], // L1=2
            vec![0.5, 0.5], // L1=1
            vec![0.1, 0.1], // L1=0.2
        ],
    );
    let reduced = reduce_girard(&z, 2);
    // 2 kept + up to 2 axis-aligned box generators for the merged.
    assert!(reduced.num_generators() >= 2);
    assert_eq!(reduced.center, z.center);
}

#[test]
fn test_girard_preserves_hull() {
    let z = ConcreteZonotope::new(
        vec![1.0, 2.0],
        vec![
            vec![3.0, 0.0],
            vec![0.0, 2.0],
            vec![0.5, 0.5],
            vec![-0.3, 0.1],
        ],
    );
    let reduced = reduce_girard(&z, 2);

    // Girard should preserve interval hull.
    let orig_hw = hull_half_widths(&z);
    let reduced_hw = hull_half_widths(&reduced);
    for j in 0..2 {
        assert!(
            approx_eq(orig_hw[j], reduced_hw[j]),
            "dim {j}: orig={}, reduced={}",
            orig_hw[j],
            reduced_hw[j]
        );
    }
}

#[test]
fn test_girard_identity_when_under_limit() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0], vec![2.0]]);
    let reduced = reduce_girard(&z, 10);
    assert_eq!(reduced.num_generators(), 2);
    assert_eq!(reduced.generators, z.generators);
}

#[test]
fn test_girard_empty_generators() {
    let z = ConcreteZonotope::new(vec![3.0, 4.0], vec![]);
    let reduced = reduce_girard(&z, 5);
    assert!(reduced.generators.is_empty());
}

#[test]
fn test_girard_creates_axis_aligned_generators() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![
            vec![5.0, 0.0], // L1=5, kept
            vec![0.5, 0.5], // L1=1, merged
            vec![0.3, 0.1], // L1=0.4, merged
        ],
    );
    let reduced = reduce_girard(&z, 1);
    // 1 kept + 2 axis-aligned box generators.
    assert!(reduced.num_generators() >= 2);

    // Check that merged generators are axis-aligned (only one nonzero per gen).
    let merged_gens = &reduced.generators[1..];
    for g in merged_gens {
        let nonzero_count = g.iter().filter(|&&v| v.abs() > EPS).count();
        assert_eq!(
            nonzero_count, 1,
            "Girard box generators should be axis-aligned, got {g:?}"
        );
    }
}

#[test]
fn test_girard_soundness_sampling() {
    let z = ConcreteZonotope::new(
        vec![1.0, -2.0, 3.0],
        vec![
            vec![2.0, 0.0, 1.0],
            vec![0.0, 1.5, 0.0],
            vec![0.5, 0.5, 0.5],
            vec![0.1, -0.2, 0.3],
        ],
    );
    for target in 0..=4 {
        let reduced = reduce_girard(&z, target);
        assert!(
            verify_reduction_soundness(&z, &reduced),
            "Girard reduction to {target} should be sound"
        );
    }
}

#[test]
fn test_girard_skips_zero_box_components() {
    // If merged generators have zero contribution in a dimension,
    // no axis-aligned generator is created for that dimension.
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![
            vec![5.0, 0.0], // L1=5, kept
            vec![0.3, 0.0], // L1=0.3, merged (only x component)
        ],
    );
    let reduced = reduce_girard(&z, 1);
    // Should have 1 kept + 1 axis-aligned (x only, y is zero).
    assert_eq!(reduced.num_generators(), 2);
}

// ---------------------------------------------------------------------------
// verify_reduction_soundness
// ---------------------------------------------------------------------------

#[test]
fn test_soundness_identical_zonotopes() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    assert!(verify_reduction_soundness(&z, &z));
}

#[test]
fn test_soundness_wider_reduced_passes() {
    let original = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let wider = ConcreteZonotope::new(vec![0.0], vec![vec![2.0]]);
    assert!(verify_reduction_soundness(&original, &wider));
}

#[test]
fn test_soundness_narrower_reduced_fails() {
    let original = ConcreteZonotope::new(vec![0.0], vec![vec![3.0]]);
    let narrower = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    assert!(!verify_reduction_soundness(&original, &narrower));
}

#[test]
fn test_soundness_empty_original() {
    let original = ConcreteZonotope::new(vec![5.0], vec![]);
    let reduced = ConcreteZonotope::new(vec![5.0], vec![]);
    assert!(verify_reduction_soundness(&original, &reduced));
}

// ---------------------------------------------------------------------------
// reduction_error_bound
// ---------------------------------------------------------------------------

#[test]
fn test_error_bound_identical_is_zero() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 2.0], vec![3.0, 4.0]]);
    assert!(approx_eq(reduction_error_bound(&z, &z), 0.0));
}

#[test]
fn test_error_bound_magnitude_reduction_is_zero() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![3.0, 0.0], vec![0.0, 2.0], vec![0.5, 0.5]],
    );
    let reduced = reduce_by_magnitude(&z, 1);
    let bound = reduction_error_bound(&z, &reduced);
    assert!(
        approx_eq(bound, 0.0),
        "magnitude reduction should have 0 hull error, got {bound}"
    );
}

#[test]
fn test_error_bound_girard_is_zero() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![3.0, 0.0], vec![0.0, 2.0], vec![0.5, 0.5]],
    );
    let reduced = reduce_girard(&z, 1);
    let bound = reduction_error_bound(&z, &reduced);
    assert!(
        approx_eq(bound, 0.0),
        "Girard reduction should have 0 hull error, got {bound}"
    );
}

#[test]
fn test_error_bound_known_value() {
    let original = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![3.0, 1.0], vec![1.0, 2.0]]);
    // Reduced with smaller generators.
    let reduced = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![2.0, 1.0]]);
    // orig spreads: [4.0, 3.0], comp spreads: [2.0, 1.0]
    // diffs: [2.0, 2.0], max = 2.0
    let bound = reduction_error_bound(&original, &reduced);
    assert!(approx_eq(bound, 2.0));
}

#[test]
fn test_error_bound_empty_zonotopes() {
    let z = ConcreteZonotope::new(vec![0.0; 0], vec![]);
    assert!(approx_eq(reduction_error_bound(&z, &z), 0.0));
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_zero_generators_all_methods() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0, 3.0], vec![]);

    let r1 = reduce_by_magnitude(&z, 5);
    assert!(r1.generators.is_empty());

    let r2 = reduce_by_pca(&z, 3);
    assert!(r2.generators.is_empty());

    let r3 = reduce_girard(&z, 2);
    assert!(r3.generators.is_empty());
}

#[test]
fn test_one_generator_magnitude() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 2.0]]);
    let reduced = reduce_by_magnitude(&z, 0);
    assert_eq!(reduced.num_generators(), 1);
    // Merged into hull: abs values.
    assert!(approx_eq(reduced.generators[0][0], 1.0));
    assert!(approx_eq(reduced.generators[0][1], 2.0));
}

#[test]
fn test_one_generator_girard() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 2.0]]);
    let reduced = reduce_girard(&z, 0);
    // Merged into 2 axis-aligned generators.
    assert!(reduced.num_generators() >= 1);
    assert!(verify_reduction_soundness(&z, &reduced));
}

#[test]
fn test_high_dimensional_reduction() {
    let d = 10;
    let n = 50;
    let generators: Vec<Vec<f64>> = (0..n)
        .map(|i| {
            (0..d)
                .map(|j| ((i * 7 + j * 13 + 3) % 11) as f64 - 5.0)
                .collect()
        })
        .collect();
    let z = ConcreteZonotope::new(vec![0.0; d], generators);

    let r1 = reduce_by_magnitude(&z, 10);
    assert!(verify_reduction_soundness(&z, &r1));
    assert!(approx_eq(reduction_error_bound(&z, &r1), 0.0));

    let r2 = reduce_girard(&z, 10);
    assert!(verify_reduction_soundness(&z, &r2));
    assert!(approx_eq(reduction_error_bound(&z, &r2), 0.0));
}

#[test]
fn test_magnitude_reduce_to_zero_merges_all() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.5, 0.5]],
    );
    let reduced = reduce_by_magnitude(&z, 0);
    // All merged into one interval hull generator.
    assert_eq!(reduced.num_generators(), 1);
    assert!(approx_eq(reduced.generators[0][0], 1.5)); // |1|+|0|+|0.5|
    assert!(approx_eq(reduced.generators[0][1], 1.5)); // |0|+|1|+|0.5|
}

#[test]
fn test_center_preserved_across_all_methods() {
    let center = vec![std::f64::consts::PI, -2.72, 1.41];
    let z = ConcreteZonotope::new(
        center.clone(),
        vec![
            vec![1.0, 0.0, 0.0],
            vec![0.0, 1.0, 0.0],
            vec![0.0, 0.0, 1.0],
        ],
    );

    assert_eq!(reduce_by_magnitude(&z, 1).center, center);
    assert_eq!(reduce_by_pca(&z, 1).center, center);
    assert_eq!(reduce_girard(&z, 1).center, center);
}
