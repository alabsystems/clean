// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for sampling-based runtime verification (verify.rs).
//! Covers T01, T02, T08, T12 via deterministic pseudo-random sampling.

use super::concrete::ConcreteZonotope;
use super::verify::*;

// ---------------------------------------------------------------------------
// T01: verify_hull_soundness
// ---------------------------------------------------------------------------

#[test]
fn test_hull_soundness_1d_single_gen() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    assert!(verify_hull_soundness(&z, 50));
}

#[test]
fn test_hull_soundness_2d_axis_aligned() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    assert!(verify_hull_soundness(&z, 50));
}

#[test]
fn test_hull_soundness_point_zonotope() {
    let z = ConcreteZonotope::new(vec![3.0, -1.0], vec![]);
    assert!(verify_hull_soundness(&z, 50));
}

#[test]
fn test_hull_soundness_many_generators() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![
            vec![1.0, 0.5],
            vec![0.3, -0.7],
            vec![-0.2, 0.4],
            vec![0.8, 0.1],
            vec![-0.5, 0.9],
        ],
    );
    assert!(verify_hull_soundness(&z, 100));
}

#[test]
fn test_hull_soundness_zero_samples() {
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![5.0]]);
    assert!(verify_hull_soundness(&z, 0));
}

#[test]
fn test_hull_soundness_one_sample() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    assert!(verify_hull_soundness(&z, 1));
}

#[test]
fn test_hull_soundness_100_samples() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    assert!(verify_hull_soundness(&z, 100));
}

#[test]
fn test_hull_soundness_10d() {
    let gens: Vec<Vec<f64>> = (0..10)
        .map(|i| {
            let mut g = vec![0.0; 10];
            g[i] = 1.0;
            g
        })
        .collect();
    let z = ConcreteZonotope::new(vec![0.0; 10], gens);
    assert!(verify_hull_soundness(&z, 200));
}

#[test]
fn test_hull_soundness_negative_center() {
    let z = ConcreteZonotope::new(vec![-5.0, -3.0], vec![vec![1.0, 0.0], vec![0.0, 2.0]]);
    assert!(verify_hull_soundness(&z, 50));
}

#[test]
fn test_hull_soundness_large_generators() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1e6], vec![2e6]]);
    assert!(verify_hull_soundness(&z, 50));
}

#[test]
fn test_hull_soundness_tiny_generators() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1e-12, 0.0], vec![0.0, 1e-12]]);
    assert!(verify_hull_soundness(&z, 50));
}

// ---------------------------------------------------------------------------
// T02: verify_linear_transform
// ---------------------------------------------------------------------------

#[test]
fn test_linear_transform_identity() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let w: &[&[f64]] = &[&[1.0, 0.0], &[0.0, 1.0]];
    let b = [0.0, 0.0];
    assert!(verify_linear_transform(&z, w, &b, 50));
}

#[test]
fn test_linear_transform_scaling() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let w: &[&[f64]] = &[&[2.0, 0.0], &[0.0, 3.0]];
    let b = [0.0, 0.0];
    assert!(verify_linear_transform(&z, w, &b, 50));
}

#[test]
fn test_linear_transform_translation_only() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let w: &[&[f64]] = &[&[1.0, 0.0], &[0.0, 1.0]];
    let b = [1.0, 2.0];
    assert!(verify_linear_transform(&z, w, &b, 50));
}

#[test]
fn test_linear_transform_rotation() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let w: &[&[f64]] = &[&[0.0, -1.0], &[1.0, 0.0]];
    let b = [0.0, 0.0];
    assert!(verify_linear_transform(&z, w, &b, 50));
}

#[test]
fn test_linear_transform_dim_reduction() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let w: &[&[f64]] = &[&[1.0, 1.0]];
    let b = [0.0];
    assert!(verify_linear_transform(&z, w, &b, 50));
}

#[test]
fn test_linear_transform_dim_expansion() {
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![2.0]]);
    let w: &[&[f64]] = &[&[1.0], &[1.0]];
    let b = [0.0, 0.0];
    assert!(verify_linear_transform(&z, w, &b, 50));
}

#[test]
fn test_linear_transform_zero_weight() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![3.0, 0.0], vec![0.0, 4.0]]);
    let w: &[&[f64]] = &[&[0.0, 0.0], &[0.0, 0.0]];
    let b = [5.0, 6.0];
    assert!(verify_linear_transform(&z, w, &b, 50));
}

#[test]
fn test_linear_transform_single_gen() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 1.0]]);
    let w: &[&[f64]] = &[&[2.0, -1.0]];
    let b = [0.0];
    assert!(verify_linear_transform(&z, w, &b, 50));
}

#[test]
fn test_linear_transform_multi_gen_nontrivial() {
    let z = ConcreteZonotope::new(
        vec![1.0, -1.0],
        vec![vec![0.5, 0.3], vec![-0.2, 0.7], vec![0.1, -0.4]],
    );
    let w: &[&[f64]] = &[&[1.0, 2.0], &[-1.0, 0.5]];
    let b = [0.1, -0.2];
    assert!(verify_linear_transform(&z, w, &b, 100));
}

#[test]
fn test_linear_transform_zero_samples() {
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![1.0]]);
    let w: &[&[f64]] = &[&[2.0]];
    let b = [1.0];
    assert!(verify_linear_transform(&z, w, &b, 0));
}

#[test]
fn test_linear_transform_100_samples() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let w: &[&[f64]] = &[&[1.0, 1.0], &[1.0, -1.0]];
    let b = [0.0, 0.0];
    assert!(verify_linear_transform(&z, w, &b, 100));
}

#[test]
fn test_linear_transform_point_zonotope() {
    let z = ConcreteZonotope::new(vec![2.0, 3.0], vec![]);
    let w: &[&[f64]] = &[&[1.0, 0.0], &[0.0, 1.0]];
    let b = [1.0, 1.0];
    assert!(verify_linear_transform(&z, w, &b, 50));
}

// ---------------------------------------------------------------------------
// T12: verify_compress_hull_exact
// ---------------------------------------------------------------------------

#[test]
fn test_compress_hull_keep_all() {
    let z = ConcreteZonotope::new(
        vec![1.0, 2.0],
        vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.5, 0.5]],
    );
    assert!(verify_compress_hull_exact(&z, &[0, 1, 2]));
}

#[test]
fn test_compress_hull_keep_none() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.5, 0.5]],
    );
    assert!(verify_compress_hull_exact(&z, &[]));
}

#[test]
fn test_compress_hull_keep_subset() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.5, 0.5]],
    );
    assert!(verify_compress_hull_exact(&z, &[0]));
}

#[test]
fn test_compress_hull_single_gen_keep() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![3.0]]);
    assert!(verify_compress_hull_exact(&z, &[0]));
}

#[test]
fn test_compress_hull_single_gen_drop() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![3.0]]);
    assert!(verify_compress_hull_exact(&z, &[]));
}

#[test]
fn test_compress_hull_keep_first_only() {
    let z = ConcreteZonotope::new(
        vec![1.0, 2.0],
        vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.3, 0.7]],
    );
    assert!(verify_compress_hull_exact(&z, &[0]));
}

#[test]
fn test_compress_hull_keep_last_only() {
    let z = ConcreteZonotope::new(
        vec![1.0, 2.0],
        vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.3, 0.7]],
    );
    assert!(verify_compress_hull_exact(&z, &[2]));
}

#[test]
fn test_compress_hull_3d_five_gens() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0, 0.0],
        vec![
            vec![1.0, 0.0, 0.0],
            vec![0.0, 1.0, 0.0],
            vec![0.0, 0.0, 1.0],
            vec![0.5, 0.5, 0.0],
            vec![0.0, 0.5, 0.5],
        ],
    );
    assert!(verify_compress_hull_exact(&z, &[0, 2, 4]));
}

#[test]
fn test_compress_hull_3d_five_gens_keep_two() {
    let z = ConcreteZonotope::new(
        vec![1.0, -1.0, 0.5],
        vec![
            vec![1.0, 0.0, 0.0],
            vec![0.0, 1.0, 0.0],
            vec![0.0, 0.0, 1.0],
            vec![0.5, 0.5, 0.0],
            vec![0.0, 0.5, 0.5],
        ],
    );
    assert!(verify_compress_hull_exact(&z, &[1, 3]));
}

#[test]
fn test_compress_hull_empty_generators() {
    let z = ConcreteZonotope::new(vec![5.0, -3.0], vec![]);
    assert!(verify_compress_hull_exact(&z, &[]));
}

#[test]
fn test_compress_hull_negative_generators() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![-1.0, -2.0], vec![-0.5, 0.3]]);
    assert!(verify_compress_hull_exact(&z, &[0]));
}

// ---------------------------------------------------------------------------
// T08: verify_minkowski_sum
// ---------------------------------------------------------------------------

#[test]
fn test_minkowski_sum_1d_basic() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    assert!(verify_minkowski_sum(&z1, &z2, 50));
}

#[test]
fn test_minkowski_sum_2d_axis_aligned() {
    let z1 = ConcreteZonotope::new(vec![1.0, 0.0], vec![vec![1.0, 0.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0, 1.0], vec![vec![0.0, 1.0]]);
    assert!(verify_minkowski_sum(&z1, &z2, 50));
}

#[test]
fn test_minkowski_sum_point_plus_zonotope() {
    let z1 = ConcreteZonotope::new(vec![5.0, 3.0], vec![]);
    let z2 = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    assert!(verify_minkowski_sum(&z1, &z2, 50));
}

#[test]
fn test_minkowski_sum_zonotope_plus_point() {
    let z1 = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let z2 = ConcreteZonotope::new(vec![5.0, 3.0], vec![]);
    assert!(verify_minkowski_sum(&z1, &z2, 50));
}

#[test]
fn test_minkowski_sum_point_plus_point() {
    let z1 = ConcreteZonotope::new(vec![1.0, 2.0], vec![]);
    let z2 = ConcreteZonotope::new(vec![3.0, 4.0], vec![]);
    assert!(verify_minkowski_sum(&z1, &z2, 50));
}

#[test]
fn test_minkowski_sum_self() {
    let z = ConcreteZonotope::new(vec![1.0, -1.0], vec![vec![0.5, 0.3], vec![-0.2, 0.7]]);
    assert!(verify_minkowski_sum(&z, &z, 100));
}

#[test]
fn test_minkowski_sum_different_gen_counts() {
    let z1 = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0]]);
    let z2 = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![0.0, 1.0], vec![0.5, 0.5], vec![0.3, -0.2]],
    );
    assert!(verify_minkowski_sum(&z1, &z2, 50));
}

#[test]
fn test_minkowski_sum_many_generators() {
    let z1 = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![
            vec![1.0, 0.0],
            vec![0.0, 1.0],
            vec![0.5, 0.5],
            vec![-0.3, 0.7],
            vec![0.2, -0.4],
        ],
    );
    let z2 = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![
            vec![0.3, 0.0],
            vec![0.0, 0.6],
            vec![-0.1, 0.2],
            vec![0.4, -0.3],
            vec![0.1, 0.8],
        ],
    );
    assert!(verify_minkowski_sum(&z1, &z2, 200));
}

#[test]
fn test_minkowski_sum_zero_samples() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    assert!(verify_minkowski_sum(&z1, &z2, 0));
}

#[test]
fn test_minkowski_sum_100_samples() {
    let z1 = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let z2 = ConcreteZonotope::new(vec![-1.0, 0.0], vec![vec![0.5, 0.5]]);
    assert!(verify_minkowski_sum(&z1, &z2, 100));
}

#[test]
fn test_minkowski_sum_negative_centers() {
    let z1 = ConcreteZonotope::new(vec![-3.0, -5.0], vec![vec![1.0, 0.0]]);
    let z2 = ConcreteZonotope::new(vec![-2.0, -1.0], vec![vec![0.0, 1.0]]);
    assert!(verify_minkowski_sum(&z1, &z2, 50));
}

#[test]
fn test_minkowski_sum_different_magnitudes() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![100.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![0.001]]);
    assert!(verify_minkowski_sum(&z1, &z2, 50));
}

#[test]
fn test_minkowski_sum_3d() {
    let z1 = ConcreteZonotope::new(
        vec![1.0, 2.0, 3.0],
        vec![vec![1.0, 0.0, 0.0], vec![0.0, 1.0, 0.0]],
    );
    let z2 = ConcreteZonotope::new(
        vec![0.0, 0.0, 0.0],
        vec![vec![0.0, 0.0, 1.0], vec![0.5, 0.5, 0.5]],
    );
    assert!(verify_minkowski_sum(&z1, &z2, 100));
}

// ---------------------------------------------------------------------------
// Determinism: fixed seed guarantees identical results across calls
// ---------------------------------------------------------------------------

#[test]
fn test_hull_soundness_deterministic() {
    let z = ConcreteZonotope::new(
        vec![1.0, -2.0],
        vec![vec![0.5, 0.3], vec![-0.2, 0.7], vec![0.4, -0.1]],
    );
    let r1 = verify_hull_soundness(&z, 200);
    let r2 = verify_hull_soundness(&z, 200);
    assert_eq!(r1, r2);
}

#[test]
fn test_linear_transform_deterministic() {
    let z = ConcreteZonotope::new(vec![1.0, 0.0], vec![vec![1.0, 0.5], vec![-0.3, 0.8]]);
    let w: &[&[f64]] = &[&[2.0, -1.0], &[0.5, 1.5]];
    let b = [0.1, -0.3];
    let r1 = verify_linear_transform(&z, w, &b, 200);
    let r2 = verify_linear_transform(&z, w, &b, 200);
    assert_eq!(r1, r2);
}

#[test]
fn test_minkowski_sum_deterministic() {
    let z1 = ConcreteZonotope::new(vec![1.0, -1.0], vec![vec![0.5, 0.3], vec![-0.2, 0.7]]);
    let z2 = ConcreteZonotope::new(vec![0.0, 2.0], vec![vec![0.1, -0.4], vec![0.6, 0.2]]);
    let r1 = verify_minkowski_sum(&z1, &z2, 200);
    let r2 = verify_minkowski_sum(&z1, &z2, 200);
    assert_eq!(r1, r2);
}

// ---------------------------------------------------------------------------
// Edge cases and combined scenarios
// ---------------------------------------------------------------------------

#[test]
fn test_hull_soundness_1d_zero_center() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![0.0]]);
    assert!(verify_hull_soundness(&z, 50));
}

#[test]
fn test_linear_transform_negative_bias() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let w: &[&[f64]] = &[&[1.0, 0.0], &[0.0, 1.0]];
    let b = [-10.0, -20.0];
    assert!(verify_linear_transform(&z, w, &b, 50));
}

#[test]
fn test_compress_hull_keep_middle() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.5, 0.5]],
    );
    assert!(verify_compress_hull_exact(&z, &[1]));
}

#[test]
fn test_minkowski_sum_1d_negative_gens() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![-1.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![-2.0]]);
    assert!(verify_minkowski_sum(&z1, &z2, 50));
}

#[test]
fn test_hull_soundness_mixed_sign_gens() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, -1.0], vec![-1.0, 1.0]]);
    assert!(verify_hull_soundness(&z, 100));
}
