// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for ConcreteZonotope: hull, containment, transform, compression,
//! Minkowski sum, and soundness verification properties.

use super::concrete::ConcreteZonotope;

const EPS: f64 = 1e-9;

fn approx_eq(a: f64, b: f64) -> bool {
    (a - b).abs() < EPS
}

// ---------------------------------------------------------------------------
// 1D zonotope basics
// ---------------------------------------------------------------------------

#[test]
fn test_1d_zonotope_hull() {
    // center=5, gen=[3] -> hull = [5-3, 5+3] = [2, 8]
    let z = ConcreteZonotope::new(vec![5.0], vec![vec![3.0]]);
    let (lo, hi) = z.to_interval();
    assert!(approx_eq(lo[0], 2.0), "lower should be 2, got {}", lo[0]);
    assert!(approx_eq(hi[0], 8.0), "upper should be 8, got {}", hi[0]);
}

#[test]
fn test_1d_zonotope_containment() {
    let z = ConcreteZonotope::new(vec![5.0], vec![vec![3.0]]);
    // Points inside: center, endpoints, interior
    assert!(z.contains(&[5.0]), "center should be inside");
    assert!(z.contains(&[2.0]), "lower endpoint should be inside");
    assert!(z.contains(&[8.0]), "upper endpoint should be inside");
    assert!(z.contains(&[3.5]), "interior point should be inside");
    // Points outside
    assert!(!z.contains(&[1.9]), "below lower should be outside");
    assert!(!z.contains(&[8.1]), "above upper should be outside");
}

#[test]
fn test_1d_two_generators_hull() {
    // center=0, gens=[2, 3] -> hull = [-5, 5]
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![2.0], vec![3.0]]);
    let (lo, hi) = z.to_interval();
    assert!(approx_eq(lo[0], -5.0));
    assert!(approx_eq(hi[0], 5.0));
}

// ---------------------------------------------------------------------------
// 2D zonotope with 2 generators
// ---------------------------------------------------------------------------

#[test]
fn test_2d_zonotope_hull() {
    // center=(1,2), gens=[(1,0),(0,2)]
    // hull_x = [1-1-0, 1+1+0] = [0, 2]
    // hull_y = [2-0-2, 2+0+2] = [0, 4]
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 2.0]]);
    let (lo, hi) = z.to_interval();
    assert!(approx_eq(lo[0], 0.0));
    assert!(approx_eq(hi[0], 2.0));
    assert!(approx_eq(lo[1], 0.0));
    assert!(approx_eq(hi[1], 4.0));
}

#[test]
fn test_2d_zonotope_containment() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 2.0]]);
    // Center
    assert!(z.contains(&[1.0, 2.0]));
    // Vertices: (1 +/- 1, 2 +/- 2)
    assert!(z.contains(&[2.0, 4.0])); // eps=(+1,+1)
    assert!(z.contains(&[0.0, 0.0])); // eps=(-1,-1)
    assert!(z.contains(&[2.0, 0.0])); // eps=(+1,-1)
    assert!(z.contains(&[0.0, 4.0])); // eps=(-1,+1)
                                      // Outside
    assert!(!z.contains(&[3.0, 2.0]));
}

#[test]
fn test_2d_diagonal_generators_hull() {
    // center=(0,0), gens=[(1,1),(1,-1)]
    // hull_x = [-2, 2], hull_y = [-2, 2]
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 1.0], vec![1.0, -1.0]]);
    let (lo, hi) = z.to_interval();
    assert!(approx_eq(lo[0], -2.0));
    assert!(approx_eq(hi[0], 2.0));
    assert!(approx_eq(lo[1], -2.0));
    assert!(approx_eq(hi[1], 2.0));
}

// ---------------------------------------------------------------------------
// Linear transform (T02)
// ---------------------------------------------------------------------------

#[test]
fn test_linear_transform_identity() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![3.0, 0.0], vec![0.0, 4.0]]);
    let id: Vec<&[f64]> = vec![&[1.0, 0.0], &[0.0, 1.0]];
    let bias = vec![0.0, 0.0];
    let result = z.linear_transform(&id, &bias);
    assert_eq!(result.center, z.center);
    assert_eq!(result.generators, z.generators);
}

#[test]
fn test_linear_transform_scaling() {
    // Scale x by 2, y by 3
    let z = ConcreteZonotope::new(vec![1.0, 1.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let w: Vec<&[f64]> = vec![&[2.0, 0.0], &[0.0, 3.0]];
    let bias = vec![0.0, 0.0];
    let result = z.linear_transform(&w, &bias);
    assert!(approx_eq(result.center[0], 2.0));
    assert!(approx_eq(result.center[1], 3.0));
    // gen[0] = [2*1, 3*0] = [2, 0]
    assert!(approx_eq(result.generators[0][0], 2.0));
    assert!(approx_eq(result.generators[0][1], 0.0));
    // gen[1] = [2*0, 3*1] = [0, 3]
    assert!(approx_eq(result.generators[1][0], 0.0));
    assert!(approx_eq(result.generators[1][1], 3.0));
}

#[test]
fn test_linear_transform_with_bias() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let w: Vec<&[f64]> = vec![&[1.0]];
    let bias = vec![5.0];
    let result = z.linear_transform(&w, &bias);
    assert!(approx_eq(result.center[0], 5.0));
    // Generator unchanged
    assert!(approx_eq(result.generators[0][0], 1.0));
}

#[test]
fn test_linear_transform_dimension_change() {
    // Project 2D -> 1D: W = [[1, 1]], b = [0]
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let w: Vec<&[f64]> = vec![&[1.0, 1.0]];
    let bias = vec![0.0];
    let result = z.linear_transform(&w, &bias);
    assert_eq!(result.dim(), 1);
    assert!(approx_eq(result.center[0], 3.0)); // 1+2
                                               // gen[0] = [1*1 + 1*0] = [1]
    assert!(approx_eq(result.generators[0][0], 1.0));
    // gen[1] = [1*0 + 1*1] = [1]
    assert!(approx_eq(result.generators[1][0], 1.0));
}

#[test]
fn test_linear_transform_rotation_hull() {
    // 90-degree rotation: [[0, -1], [1, 0]]
    // center=(1,0), gen=[(1,0)] -> center'=(0,1), gen'=[(0,1)]
    let z = ConcreteZonotope::new(vec![1.0, 0.0], vec![vec![1.0, 0.0]]);
    let w: Vec<&[f64]> = vec![&[0.0, -1.0], &[1.0, 0.0]];
    let bias = vec![0.0, 0.0];
    let result = z.linear_transform(&w, &bias);
    assert!(approx_eq(result.center[0], 0.0));
    assert!(approx_eq(result.center[1], 1.0));
    assert!(approx_eq(result.generators[0][0], 0.0));
    assert!(approx_eq(result.generators[0][1], 1.0));
}

// ---------------------------------------------------------------------------
// Compression (T10)
// ---------------------------------------------------------------------------

#[test]
fn test_compress_merge_all() {
    // Keep nothing -> single merged generator
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, -2.0], vec![3.0, 4.0]]);
    let compressed = z.compress(&[]);
    assert_eq!(compressed.num_generators(), 1);
    // merged = [|1|+|3|, |-2|+|4|] = [4, 6]
    assert!(approx_eq(compressed.generators[0][0], 4.0));
    assert!(approx_eq(compressed.generators[0][1], 6.0));
}

#[test]
fn test_compress_keep_all() {
    // Keep everything -> no merging, same zonotope
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![2.0], vec![3.0]]);
    let compressed = z.compress(&[0, 1]);
    assert_eq!(compressed.num_generators(), 2);
    assert!(approx_eq(compressed.generators[0][0], 2.0));
    assert!(approx_eq(compressed.generators[1][0], 3.0));
}

#[test]
fn test_compress_keep_one() {
    // 3 generators, keep index 1 -> kept gen + 1 merged gen
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![1.0, 2.0], vec![3.0, 4.0], vec![5.0, 6.0]],
    );
    let compressed = z.compress(&[1]);
    assert_eq!(compressed.num_generators(), 2);
    // Kept: gen[1] = [3, 4]
    assert!(approx_eq(compressed.generators[0][0], 3.0));
    assert!(approx_eq(compressed.generators[0][1], 4.0));
    // Merged from gen[0] and gen[2]: [|1|+|5|, |2|+|6|] = [6, 8]
    assert!(approx_eq(compressed.generators[1][0], 6.0));
    assert!(approx_eq(compressed.generators[1][1], 8.0));
}

#[test]
fn test_compress_hull_unchanged_t12() {
    // T12: hull(compress(Z)) == hull(Z)
    let z = ConcreteZonotope::new(
        vec![1.0, 2.0],
        vec![vec![1.0, -2.0], vec![3.0, 4.0], vec![-2.0, 1.0]],
    );
    assert!(z.verify_compress_hull_exact(&[]));
    assert!(z.verify_compress_hull_exact(&[0]));
    assert!(z.verify_compress_hull_exact(&[1]));
    assert!(z.verify_compress_hull_exact(&[2]));
    assert!(z.verify_compress_hull_exact(&[0, 1]));
    assert!(z.verify_compress_hull_exact(&[0, 2]));
    assert!(z.verify_compress_hull_exact(&[1, 2]));
    assert!(z.verify_compress_hull_exact(&[0, 1, 2]));
}

#[test]
fn test_compress_hull_exact_negative_generators() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![-3.0], vec![-7.0]]);
    // Hull: [-10, 10]
    assert!(z.verify_compress_hull_exact(&[]));
    assert!(z.verify_compress_hull_exact(&[0]));
}

// ---------------------------------------------------------------------------
// Minkowski sum (T08)
// ---------------------------------------------------------------------------

#[test]
fn test_minkowski_add_basic() {
    let z1 = ConcreteZonotope::new(vec![1.0], vec![vec![2.0]]);
    let z2 = ConcreteZonotope::new(vec![3.0], vec![vec![4.0]]);
    let sum = z1.minkowski_add(&z2);
    assert!(approx_eq(sum.center[0], 4.0)); // 1+3
    assert_eq!(sum.num_generators(), 2);
    assert!(approx_eq(sum.generators[0][0], 2.0));
    assert!(approx_eq(sum.generators[1][0], 4.0));
}

#[test]
fn test_minkowski_add_hulls_additive() {
    // hull(Z1+Z2) should equal hull(Z1) + hull(Z2) in the Minkowski sense:
    // [lo1+lo2, hi1+hi2]
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![3.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![5.0]]);
    let sum = z1.minkowski_add(&z2);

    let (lo1, hi1) = z1.to_interval();
    let (lo2, hi2) = z2.to_interval();
    let (lo_sum, hi_sum) = sum.to_interval();

    assert!(approx_eq(lo_sum[0], lo1[0] + lo2[0]));
    assert!(approx_eq(hi_sum[0], hi1[0] + hi2[0]));
}

#[test]
fn test_minkowski_add_2d() {
    let z1 = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0]]);
    let z2 = ConcreteZonotope::new(vec![3.0, 4.0], vec![vec![0.0, 1.0]]);
    let sum = z1.minkowski_add(&z2);
    assert!(approx_eq(sum.center[0], 4.0));
    assert!(approx_eq(sum.center[1], 6.0));
    assert_eq!(sum.num_generators(), 2);
}

#[test]
fn test_minkowski_add_hull_additive_2d() {
    let z1 = ConcreteZonotope::new(vec![1.0, 0.0], vec![vec![2.0, 1.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0, 3.0], vec![vec![1.0, 4.0]]);
    let sum = z1.minkowski_add(&z2);

    let (lo1, hi1) = z1.to_interval();
    let (lo2, hi2) = z2.to_interval();
    let (lo_s, hi_s) = sum.to_interval();

    for j in 0..2 {
        assert!(
            approx_eq(lo_s[j], lo1[j] + lo2[j]),
            "dim {j}: lo_sum={} != lo1+lo2={}",
            lo_s[j],
            lo1[j] + lo2[j]
        );
        assert!(
            approx_eq(hi_s[j], hi1[j] + hi2[j]),
            "dim {j}: hi_sum={} != hi1+hi2={}",
            hi_s[j],
            hi1[j] + hi2[j]
        );
    }
}

// ---------------------------------------------------------------------------
// Hull soundness (T01)
// ---------------------------------------------------------------------------

#[test]
fn test_hull_soundness_interior_points() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    // All zonotope interior points should satisfy hull soundness
    assert!(z.verify_hull_sound(&[0.0, 0.0]));
    assert!(z.verify_hull_sound(&[1.0, 1.0]));
    assert!(z.verify_hull_sound(&[-1.0, -1.0]));
}

#[test]
fn test_hull_soundness_exterior_points_vacuous() {
    // Points outside the zonotope: implication is vacuously true
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    assert!(z.verify_hull_sound(&[5.0]));
    assert!(z.verify_hull_sound(&[-5.0]));
}

#[test]
fn test_hull_soundness_random_coefficients() {
    // Sample 100 random coefficient vectors, verify T01
    let z = ConcreteZonotope::new(
        vec![1.0, 2.0, 3.0],
        vec![
            vec![1.0, 0.0, -1.0],
            vec![0.0, 2.0, 1.0],
            vec![-1.0, 1.0, 0.5],
        ],
    );

    // Use a simple LCG for deterministic "random" coefficients
    let mut seed: u64 = 42;
    for _ in 0..100 {
        // Generate eps_i in [-1, 1] for each generator
        let mut point = z.center.clone();
        for gvec in &z.generators {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            let eps = ((seed >> 33) as f64 / (u32::MAX as f64)) * 2.0 - 1.0;
            for (j, g) in gvec.iter().enumerate() {
                point[j] += eps * g;
            }
        }
        assert!(
            z.verify_hull_sound(&point),
            "hull soundness failed for random point {:?}",
            point
        );
    }
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_zero_generators_containment() {
    let z = ConcreteZonotope::new(vec![3.0, 4.0], vec![]);
    assert!(z.contains(&[3.0, 4.0]));
    assert!(!z.contains(&[3.0, 4.1]));
}

#[test]
fn test_zero_generators_hull() {
    let z = ConcreteZonotope::new(vec![7.0], vec![]);
    let (lo, hi) = z.to_interval();
    assert!(approx_eq(lo[0], 7.0));
    assert!(approx_eq(hi[0], 7.0));
}

#[test]
fn test_single_generator() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 2.0]]);
    // This is a line segment from (-1, -2) to (1, 2)
    let (lo, hi) = z.to_interval();
    assert!(approx_eq(lo[0], -1.0));
    assert!(approx_eq(hi[0], 1.0));
    assert!(approx_eq(lo[1], -2.0));
    assert!(approx_eq(hi[1], 2.0));
    assert!(z.contains(&[0.0, 0.0]));
    assert!(z.contains(&[1.0, 2.0]));
    assert!(z.contains(&[-1.0, -2.0]));
    assert!(z.contains(&[0.5, 1.0]));
}

#[test]
fn test_zero_width_dimension() {
    // Generator has zero in one dimension -> hull is a point in that dim
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![3.0, 0.0]]);
    let (lo, hi) = z.to_interval();
    assert!(approx_eq(lo[0], -2.0));
    assert!(approx_eq(hi[0], 4.0));
    assert!(approx_eq(lo[1], 2.0)); // zero width
    assert!(approx_eq(hi[1], 2.0)); // zero width
}

#[test]
fn test_compress_zero_generators() {
    let z = ConcreteZonotope::new(vec![1.0], vec![]);
    let compressed = z.compress(&[]);
    assert_eq!(compressed.num_generators(), 0);
    assert!(approx_eq(compressed.center[0], 1.0));
}

#[test]
fn test_minkowski_add_zero_generators() {
    let z1 = ConcreteZonotope::new(vec![1.0], vec![]);
    let z2 = ConcreteZonotope::new(vec![2.0], vec![vec![3.0]]);
    let sum = z1.minkowski_add(&z2);
    assert!(approx_eq(sum.center[0], 3.0));
    assert_eq!(sum.num_generators(), 1);
}

#[test]
fn test_linear_transform_zero_generators() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![]);
    let w: Vec<&[f64]> = vec![&[2.0, 0.0], &[0.0, 3.0]];
    let bias = vec![1.0, 1.0];
    let result = z.linear_transform(&w, &bias);
    assert!(approx_eq(result.center[0], 3.0)); // 2*1 + 0*2 + 1
    assert!(approx_eq(result.center[1], 7.0)); // 0*1 + 3*2 + 1
    assert_eq!(result.num_generators(), 0);
}

// ---------------------------------------------------------------------------
// Composition: transform then compress
// ---------------------------------------------------------------------------

#[test]
fn test_transform_then_compress_hull_exact() {
    // Apply a linear transform, then compress, verify T12
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.5, 0.5]],
    );
    let w: Vec<&[f64]> = vec![&[2.0, 0.0], &[0.0, 1.0]];
    let bias = vec![0.0, 0.0];
    let transformed = z.linear_transform(&w, &bias);
    // After transform: center=(0,0), gens=[(2,0),(0,1),(1,0.5)]
    assert!(transformed.verify_compress_hull_exact(&[0]));
    assert!(transformed.verify_compress_hull_exact(&[1]));
    assert!(transformed.verify_compress_hull_exact(&[0, 2]));
}

#[test]
fn test_minkowski_then_compress_hull_exact() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0], vec![2.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![3.0]]);
    let sum = z1.minkowski_add(&z2);
    // sum has 3 generators: [1], [2], [3]
    assert!(sum.verify_compress_hull_exact(&[0]));
    assert!(sum.verify_compress_hull_exact(&[2]));
    assert!(sum.verify_compress_hull_exact(&[]));
}

// ===========================================================================
// New API tests: try_new, contains_point, sample_point, minkowski_sum,
// ZonotopeError, and verify module functions.
// ===========================================================================

use super::concrete::ZonotopeError;
use super::verify::{verify_hull_soundness, verify_linear_transform, verify_minkowski_sum};

// ---------------------------------------------------------------------------
// try_new (checked constructor)
// ---------------------------------------------------------------------------

#[test]
fn test_try_new_valid_1d() {
    let z = ConcreteZonotope::try_new(vec![0.0], vec![vec![1.0]]).expect("valid 1D zonotope");
    assert_eq!(z.dim(), 1);
    assert_eq!(z.num_generators(), 1);
}

#[test]
fn test_try_new_valid_2d_two_generators() {
    let z = ConcreteZonotope::try_new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]])
        .expect("valid 2D zonotope");
    assert_eq!(z.dim(), 2);
    assert_eq!(z.num_generators(), 2);
}

#[test]
fn test_try_new_dimension_mismatch_first_gen() {
    let result = ConcreteZonotope::try_new(
        vec![0.0, 0.0],
        vec![vec![1.0]], // wrong dim
    );
    assert!(matches!(
        result,
        Err(ZonotopeError::DimensionMismatch {
            center_dim: 2,
            gen_index: 0,
            gen_dim: 1,
        })
    ));
}

#[test]
fn test_try_new_dimension_mismatch_second_gen() {
    let result = ConcreteZonotope::try_new(
        vec![0.0, 0.0],
        vec![vec![1.0, 0.0], vec![1.0]], // second gen wrong
    );
    assert!(matches!(
        result,
        Err(ZonotopeError::DimensionMismatch {
            center_dim: 2,
            gen_index: 1,
            gen_dim: 1,
        })
    ));
}

#[test]
fn test_try_new_empty_generators() {
    let z = ConcreteZonotope::try_new(vec![5.0], vec![])
        .expect("empty generators is valid (point zonotope)");
    assert_eq!(z.num_generators(), 0);
}

// ---------------------------------------------------------------------------
// contains_point (hull-based, dimension-safe)
// ---------------------------------------------------------------------------

#[test]
fn test_contains_point_center() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    assert!(z.contains_point(&[1.0, 2.0]));
}

#[test]
fn test_contains_point_boundary() {
    // center=0, gen=[1] => hull = [-1, 1]
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    assert!(z.contains_point(&[1.0]));
    assert!(z.contains_point(&[-1.0]));
}

#[test]
fn test_contains_point_outside() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    assert!(!z.contains_point(&[1.5]));
    assert!(!z.contains_point(&[-1.5]));
}

#[test]
fn test_contains_point_wrong_dim_returns_false() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0]]);
    assert!(!z.contains_point(&[0.0])); // too few
    assert!(!z.contains_point(&[0.0, 0.0, 0.0])); // too many
}

// ---------------------------------------------------------------------------
// sample_point
// ---------------------------------------------------------------------------

#[test]
fn test_sample_point_zero_coeffs_is_center() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let p = z.sample_point(&[0.0, 0.0]).expect("valid coeffs");
    assert!(approx_eq(p[0], 1.0));
    assert!(approx_eq(p[1], 2.0));
}

#[test]
fn test_sample_point_extreme_positive() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![3.0]]);
    let p = z.sample_point(&[1.0]).expect("valid");
    assert!(approx_eq(p[0], 3.0));
}

#[test]
fn test_sample_point_extreme_negative() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![3.0]]);
    let p = z.sample_point(&[-1.0]).expect("valid");
    assert!(approx_eq(p[0], -3.0));
}

#[test]
fn test_sample_point_wrong_coeff_count() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let result = z.sample_point(&[0.5, 0.5]);
    assert!(matches!(
        result,
        Err(ZonotopeError::InvalidCoefficients {
            expected: 1,
            got: 2,
        })
    ));
}

#[test]
fn test_sample_point_empty_generators() {
    let z = ConcreteZonotope::new(vec![7.0], vec![]);
    let p = z.sample_point(&[]).expect("valid empty coeffs");
    assert!(approx_eq(p[0], 7.0));
}

#[test]
fn test_sample_point_in_hull() {
    // Any point sampled with |e| <= 1 must be in the hull
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.5], vec![-0.5, 1.0]]);
    let p = z.sample_point(&[0.3, -0.7]).expect("valid");
    assert!(z.contains_point(&p));
}

// ---------------------------------------------------------------------------
// minkowski_sum (checked)
// ---------------------------------------------------------------------------

#[test]
fn test_minkowski_sum_valid() {
    let z1 = ConcreteZonotope::new(vec![1.0], vec![vec![2.0]]);
    let z2 = ConcreteZonotope::new(vec![3.0], vec![vec![4.0]]);
    let zs = z1.minkowski_sum(&z2).expect("valid");
    assert!(approx_eq(zs.center[0], 4.0));
    assert_eq!(zs.num_generators(), 2);
}

#[test]
fn test_minkowski_sum_dimension_mismatch() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0]]);
    let result = z1.minkowski_sum(&z2);
    assert!(matches!(
        result,
        Err(ZonotopeError::OperandDimensionMismatch {
            left_dim: 1,
            right_dim: 2,
        })
    ));
}

// ---------------------------------------------------------------------------
// ZonotopeError display
// ---------------------------------------------------------------------------

#[test]
fn test_error_display_dimension_mismatch() {
    let e = ZonotopeError::DimensionMismatch {
        center_dim: 3,
        gen_index: 1,
        gen_dim: 2,
    };
    let msg = e.to_string();
    assert!(msg.contains("dimension mismatch"), "got: {msg}");
    assert!(msg.contains("3"), "got: {msg}");
    assert!(msg.contains("2"), "got: {msg}");
}

#[test]
fn test_error_display_invalid_coefficients() {
    let e = ZonotopeError::InvalidCoefficients {
        expected: 5,
        got: 3,
    };
    let msg = e.to_string();
    assert!(msg.contains("invalid coefficients"), "got: {msg}");
}

#[test]
fn test_error_display_operand_mismatch() {
    let e = ZonotopeError::OperandDimensionMismatch {
        left_dim: 2,
        right_dim: 3,
    };
    let msg = e.to_string();
    assert!(msg.contains("operand dimension mismatch"), "got: {msg}");
}

// ---------------------------------------------------------------------------
// verify module: hull soundness (T01)
// ---------------------------------------------------------------------------

#[test]
fn test_verify_hull_soundness_1d() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![5.0]]);
    assert!(verify_hull_soundness(&z, 1000));
}

#[test]
fn test_verify_hull_soundness_2d() {
    let z = ConcreteZonotope::new(vec![1.0, -1.0], vec![vec![2.0, 0.5], vec![-1.0, 3.0]]);
    assert!(verify_hull_soundness(&z, 1000));
}

#[test]
fn test_verify_hull_soundness_3d_four_generators() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0, 0.0],
        vec![
            vec![1.0, 0.0, 0.0],
            vec![0.0, 1.0, 0.0],
            vec![0.0, 0.0, 1.0],
            vec![0.5, 0.5, 0.5],
        ],
    );
    assert!(verify_hull_soundness(&z, 1000));
}

#[test]
fn test_verify_hull_soundness_point_zonotope() {
    let z = ConcreteZonotope::new(vec![42.0], vec![]);
    assert!(verify_hull_soundness(&z, 100));
}

// ---------------------------------------------------------------------------
// verify module: linear transform (T02)
// ---------------------------------------------------------------------------

#[test]
fn test_verify_linear_transform_identity() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let w: Vec<&[f64]> = vec![&[1.0, 0.0], &[0.0, 1.0]];
    let b = vec![0.0, 0.0];
    assert!(verify_linear_transform(&z, &w, &b, 500));
}

#[test]
fn test_verify_linear_transform_scaling_with_bias() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let w: Vec<&[f64]> = vec![&[3.0]];
    let b = vec![1.0];
    assert!(verify_linear_transform(&z, &w, &b, 500));
}

#[test]
fn test_verify_linear_transform_projection() {
    let z = ConcreteZonotope::new(
        vec![1.0, 2.0, 3.0],
        vec![vec![1.0, 0.0, 0.0], vec![0.0, 1.0, 0.0]],
    );
    let w: Vec<&[f64]> = vec![&[1.0, 0.0, 0.0]];
    let b = vec![0.0];
    assert!(verify_linear_transform(&z, &w, &b, 500));
}

// ---------------------------------------------------------------------------
// verify module: Minkowski sum (T08)
// ---------------------------------------------------------------------------

#[test]
fn test_verify_minkowski_sum_1d() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![2.0]]);
    assert!(verify_minkowski_sum(&z1, &z2, 500));
}

#[test]
fn test_verify_minkowski_sum_2d() {
    let z1 = ConcreteZonotope::new(vec![1.0, 0.0], vec![vec![1.0, 0.0], vec![0.5, 0.5]]);
    let z2 = ConcreteZonotope::new(vec![0.0, 1.0], vec![vec![0.0, 1.0]]);
    assert!(verify_minkowski_sum(&z1, &z2, 500));
}
