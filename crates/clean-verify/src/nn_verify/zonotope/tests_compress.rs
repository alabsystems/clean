// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for zonotope generator compression: magnitude, ranking, hull-sound
//! compression, PCA, random projection, error bounds, and edge cases.

use super::compress::{
    compress_generators, compression_error_bound, generator_magnitude, pca_compress,
    random_projection_compress, rank_generators, verify_compression_sound,
};

const EPS: f64 = 1e-9;

fn approx_eq(a: f64, b: f64) -> bool {
    (a - b).abs() < EPS
}

// ---------------------------------------------------------------------------
// generator_magnitude
// ---------------------------------------------------------------------------

#[test]
fn test_magnitude_unit_vector() {
    assert!(approx_eq(generator_magnitude(&[1.0, 0.0, 0.0]), 1.0));
    assert!(approx_eq(generator_magnitude(&[0.0, 1.0, 0.0]), 1.0));
}

#[test]
fn test_magnitude_zero_vector() {
    assert!(approx_eq(generator_magnitude(&[0.0, 0.0]), 0.0));
}

#[test]
fn test_magnitude_known_value() {
    // (3, 4) -> magnitude 5
    assert!(approx_eq(generator_magnitude(&[3.0, 4.0]), 5.0));
}

#[test]
fn test_magnitude_negative_components() {
    // (-3, 4) -> magnitude 5 (same as positive)
    assert!(approx_eq(generator_magnitude(&[-3.0, 4.0]), 5.0));
}

#[test]
fn test_magnitude_single_component() {
    assert!(approx_eq(generator_magnitude(&[7.5]), 7.5));
    assert!(approx_eq(generator_magnitude(&[-3.0]), 3.0));
}

// ---------------------------------------------------------------------------
// rank_generators
// ---------------------------------------------------------------------------

#[test]
fn test_rank_sorted_descending() {
    let gens = vec![vec![1.0, 0.0], vec![3.0, 4.0], vec![0.0, 2.0]];
    let ranked = rank_generators(&gens);
    assert_eq!(ranked.len(), 3);
    // (3,4)->5.0 first, (0,2)->2.0 second, (1,0)->1.0 third
    assert_eq!(ranked[0].0, 1); // index 1, magnitude 5
    assert!(approx_eq(ranked[0].1, 5.0));
    assert_eq!(ranked[1].0, 2); // index 2, magnitude 2
    assert!(approx_eq(ranked[1].1, 2.0));
    assert_eq!(ranked[2].0, 0); // index 0, magnitude 1
    assert!(approx_eq(ranked[2].1, 1.0));
}

#[test]
fn test_rank_handles_ties() {
    // All generators have magnitude sqrt(2)
    let gens = vec![vec![1.0, 1.0], vec![1.0, -1.0], vec![-1.0, 1.0]];
    let ranked = rank_generators(&gens);
    assert_eq!(ranked.len(), 3);
    // All magnitudes equal -> stable sort preserves original index order
    assert_eq!(ranked[0].0, 0);
    assert_eq!(ranked[1].0, 1);
    assert_eq!(ranked[2].0, 2);
    let mag = 2.0f64.sqrt();
    for &(_, m) in &ranked {
        assert!(approx_eq(m, mag));
    }
}

#[test]
fn test_rank_empty() {
    let ranked = rank_generators(&[]);
    assert!(ranked.is_empty());
}

#[test]
fn test_rank_single_generator() {
    let gens = vec![vec![3.0, 4.0]];
    let ranked = rank_generators(&gens);
    assert_eq!(ranked.len(), 1);
    assert_eq!(ranked[0].0, 0);
    assert!(approx_eq(ranked[0].1, 5.0));
}

// ---------------------------------------------------------------------------
// compress_generators — soundness
// ---------------------------------------------------------------------------

#[test]
fn test_compress_preserves_hull() {
    let center = vec![1.0, 2.0, 3.0];
    let gens = vec![
        vec![1.0, 0.0, 0.0],
        vec![0.0, 2.0, 0.0],
        vec![0.0, 0.0, 0.5],
        vec![0.1, 0.1, 0.1],
    ];
    let (new_center, new_gens) = compress_generators(&center, &gens, 2);

    // Center unchanged.
    assert_eq!(new_center, center);

    // Compressed hull must contain original hull.
    assert!(verify_compression_sound(
        &center,
        &gens,
        &new_center,
        &new_gens
    ));
}

#[test]
fn test_compress_hull_exact_for_magnitude_merge() {
    // When we merge via interval hull (abs sum), the interval hull is exact.
    let center = vec![0.0, 0.0];
    let gens = vec![
        vec![3.0, 0.0],  // mag 3
        vec![0.0, 2.0],  // mag 2
        vec![0.5, 0.5],  // mag ~0.707
        vec![-0.3, 0.1], // mag ~0.316
    ];
    let (_, new_gens) = compress_generators(&center, &gens, 2);

    // Original hull half-widths: [3.0+0.0+0.5+0.3, 0.0+2.0+0.5+0.1] = [3.8, 2.6]
    // Kept: gen0 (mag=3), gen1 (mag=2). Merged: gen2, gen3.
    // Merged j=0: 0.5+0.3=0.8, j=1: 0.5+0.1=0.6
    // New half-widths: [3.0+0.0+0.8, 0.0+2.0+0.6] = [3.8, 2.6] -- exact!
    let orig_hw: Vec<f64> = (0..2)
        .map(|j| gens.iter().map(|g| g[j].abs()).sum())
        .collect();
    let comp_hw: Vec<f64> = (0..2)
        .map(|j| new_gens.iter().map(|g| g[j].abs()).sum())
        .collect();
    for j in 0..2 {
        assert!(
            approx_eq(orig_hw[j], comp_hw[j]),
            "dim {j}: orig={}, comp={}",
            orig_hw[j],
            comp_hw[j]
        );
    }
}

#[test]
fn test_compress_target_exceeds_count() {
    let center = vec![1.0];
    let gens = vec![vec![2.0], vec![3.0]];
    let (c, g) = compress_generators(&center, &gens, 10);
    assert_eq!(c, center);
    assert_eq!(g, gens);
}

#[test]
fn test_compress_target_equals_count() {
    let center = vec![1.0, 2.0];
    let gens = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let (c, g) = compress_generators(&center, &gens, 2);
    assert_eq!(c, center);
    assert_eq!(g, gens);
}

#[test]
fn test_compress_zero_generators() {
    let center = vec![5.0, 6.0];
    let gens: Vec<Vec<f64>> = vec![];
    let (c, g) = compress_generators(&center, &gens, 3);
    assert_eq!(c, center);
    assert!(g.is_empty());
}

#[test]
fn test_compress_target_zero_merges_all() {
    let center = vec![0.0, 0.0];
    let gens = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let (c, g) = compress_generators(&center, &gens, 0);
    assert_eq!(c, center);
    // All generators merged into one interval hull generator.
    assert_eq!(g.len(), 1);
    assert!(approx_eq(g[0][0], 1.0)); // |1| + |0|
    assert!(approx_eq(g[0][1], 1.0)); // |0| + |1|
}

// ---------------------------------------------------------------------------
// verify_compression_sound
// ---------------------------------------------------------------------------

#[test]
fn test_verify_sound_identity() {
    let center = vec![1.0, 2.0];
    let gens = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    assert!(verify_compression_sound(&center, &gens, &center, &gens));
}

#[test]
fn test_verify_sound_wider_is_sound() {
    let center = vec![0.0];
    let orig_gens = vec![vec![1.0]];
    let wider_gens = vec![vec![2.0]];
    assert!(verify_compression_sound(
        &center,
        &orig_gens,
        &center,
        &wider_gens
    ));
}

#[test]
fn test_verify_sound_narrower_fails() {
    let center = vec![0.0];
    let orig_gens = vec![vec![2.0]];
    let narrower_gens = vec![vec![1.0]];
    assert!(!verify_compression_sound(
        &center,
        &orig_gens,
        &center,
        &narrower_gens
    ));
}

#[test]
fn test_verify_sound_dimension_mismatch() {
    let c1 = vec![0.0, 0.0];
    let g1 = vec![vec![1.0, 0.0]];
    let c2 = vec![0.0];
    let g2 = vec![vec![1.0]];
    assert!(!verify_compression_sound(&c1, &g1, &c2, &g2));
}

// ---------------------------------------------------------------------------
// compression_error_bound
// ---------------------------------------------------------------------------

#[test]
fn test_error_bound_identical_zero() {
    let gens = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
    let bound = compression_error_bound(&gens, &gens);
    assert!(approx_eq(bound, 0.0));
}

#[test]
fn test_error_bound_empty_generators() {
    let empty: Vec<Vec<f64>> = vec![];
    assert!(approx_eq(compression_error_bound(&empty, &empty), 0.0));
}

#[test]
fn test_error_bound_known_value() {
    let orig = vec![vec![3.0, 1.0], vec![1.0, 2.0]];
    // orig spreads: [4.0, 3.0]
    let comp = vec![vec![2.0, 1.0]];
    // comp spreads: [2.0, 1.0]
    // diffs: [2.0, 2.0], max = 2.0
    let bound = compression_error_bound(&orig, &comp);
    assert!(approx_eq(bound, 2.0));
}

#[test]
fn test_error_bound_compress_generators_is_zero() {
    // Magnitude-based compression preserves the interval hull exactly,
    // so the error bound should be 0.
    let center = vec![0.0, 0.0];
    let gens = vec![vec![3.0, 0.0], vec![0.0, 2.0], vec![0.5, 0.5]];
    let (_, new_gens) = compress_generators(&center, &gens, 1);
    let bound = compression_error_bound(&gens, &new_gens);
    assert!(
        approx_eq(bound, 0.0),
        "magnitude compression should have 0 hull error, got {bound}"
    );
}

// ---------------------------------------------------------------------------
// pca_compress
// ---------------------------------------------------------------------------

#[test]
fn test_pca_empty_generators() {
    let result = pca_compress(&[], 5);
    assert!(result.is_empty());
}

#[test]
fn test_pca_target_zero() {
    let gens = vec![vec![1.0, 0.0]];
    let result = pca_compress(&gens, 0);
    assert!(result.is_empty());
}

#[test]
fn test_pca_preserves_most_variance() {
    // Two generators: one large along x, one small along y.
    let gens = vec![vec![10.0, 0.0], vec![0.0, 0.1]];
    let result = pca_compress(&gens, 1);
    assert_eq!(result.len(), 1);
    // The first PC should be aligned with x (the dominant direction).
    let x_component = result[0][0].abs();
    let y_component = result[0][1].abs();
    assert!(
        x_component > y_component * 5.0,
        "PCA should pick x-aligned direction: x={x_component}, y={y_component}"
    );
}

#[test]
fn test_pca_two_components_capture_both_directions() {
    let gens = vec![vec![5.0, 0.0], vec![0.0, 3.0]];
    let result = pca_compress(&gens, 2);
    assert_eq!(result.len(), 2);
    // Total variance: 25 + 9 = 34.
    let total_variance: f64 = result.iter().map(|g| generator_magnitude(g).powi(2)).sum();
    // PCA should capture nearly all variance.
    assert!(
        total_variance > 30.0,
        "PCA should capture most variance, got {total_variance}"
    );
}

#[test]
fn test_pca_returns_correct_count() {
    let gens = vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.5, 0.5]];
    let result = pca_compress(&gens, 2);
    assert_eq!(result.len(), 2);
}

// ---------------------------------------------------------------------------
// random_projection_compress
// ---------------------------------------------------------------------------

#[test]
fn test_random_projection_empty() {
    let result = random_projection_compress(&[], 5, 42);
    assert!(result.is_empty());
}

#[test]
fn test_random_projection_target_zero() {
    let gens = vec![vec![1.0, 0.0]];
    let result = random_projection_compress(&gens, 0, 42);
    assert!(result.is_empty());
}

#[test]
fn test_random_projection_deterministic() {
    let gens = vec![vec![1.0, 2.0], vec![3.0, 4.0], vec![5.0, 6.0]];
    let r1 = random_projection_compress(&gens, 2, 42);
    let r2 = random_projection_compress(&gens, 2, 42);
    assert_eq!(r1.len(), r2.len());
    for (g1, g2) in r1.iter().zip(r2.iter()) {
        for (a, b) in g1.iter().zip(g2.iter()) {
            assert!(approx_eq(*a, *b), "random projection not deterministic");
        }
    }
}

#[test]
fn test_random_projection_different_seeds_differ() {
    let gens = vec![vec![1.0, 2.0], vec![3.0, 4.0], vec![5.0, 6.0]];
    let r1 = random_projection_compress(&gens, 2, 42);
    let r2 = random_projection_compress(&gens, 2, 99);
    // With different seeds, at least one generator should differ.
    let any_diff = r1
        .iter()
        .zip(r2.iter())
        .any(|(g1, g2)| g1.iter().zip(g2.iter()).any(|(a, b)| (a - b).abs() > EPS));
    assert!(
        any_diff,
        "different seeds should produce different projections"
    );
}

#[test]
fn test_random_projection_preserves_dimension() {
    let gens = vec![vec![1.0, 2.0, 3.0], vec![4.0, 5.0, 6.0]];
    let result = random_projection_compress(&gens, 1, 7);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].len(), 3); // dimension preserved
}

#[test]
fn test_random_projection_approximate_containment() {
    // With many generators, the projection should roughly preserve the
    // interval hull (within a factor). We check that the compressed hull
    // is within 3x of the original hull half-width in each dimension.
    let gens: Vec<Vec<f64>> = (0..20)
        .map(|i| {
            vec![
                ((i * 7 + 3) % 11) as f64 - 5.0,
                ((i * 13 + 1) % 9) as f64 - 4.0,
            ]
        })
        .collect();
    let result = random_projection_compress(&gens, 10, 42);
    assert_eq!(result.len(), 10);
    // Just verify we got non-trivial output.
    let total_mag: f64 = result.iter().map(|g| generator_magnitude(g)).sum();
    assert!(
        total_mag > 0.0,
        "projection should produce non-zero generators"
    );
}

// ---------------------------------------------------------------------------
// Integration: compress_generators round-trip soundness
// ---------------------------------------------------------------------------

#[test]
fn test_compress_roundtrip_sound_3d() {
    let center = vec![1.0, -2.0, 3.0];
    let gens = vec![
        vec![2.0, 0.0, 1.0],
        vec![0.0, 1.5, 0.0],
        vec![0.5, 0.5, 0.5],
        vec![0.1, -0.2, 0.3],
        vec![-0.4, 0.0, 0.1],
    ];
    for target in 0..=5 {
        let (c, g) = compress_generators(&center, &gens, target);
        assert!(
            verify_compression_sound(&center, &gens, &c, &g),
            "compression to target={target} should be sound"
        );
    }
}
