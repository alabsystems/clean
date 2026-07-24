// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Minkowski sum operations: core sum, containment verification,
//! overapproximation, generator reduction, Hausdorff bounds, interval hull,
//! residual connection soundness, generator count prediction, and scaling.

use super::concrete::ConcreteZonotope;
use super::minkowski::{
    generator_count_after_sum, minkowski_hausdorff_bound, minkowski_interval_hull,
    minkowski_overapprox, minkowski_scaling, minkowski_sum, minkowski_with_reduction,
    verify_minkowski_containment, verify_reduction_sound, verify_residual_sound,
    T08A_MINKOWSKI_SUM_SOUND, T08B_MINKOWSKI_REDUCTION_SOUND, T08C_RESIDUAL_CONTAINMENT,
};
use crate::spec::ProofStatus;

fn approx_eq(a: f64, b: f64) -> bool {
    (a - b).abs() < 1e-9
}

// ---------------------------------------------------------------------------
// Proof status constants
// ---------------------------------------------------------------------------

#[test]
fn test_proof_status_t08a() {
    assert!(matches!(
        T08A_MINKOWSKI_SUM_SOUND,
        ProofStatus::DerivedPending
    ));
}

#[test]
fn test_proof_status_t08b() {
    assert!(matches!(
        T08B_MINKOWSKI_REDUCTION_SOUND,
        ProofStatus::DerivedPending
    ));
}

#[test]
fn test_proof_status_t08c() {
    assert!(matches!(
        T08C_RESIDUAL_CONTAINMENT,
        ProofStatus::DerivedPending
    ));
}

// ---------------------------------------------------------------------------
// minkowski_sum
// ---------------------------------------------------------------------------

#[test]
fn test_minkowski_sum_basic_2d() {
    let z1 = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0]]);
    let z2 = ConcreteZonotope::new(vec![3.0, 4.0], vec![vec![0.0, 1.0]]);
    let sum = minkowski_sum(&z1, &z2).expect("same dimension");
    assert!(approx_eq(sum.center[0], 4.0));
    assert!(approx_eq(sum.center[1], 6.0));
    assert_eq!(sum.num_generators(), 2);
}

#[test]
fn test_minkowski_sum_generators_concatenated() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0], vec![2.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![3.0]]);
    let sum = minkowski_sum(&z1, &z2).expect("same dimension");
    assert_eq!(sum.num_generators(), 3);
    assert!(approx_eq(sum.generators[0][0], 1.0));
    assert!(approx_eq(sum.generators[1][0], 2.0));
    assert!(approx_eq(sum.generators[2][0], 3.0));
}

#[test]
fn test_minkowski_sum_dimension_mismatch() {
    let z1 = ConcreteZonotope::new(vec![1.0, 2.0], vec![]);
    let z2 = ConcreteZonotope::new(vec![1.0, 2.0, 3.0], vec![]);
    assert!(minkowski_sum(&z1, &z2).is_err());
}

#[test]
fn test_minkowski_sum_zero_generators() {
    let z1 = ConcreteZonotope::new(vec![1.0, 2.0], vec![]);
    let z2 = ConcreteZonotope::new(vec![3.0, 4.0], vec![]);
    let sum = minkowski_sum(&z1, &z2).expect("same dimension");
    assert!(approx_eq(sum.center[0], 4.0));
    assert!(approx_eq(sum.center[1], 6.0));
    assert_eq!(sum.num_generators(), 0);
}

#[test]
fn test_minkowski_sum_single_point_plus_zonotope() {
    // Single point (no generators) + zonotope = translated zonotope
    let point = ConcreteZonotope::new(vec![10.0, 20.0], vec![]);
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let sum = minkowski_sum(&point, &z).expect("same dimension");
    assert!(approx_eq(sum.center[0], 10.0));
    assert!(approx_eq(sum.center[1], 20.0));
    assert_eq!(sum.num_generators(), 2);
}

#[test]
fn test_minkowski_sum_1d() {
    // 1D: interval [-1, 3] + interval [2, 6] = interval [1, 9]
    let z1 = ConcreteZonotope::new(vec![1.0], vec![vec![2.0]]);
    let z2 = ConcreteZonotope::new(vec![4.0], vec![vec![2.0]]);
    let sum = minkowski_sum(&z1, &z2).expect("same dimension");
    let (lo, hi) = sum.to_interval();
    assert!(approx_eq(lo[0], 1.0));
    assert!(approx_eq(hi[0], 9.0));
}

// ---------------------------------------------------------------------------
// verify_minkowski_containment
// ---------------------------------------------------------------------------

#[test]
fn test_verify_containment_basic() {
    let z1 = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![0.5, 0.0], vec![0.0, 0.5]]);
    assert!(verify_minkowski_containment(&z1, &z2, 200));
}

#[test]
fn test_verify_containment_single_generator() {
    let z1 = ConcreteZonotope::new(vec![1.0], vec![vec![3.0]]);
    let z2 = ConcreteZonotope::new(vec![2.0], vec![vec![4.0]]);
    assert!(verify_minkowski_containment(&z1, &z2, 100));
}

#[test]
fn test_verify_containment_zero_generators() {
    let z1 = ConcreteZonotope::new(vec![5.0], vec![]);
    let z2 = ConcreteZonotope::new(vec![7.0], vec![]);
    assert!(verify_minkowski_containment(&z1, &z2, 10));
}

// ---------------------------------------------------------------------------
// minkowski_overapprox
// ---------------------------------------------------------------------------

#[test]
fn test_overapprox_basic() {
    let z1 = ConcreteZonotope::new(vec![1.0], vec![vec![2.0]]);
    let z2 = ConcreteZonotope::new(vec![3.0], vec![vec![4.0]]);
    let (lo, hi) = minkowski_overapprox(&z1, &z2).expect("same dim");
    // center=4, gen sum abs = 2+4=6 => [-2, 10]
    assert!(approx_eq(lo[0], -2.0));
    assert!(approx_eq(hi[0], 10.0));
}

#[test]
fn test_overapprox_dimension_mismatch() {
    let z1 = ConcreteZonotope::new(vec![1.0], vec![]);
    let z2 = ConcreteZonotope::new(vec![1.0, 2.0], vec![]);
    assert!(minkowski_overapprox(&z1, &z2).is_err());
}

// ---------------------------------------------------------------------------
// minkowski_with_reduction
// ---------------------------------------------------------------------------

#[test]
fn test_reduction_no_reduction_needed() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![2.0]]);
    // keep_count=2 >= total generators=2 => no reduction
    let reduced = minkowski_with_reduction(&z1, &z2, 2).expect("same dim");
    assert_eq!(reduced.num_generators(), 2);
}

#[test]
fn test_reduction_merges_small_generators() {
    let z1 = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![10.0, 0.0], vec![0.01, 0.01]]);
    let z2 = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![0.0, 10.0], vec![0.02, 0.02]]);
    // 4 generators total, keep 2 => 2 kept + 1 merged = 3
    let reduced = minkowski_with_reduction(&z1, &z2, 2).expect("same dim");
    assert!(reduced.num_generators() <= 3);
}

#[test]
fn test_reduction_hull_preserved() {
    let z1 = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![3.0, 0.0], vec![0.0, 1.0]]);
    let z2 = ConcreteZonotope::new(vec![4.0, 5.0], vec![vec![1.0, 0.0], vec![0.0, 2.0]]);
    let full_sum = z1.minkowski_add(&z2);
    let reduced = minkowski_with_reduction(&z1, &z2, 2).expect("same dim");
    // Compression preserves per-dim absolute sum => hull identical
    let (lo_f, hi_f) = full_sum.to_interval();
    let (lo_r, hi_r) = reduced.to_interval();
    for j in 0..2 {
        assert!(approx_eq(lo_f[j], lo_r[j]));
        assert!(approx_eq(hi_f[j], hi_r[j]));
    }
}

#[test]
fn test_reduction_dimension_mismatch() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![]);
    let z2 = ConcreteZonotope::new(vec![0.0, 0.0], vec![]);
    assert!(minkowski_with_reduction(&z1, &z2, 1).is_err());
}

// ---------------------------------------------------------------------------
// verify_reduction_sound
// ---------------------------------------------------------------------------

#[test]
fn test_verify_reduction_sound_identical() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    assert!(verify_reduction_sound(&z, &z));
}

#[test]
fn test_verify_reduction_sound_after_compress() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![3.0, 0.0], vec![0.0, 2.0], vec![0.1, 0.1]],
    );
    let compressed = z.compress(&[0, 1]);
    assert!(verify_reduction_sound(&z, &compressed));
}

#[test]
fn test_verify_reduction_sound_dim_mismatch_false() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![]);
    let z2 = ConcreteZonotope::new(vec![0.0, 0.0], vec![]);
    assert!(!verify_reduction_sound(&z1, &z2));
}

#[test]
fn test_verify_reduction_sound_smaller_hull_false() {
    // Reduced hull is strictly smaller => should fail
    let full = ConcreteZonotope::new(vec![0.0], vec![vec![5.0]]);
    let smaller = ConcreteZonotope::new(vec![0.0], vec![vec![3.0]]);
    assert!(!verify_reduction_sound(&full, &smaller));
}

// ---------------------------------------------------------------------------
// minkowski_hausdorff_bound
// ---------------------------------------------------------------------------

#[test]
fn test_hausdorff_no_reduction() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![2.0]]);
    assert!(approx_eq(minkowski_hausdorff_bound(&z1, &z2, 10), 0.0));
}

#[test]
fn test_hausdorff_remove_one() {
    // 2 generators: [3,0] (norm=3), [0,4] (norm=4). Keep 1 => remove [3,0]
    let z1 = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![3.0, 0.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![0.0, 4.0]]);
    let bound = minkowski_hausdorff_bound(&z1, &z2, 1);
    // Kept: [0,4] (norm=4). Removed: [3,0] (norm=3). Bound = 3.0.
    assert!(approx_eq(bound, 3.0));
}

#[test]
fn test_hausdorff_remove_all() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0], vec![2.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![3.0]]);
    let bound = minkowski_hausdorff_bound(&z1, &z2, 0);
    // Remove all 3 generators: norms 1, 2, 3. Sum = 6.
    assert!(approx_eq(bound, 6.0));
}

#[test]
fn test_hausdorff_zero_generators() {
    let z1 = ConcreteZonotope::new(vec![5.0], vec![]);
    let z2 = ConcreteZonotope::new(vec![7.0], vec![]);
    assert!(approx_eq(minkowski_hausdorff_bound(&z1, &z2, 0), 0.0));
}

// ---------------------------------------------------------------------------
// minkowski_interval_hull
// ---------------------------------------------------------------------------

#[test]
fn test_interval_hull_matches_overapprox() {
    let z1 = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0]]);
    let z2 = ConcreteZonotope::new(vec![3.0, 4.0], vec![vec![0.0, 1.0]]);
    let (lo1, hi1) = minkowski_interval_hull(&z1, &z2).expect("same dim");
    let (lo2, hi2) = minkowski_overapprox(&z1, &z2).expect("same dim");
    for j in 0..2 {
        assert!(approx_eq(lo1[j], lo2[j]));
        assert!(approx_eq(hi1[j], hi2[j]));
    }
}

#[test]
fn test_interval_hull_error_on_mismatch() {
    let z1 = ConcreteZonotope::new(vec![0.0; 3], vec![]);
    let z2 = ConcreteZonotope::new(vec![0.0; 2], vec![]);
    assert!(minkowski_interval_hull(&z1, &z2).is_err());
}

// ---------------------------------------------------------------------------
// verify_residual_sound
// ---------------------------------------------------------------------------

#[test]
fn test_residual_basic() {
    let z_in = ConcreteZonotope::new(vec![1.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let z_branch = ConcreteZonotope::new(vec![0.5, 0.5], vec![vec![0.5, 0.0], vec![0.0, 0.5]]);
    assert!(verify_residual_sound(&z_in, &z_branch, 200));
}

#[test]
fn test_residual_identity_branch() {
    // f(x) = 0 (branch contributes nothing)
    let z_in = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let z_branch = ConcreteZonotope::new(vec![0.0, 0.0], vec![]);
    assert!(verify_residual_sound(&z_in, &z_branch, 50));
}

#[test]
fn test_residual_large_branch() {
    let z_in = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let z_branch = ConcreteZonotope::new(vec![0.0], vec![vec![100.0]]);
    assert!(verify_residual_sound(&z_in, &z_branch, 100));
}

// ---------------------------------------------------------------------------
// generator_count_after_sum
// ---------------------------------------------------------------------------

#[test]
fn test_generator_count_basic() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![vec![1.0], vec![2.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![vec![3.0]]);
    assert_eq!(generator_count_after_sum(&z1, &z2), 3);
}

#[test]
fn test_generator_count_both_empty() {
    let z1 = ConcreteZonotope::new(vec![0.0], vec![]);
    let z2 = ConcreteZonotope::new(vec![0.0], vec![]);
    assert_eq!(generator_count_after_sum(&z1, &z2), 0);
}

#[test]
fn test_generator_count_one_empty() {
    let z1 = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0, 0.0], vec![]);
    assert_eq!(generator_count_after_sum(&z1, &z2), 2);
    assert_eq!(generator_count_after_sum(&z2, &z1), 2);
}

#[test]
fn test_generator_count_matches_actual() {
    let z1 = ConcreteZonotope::new(vec![0.0; 3], vec![vec![1.0; 3]; 5]);
    let z2 = ConcreteZonotope::new(vec![0.0; 3], vec![vec![2.0; 3]; 7]);
    let predicted = generator_count_after_sum(&z1, &z2);
    let sum = z1.minkowski_add(&z2);
    assert_eq!(predicted, sum.num_generators());
}

// ---------------------------------------------------------------------------
// minkowski_scaling
// ---------------------------------------------------------------------------

#[test]
fn test_scaling_by_one() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![3.0, 0.0], vec![0.0, 4.0]]);
    let scaled = minkowski_scaling(&z, 1.0);
    assert!(approx_eq(scaled.center[0], 1.0));
    assert!(approx_eq(scaled.center[1], 2.0));
    assert!(approx_eq(scaled.generators[0][0], 3.0));
}

#[test]
fn test_scaling_by_zero() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![3.0, 0.0]]);
    let scaled = minkowski_scaling(&z, 0.0);
    assert!(approx_eq(scaled.center[0], 0.0));
    assert!(approx_eq(scaled.center[1], 0.0));
    assert!(approx_eq(scaled.generators[0][0], 0.0));
    assert!(approx_eq(scaled.generators[0][1], 0.0));
}

#[test]
fn test_scaling_by_two() {
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![3.0]]);
    let scaled = minkowski_scaling(&z, 2.0);
    assert!(approx_eq(scaled.center[0], 2.0));
    assert!(approx_eq(scaled.generators[0][0], 6.0));
}

#[test]
fn test_scaling_negative() {
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![2.0]]);
    let scaled = minkowski_scaling(&z, -1.0);
    assert!(approx_eq(scaled.center[0], -1.0));
    assert!(approx_eq(scaled.generators[0][0], -2.0));
    // Interval of original: [-1, 3]. Interval of scaled: [-3, 1].
    let (lo, hi) = scaled.to_interval();
    assert!(approx_eq(lo[0], -3.0));
    assert!(approx_eq(hi[0], 1.0));
}

// ---------------------------------------------------------------------------
// Combined / integration tests
// ---------------------------------------------------------------------------

#[test]
fn test_sum_then_reduce_then_verify() {
    let z1 = ConcreteZonotope::new(
        vec![1.0, 2.0, 3.0],
        vec![
            vec![1.0, 0.0, 0.0],
            vec![0.0, 1.0, 0.0],
            vec![0.0, 0.0, 1.0],
        ],
    );
    let z2 = ConcreteZonotope::new(
        vec![4.0, 5.0, 6.0],
        vec![vec![0.5, 0.0, 0.0], vec![0.0, 0.5, 0.0]],
    );
    let full = minkowski_sum(&z1, &z2).expect("same dim");
    let reduced = minkowski_with_reduction(&z1, &z2, 3).expect("same dim");
    assert!(verify_reduction_sound(&full, &reduced));
    assert!(verify_minkowski_containment(&z1, &z2, 100));
}

#[test]
fn test_scaling_then_sum() {
    // 2 * Z1 + Z2 via scaling then Minkowski sum
    let z1 = ConcreteZonotope::new(vec![1.0, 0.0], vec![vec![1.0, 0.0]]);
    let z2 = ConcreteZonotope::new(vec![0.0, 1.0], vec![vec![0.0, 1.0]]);
    let scaled_z1 = minkowski_scaling(&z1, 2.0);
    let sum = minkowski_sum(&scaled_z1, &z2).expect("same dim");
    assert!(approx_eq(sum.center[0], 2.0));
    assert!(approx_eq(sum.center[1], 1.0));
    assert_eq!(sum.num_generators(), 2);
}

#[test]
fn test_sum_commutativity_hull() {
    // Z1 + Z2 and Z2 + Z1 should have the same interval hull
    let z1 = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![3.0, 1.0], vec![0.5, 2.0]]);
    let z2 = ConcreteZonotope::new(vec![4.0, 5.0], vec![vec![1.0, 0.0]]);
    let (lo12, hi12) = minkowski_overapprox(&z1, &z2).expect("same dim");
    let (lo21, hi21) = minkowski_overapprox(&z2, &z1).expect("same dim");
    for j in 0..2 {
        assert!(approx_eq(lo12[j], lo21[j]));
        assert!(approx_eq(hi12[j], hi21[j]));
    }
}

#[test]
fn test_sum_associativity_hull() {
    // (Z1 + Z2) + Z3 vs Z1 + (Z2 + Z3): same interval hull
    let z1 = ConcreteZonotope::new(vec![1.0], vec![vec![1.0]]);
    let z2 = ConcreteZonotope::new(vec![2.0], vec![vec![2.0]]);
    let z3 = ConcreteZonotope::new(vec![3.0], vec![vec![3.0]]);
    let sum12 = z1.minkowski_add(&z2);
    let lhs = sum12.minkowski_add(&z3);
    let sum23 = z2.minkowski_add(&z3);
    let rhs = z1.minkowski_add(&sum23);
    let (lo_l, hi_l) = lhs.to_interval();
    let (lo_r, hi_r) = rhs.to_interval();
    assert!(approx_eq(lo_l[0], lo_r[0]));
    assert!(approx_eq(hi_l[0], hi_r[0]));
}

#[test]
fn test_hausdorff_decreases_with_more_kept() {
    let z1 = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![5.0, 0.0], vec![0.0, 3.0], vec![1.0, 1.0]],
    );
    let z2 = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![0.0, 4.0], vec![2.0, 0.0]]);
    let h0 = minkowski_hausdorff_bound(&z1, &z2, 0);
    let h2 = minkowski_hausdorff_bound(&z1, &z2, 2);
    let h4 = minkowski_hausdorff_bound(&z1, &z2, 4);
    let h5 = minkowski_hausdorff_bound(&z1, &z2, 5);
    assert!(h0 >= h2);
    assert!(h2 >= h4);
    assert!(approx_eq(h5, 0.0));
}

#[test]
fn test_reduction_hull_contains_full_sum_hull() {
    let z1 = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.5, 0.5]],
    );
    let z2 = ConcreteZonotope::new(
        vec![0.0, 0.0],
        vec![vec![0.3, 0.0], vec![0.0, 0.3], vec![0.1, 0.1]],
    );
    let reduced = minkowski_with_reduction(&z1, &z2, 3).expect("same dim");
    let full = z1.minkowski_add(&z2);
    assert!(verify_reduction_sound(&full, &reduced));
}
