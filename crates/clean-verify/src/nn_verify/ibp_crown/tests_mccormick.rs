// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for McCormick envelope relaxation (T50-T52).

use super::mccormick::*;

// ---------------------------------------------------------------------------
// mccormick_envelope: corner product correctness for various sign patterns
// ---------------------------------------------------------------------------

#[test]
fn test_mccormick_envelope_both_positive() {
    let b = mccormick_envelope(1.0, 3.0, 2.0, 4.0);
    // Corners: 1*2=2, 1*4=4, 3*2=6, 3*4=12
    assert!((b.lower - 2.0).abs() < 1e-10);
    assert!((b.upper - 12.0).abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_negative_x_positive_y() {
    let b = mccormick_envelope(-3.0, -1.0, 2.0, 4.0);
    // Corners: -3*2=-6, -3*4=-12, -1*2=-2, -1*4=-4
    assert!((b.lower - (-12.0)).abs() < 1e-10);
    assert!((b.upper - (-2.0)).abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_positive_x_negative_y() {
    let b = mccormick_envelope(1.0, 3.0, -4.0, -2.0);
    // Corners: 1*(-4)=-4, 1*(-2)=-2, 3*(-4)=-12, 3*(-2)=-6
    assert!((b.lower - (-12.0)).abs() < 1e-10);
    assert!((b.upper - (-2.0)).abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_both_negative() {
    let b = mccormick_envelope(-4.0, -1.0, -3.0, -2.0);
    // Corners: (-4)*(-3)=12, (-4)*(-2)=8, (-1)*(-3)=3, (-1)*(-2)=2
    assert!((b.lower - 2.0).abs() < 1e-10);
    assert!((b.upper - 12.0).abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_x_crossing_zero_positive_y() {
    let b = mccormick_envelope(-2.0, 3.0, 1.0, 4.0);
    // Corners: -2*1=-2, -2*4=-8, 3*1=3, 3*4=12
    assert!((b.lower - (-8.0)).abs() < 1e-10);
    assert!((b.upper - 12.0).abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_x_crossing_zero_negative_y() {
    let b = mccormick_envelope(-2.0, 3.0, -4.0, -1.0);
    // Corners: -2*(-4)=8, -2*(-1)=2, 3*(-4)=-12, 3*(-1)=-3
    assert!((b.lower - (-12.0)).abs() < 1e-10);
    assert!((b.upper - 8.0).abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_both_crossing_zero() {
    let b = mccormick_envelope(-2.0, 3.0, -1.0, 4.0);
    // Corners: (-2)*(-1)=2, (-2)*4=-8, 3*(-1)=-3, 3*4=12
    assert!((b.lower - (-8.0)).abs() < 1e-10);
    assert!((b.upper - 12.0).abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_y_crossing_zero_positive_x() {
    let b = mccormick_envelope(1.0, 5.0, -3.0, 2.0);
    // Corners: 1*(-3)=-3, 1*2=2, 5*(-3)=-15, 5*2=10
    assert!((b.lower - (-15.0)).abs() < 1e-10);
    assert!((b.upper - 10.0).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// Degenerate cases: point intervals, zero-width, zero intervals
// ---------------------------------------------------------------------------

#[test]
fn test_mccormick_envelope_point_interval_both() {
    let b = mccormick_envelope(2.0, 2.0, 3.0, 3.0);
    assert!((b.lower - 6.0).abs() < 1e-10);
    assert!((b.upper - 6.0).abs() < 1e-10);
    assert!(b.width().abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_point_interval_x_only() {
    let b = mccormick_envelope(4.0, 4.0, 1.0, 3.0);
    // Product is exactly [4*1, 4*3] = [4, 12]
    assert!((b.lower - 4.0).abs() < 1e-10);
    assert!((b.upper - 12.0).abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_point_interval_y_only() {
    let b = mccormick_envelope(-2.0, 5.0, 3.0, 3.0);
    // Product is [min(-6,15), max(-6,15)] = [-6, 15]
    assert!((b.lower - (-6.0)).abs() < 1e-10);
    assert!((b.upper - 15.0).abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_point_interval_negative() {
    let b = mccormick_envelope(-3.0, -3.0, -2.0, -2.0);
    assert!((b.lower - 6.0).abs() < 1e-10);
    assert!((b.upper - 6.0).abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_zero_point() {
    let b = mccormick_envelope(0.0, 0.0, 0.0, 0.0);
    assert!(b.lower.abs() < 1e-10);
    assert!(b.upper.abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_x_zero_interval() {
    let b = mccormick_envelope(0.0, 0.0, -100.0, 100.0);
    // 0 * anything = 0
    assert!(b.lower.abs() < 1e-10);
    assert!(b.upper.abs() < 1e-10);
}

#[test]
fn test_mccormick_envelope_y_zero_interval() {
    let b = mccormick_envelope(-100.0, 100.0, 0.0, 0.0);
    assert!(b.lower.abs() < 1e-10);
    assert!(b.upper.abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// Large and tiny intervals
// ---------------------------------------------------------------------------

#[test]
fn test_mccormick_envelope_large_intervals() {
    let b = mccormick_envelope(-1000.0, 1000.0, -500.0, 500.0);
    // Max product at corners: 1000*500=500_000, min: -500_000
    assert!((b.lower - (-500_000.0)).abs() < 1e-4);
    assert!((b.upper - 500_000.0).abs() < 1e-4);
}

#[test]
fn test_mccormick_envelope_tiny_intervals_near_zero() {
    let b = mccormick_envelope(-1e-10, 1e-10, -1e-10, 1e-10);
    // Products are +/-1e-20, very close to zero
    assert!(b.lower >= -1e-19);
    assert!(b.upper <= 1e-19);
}

#[test]
fn test_mccormick_envelope_asymmetric_tiny() {
    let b = mccormick_envelope(1e-8, 2e-8, 3e-8, 4e-8);
    let expected_lo = 1e-8 * 3e-8; // 3e-16
    let expected_hi = 2e-8 * 4e-8; // 8e-16
    assert!((b.lower - expected_lo).abs() < 1e-25);
    assert!((b.upper - expected_hi).abs() < 1e-25);
}

// ---------------------------------------------------------------------------
// Symmetry: mccormick(x,y) product bounds == mccormick(y,x) product bounds
// ---------------------------------------------------------------------------

#[test]
fn test_mccormick_symmetry_positive() {
    let b_xy = mccormick_envelope(1.0, 3.0, 2.0, 5.0);
    let b_yx = mccormick_envelope(2.0, 5.0, 1.0, 3.0);
    assert!((b_xy.lower - b_yx.lower).abs() < 1e-10);
    assert!((b_xy.upper - b_yx.upper).abs() < 1e-10);
}

#[test]
fn test_mccormick_symmetry_mixed_sign() {
    let b_xy = mccormick_envelope(-3.0, 2.0, -1.0, 4.0);
    let b_yx = mccormick_envelope(-1.0, 4.0, -3.0, 2.0);
    assert!((b_xy.lower - b_yx.lower).abs() < 1e-10);
    assert!((b_xy.upper - b_yx.upper).abs() < 1e-10);
}

#[test]
fn test_mccormick_symmetry_negative() {
    let b_xy = mccormick_envelope(-5.0, -1.0, -4.0, -2.0);
    let b_yx = mccormick_envelope(-4.0, -2.0, -5.0, -1.0);
    assert!((b_xy.lower - b_yx.lower).abs() < 1e-10);
    assert!((b_xy.upper - b_yx.upper).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// Corner product exhaustive verification
// ---------------------------------------------------------------------------

fn verify_all_corners(x_l: f64, x_u: f64, y_l: f64, y_u: f64) {
    let b = mccormick_envelope(x_l, x_u, y_l, y_u);
    let corners = [(x_l, y_l), (x_l, y_u), (x_u, y_l), (x_u, y_u)];
    for (x, y) in &corners {
        let product = x * y;
        assert!(
            product >= b.lower - 1e-10 && product <= b.upper + 1e-10,
            "corner ({x}, {y}) product {product} outside bounds [{}, {}]",
            b.lower,
            b.upper
        );
    }
}

#[test]
fn test_corner_exhaustive_positive() {
    verify_all_corners(1.0, 3.0, 2.0, 4.0);
}

#[test]
fn test_corner_exhaustive_negative() {
    verify_all_corners(-4.0, -1.0, -3.0, -2.0);
}

#[test]
fn test_corner_exhaustive_mixed() {
    verify_all_corners(-2.0, 3.0, -5.0, 4.0);
}

#[test]
fn test_corner_exhaustive_point() {
    verify_all_corners(7.0, 7.0, -3.0, -3.0);
}

#[test]
fn test_corner_exhaustive_zero_crossing() {
    verify_all_corners(-10.0, 10.0, -10.0, 10.0);
}

// ---------------------------------------------------------------------------
// Random sampling: product of random (x,y) within bounds
// ---------------------------------------------------------------------------

/// Simple deterministic pseudo-random for test reproducibility (xorshift32).
fn xorshift32(state: &mut u32) -> u32 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    x
}

fn random_f64_in_range(state: &mut u32, lo: f64, hi: f64) -> f64 {
    let r = (xorshift32(state) as f64) / (u32::MAX as f64);
    lo + r * (hi - lo)
}

#[test]
fn test_random_sampling_100_points_positive() {
    let b = mccormick_envelope(1.0, 10.0, 2.0, 8.0);
    let mut rng = 42u32;
    for _ in 0..100 {
        let x = random_f64_in_range(&mut rng, 1.0, 10.0);
        let y = random_f64_in_range(&mut rng, 2.0, 8.0);
        assert!(
            verify_mccormick_sound(x, y, &b),
            "soundness failed at x={x}, y={y}, product={}, bounds=[{}, {}]",
            x * y,
            b.lower,
            b.upper
        );
    }
}

#[test]
fn test_random_sampling_100_points_mixed_sign() {
    let b = mccormick_envelope(-5.0, 5.0, -3.0, 7.0);
    let mut rng = 1337u32;
    for _ in 0..100 {
        let x = random_f64_in_range(&mut rng, -5.0, 5.0);
        let y = random_f64_in_range(&mut rng, -3.0, 7.0);
        assert!(
            verify_mccormick_sound(x, y, &b),
            "soundness failed at x={x}, y={y}, product={}, bounds=[{}, {}]",
            x * y,
            b.lower,
            b.upper
        );
    }
}

#[test]
fn test_random_sampling_100_points_both_negative() {
    let b = mccormick_envelope(-10.0, -1.0, -8.0, -2.0);
    let mut rng = 9999u32;
    for _ in 0..100 {
        let x = random_f64_in_range(&mut rng, -10.0, -1.0);
        let y = random_f64_in_range(&mut rng, -8.0, -2.0);
        assert!(
            verify_mccormick_sound(x, y, &b),
            "soundness failed at x={x}, y={y}, product={}, bounds=[{}, {}]",
            x * y,
            b.lower,
            b.upper
        );
    }
}

// ---------------------------------------------------------------------------
// Parameterized representative intervals
// ---------------------------------------------------------------------------

fn check_interval_pair(x_l: f64, x_u: f64, y_l: f64, y_u: f64) {
    let b = mccormick_envelope(x_l, x_u, y_l, y_u);
    // Lower bound must not exceed upper bound
    assert!(
        b.lower <= b.upper + 1e-10,
        "lower {lo} > upper {hi} for x=[{x_l},{x_u}], y=[{y_l},{y_u}]",
        lo = b.lower,
        hi = b.upper,
    );
    // All corners must be within bounds
    verify_all_corners(x_l, x_u, y_l, y_u);
    // Product interval agrees
    let (pi_lo, pi_hi) = mccormick_product_interval((x_l, x_u), (y_l, y_u));
    assert!((pi_lo - b.lower).abs() < 1e-10);
    assert!((pi_hi - b.upper).abs() < 1e-10);
}

#[test]
fn test_parameterized_representative_intervals() {
    // Both positive
    check_interval_pair(0.5, 1.5, 0.5, 1.5);
    // Both negative
    check_interval_pair(-1.5, -0.5, -1.5, -0.5);
    // Mixed: x negative, y positive
    check_interval_pair(-3.0, -0.1, 0.1, 3.0);
    // Mixed: x positive, y negative
    check_interval_pair(0.1, 3.0, -3.0, -0.1);
    // Both crossing zero
    check_interval_pair(-1.0, 1.0, -1.0, 1.0);
    // Asymmetric crossing
    check_interval_pair(-0.5, 10.0, -20.0, 0.5);
    // Wide x, narrow y
    check_interval_pair(-100.0, 100.0, 0.99, 1.01);
    // Narrow x, wide y
    check_interval_pair(0.99, 1.01, -100.0, 100.0);
}

// ---------------------------------------------------------------------------
// verify_mccormick_sound: edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_verify_sound_interior_point() {
    let b = mccormick_envelope(1.0, 3.0, 2.0, 4.0);
    assert!(verify_mccormick_sound(2.0, 3.0, &b));
}

#[test]
fn test_verify_sound_all_four_corners() {
    let b = mccormick_envelope(-2.0, 3.0, -1.0, 4.0);
    assert!(verify_mccormick_sound(-2.0, -1.0, &b));
    assert!(verify_mccormick_sound(-2.0, 4.0, &b));
    assert!(verify_mccormick_sound(3.0, -1.0, &b));
    assert!(verify_mccormick_sound(3.0, 4.0, &b));
}

#[test]
fn test_verify_sound_x_out_of_range() {
    let b = mccormick_envelope(1.0, 3.0, 2.0, 4.0);
    assert!(!verify_mccormick_sound(5.0, 3.0, &b));
}

#[test]
fn test_verify_sound_y_out_of_range() {
    let b = mccormick_envelope(1.0, 3.0, 2.0, 4.0);
    assert!(!verify_mccormick_sound(2.0, 6.0, &b));
}

#[test]
fn test_verify_sound_both_out_of_range() {
    let b = mccormick_envelope(1.0, 3.0, 2.0, 4.0);
    assert!(!verify_mccormick_sound(0.0, 0.0, &b));
}

#[test]
fn test_verify_sound_boundary_edge_midpoints() {
    let b = mccormick_envelope(0.0, 4.0, 0.0, 4.0);
    // Midpoint of edges
    assert!(verify_mccormick_sound(0.0, 2.0, &b)); // left edge
    assert!(verify_mccormick_sound(4.0, 2.0, &b)); // right edge
    assert!(verify_mccormick_sound(2.0, 0.0, &b)); // bottom edge
    assert!(verify_mccormick_sound(2.0, 4.0, &b)); // top edge
}

// ---------------------------------------------------------------------------
// Grid-based sampling for a large box
// ---------------------------------------------------------------------------

#[test]
fn test_verify_sound_grid_sampling() {
    let b = mccormick_envelope(-5.0, 5.0, -3.0, 7.0);
    let n = 50;
    for i in 0..=n {
        for j in 0..=n {
            let x = -5.0 + 10.0 * (i as f64 / n as f64);
            let y = -3.0 + 10.0 * (j as f64 / n as f64);
            assert!(
                verify_mccormick_sound(x, y, &b),
                "soundness violated at x={x}, y={y}, product={}, bounds=[{}, {}]",
                x * y,
                b.lower,
                b.upper
            );
        }
    }
}

// ---------------------------------------------------------------------------
// mccormick_product_interval
// ---------------------------------------------------------------------------

#[test]
fn test_product_interval_positive() {
    let (lo, hi) = mccormick_product_interval((1.0, 3.0), (2.0, 4.0));
    assert!((lo - 2.0).abs() < 1e-10);
    assert!((hi - 12.0).abs() < 1e-10);
}

#[test]
fn test_product_interval_crossing() {
    let (lo, hi) = mccormick_product_interval((-1.0, 1.0), (-1.0, 1.0));
    assert!((lo - (-1.0)).abs() < 1e-10);
    assert!((hi - 1.0).abs() < 1e-10);
}

#[test]
fn test_product_interval_agrees_with_envelope() {
    let b = mccormick_envelope(-3.0, 2.0, -4.0, 5.0);
    let (lo, hi) = mccormick_product_interval((-3.0, 2.0), (-4.0, 5.0));
    assert!((lo - b.lower).abs() < 1e-10);
    assert!((hi - b.upper).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// BilinearBounds stored metadata
// ---------------------------------------------------------------------------

#[test]
fn test_bilinear_bounds_stores_input_ranges() {
    let b = mccormick_envelope(1.0, 5.0, -2.0, 3.0);
    assert!((b.x_lower - 1.0).abs() < 1e-10);
    assert!((b.x_upper - 5.0).abs() < 1e-10);
    assert!((b.y_lower - (-2.0)).abs() < 1e-10);
    assert!((b.y_upper - 3.0).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// Tightness: bounds are achieved at corners
// ---------------------------------------------------------------------------

#[test]
fn test_mccormick_tightness_lower_achieved() {
    let b = mccormick_envelope(-2.0, 3.0, -1.0, 4.0);
    let corners = [(-2.0f64) * (-1.0), (-2.0) * 4.0, -3.0, 3.0 * 4.0];
    let min_corner = corners.iter().copied().fold(f64::INFINITY, f64::min);
    assert!(
        (b.lower - min_corner).abs() < 1e-10,
        "lower bound must be achieved at a corner"
    );
}

#[test]
fn test_mccormick_tightness_upper_achieved() {
    let b = mccormick_envelope(-2.0, 3.0, -1.0, 4.0);
    let corners = [(-2.0f64) * (-1.0), (-2.0) * 4.0, -3.0, 3.0 * 4.0];
    let max_corner = corners.iter().copied().fold(f64::NEG_INFINITY, f64::max);
    assert!(
        (b.upper - max_corner).abs() < 1e-10,
        "upper bound must be achieved at a corner"
    );
}

// ---------------------------------------------------------------------------
// Width monotonicity: wider input intervals produce wider product intervals
// ---------------------------------------------------------------------------

#[test]
fn test_width_monotonicity_widening_x() {
    let b_narrow = mccormick_envelope(1.0, 2.0, 1.0, 3.0);
    let b_wide = mccormick_envelope(0.0, 3.0, 1.0, 3.0);
    assert!(
        b_wide.width() >= b_narrow.width() - 1e-10,
        "wider x should produce wider or equal product interval"
    );
}

#[test]
fn test_width_monotonicity_widening_y() {
    let b_narrow = mccormick_envelope(1.0, 3.0, 1.0, 2.0);
    let b_wide = mccormick_envelope(1.0, 3.0, 0.0, 3.0);
    assert!(
        b_wide.width() >= b_narrow.width() - 1e-10,
        "wider y should produce wider or equal product interval"
    );
}

// ---------------------------------------------------------------------------
// Containment: superset input intervals produce superset product bounds
// ---------------------------------------------------------------------------

#[test]
fn test_containment_superset_x() {
    let b_inner = mccormick_envelope(1.0, 2.0, 1.0, 3.0);
    let b_outer = mccormick_envelope(0.0, 3.0, 1.0, 3.0);
    assert!(b_outer.lower <= b_inner.lower + 1e-10);
    assert!(b_outer.upper >= b_inner.upper - 1e-10);
}

#[test]
fn test_containment_superset_both() {
    let b_inner = mccormick_envelope(-1.0, 1.0, -1.0, 1.0);
    let b_outer = mccormick_envelope(-2.0, 2.0, -2.0, 2.0);
    assert!(b_outer.lower <= b_inner.lower + 1e-10);
    assert!(b_outer.upper >= b_inner.upper - 1e-10);
}
