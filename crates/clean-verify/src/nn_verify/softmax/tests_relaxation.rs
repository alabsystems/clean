// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for softmax convex relaxation.
//!
//! Tests the full pipeline: LSE decomposition -> convex relaxation -> tightness
//! verification. Focuses on properties that span multiple sub-modules.

use super::convex_relaxation::{
    softmax_convex_relaxation, tightness_ratio, verify_o_range_tightness,
    verify_relaxation_soundness,
};
use super::lse::{log_sum_exp, softmax, softmax_via_lse, verify_lse_squeeze};

/// Tightness constant C for the O(range) bound.
/// The interval-arithmetic method gives C <= 1 for reasonable inputs.
const TIGHTNESS_BOUND: f64 = 1.0;
const EPS: f64 = 1e-10;

#[test]
fn test_softmax_lse_identity() {
    // Core identity: softmax(x)_i = exp(x_i - LSE(x))
    let x = vec![1.0, 3.0, 5.0, 2.0, 4.0];
    let s_direct = softmax(&x);
    let lse = log_sum_exp(&x);

    for (i, &xi) in x.iter().enumerate() {
        let s_from_lse = (xi - lse).exp();
        assert!(
            (s_direct[i] - s_from_lse).abs() < EPS,
            "softmax_via_lse identity failed at index {i}"
        );
    }
}

#[test]
fn test_relaxation_soundness_exhaustive_corners() {
    // Test all 2^3 = 8 corners of a 3D box
    let lower = vec![0.0, 1.0, 2.0];
    let upper = vec![1.0, 2.0, 3.0];
    let relax = softmax_convex_relaxation(&lower, &upper);

    for a in 0..2 {
        for b in 0..2 {
            for c in 0..2 {
                let x = vec![
                    if a == 0 { lower[0] } else { upper[0] },
                    if b == 0 { lower[1] } else { upper[1] },
                    if c == 0 { lower[2] } else { upper[2] },
                ];

                let violation = verify_relaxation_soundness(&x, &lower, &upper, &relax);
                assert!(
                    violation < EPS,
                    "soundness violated at corner ({a},{b},{c}): violation = {violation}"
                );
            }
        }
    }
}

#[test]
fn test_lse_squeeze_across_ranges() {
    // Verify LSE squeeze at different ranges
    let test_cases = vec![
        vec![0.0, 0.0, 0.0],       // range = 0
        vec![0.0, 1.0, 2.0],       // range = 2
        vec![-10.0, 0.0, 10.0],    // range = 20
        vec![100.0, 100.1, 100.2], // small range, large values
    ];

    for x in &test_cases {
        let (lower_gap, upper_gap) = verify_lse_squeeze(x);
        assert!(
            lower_gap >= -EPS,
            "LSE squeeze lower failed for {x:?}: gap = {lower_gap}"
        );
        assert!(
            upper_gap >= -EPS,
            "LSE squeeze upper failed for {x:?}: gap = {upper_gap}"
        );
    }
}

#[test]
fn test_tightness_scales_with_range() {
    // As range increases, gap should increase approximately linearly
    let base = vec![0.0, 0.0, 0.0];
    let mut prev_gap = 0.0;
    let mut prev_range = 0.0;

    for scale in [0.1, 0.5, 1.0, 2.0, 5.0] {
        let upper: Vec<f64> = base.iter().map(|&x| x + scale).collect();
        let relax = softmax_convex_relaxation(&base, &upper);

        if prev_range > 0.0 {
            // Gap should grow roughly proportionally to range
            let gap_ratio = relax.max_gap / prev_gap;
            let range_ratio = relax.input_range / prev_range;

            // Allow some nonlinearity but should be in the right ballpark
            // (within 5x of linear scaling)
            assert!(
                gap_ratio < range_ratio * 5.0,
                "gap scaling too fast: gap_ratio={gap_ratio}, range_ratio={range_ratio}"
            );
        }

        prev_gap = relax.max_gap.max(EPS);
        prev_range = relax.input_range;
    }
}

#[test]
fn test_o_range_tightness_property() {
    // The main theorem: gap / range is bounded by a constant
    let test_cases = vec![
        (vec![0.0, 0.0, 0.0], vec![1.0, 1.0, 1.0]),
        (vec![-1.0, 0.0, 1.0], vec![0.0, 1.0, 2.0]),
        (vec![0.0, 0.0], vec![3.0, 3.0]),
        (vec![-5.0, -5.0, -5.0, -5.0], vec![5.0, 5.0, 5.0, 5.0]),
    ];

    for (lower, upper) in &test_cases {
        let relax = softmax_convex_relaxation(lower, upper);
        let (is_tight, ratio) = verify_o_range_tightness(&relax, TIGHTNESS_BOUND);
        assert!(
            is_tight,
            "O(range) tightness failed for [{lower:?}, {upper:?}]: ratio = {ratio}"
        );
    }
}

#[test]
fn test_relaxation_sum_bounds_contain_one() {
    // Since softmax sums to 1, the interval [sum(lower), sum(upper)]
    // must contain 1.0
    let lower = vec![0.0, 1.0, 2.0, 3.0];
    let upper = vec![1.0, 2.0, 3.0, 4.0];
    let relax = softmax_convex_relaxation(&lower, &upper);

    let sum_lo: f64 = relax.lower.iter().sum();
    let sum_hi: f64 = relax.upper.iter().sum();

    assert!(
        sum_lo <= 1.0 + EPS,
        "sum of lower bounds must be <= 1: {sum_lo}"
    );
    assert!(
        sum_hi >= 1.0 - EPS,
        "sum of upper bounds must be >= 1: {sum_hi}"
    );
}

#[test]
fn test_softmax_via_lse_consistency() {
    // Verify that the two softmax implementations agree
    let inputs = vec![
        vec![0.0, 0.0, 0.0],
        vec![1.0, 2.0, 3.0],
        vec![-5.0, 0.0, 5.0],
        vec![100.0, 100.0],
    ];

    for x in &inputs {
        let s1 = softmax(x);
        let s2 = softmax_via_lse(x);

        for (a, b) in s1.iter().zip(s2.iter()) {
            assert!(
                (a - b).abs() < EPS,
                "softmax implementations disagree at {x:?}: {a} vs {b}"
            );
        }
    }
}

#[test]
fn test_relaxation_monotone_in_range() {
    // Gap should be non-decreasing as the box expands
    let center = [1.0, 2.0, 3.0];
    let mut prev_gap = 0.0;

    for eps in [0.0, 0.01, 0.1, 0.5, 1.0, 2.0] {
        let lower: Vec<f64> = center.iter().map(|&c| c - eps).collect();
        let upper: Vec<f64> = center.iter().map(|&c| c + eps).collect();
        let relax = softmax_convex_relaxation(&lower, &upper);

        assert!(
            relax.max_gap >= prev_gap - EPS,
            "gap should be non-decreasing: {prev_gap} -> {} at eps={eps}",
            relax.max_gap
        );
        prev_gap = relax.max_gap;
    }
}

#[test]
fn test_relaxation_tightness_ratio_bounded() {
    // For any non-point interval, the tightness ratio should be bounded
    let lower = vec![0.0, 0.0, 0.0];
    let upper = vec![2.0, 2.0, 2.0];
    let relax = softmax_convex_relaxation(&lower, &upper);

    let ratio = tightness_ratio(&relax);
    assert!(
        ratio.is_finite(),
        "tightness ratio must be finite, got {ratio}"
    );
    assert!(
        ratio >= 0.0,
        "tightness ratio must be non-negative, got {ratio}"
    );
    assert!(
        ratio <= TIGHTNESS_BOUND + EPS,
        "tightness ratio must be <= {TIGHTNESS_BOUND}, got {ratio}"
    );
}

#[test]
fn test_relaxation_asymmetric_box() {
    // Asymmetric box where one dimension has much wider range
    let lower = vec![0.0, 0.0, 0.0];
    let upper = vec![10.0, 0.1, 0.1];
    let relax = softmax_convex_relaxation(&lower, &upper);

    // The first output should have the widest bound range
    // (since its input range is widest)
    let gap_0 = relax.upper[0] - relax.lower[0];
    assert!(
        gap_0 > 0.0,
        "asymmetric box should produce non-trivial bounds for wide dimension"
    );

    // Soundness at midpoint
    let mid: Vec<f64> = lower
        .iter()
        .zip(upper.iter())
        .map(|(l, u)| (l + u) / 2.0)
        .collect();
    let violation = verify_relaxation_soundness(&mid, &lower, &upper, &relax);
    assert!(violation < EPS, "soundness at midpoint of asymmetric box");
}
