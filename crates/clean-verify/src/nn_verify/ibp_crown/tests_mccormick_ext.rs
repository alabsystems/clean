// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended McCormick relaxation functions:
//! mccormick_tight_bounds, multi_term_product_bound, mccormick_division_bounds,
//! verify_mccormick_tighter_than_naive, mccormick_quadratic_bound,
//! softmax_attention_bound.

use super::mccormick::*;

// ---------------------------------------------------------------------------
// Helper: deterministic pseudo-random (xorshift32)
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// mccormick_tight_bounds: basic correctness
// ---------------------------------------------------------------------------

#[test]
fn test_tight_bounds_both_positive() {
    let (lo, hi) = mccormick_tight_bounds(1.0, 3.0, 2.0, 4.0);
    assert!((lo - 2.0).abs() < 1e-10);
    assert!((hi - 12.0).abs() < 1e-10);
}

#[test]
fn test_tight_bounds_crossing_zero() {
    let (lo, hi) = mccormick_tight_bounds(-2.0, 3.0, -1.0, 4.0);
    assert!((lo - (-8.0)).abs() < 1e-10);
    assert!((hi - 12.0).abs() < 1e-10);
}

#[test]
fn test_tight_bounds_agrees_with_envelope() {
    let b = mccormick_envelope(-5.0, 3.0, -2.0, 7.0);
    let (lo, hi) = mccormick_tight_bounds(-5.0, 3.0, -2.0, 7.0);
    assert!((lo - b.lower).abs() < 1e-10);
    assert!((hi - b.upper).abs() < 1e-10);
}

// ---------------------------------------------------------------------------
// verify_mccormick_tighter_than_naive
// ---------------------------------------------------------------------------

#[test]
fn test_tighter_than_naive_positive_intervals() {
    assert!(verify_mccormick_tighter_than_naive((1.0, 3.0), (2.0, 4.0)));
}

#[test]
fn test_tighter_than_naive_crossing_zero() {
    assert!(verify_mccormick_tighter_than_naive(
        (-2.0, 3.0),
        (-1.0, 4.0)
    ));
}

#[test]
fn test_tighter_than_naive_both_negative() {
    assert!(verify_mccormick_tighter_than_naive(
        (-4.0, -1.0),
        (-3.0, -2.0)
    ));
}

#[test]
fn test_tighter_than_naive_random_intervals() {
    let mut rng = 12345u32;
    for _ in 0..50 {
        let x_lo = random_f64_in_range(&mut rng, -10.0, 0.0);
        let x_hi = random_f64_in_range(&mut rng, 0.0, 10.0);
        let y_lo = random_f64_in_range(&mut rng, -10.0, 0.0);
        let y_hi = random_f64_in_range(&mut rng, 0.0, 10.0);
        assert!(
            verify_mccormick_tighter_than_naive((x_lo, x_hi), (y_lo, y_hi)),
            "McCormick not tighter for x=[{x_lo},{x_hi}], y=[{y_lo},{y_hi}]"
        );
    }
}

// ---------------------------------------------------------------------------
// multi_term_product_bound
// ---------------------------------------------------------------------------

#[test]
fn test_multi_term_product_empty() {
    let (lo, hi) = multi_term_product_bound(&[]);
    assert!((lo - 1.0).abs() < 1e-10);
    assert!((hi - 1.0).abs() < 1e-10);
}

#[test]
fn test_multi_term_product_single() {
    let (lo, hi) = multi_term_product_bound(&[(2.0, 5.0)]);
    assert!((lo - 2.0).abs() < 1e-10);
    assert!((hi - 5.0).abs() < 1e-10);
}

#[test]
fn test_multi_term_product_two_terms() {
    // [1, 3] * [2, 4] = [2, 12]
    let (lo, hi) = multi_term_product_bound(&[(1.0, 3.0), (2.0, 4.0)]);
    assert!((lo - 2.0).abs() < 1e-10);
    assert!((hi - 12.0).abs() < 1e-10);
}

#[test]
fn test_multi_term_product_three_terms() {
    // [1, 2] * [1, 2] * [1, 2]: true range [1, 8]
    let (lo, hi) = multi_term_product_bound(&[(1.0, 2.0), (1.0, 2.0), (1.0, 2.0)]);
    assert!(lo <= 1.0 + 1e-10);
    assert!(hi >= 8.0 - 1e-10);
}

#[test]
fn test_multi_term_product_four_terms_positive() {
    // [1, 2]^4: true range [1, 16]
    let intervals = vec![(1.0, 2.0); 4];
    let (lo, hi) = multi_term_product_bound(&intervals);
    assert!(lo <= 1.0 + 1e-10);
    assert!(hi >= 16.0 - 1e-10);
}

#[test]
fn test_multi_term_product_mixed_signs() {
    // [-1, 1] * [-1, 1] = [-1, 1] (from McCormick)
    // Then [-1, 1] * [2, 3] = [-3, 3]
    let (lo, hi) = multi_term_product_bound(&[(-1.0, 1.0), (-1.0, 1.0), (2.0, 3.0)]);
    assert!(lo <= -3.0 + 1e-10);
    assert!(hi >= 3.0 - 1e-10);
}

#[test]
fn test_multi_term_product_soundness_sampling() {
    // Verify that sampled products of 3 intervals fall within bounds
    let intervals = [(1.0, 3.0), (-2.0, 4.0), (0.5, 2.0)];
    let (lo, hi) = multi_term_product_bound(&intervals);
    let mut rng = 777u32;
    for _ in 0..100 {
        let v0 = random_f64_in_range(&mut rng, 1.0, 3.0);
        let v1 = random_f64_in_range(&mut rng, -2.0, 4.0);
        let v2 = random_f64_in_range(&mut rng, 0.5, 2.0);
        let product = v0 * v1 * v2;
        assert!(
            product >= lo - 1e-10 && product <= hi + 1e-10,
            "product {product} outside bounds [{lo}, {hi}]"
        );
    }
}

// ---------------------------------------------------------------------------
// mccormick_division_bounds
// ---------------------------------------------------------------------------

#[test]
fn test_division_positive_y() {
    // x in [2, 6], y in [1, 3]
    // 1/y in [1/3, 1], so x/y in [2/3, 6]
    let result = mccormick_division_bounds(2.0, 6.0, 1.0, 3.0);
    let (lo, hi) = result.expect("should be Some for positive y");
    let expected_lo = 2.0 / 3.0;
    let expected_hi = 6.0;
    assert!(
        lo <= expected_lo + 1e-10,
        "lo={lo}, expected<={expected_lo}"
    );
    assert!(
        hi >= expected_hi - 1e-10,
        "hi={hi}, expected>={expected_hi}"
    );
}

#[test]
fn test_division_negative_y() {
    // x in [2, 6], y in [-3, -1]
    // 1/y in [-1, -1/3], so x/y in [-6, -2/3]
    let result = mccormick_division_bounds(2.0, 6.0, -3.0, -1.0);
    let (lo, hi) = result.expect("should be Some for negative y");
    assert!(lo <= -6.0 + 1e-10);
    assert!(hi >= -2.0 / 3.0 - 1e-10);
}

#[test]
fn test_division_zero_crossing_y_returns_none() {
    let result = mccormick_division_bounds(1.0, 2.0, -1.0, 1.0);
    assert!(result.is_none(), "y crossing zero should return None");
}

#[test]
fn test_division_y_at_zero_lower_returns_none() {
    let result = mccormick_division_bounds(1.0, 2.0, 0.0, 1.0);
    assert!(result.is_none(), "y_lo=0 should return None");
}

#[test]
fn test_division_y_at_zero_upper_returns_none() {
    let result = mccormick_division_bounds(1.0, 2.0, -1.0, 0.0);
    assert!(result.is_none(), "y_hi=0 should return None");
}

#[test]
fn test_division_soundness_sampling() {
    let result = mccormick_division_bounds(-3.0, 5.0, 1.0, 4.0);
    let (lo, hi) = result.expect("positive y");
    let mut rng = 54321u32;
    for _ in 0..100 {
        let x = random_f64_in_range(&mut rng, -3.0, 5.0);
        let y = random_f64_in_range(&mut rng, 1.0, 4.0);
        let quotient = x / y;
        assert!(
            quotient >= lo - 1e-10 && quotient <= hi + 1e-10,
            "quotient {quotient} outside bounds [{lo}, {hi}] for x={x}, y={y}"
        );
    }
}

// ---------------------------------------------------------------------------
// mccormick_quadratic_bound
// ---------------------------------------------------------------------------

#[test]
fn test_quadratic_positive_interval() {
    // x in [2, 5]: x^2 in [4, 25]
    let (lo, hi) = mccormick_quadratic_bound(2.0, 5.0);
    assert!((lo - 4.0).abs() < 1e-10);
    assert!((hi - 25.0).abs() < 1e-10);
}

#[test]
fn test_quadratic_negative_interval() {
    // x in [-5, -2]: x^2 in [4, 25]
    let (lo, hi) = mccormick_quadratic_bound(-5.0, -2.0);
    assert!((lo - 4.0).abs() < 1e-10);
    assert!((hi - 25.0).abs() < 1e-10);
}

#[test]
fn test_quadratic_crossing_zero() {
    // x in [-3, 5]: x^2 in [0, 25]
    let (lo, hi) = mccormick_quadratic_bound(-3.0, 5.0);
    assert!(lo.abs() < 1e-10, "lo should be 0, got {lo}");
    assert!((hi - 25.0).abs() < 1e-10);
}

#[test]
fn test_quadratic_crossing_zero_symmetric() {
    // x in [-4, 4]: x^2 in [0, 16]
    let (lo, hi) = mccormick_quadratic_bound(-4.0, 4.0);
    assert!(lo.abs() < 1e-10);
    assert!((hi - 16.0).abs() < 1e-10);
}

#[test]
fn test_quadratic_tighter_than_mccormick_bilinear() {
    // When crossing zero, quadratic bound [0, max(lo^2, hi^2)] is tighter
    // than McCormick on x*x which gives [min corners, max corners].
    // McCormick on x*x with x in [-3, 5]:
    //   corners: 9, -15, -15, 25 → [-15, 25]
    // Quadratic: [0, 25] — strictly tighter lower bound.
    let (q_lo, q_hi) = mccormick_quadratic_bound(-3.0, 5.0);
    let (m_lo, m_hi) = mccormick_tight_bounds(-3.0, 5.0, -3.0, 5.0);
    assert!(
        q_lo >= m_lo - 1e-10,
        "quadratic lo={q_lo} should be >= McCormick lo={m_lo}"
    );
    assert!(
        q_hi <= m_hi + 1e-10,
        "quadratic hi={q_hi} should be <= McCormick hi={m_hi}"
    );
    // Strictly tighter in this case
    let q_width = q_hi - q_lo;
    let m_width = m_hi - m_lo;
    assert!(
        q_width < m_width - 1e-10,
        "quadratic width {q_width} should be strictly less than McCormick width {m_width}"
    );
}

#[test]
fn test_quadratic_point_interval() {
    let (lo, hi) = mccormick_quadratic_bound(3.0, 3.0);
    assert!((lo - 9.0).abs() < 1e-10);
    assert!((hi - 9.0).abs() < 1e-10);
}

#[test]
fn test_quadratic_soundness_sampling() {
    let (lo, hi) = mccormick_quadratic_bound(-4.0, 3.0);
    let mut rng = 11111u32;
    for _ in 0..100 {
        let x = random_f64_in_range(&mut rng, -4.0, 3.0);
        let sq = x * x;
        assert!(
            sq >= lo - 1e-10 && sq <= hi + 1e-10,
            "x^2={sq} outside bounds [{lo}, {hi}] for x={x}"
        );
    }
}

// ---------------------------------------------------------------------------
// softmax_attention_bound
// ---------------------------------------------------------------------------

#[test]
fn test_attention_single_dimension() {
    // q in [1, 2], k in [3, 4]: dot = q*k in [3, 8]
    let (lo, hi) = softmax_attention_bound(&[(1.0, 2.0)], &[(3.0, 4.0)]);
    assert!((lo - 3.0).abs() < 1e-10);
    assert!((hi - 8.0).abs() < 1e-10);
}

#[test]
fn test_attention_two_dimensions() {
    // q = ([1,2], [0,1]), k = ([1,1], [1,1])
    // dot = q0*k0 + q1*k1
    // q0*k0 in [1, 2], q1*k1 in [0, 1]
    // sum in [1, 3]
    let (lo, hi) = softmax_attention_bound(&[(1.0, 2.0), (0.0, 1.0)], &[(1.0, 1.0), (1.0, 1.0)]);
    assert!((lo - 1.0).abs() < 1e-10);
    assert!((hi - 3.0).abs() < 1e-10);
}

#[test]
fn test_attention_mixed_signs() {
    // q = ([-1,1], [-2,0]), k = ([1,3], [-1,2])
    // q0*k0: corners -1, -3, 1, 3 → [-3, 3]
    // q1*k1: corners 2, -4, 0, 0 → [-4, 2]
    // sum: [-7, 5]
    let (lo, hi) = softmax_attention_bound(&[(-1.0, 1.0), (-2.0, 0.0)], &[(1.0, 3.0), (-1.0, 2.0)]);
    assert!((lo - (-7.0)).abs() < 1e-10);
    assert!((hi - 5.0).abs() < 1e-10);
}

#[test]
fn test_attention_empty_dimensions() {
    let (lo, hi) = softmax_attention_bound(&[], &[]);
    assert!(lo.abs() < 1e-10);
    assert!(hi.abs() < 1e-10);
}

#[test]
fn test_attention_soundness_sampling() {
    let q_bounds = [(0.0, 1.0), (-1.0, 1.0), (0.5, 2.0)];
    let k_bounds = [(-1.0, 2.0), (0.0, 3.0), (-0.5, 0.5)];
    let (lo, hi) = softmax_attention_bound(&q_bounds, &k_bounds);
    let mut rng = 99999u32;
    for _ in 0..100 {
        let q0 = random_f64_in_range(&mut rng, 0.0, 1.0);
        let q1 = random_f64_in_range(&mut rng, -1.0, 1.0);
        let q2 = random_f64_in_range(&mut rng, 0.5, 2.0);
        let k0 = random_f64_in_range(&mut rng, -1.0, 2.0);
        let k1 = random_f64_in_range(&mut rng, 0.0, 3.0);
        let k2 = random_f64_in_range(&mut rng, -0.5, 0.5);
        let dot = q0 * k0 + q1 * k1 + q2 * k2;
        assert!(
            dot >= lo - 1e-10 && dot <= hi + 1e-10,
            "dot={dot} outside bounds [{lo}, {hi}]"
        );
    }
}

// ---------------------------------------------------------------------------
// Cross-function consistency
// ---------------------------------------------------------------------------

#[test]
fn test_tight_bounds_and_product_interval_agree() {
    let cases = [
        (1.0, 3.0, 2.0, 4.0),
        (-5.0, 5.0, -3.0, 7.0),
        (-2.0, -1.0, 3.0, 4.0),
    ];
    for (xl, xh, yl, yh) in cases {
        let (t_lo, t_hi) = mccormick_tight_bounds(xl, xh, yl, yh);
        let (p_lo, p_hi) = mccormick_product_interval((xl, xh), (yl, yh));
        assert!(
            (t_lo - p_lo).abs() < 1e-10 && (t_hi - p_hi).abs() < 1e-10,
            "tight_bounds and product_interval disagree for x=[{xl},{xh}], y=[{yl},{yh}]"
        );
    }
}

#[test]
fn test_multi_term_two_equals_tight_bounds() {
    let (lo, hi) = multi_term_product_bound(&[(2.0, 5.0), (1.0, 3.0)]);
    let (t_lo, t_hi) = mccormick_tight_bounds(2.0, 5.0, 1.0, 3.0);
    assert!((lo - t_lo).abs() < 1e-10);
    assert!((hi - t_hi).abs() < 1e-10);
}

#[test]
fn test_quadratic_vs_mccormick_positive_interval_equal() {
    // For positive intervals, quadratic and McCormick on x*x should agree
    let (q_lo, q_hi) = mccormick_quadratic_bound(2.0, 5.0);
    let (m_lo, m_hi) = mccormick_tight_bounds(2.0, 5.0, 2.0, 5.0);
    assert!((q_lo - m_lo).abs() < 1e-10);
    assert!((q_hi - m_hi).abs() < 1e-10);
}
