// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for attention mechanism bilinear bound propagation (T53-T54).

use super::attention::*;

// ---------------------------------------------------------------------------
// attention_score_bounds: dot product interval propagation
// ---------------------------------------------------------------------------

#[test]
fn test_score_bounds_identical_positive_intervals() {
    // q = k = [1,1] exactly => dot product = 2.0
    let (lo, hi) = attention_score_bounds(&[1.0, 1.0], &[1.0, 1.0], &[1.0, 1.0], &[1.0, 1.0]);
    assert!((lo - 2.0).abs() < 1e-10);
    assert!((hi - 2.0).abs() < 1e-10);
}

#[test]
fn test_score_bounds_unit_intervals() {
    // q_i in [0,1], k_i in [0,1], dim=2
    // Each coordinate product in [0, 1], sum in [0, 2]
    let (lo, hi) = attention_score_bounds(&[0.0, 0.0], &[1.0, 1.0], &[0.0, 0.0], &[1.0, 1.0]);
    assert!(lo >= -1e-10);
    assert!((hi - 2.0).abs() < 1e-10);
}

#[test]
fn test_score_bounds_single_dimension() {
    // 1D: q in [2,4], k in [3,5] => product in [6, 20]
    let (lo, hi) = attention_score_bounds(&[2.0], &[4.0], &[3.0], &[5.0]);
    assert!((lo - 6.0).abs() < 1e-10);
    assert!((hi - 20.0).abs() < 1e-10);
}

#[test]
fn test_score_bounds_mixed_sign() {
    // q in [-1, 1], k in [-1, 1], dim=1
    // Product in [-1, 1]
    let (lo, hi) = attention_score_bounds(&[-1.0], &[1.0], &[-1.0], &[1.0]);
    assert!((lo - (-1.0)).abs() < 1e-10);
    assert!((hi - 1.0).abs() < 1e-10);
}

#[test]
fn test_score_bounds_three_dim() {
    // q in [1,2] per dim, k in [1,3] per dim
    // Each coordinate product in [1, 6], sum of 3 in [3, 18]
    let (lo, hi) = attention_score_bounds(
        &[1.0, 1.0, 1.0],
        &[2.0, 2.0, 2.0],
        &[1.0, 1.0, 1.0],
        &[3.0, 3.0, 3.0],
    );
    assert!((lo - 3.0).abs() < 1e-10);
    assert!((hi - 18.0).abs() < 1e-10);
}

#[test]
fn test_score_bounds_soundness_random_sampling() {
    // q in [-2, 2], k in [-3, 3], dim=2
    let q_lo = [-2.0, -2.0];
    let q_hi = [2.0, 2.0];
    let k_lo = [-3.0, -3.0];
    let k_hi = [3.0, 3.0];
    let (bound_lo, bound_hi) = attention_score_bounds(&q_lo, &q_hi, &k_lo, &k_hi);

    // Sample corners and interior points
    let vals = [-2.0, -1.0, 0.0, 1.0, 2.0];
    let kvals = [-3.0, -1.5, 0.0, 1.5, 3.0];
    for &q0 in &vals {
        for &q1 in &vals {
            for &k0 in &kvals {
                for &k1 in &kvals {
                    let dot = q0 * k0 + q1 * k1;
                    assert!(
                        dot >= bound_lo - 1e-10 && dot <= bound_hi + 1e-10,
                        "dot={dot} outside bounds [{bound_lo}, {bound_hi}] at q=({q0},{q1}), k=({k0},{k1})"
                    );
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// softmax_bounds: interval softmax computation
// ---------------------------------------------------------------------------

#[test]
fn test_softmax_bounds_equal_scores() {
    // All scores identical => softmax = 1/n for each
    let (lo, hi) = softmax_bounds(&[0.0, 0.0, 0.0], &[0.0, 0.0, 0.0])[0];
    assert!((lo - 1.0 / 3.0).abs() < 1e-6);
    assert!((hi - 1.0 / 3.0).abs() < 1e-6);
}

#[test]
fn test_softmax_bounds_single_score() {
    // Single score => softmax = 1.0 always
    let bounds = softmax_bounds(&[0.0], &[0.0]);
    assert_eq!(bounds.len(), 1);
    assert!((bounds[0].0 - 1.0).abs() < 1e-10);
    assert!((bounds[0].1 - 1.0).abs() < 1e-10);
}

#[test]
fn test_softmax_bounds_single_score_varying() {
    // Single score with range => still softmax = 1.0
    let bounds = softmax_bounds(&[-5.0], &[5.0]);
    assert!((bounds[0].0 - 1.0).abs() < 1e-10);
    assert!((bounds[0].1 - 1.0).abs() < 1e-10);
}

#[test]
fn test_softmax_bounds_all_in_zero_one() {
    // All softmax outputs must be in [0, 1]
    let bounds = softmax_bounds(&[-10.0, -5.0, 0.0], &[0.0, 5.0, 10.0]);
    for (lo, hi) in &bounds {
        assert!(*lo >= -1e-10, "softmax lower bound {lo} < 0");
        assert!(*hi <= 1.0 + 1e-10, "softmax upper bound {hi} > 1");
        assert!(lo <= hi, "softmax lower {lo} > upper {hi}");
    }
}

#[test]
fn test_softmax_bounds_dominant_score() {
    // One score much larger than others
    let bounds = softmax_bounds(&[100.0, -100.0], &[100.0, -100.0]);
    // First element should be very close to 1.0
    assert!(bounds[0].0 > 0.99);
    assert!(bounds[0].1 > 0.99);
    // Second element should be very close to 0.0
    assert!(bounds[1].0 < 0.01);
    assert!(bounds[1].1 < 0.01);
}

#[test]
fn test_softmax_bounds_sum_upper_at_most_one_for_point_intervals() {
    // For point intervals, softmax values sum to exactly 1
    let bounds = softmax_bounds(&[1.0, 2.0, 3.0], &[1.0, 2.0, 3.0]);
    let sum: f64 = bounds.iter().map(|(lo, _)| lo).sum();
    assert!(
        (sum - 1.0).abs() < 1e-6,
        "softmax sum = {sum}, expected 1.0"
    );
}

#[test]
fn test_softmax_bounds_two_equal() {
    // Two equal scores => each softmax = 0.5
    let bounds = softmax_bounds(&[5.0, 5.0], &[5.0, 5.0]);
    assert!((bounds[0].0 - 0.5).abs() < 1e-6);
    assert!((bounds[0].1 - 0.5).abs() < 1e-6);
    assert!((bounds[1].0 - 0.5).abs() < 1e-6);
    assert!((bounds[1].1 - 0.5).abs() < 1e-6);
}

// ---------------------------------------------------------------------------
// attention_head_bounds: full pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_attention_head_bounds_simple_2d() {
    // q and k in [0, 1] per dim, v in [0, 1] per dim, d_k = 2
    let (lo, hi) = attention_head_bounds(
        &[0.0, 0.0],
        &[1.0, 1.0],
        &[0.0, 0.0],
        &[1.0, 1.0],
        &[0.0, 0.0],
        &[1.0, 1.0],
        2,
    );
    assert_eq!(lo.len(), 2);
    assert_eq!(hi.len(), 2);
    // Output must be non-negative since v >= 0 and attn_weight >= 0
    for &l in &lo {
        assert!(l >= -1e-10, "output lower bound {l} < 0");
    }
    // Output <= 1 since softmax <= 1 and v <= 1
    for &h in &hi {
        assert!(h <= 1.0 + 1e-10, "output upper bound {h} > 1");
    }
}

#[test]
fn test_attention_head_bounds_identity_qk() {
    // q = k = [1] exactly, d_k = 1 => score = 1.0, scaled = 1.0
    // sigmoid(1.0) ~ 0.731
    // v in [2, 4] => output in [0.731*2, 0.731*4] approximately
    let (lo, hi) = attention_head_bounds(&[1.0], &[1.0], &[1.0], &[1.0], &[2.0], &[4.0], 1);
    let expected_weight = 1.0 / (1.0 + (-1.0f64).exp());
    assert!(lo[0] <= expected_weight * 2.0 + 1e-6);
    assert!(hi[0] >= expected_weight * 4.0 - 1e-6);
}

#[test]
fn test_attention_head_bounds_zero_query() {
    // q = [0, 0], k in [1, 2], v in [1, 3], d_k = 2
    // score = 0 => scaled = 0 => sigmoid(0) = 0.5
    // output = 0.5 * v
    let (lo, hi) = attention_head_bounds(
        &[0.0, 0.0],
        &[0.0, 0.0],
        &[1.0, 1.0],
        &[2.0, 2.0],
        &[1.0],
        &[3.0],
        2,
    );
    // With score = 0, sigmoid(0) = 0.5, output in [0.5*1, 0.5*3] = [0.5, 1.5]
    assert!(lo[0] <= 0.5 + 1e-6);
    assert!(hi[0] >= 1.5 - 1e-6);
}

#[test]
fn test_attention_head_bounds_scaling_effect() {
    // Same q, k but different d_k values.
    // Larger d_k => smaller scaled score => sigmoid closer to 0.5
    let (_lo_small_dk, hi_small_dk) =
        attention_head_bounds(&[2.0], &[2.0], &[2.0], &[2.0], &[1.0], &[1.0], 1);
    let (_lo_large_dk, hi_large_dk) =
        attention_head_bounds(&[2.0], &[2.0], &[2.0], &[2.0], &[1.0], &[1.0], 16);
    // With d_k=1: score=4, sigmoid(4) ~ 0.982 => output ~ 0.982
    // With d_k=16: score=4, scaled=4/4=1, sigmoid(1) ~ 0.731 => output ~ 0.731
    assert!(hi_small_dk[0] > hi_large_dk[0] - 1e-6);
}

#[test]
fn test_attention_head_bounds_negative_values() {
    // Negative v bounds
    let (lo, hi) = attention_head_bounds(&[1.0], &[1.0], &[1.0], &[1.0], &[-3.0], &[-1.0], 1);
    // sigmoid(1) ~ 0.731, output in [0.731*(-3), 0.731*(-1)]
    assert!(lo[0] < 0.0);
    assert!(hi[0] < 0.0);
}

#[test]
fn test_attention_head_bounds_multi_v_dim() {
    // v has 3 dimensions, q/k have 2
    let (lo, hi) = attention_head_bounds(
        &[0.0, 0.0],
        &[1.0, 1.0],
        &[0.0, 0.0],
        &[1.0, 1.0],
        &[0.0, 1.0, -1.0],
        &[2.0, 3.0, 1.0],
        2,
    );
    assert_eq!(lo.len(), 3);
    assert_eq!(hi.len(), 3);
    // Each dimension should have valid bounds
    for i in 0..3 {
        assert!(
            lo[i] <= hi[i] + 1e-10,
            "dim {i}: lo={} > hi={}",
            lo[i],
            hi[i]
        );
    }
}

// ---------------------------------------------------------------------------
// verify_attention_soundness
// ---------------------------------------------------------------------------

#[test]
fn test_verify_soundness_exact_center() {
    let bounds = AttentionBounds {
        lower: vec![-10.0],
        upper: vec![10.0],
        d_k: 1,
    };
    // q=1, k=1, v=1 => sigmoid(1)*1 ~ 0.731, within [-10, 10]
    assert!(verify_attention_soundness(&[1.0], &[1.0], &[1.0], &bounds));
}

#[test]
fn test_verify_soundness_outside_bounds() {
    let bounds = AttentionBounds {
        lower: vec![0.9],
        upper: vec![1.0],
        d_k: 1,
    };
    // q=0, k=0, v=1 => sigmoid(0)*1 = 0.5, which is below 0.9
    assert!(!verify_attention_soundness(&[0.0], &[0.0], &[1.0], &bounds));
}

#[test]
fn test_verify_soundness_computed_bounds() {
    // Compute bounds and then verify a point inside
    let q_lo = [0.5];
    let q_hi = [1.5];
    let k_lo = [0.5];
    let k_hi = [1.5];
    let v_lo = [1.0];
    let v_hi = [2.0];
    let d_k = 1;

    let (out_lo, out_hi) = attention_head_bounds(&q_lo, &q_hi, &k_lo, &k_hi, &v_lo, &v_hi, d_k);

    let bounds = AttentionBounds {
        lower: out_lo,
        upper: out_hi,
        d_k,
    };

    // Test at various points within q/k/v ranges
    let test_vals = [0.5, 0.75, 1.0, 1.25, 1.5];
    for &q in &test_vals {
        for &k in &test_vals {
            for &v in &[1.0, 1.5, 2.0] {
                assert!(
                    verify_attention_soundness(&[q], &[k], &[v], &bounds),
                    "soundness failed at q={q}, k={k}, v={v}"
                );
            }
        }
    }
}

#[test]
fn test_verify_soundness_multidim() {
    let q_lo = [0.0, 0.0];
    let q_hi = [1.0, 1.0];
    let k_lo = [0.0, 0.0];
    let k_hi = [1.0, 1.0];
    let v_lo = [0.0, 0.0];
    let v_hi = [1.0, 1.0];
    let d_k = 2;

    let (out_lo, out_hi) = attention_head_bounds(&q_lo, &q_hi, &k_lo, &k_hi, &v_lo, &v_hi, d_k);

    let bounds = AttentionBounds {
        lower: out_lo,
        upper: out_hi,
        d_k,
    };

    // Corner points of q, k, v
    for &q0 in &[0.0, 1.0] {
        for &q1 in &[0.0, 1.0] {
            for &k0 in &[0.0, 1.0] {
                for &k1 in &[0.0, 1.0] {
                    for &v0 in &[0.0, 1.0] {
                        for &v1 in &[0.0, 1.0] {
                            assert!(
                                verify_attention_soundness(
                                    &[q0, q1],
                                    &[k0, k1],
                                    &[v0, v1],
                                    &bounds
                                ),
                                "soundness failed at q=({q0},{q1}), k=({k0},{k1}), v=({v0},{v1})"
                            );
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Edge cases and properties
// ---------------------------------------------------------------------------

#[test]
fn test_score_bounds_contain_zero_when_intervals_cross() {
    // If q and k intervals both cross zero, the dot product can be zero
    let (lo, hi) = attention_score_bounds(&[-1.0], &[1.0], &[-1.0], &[1.0]);
    assert!(lo <= 1e-10);
    assert!(hi >= -1e-10);
}

#[test]
fn test_attention_head_bounds_preserves_v_dim() {
    // v dimension can differ from q/k dimension
    let (lo, hi) = attention_head_bounds(
        &[1.0, 2.0, 3.0],
        &[1.0, 2.0, 3.0],
        &[1.0, 2.0, 3.0],
        &[1.0, 2.0, 3.0],
        &[1.0],
        &[2.0],
        3,
    );
    assert_eq!(lo.len(), 1);
    assert_eq!(hi.len(), 1);
}

#[test]
fn test_softmax_bounds_monotonicity() {
    // Higher score range should produce higher softmax upper bound
    let bounds_low = softmax_bounds(&[-1.0, 0.0], &[0.0, 0.0]);
    let bounds_high = softmax_bounds(&[0.0, 0.0], &[1.0, 0.0]);
    // The first element's upper bound should be higher when score is higher
    assert!(bounds_high[0].1 >= bounds_low[0].1 - 1e-6);
}
