// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for LayerNorm bound propagation (T20-T22).

use super::layernorm::*;

// ============================================================================
// Mean bounds tests
// ============================================================================

#[test]
fn test_mean_bounds_uniform_input() {
    // All elements in [1.0, 3.0] => mean in [1.0, 3.0]
    let lo = vec![1.0, 1.0, 1.0];
    let hi = vec![3.0, 3.0, 3.0];
    let (mean_lo, mean_hi) = compute_mean_bounds(&lo, &hi);
    assert!((mean_lo - 1.0).abs() < 1e-10);
    assert!((mean_hi - 3.0).abs() < 1e-10);
}

#[test]
fn test_mean_bounds_point_intervals() {
    // All elements are exact: [2, 4, 6] => mean = 4.0
    let lo = vec![2.0, 4.0, 6.0];
    let hi = vec![2.0, 4.0, 6.0];
    let (mean_lo, mean_hi) = compute_mean_bounds(&lo, &hi);
    assert!((mean_lo - 4.0).abs() < 1e-10);
    assert!((mean_hi - 4.0).abs() < 1e-10);
}

#[test]
fn test_mean_bounds_asymmetric() {
    // [0, 10], [0, 0] => mean_lo = (0+0)/2 = 0, mean_hi = (10+0)/2 = 5
    let lo = vec![0.0, 0.0];
    let hi = vec![10.0, 0.0];
    let (mean_lo, mean_hi) = compute_mean_bounds(&lo, &hi);
    assert!((mean_lo - 0.0).abs() < 1e-10);
    assert!((mean_hi - 5.0).abs() < 1e-10);
}

#[test]
fn test_mean_bounds_negative_intervals() {
    let lo = vec![-5.0, -3.0];
    let hi = vec![-1.0, -2.0];
    let (mean_lo, mean_hi) = compute_mean_bounds(&lo, &hi);
    assert!((mean_lo - (-4.0)).abs() < 1e-10); // (-5 + -3) / 2
    assert!((mean_hi - (-1.5)).abs() < 1e-10); // (-1 + -2) / 2
}

#[test]
fn test_mean_bounds_single_element() {
    let lo = vec![3.0];
    let hi = vec![7.0];
    let (mean_lo, mean_hi) = compute_mean_bounds(&lo, &hi);
    assert!((mean_lo - 3.0).abs() < 1e-10);
    assert!((mean_hi - 7.0).abs() < 1e-10);
}

#[test]
fn test_mean_bounds_wide_range() {
    // All elements in [0, 100] => mean in [0, 100]
    let d = 10;
    let lo = vec![0.0; d];
    let hi = vec![100.0; d];
    let (mean_lo, mean_hi) = compute_mean_bounds(&lo, &hi);
    assert!((mean_lo - 0.0).abs() < 1e-10);
    assert!((mean_hi - 100.0).abs() < 1e-10);
}

#[test]
fn test_mean_bounds_alternating_wide_narrow() {
    // Alternating: wide [0,100] and narrow [49,51]
    let lo = vec![0.0, 49.0, 0.0, 49.0];
    let hi = vec![100.0, 51.0, 100.0, 51.0];
    let (mean_lo, mean_hi) = compute_mean_bounds(&lo, &hi);
    // mean_lo = (0 + 49 + 0 + 49) / 4 = 24.5
    // mean_hi = (100 + 51 + 100 + 51) / 4 = 75.5
    assert!((mean_lo - 24.5).abs() < 1e-10);
    assert!((mean_hi - 75.5).abs() < 1e-10);
}

#[test]
fn test_mean_bounds_random_sampling_soundness() {
    // For 100 random samples within bounds, verify mean_lower <= true_mean <= mean_upper
    let lo = vec![1.0, -3.0, 5.0, -10.0];
    let hi = vec![4.0, 2.0, 12.0, 0.0];
    let (mean_lo, mean_hi) = compute_mean_bounds(&lo, &hi);

    // Deterministic LCG for reproducibility
    let mut rng: u64 = 12345;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };

    for _ in 0..100 {
        let x: Vec<f64> = lo
            .iter()
            .zip(hi.iter())
            .map(|(&l, &u)| l + lcg(&mut rng) * (u - l))
            .collect();
        let true_mean: f64 = x.iter().sum::<f64>() / x.len() as f64;
        assert!(
            mean_lo <= true_mean + 1e-10,
            "mean_lo={mean_lo} > true_mean={true_mean}"
        );
        assert!(
            true_mean <= mean_hi + 1e-10,
            "true_mean={true_mean} > mean_hi={mean_hi}"
        );
    }
}

#[test]
fn test_mean_bounds_large_dimension() {
    // d = 128, all [0, 1]
    let d = 128;
    let lo = vec![0.0; d];
    let hi = vec![1.0; d];
    let (mean_lo, mean_hi) = compute_mean_bounds(&lo, &hi);
    assert!((mean_lo - 0.0).abs() < 1e-10);
    assert!((mean_hi - 1.0).abs() < 1e-10);
}

#[test]
fn test_mean_bounds_mixed_positive_negative() {
    let lo = vec![-100.0, 50.0, -20.0];
    let hi = vec![-10.0, 80.0, 10.0];
    let (mean_lo, mean_hi) = compute_mean_bounds(&lo, &hi);
    // mean_lo = (-100 + 50 + -20) / 3 = -70/3 ~ -23.33
    // mean_hi = (-10 + 80 + 10) / 3 = 80/3 ~ 26.67
    assert!((mean_lo - (-70.0 / 3.0)).abs() < 1e-10);
    assert!((mean_hi - (80.0 / 3.0)).abs() < 1e-10);
}

// ============================================================================
// Variance bounds tests
// ============================================================================

#[test]
fn test_variance_bounds_uniform_point() {
    // All elements are 5.0 => variance = 0
    let lo = vec![5.0, 5.0, 5.0];
    let hi = vec![5.0, 5.0, 5.0];
    let mean_bounds = compute_mean_bounds(&lo, &hi);
    let (var_lo, var_hi) = compute_variance_bounds(&lo, &hi, mean_bounds);
    assert!(var_lo.abs() < 1e-10);
    assert!(var_hi.abs() < 1e-10);
}

#[test]
fn test_variance_bounds_overlapping_intervals_can_be_zero() {
    // All intervals are [0, 10] => they all overlap => variance can be 0
    let lo = vec![0.0, 0.0, 0.0];
    let hi = vec![10.0, 10.0, 10.0];
    let mean_bounds = compute_mean_bounds(&lo, &hi);
    let (var_lo, _var_hi) = compute_variance_bounds(&lo, &hi, mean_bounds);
    assert!(
        var_lo <= 1e-10,
        "variance lower bound should be 0 when intervals overlap"
    );
}

#[test]
fn test_variance_bounds_upper_positive() {
    // Non-point intervals should have positive upper variance bound
    let lo = vec![0.0, 0.0];
    let hi = vec![10.0, 10.0];
    let mean_bounds = compute_mean_bounds(&lo, &hi);
    let (_var_lo, var_hi) = compute_variance_bounds(&lo, &hi, mean_bounds);
    assert!(
        var_hi > 0.0,
        "variance upper bound must be positive for non-point intervals"
    );
}

#[test]
fn test_variance_bounds_wider_intervals_larger_upper() {
    // Wider intervals should give a larger upper bound on variance
    let lo_narrow = vec![4.0, 4.0];
    let hi_narrow = vec![6.0, 6.0];
    let mean_narrow = compute_mean_bounds(&lo_narrow, &hi_narrow);
    let (_, var_hi_narrow) = compute_variance_bounds(&lo_narrow, &hi_narrow, mean_narrow);

    let lo_wide = vec![0.0, 0.0];
    let hi_wide = vec![10.0, 10.0];
    let mean_wide = compute_mean_bounds(&lo_wide, &hi_wide);
    let (_, var_hi_wide) = compute_variance_bounds(&lo_wide, &hi_wide, mean_wide);

    assert!(
        var_hi_wide > var_hi_narrow,
        "wider intervals should give larger variance upper bound"
    );
}

#[test]
fn test_variance_bounds_single_element_is_zero() {
    // Single element: variance = 0 trivially (no other elements to differ from)
    let lo = vec![42.0];
    let hi = vec![42.0];
    let mean_bounds = compute_mean_bounds(&lo, &hi);
    let (var_lo, var_hi) = compute_variance_bounds(&lo, &hi, mean_bounds);
    assert!(
        var_lo.abs() < 1e-10,
        "single point element variance lower should be 0"
    );
    assert!(
        var_hi.abs() < 1e-10,
        "single point element variance upper should be 0"
    );
}

#[test]
fn test_variance_bounds_single_element_interval() {
    // Single element interval [1, 5]: variance = 0 always for d=1
    // mean = x, so (x - mean)^2 = 0
    let lo = vec![1.0];
    let hi = vec![5.0];
    let mean_bounds = compute_mean_bounds(&lo, &hi);
    let (var_lo, var_hi) = compute_variance_bounds(&lo, &hi, mean_bounds);
    // For d=1, variance is always 0 regardless of x (since mean = x)
    // But our conservative computation may overestimate var_hi since
    // it considers x and mean independently.
    assert!(var_lo >= -1e-10, "variance lower must be non-negative");
    assert!(var_hi >= var_lo - 1e-10, "variance upper >= lower");
}

#[test]
fn test_variance_bounds_high_variance_case() {
    // [-100, 100] and [0, 1]: non-overlapping ranges
    let lo = vec![-100.0, 0.0];
    let hi = vec![100.0, 1.0];
    let mean_bounds = compute_mean_bounds(&lo, &hi);
    let (var_lo, var_hi) = compute_variance_bounds(&lo, &hi, mean_bounds);
    // var_upper should be large because inputs can be very far apart
    assert!(
        var_hi > 100.0,
        "high-variance case should have large upper bound"
    );
    assert!(var_lo >= -1e-10, "variance lower must be non-negative");
}

#[test]
fn test_variance_bounds_non_overlapping_intervals() {
    // [0, 1] and [10, 11]: no overlap, so elements cannot all be equal
    let lo = vec![0.0, 10.0];
    let hi = vec![1.0, 11.0];
    let mean_bounds = compute_mean_bounds(&lo, &hi);
    let (_var_lo, var_hi) = compute_variance_bounds(&lo, &hi, mean_bounds);
    // Upper bound should capture that the elements are far apart
    assert!(
        var_hi > 0.0,
        "non-overlapping intervals must have positive variance upper"
    );
}

#[test]
fn test_variance_bounds_random_sampling_soundness() {
    // For 100 random samples, verify var_lower <= true_var <= var_upper
    let lo = vec![0.0, 1.0, 2.0, 3.0];
    let hi = vec![5.0, 6.0, 7.0, 8.0];
    let mean_bounds = compute_mean_bounds(&lo, &hi);
    let (var_lo, var_hi) = compute_variance_bounds(&lo, &hi, mean_bounds);

    let mut rng: u64 = 54321;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };

    for _ in 0..100 {
        let x: Vec<f64> = lo
            .iter()
            .zip(hi.iter())
            .map(|(&l, &u)| l + lcg(&mut rng) * (u - l))
            .collect();
        let d = x.len() as f64;
        let mean: f64 = x.iter().sum::<f64>() / d;
        let var: f64 = x.iter().map(|xi| (xi - mean).powi(2)).sum::<f64>() / d;
        assert!(var_lo <= var + 1e-10, "var_lo={var_lo} > true_var={var}");
        assert!(var <= var_hi + 1e-10, "true_var={var} > var_hi={var_hi}");
    }
}

#[test]
fn test_variance_bounds_are_sigma_squared() {
    // Verify that variance_bounds are sigma^2, not sigma.
    // For input [0, 4] (point), mean = 2, var = ((0-2)^2 + (4-2)^2)/2 = 4
    let lo = vec![0.0, 4.0];
    let hi = vec![0.0, 4.0];
    let mean_bounds = compute_mean_bounds(&lo, &hi);
    let (var_lo, var_hi) = compute_variance_bounds(&lo, &hi, mean_bounds);
    // Both bounds should be exactly 4.0 (not 2.0 which would be sqrt(4))
    assert!(
        (var_lo - 4.0).abs() < 1e-10 || var_lo < 4.0,
        "variance lower should be <= 4.0 (sigma^2, not sigma)"
    );
    assert!(
        var_hi >= 4.0 - 1e-10,
        "variance upper should be >= 4.0 (sigma^2, not sigma)"
    );
}

#[test]
fn test_variance_bounds_nonnegative_always() {
    // Variance can never be negative
    let test_cases: Vec<(Vec<f64>, Vec<f64>)> = vec![
        (vec![-10.0, -5.0], vec![10.0, 5.0]),
        (vec![0.0, 0.0, 0.0], vec![1.0, 2.0, 3.0]),
        (vec![-1.0], vec![1.0]),
        (vec![100.0, 200.0, 300.0], vec![101.0, 201.0, 301.0]),
    ];
    for (lo, hi) in &test_cases {
        let mean_bounds = compute_mean_bounds(lo, hi);
        let (var_lo, var_hi) = compute_variance_bounds(lo, hi, mean_bounds);
        assert!(var_lo >= -1e-10, "variance lower must be non-negative");
        assert!(var_hi >= var_lo - 1e-10, "variance upper >= lower");
    }
}

// ============================================================================
// Full LayerNorm tests
// ============================================================================

#[test]
fn test_layernorm_forward_uniform_input_identity_params() {
    // Uniform input [c, c], gamma=1, beta=0 => centered = 0, normalized = 0
    let lo = vec![5.0, 5.0, 5.0];
    let hi = vec![5.0, 5.0, 5.0];
    let gamma = vec![1.0, 1.0, 1.0];
    let beta = vec![0.0, 0.0, 0.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);

    for i in 0..3 {
        assert!(
            bounds.lower[i] <= 1e-6,
            "lower[{i}] = {} should be near 0",
            bounds.lower[i]
        );
        assert!(
            bounds.upper[i] >= -1e-6,
            "upper[{i}] = {} should be near 0",
            bounds.upper[i]
        );
    }
}

#[test]
fn test_layernorm_forward_with_beta_offset() {
    // Uniform input, gamma=1, beta=2 => output should be near 2.0 for each element
    let lo = vec![3.0, 3.0];
    let hi = vec![3.0, 3.0];
    let gamma = vec![1.0, 1.0];
    let beta = vec![2.0, 2.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);
    for i in 0..2 {
        assert!(
            bounds.lower[i] <= 2.0 + 1e-6 && bounds.upper[i] >= 2.0 - 1e-6,
            "output bounds should contain 2.0 at index {i}"
        );
    }
}

#[test]
fn test_layernorm_forward_gamma_scaling() {
    // Uniform input, gamma=3, beta=0 => output should be near 0 (since centered = 0)
    let lo = vec![1.0, 1.0];
    let hi = vec![1.0, 1.0];
    let gamma = vec![3.0, 3.0];
    let beta = vec![0.0, 0.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);
    for i in 0..2 {
        assert!(bounds.lower[i] <= 1e-6 && bounds.upper[i] >= -1e-6);
    }
}

#[test]
fn test_layernorm_forward_negative_gamma() {
    // Negative gamma flips the sign of the normalized output
    let lo = vec![1.0, 1.0];
    let hi = vec![1.0, 1.0];
    let gamma = vec![-2.0, -2.0];
    let beta = vec![0.0, 0.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);
    for i in 0..2 {
        assert!(bounds.lower[i] <= 1e-6 && bounds.upper[i] >= -1e-6);
    }
}

#[test]
fn test_layernorm_forward_zero_gamma() {
    // Zero gamma: output = 0 * normalized + beta = beta for all inputs
    let lo = vec![0.0, 5.0, -3.0];
    let hi = vec![10.0, 15.0, 7.0];
    let gamma = vec![0.0, 0.0, 0.0];
    let beta = vec![1.0, 2.0, 3.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);
    for (i, &b) in beta.iter().enumerate() {
        assert!(
            bounds.lower[i] <= b + 1e-6 && bounds.upper[i] >= b - 1e-6,
            "with gamma=0, output[{i}] should be beta[{i}]={}",
            b
        );
    }
}

#[test]
fn test_layernorm_forward_negative_gamma_bounds_flip() {
    // With non-uniform point input and negative gamma, bounds should flip
    let lo = vec![1.0, 3.0];
    let hi = vec![1.0, 3.0];
    let gamma_pos = vec![1.0, 1.0];
    let gamma_neg = vec![-1.0, -1.0];
    let beta = vec![0.0, 0.0];
    let bounds_pos = verify_layernorm_forward(&lo, &hi, &gamma_pos, &beta);
    let bounds_neg = verify_layernorm_forward(&lo, &hi, &gamma_neg, &beta);

    // With negative gamma, bounds should be negated
    for i in 0..2 {
        assert!(
            (bounds_pos.lower[i] + bounds_neg.upper[i]).abs() < 1e-6,
            "negative gamma should negate: pos.lo={} neg.hi={}",
            bounds_pos.lower[i],
            bounds_neg.upper[i]
        );
    }
}

#[test]
fn test_layernorm_forward_bounds_contain_exact_result() {
    // For a point input [1, 3], exact LayerNorm with gamma=1, beta=0:
    // mean = 2, var = ((1-2)^2 + (3-2)^2)/2 = 1, sigma = 1
    // normalized: [(1-2)/sqrt(1+eps), (3-2)/sqrt(1+eps)]
    let lo = vec![1.0, 3.0];
    let hi = vec![1.0, 3.0];
    let gamma = vec![1.0, 1.0];
    let beta = vec![0.0, 0.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);

    let eps: f64 = 1e-5;
    let expected_0 = -1.0 / (1.0_f64 + eps).sqrt();
    let expected_1 = 1.0 / (1.0_f64 + eps).sqrt();

    assert!(
        bounds.lower[0] <= expected_0 + 1e-6 && bounds.upper[0] >= expected_0 - 1e-6,
        "bounds at 0 should contain {expected_0}: [{}, {}]",
        bounds.lower[0],
        bounds.upper[0]
    );
    assert!(
        bounds.lower[1] <= expected_1 + 1e-6 && bounds.upper[1] >= expected_1 - 1e-6,
        "bounds at 1 should contain {expected_1}: [{}, {}]",
        bounds.lower[1],
        bounds.upper[1]
    );
}

#[test]
fn test_layernorm_forward_mean_bounds_correct() {
    let lo = vec![0.0, 2.0];
    let hi = vec![4.0, 6.0];
    let gamma = vec![1.0, 1.0];
    let beta = vec![0.0, 0.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);
    // mean_lo = (0+2)/2 = 1, mean_hi = (4+6)/2 = 5
    assert!((bounds.mean_bounds.0 - 1.0).abs() < 1e-10);
    assert!((bounds.mean_bounds.1 - 5.0).abs() < 1e-10);
}

#[test]
fn test_layernorm_forward_variance_bounds_nonnegative() {
    let lo = vec![-5.0, -3.0, 1.0, 7.0];
    let hi = vec![5.0, 3.0, 9.0, 15.0];
    let gamma = vec![1.0, 1.0, 1.0, 1.0];
    let beta = vec![0.0, 0.0, 0.0, 0.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);
    assert!(
        bounds.variance_bounds.0 >= -1e-10,
        "variance lower bound must be non-negative"
    );
    assert!(
        bounds.variance_bounds.1 >= bounds.variance_bounds.0 - 1e-10,
        "variance upper must be >= lower"
    );
}

#[test]
fn test_layernorm_forward_output_bounds_ordered() {
    let lo = vec![0.0, 1.0, 2.0];
    let hi = vec![3.0, 4.0, 5.0];
    let gamma = vec![1.0, 2.0, 0.5];
    let beta = vec![0.0, 1.0, -1.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);
    for i in 0..3 {
        assert!(
            bounds.lower[i] <= bounds.upper[i] + 1e-10,
            "lower[{i}]={} must be <= upper[{i}]={}",
            bounds.lower[i],
            bounds.upper[i]
        );
    }
}

#[test]
fn test_layernorm_forward_single_element() {
    // Single element: mean = x, centered = 0, normalized = 0
    // output = gamma * 0 + beta = beta
    let lo = vec![3.0];
    let hi = vec![7.0];
    let gamma = vec![2.0];
    let beta = vec![5.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);
    assert!(
        bounds.lower[0] <= 5.0 + 1e-6 && bounds.upper[0] >= 5.0 - 1e-6,
        "single element LayerNorm output should contain beta=5.0"
    );
}

#[test]
fn test_layernorm_forward_two_element_analytic() {
    // 2-element input [a, b] with exact values: a=0, b=4
    // mean = 2, var = ((0-2)^2 + (4-2)^2)/2 = 4
    // normalized = [(0-2)/sqrt(4+eps), (4-2)/sqrt(4+eps)]
    //            = [-2/sqrt(4+eps), 2/sqrt(4+eps)]
    // With gamma=[1,1], beta=[0,0]: output = normalized
    let lo = vec![0.0, 4.0];
    let hi = vec![0.0, 4.0];
    let gamma = vec![1.0, 1.0];
    let beta = vec![0.0, 0.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);

    let eps = 1e-5;
    let expected_0 = -2.0 / (4.0_f64 + eps).sqrt();
    let expected_1 = 2.0 / (4.0_f64 + eps).sqrt();

    assert!(
        bounds.lower[0] <= expected_0 + 1e-6 && bounds.upper[0] >= expected_0 - 1e-6,
        "2-element analytic: bounds[0] should contain {expected_0}: [{}, {}]",
        bounds.lower[0],
        bounds.upper[0]
    );
    assert!(
        bounds.lower[1] <= expected_1 + 1e-6 && bounds.upper[1] >= expected_1 - 1e-6,
        "2-element analytic: bounds[1] should contain {expected_1}: [{}, {}]",
        bounds.lower[1],
        bounds.upper[1]
    );
}

#[test]
fn test_layernorm_forward_soundness_random_sampling() {
    // For random inputs within bounds, verify LayerNorm output is within computed bounds
    let lo = vec![0.0, 1.0, 2.0, 3.0];
    let hi = vec![5.0, 6.0, 7.0, 8.0];
    let gamma = vec![1.0, 0.5, 2.0, -1.0];
    let beta = vec![0.0, 1.0, -1.0, 0.5];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);

    let mut rng: u64 = 99999;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };

    let eps = 1e-5;
    for _ in 0..100 {
        let x: Vec<f64> = lo
            .iter()
            .zip(hi.iter())
            .map(|(&l, &u)| l + lcg(&mut rng) * (u - l))
            .collect();
        let d = x.len() as f64;
        let mean = x.iter().sum::<f64>() / d;
        let var = x.iter().map(|xi| (xi - mean).powi(2)).sum::<f64>() / d;
        let sigma = (var + eps).sqrt();

        for (i, &xi) in x.iter().enumerate() {
            let normalized = (xi - mean) / sigma;
            let output = gamma[i] * normalized + beta[i];
            assert!(
                bounds.lower[i] <= output + 1e-6,
                "output[{i}]={output} < lower[{i}]={}",
                bounds.lower[i]
            );
            assert!(
                output <= bounds.upper[i] + 1e-6,
                "output[{i}]={output} > upper[{i}]={}",
                bounds.upper[i]
            );
        }
    }
}

#[test]
fn test_layernorm_forward_transformer_scale() {
    // Transformer-scale: d=768 with realistic gamma/beta distributions
    let d = 768;
    let mut rng: u64 = 42;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };

    let lo: Vec<f64> = (0..d).map(|_| -1.0 + lcg(&mut rng) * 0.5).collect();
    let hi: Vec<f64> = lo.iter().map(|&l| l + 0.1 + lcg(&mut rng) * 0.5).collect();
    // Gamma near 1.0, beta near 0.0 (typical initialization)
    let gamma: Vec<f64> = (0..d).map(|_| 0.9 + lcg(&mut rng) * 0.2).collect();
    let beta: Vec<f64> = (0..d).map(|_| -0.1 + lcg(&mut rng) * 0.2).collect();

    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);

    // Basic sanity: all bounds should be ordered
    for i in 0..d {
        assert!(
            bounds.lower[i] <= bounds.upper[i] + 1e-6,
            "transformer-scale: lower[{i}] > upper[{i}]"
        );
    }
    // Variance should be non-negative
    assert!(bounds.variance_bounds.0 >= -1e-10);
    assert!(bounds.variance_bounds.1 >= bounds.variance_bounds.0 - 1e-10);
}

#[test]
fn test_layernorm_forward_numerical_stability_small() {
    // Very small input values near floating-point underflow
    let lo = vec![1e-300, 2e-300, 3e-300];
    let hi = vec![1e-300, 2e-300, 3e-300];
    let gamma = vec![1.0, 1.0, 1.0];
    let beta = vec![0.0, 0.0, 0.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);
    for i in 0..3 {
        assert!(
            bounds.lower[i].is_finite() && bounds.upper[i].is_finite(),
            "small inputs should produce finite bounds at index {i}"
        );
        assert!(bounds.lower[i] <= bounds.upper[i] + 1e-6);
    }
}

#[test]
fn test_layernorm_forward_numerical_stability_large() {
    // Very large input values
    let lo = vec![1e10, 2e10, 3e10];
    let hi = vec![1e10, 2e10, 3e10];
    let gamma = vec![1.0, 1.0, 1.0];
    let beta = vec![0.0, 0.0, 0.0];
    let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);
    for i in 0..3 {
        assert!(
            bounds.lower[i].is_finite() && bounds.upper[i].is_finite(),
            "large inputs should produce finite bounds at index {i}"
        );
        assert!(bounds.lower[i] <= bounds.upper[i] + 1e-6);
    }
}

// ============================================================================
// Parameterized dimension sweep
// ============================================================================

#[test]
fn test_layernorm_dimension_sweep_soundness() {
    // For dimensions d in [1, 2, 4, 8, 64], generate bounds and verify soundness
    let eps = 1e-5;
    for &d in &[1, 2, 4, 8, 64] {
        let mut rng: u64 = d as u64 * 1000 + 7;
        let lcg = |state: &mut u64| -> f64 {
            *state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            (*state >> 33) as f64 / (1u64 << 31) as f64
        };

        let lo: Vec<f64> = (0..d).map(|_| -5.0 + lcg(&mut rng) * 3.0).collect();
        let hi: Vec<f64> = lo.iter().map(|&l| l + 0.1 + lcg(&mut rng) * 5.0).collect();
        let gamma: Vec<f64> = (0..d).map(|_| -2.0 + lcg(&mut rng) * 4.0).collect();
        let beta: Vec<f64> = (0..d).map(|_| -1.0 + lcg(&mut rng) * 2.0).collect();

        let bounds = verify_layernorm_forward(&lo, &hi, &gamma, &beta);

        // Verify bounds are ordered
        for i in 0..d {
            assert!(
                bounds.lower[i] <= bounds.upper[i] + 1e-6,
                "d={d}, bounds not ordered at index {i}"
            );
        }

        // Verify soundness with random samples
        for _ in 0..50 {
            let x: Vec<f64> = lo
                .iter()
                .zip(hi.iter())
                .map(|(&l, &u)| l + lcg(&mut rng) * (u - l))
                .collect();
            let df = x.len() as f64;
            let mean = x.iter().sum::<f64>() / df;
            let var = x.iter().map(|xi| (xi - mean).powi(2)).sum::<f64>() / df;
            let sigma = (var + eps).sqrt();

            for (i, &xi) in x.iter().enumerate() {
                let normalized = (xi - mean) / sigma;
                let output = gamma[i] * normalized + beta[i];
                assert!(
                    bounds.lower[i] <= output + 1e-4,
                    "d={d}, output[{i}]={output} < lower={}",
                    bounds.lower[i]
                );
                assert!(
                    output <= bounds.upper[i] + 1e-4,
                    "d={d}, output[{i}]={output} > upper={}",
                    bounds.upper[i]
                );
            }
        }
    }
}

// ============================================================================
// Proof spec tests
// ============================================================================

#[test]
fn test_layernorm_center_spec_status() {
    let spec = LayerNormCenterSpec::new();
    assert_eq!(
        spec.status(),
        crate::spec::ProofStatus::DerivedPending,
        "T20 should be DerivedPending"
    );
}

#[test]
fn test_layernorm_scale_spec_status() {
    let spec = LayerNormScaleSpec::new();
    assert_eq!(
        spec.status(),
        crate::spec::ProofStatus::DerivedPending,
        "T21 should be DerivedPending"
    );
}

#[test]
fn test_layernorm_full_spec_status() {
    let spec = LayerNormFullSpec::new();
    assert_eq!(
        spec.status(),
        crate::spec::ProofStatus::DerivedPending,
        "T22 should be DerivedPending"
    );
}

#[test]
fn test_layernorm_specs_default() {
    let center = LayerNormCenterSpec::default();
    let scale = LayerNormScaleSpec::default();
    let full = LayerNormFullSpec::default();
    assert_eq!(center.status(), crate::spec::ProofStatus::DerivedPending);
    assert_eq!(scale.status(), crate::spec::ProofStatus::DerivedPending);
    assert_eq!(full.status(), crate::spec::ProofStatus::DerivedPending);
}
