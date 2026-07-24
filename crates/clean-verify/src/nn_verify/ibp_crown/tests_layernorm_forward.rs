// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for tuple-based layernorm_forward functions (compute_mean_interval,
//! compute_centered_bounds, compute_variance_interval, compute_inv_sqrt_interval,
//! layernorm_forward_bounds, verify_layernorm_containment).

use super::layernorm_forward::*;

/// Mirror of the private DEFAULT_EPS constant for testing.
const TEST_EPS: f64 = 1e-5;

// --- compute_mean_interval tests ---

#[test]
fn test_mean_interval_uniform() {
    let bounds = vec![(2.0, 4.0), (2.0, 4.0), (2.0, 4.0)];
    let (lo, hi) = compute_mean_interval(&bounds);
    assert!((lo - 2.0).abs() < 1e-10);
    assert!((hi - 4.0).abs() < 1e-10);
}

#[test]
fn test_mean_interval_mixed() {
    let bounds = vec![(0.0, 10.0), (4.0, 6.0)];
    let (lo, hi) = compute_mean_interval(&bounds);
    assert!((lo - 2.0).abs() < 1e-10);
    assert!((hi - 8.0).abs() < 1e-10);
}

#[test]
fn test_mean_interval_single_element() {
    let bounds = vec![(3.0, 7.0)];
    let (lo, hi) = compute_mean_interval(&bounds);
    assert!((lo - 3.0).abs() < 1e-10);
    assert!((hi - 7.0).abs() < 1e-10);
}

#[test]
fn test_mean_interval_negative_values() {
    let bounds = vec![(-10.0, -2.0), (-6.0, -1.0), (-8.0, -3.0)];
    let (lo, hi) = compute_mean_interval(&bounds);
    assert!((lo - (-8.0)).abs() < 1e-10);
    assert!((hi - (-2.0)).abs() < 1e-10);
}

#[test]
fn test_mean_interval_point_intervals() {
    let bounds = vec![(1.0, 1.0), (3.0, 3.0), (5.0, 5.0)];
    let (lo, hi) = compute_mean_interval(&bounds);
    assert!((lo - 3.0).abs() < 1e-10);
    assert!((hi - 3.0).abs() < 1e-10);
}

// --- compute_centered_bounds tests ---

#[test]
fn test_centered_bounds_zero_mean() {
    let bounds = vec![(1.0, 3.0), (2.0, 4.0)];
    let mean = (0.0, 0.0);
    let centered = compute_centered_bounds(&bounds, mean);
    assert!((centered[0].0 - 1.0).abs() < 1e-10);
    assert!((centered[0].1 - 3.0).abs() < 1e-10);
    assert!((centered[1].0 - 2.0).abs() < 1e-10);
    assert!((centered[1].1 - 4.0).abs() < 1e-10);
}

#[test]
fn test_centered_bounds_nonzero_mean() {
    let bounds = vec![(1.0, 5.0), (3.0, 7.0)];
    let mean = (2.0, 4.0);
    let centered = compute_centered_bounds(&bounds, mean);
    assert!((centered[0].0 - (-3.0)).abs() < 1e-10);
    assert!((centered[0].1 - 3.0).abs() < 1e-10);
    assert!((centered[1].0 - (-1.0)).abs() < 1e-10);
    assert!((centered[1].1 - 5.0).abs() < 1e-10);
}

#[test]
fn test_centered_bounds_point_mean() {
    let bounds = vec![(0.0, 10.0)];
    let mean = (5.0, 5.0);
    let centered = compute_centered_bounds(&bounds, mean);
    assert!((centered[0].0 - (-5.0)).abs() < 1e-10);
    assert!((centered[0].1 - 5.0).abs() < 1e-10);
}

// --- compute_variance_interval tests ---

#[test]
fn test_variance_interval_all_same() {
    let centered = vec![(0.0, 0.0), (0.0, 0.0), (0.0, 0.0)];
    let (lo, hi) = compute_variance_interval(&centered);
    assert!(lo.abs() < 1e-10);
    assert!(hi.abs() < 1e-10);
}

#[test]
fn test_variance_interval_varied() {
    let centered = vec![(-2.0, 2.0), (-1.0, 1.0)];
    let (lo, hi) = compute_variance_interval(&centered);
    assert!(lo.abs() < 1e-10);
    assert!((hi - 2.5).abs() < 1e-10);
}

#[test]
fn test_variance_interval_point_intervals() {
    let centered = vec![(3.0, 3.0), (-1.0, -1.0)];
    let (lo, hi) = compute_variance_interval(&centered);
    assert!((lo - 5.0).abs() < 1e-10);
    assert!((hi - 5.0).abs() < 1e-10);
}

#[test]
fn test_variance_interval_positive_range() {
    let centered = vec![(1.0, 3.0)];
    let (lo, hi) = compute_variance_interval(&centered);
    assert!((lo - 1.0).abs() < 1e-10);
    assert!((hi - 9.0).abs() < 1e-10);
}

#[test]
fn test_variance_interval_negative_range() {
    let centered = vec![(-4.0, -2.0)];
    let (lo, hi) = compute_variance_interval(&centered);
    assert!((lo - 4.0).abs() < 1e-10);
    assert!((hi - 16.0).abs() < 1e-10);
}

#[test]
fn test_variance_interval_nonnegative() {
    let test_cases: Vec<Vec<(f64, f64)>> = vec![
        vec![(-5.0, 5.0), (-3.0, 3.0)],
        vec![(-1.0, 0.0), (0.0, 1.0)],
        vec![(0.0, 0.0)],
        vec![(10.0, 20.0), (-20.0, -10.0)],
    ];
    for centered in &test_cases {
        let (lo, hi) = compute_variance_interval(centered);
        assert!(lo >= -1e-10, "variance lower must be non-negative");
        assert!(hi >= lo - 1e-10, "variance upper >= lower");
    }
}

// --- compute_inv_sqrt_interval tests ---

#[test]
fn test_inv_sqrt_interval_small_epsilon() {
    let (lo, hi) = compute_inv_sqrt_interval((1.0, 4.0), 1e-5);
    assert!((lo - 1.0 / (4.0 + 1e-5_f64).sqrt()).abs() < 1e-10);
    assert!((hi - 1.0 / (1.0 + 1e-5_f64).sqrt()).abs() < 1e-10);
}

#[test]
fn test_inv_sqrt_interval_large_variance() {
    let (lo, hi) = compute_inv_sqrt_interval((100.0, 10000.0), 0.01);
    assert!((lo - 1.0 / (10000.01_f64).sqrt()).abs() < 1e-10);
    assert!((hi - 1.0 / (100.01_f64).sqrt()).abs() < 1e-10);
    assert!(lo < hi, "inv_sqrt lo < hi since 1/sqrt is decreasing");
}

#[test]
fn test_inv_sqrt_interval_point_variance() {
    let (lo, hi) = compute_inv_sqrt_interval((4.0, 4.0), 1e-10);
    assert!((lo - 0.5).abs() < 1e-6);
    assert!((hi - 0.5).abs() < 1e-6);
}

#[test]
fn test_inv_sqrt_interval_zero_variance() {
    let (lo, hi) = compute_inv_sqrt_interval((0.0, 0.0), 1.0);
    assert!((lo - 1.0).abs() < 1e-10);
    assert!((hi - 1.0).abs() < 1e-10);
}

#[test]
fn test_inv_sqrt_interval_monotonicity() {
    let (lo_narrow, hi_narrow) = compute_inv_sqrt_interval((3.0, 5.0), 1e-5);
    let (lo_wide, hi_wide) = compute_inv_sqrt_interval((1.0, 10.0), 1e-5);
    assert!(lo_wide <= lo_narrow + 1e-10);
    assert!(hi_wide >= hi_narrow - 1e-10);
}

// --- layernorm_forward_bounds tests ---

#[test]
fn test_forward_bounds_identity_gamma_beta() {
    let input = vec![(5.0, 5.0), (5.0, 5.0), (5.0, 5.0)];
    let gamma = vec![1.0, 1.0, 1.0];
    let beta = vec![0.0, 0.0, 0.0];
    let output = layernorm_forward_bounds(&input, &gamma, &beta, TEST_EPS);
    for (i, out) in output.iter().enumerate() {
        assert!(out.0 <= 1e-6, "lower[{i}] should be near 0");
        assert!(out.1 >= -1e-6, "upper[{i}] should be near 0");
    }
}

#[test]
fn test_forward_bounds_scaling() {
    let input = vec![(1.0, 1.0), (3.0, 3.0)];
    let gamma = vec![2.0, 2.0];
    let beta = vec![1.0, 1.0];
    let output = layernorm_forward_bounds(&input, &gamma, &beta, TEST_EPS);

    let eps: f64 = TEST_EPS;
    let inv_sigma = 1.0 / (1.0_f64 + eps).sqrt();
    let expected_0 = 2.0 * -inv_sigma + 1.0;
    let expected_1 = 2.0 * (1.0 * inv_sigma) + 1.0;

    assert!(output[0].0 <= expected_0 + 1e-6 && output[0].1 >= expected_0 - 1e-6);
    assert!(output[1].0 <= expected_1 + 1e-6 && output[1].1 >= expected_1 - 1e-6);
}

#[test]
fn test_forward_bounds_2d() {
    let input = vec![(0.0, 2.0), (3.0, 5.0)];
    let gamma = vec![1.0, 1.0];
    let beta = vec![0.0, 0.0];
    let output = layernorm_forward_bounds(&input, &gamma, &beta, TEST_EPS);
    for (i, out) in output.iter().enumerate() {
        assert!(out.0 <= out.1 + 1e-6, "bounds must be ordered at {i}");
    }
}

#[test]
fn test_forward_bounds_3d() {
    let input = vec![(1.0, 2.0), (3.0, 4.0), (5.0, 6.0)];
    let gamma = vec![1.0, 1.0, 1.0];
    let beta = vec![0.0, 0.0, 0.0];
    let output = layernorm_forward_bounds(&input, &gamma, &beta, TEST_EPS);
    assert_eq!(output.len(), 3);
    for (i, out) in output.iter().enumerate() {
        assert!(out.0 <= out.1 + 1e-6, "bounds ordered at {i}");
        assert!(out.0.is_finite() && out.1.is_finite());
    }
}

#[test]
fn test_forward_bounds_soundness_random_sampling() {
    let input_bounds = vec![(0.0, 5.0), (1.0, 6.0), (2.0, 7.0), (3.0, 8.0)];
    let gamma = vec![1.0, 0.5, 2.0, -1.0];
    let beta = vec![0.0, 1.0, -1.0, 0.5];
    let eps = TEST_EPS;
    let output_bounds = layernorm_forward_bounds(&input_bounds, &gamma, &beta, eps);

    let mut rng: u64 = 77777;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };

    for _ in 0..100 {
        let x: Vec<f64> = input_bounds
            .iter()
            .map(|&(lo, hi)| lo + lcg(&mut rng) * (hi - lo))
            .collect();
        let d = x.len() as f64;
        let mean = x.iter().sum::<f64>() / d;
        let var = x.iter().map(|xi| (xi - mean).powi(2)).sum::<f64>() / d;
        let sigma = (var + eps).sqrt();

        for (i, &xi) in x.iter().enumerate() {
            let normalized = (xi - mean) / sigma;
            let output = gamma[i] * normalized + beta[i];
            assert!(
                output_bounds[i].0 <= output + 1e-6,
                "output[{i}]={output} < lower={}",
                output_bounds[i].0
            );
            assert!(
                output <= output_bounds[i].1 + 1e-6,
                "output[{i}]={output} > upper={}",
                output_bounds[i].1
            );
        }
    }
}

#[test]
fn test_forward_bounds_beta_only() {
    let input = vec![(0.0, 100.0), (-50.0, 50.0)];
    let gamma = vec![0.0, 0.0];
    let beta = vec![3.0, -2.0];
    let output = layernorm_forward_bounds(&input, &gamma, &beta, TEST_EPS);
    for i in 0..2 {
        assert!(
            output[i].0 <= beta[i] + 1e-6 && output[i].1 >= beta[i] - 1e-6,
            "with gamma=0, output should be beta"
        );
    }
}

// --- verify_layernorm_containment tests ---

#[test]
fn test_containment_within_bounds() {
    let input = vec![(0.0, 4.0), (2.0, 6.0)];
    let gamma = vec![1.0, 1.0];
    let beta = vec![0.0, 0.0];
    let eps = TEST_EPS;
    let output_bounds = layernorm_forward_bounds(&input, &gamma, &beta, eps);

    let concrete = vec![2.0, 4.0];
    assert!(
        verify_layernorm_containment(&concrete, &output_bounds, &gamma, &beta, eps),
        "input within bounds should pass containment check"
    );
}

#[test]
fn test_containment_boundary_values() {
    let input = vec![(1.0, 3.0), (2.0, 4.0)];
    let gamma = vec![1.0, 1.0];
    let beta = vec![0.0, 0.0];
    let eps = TEST_EPS;
    let output_bounds = layernorm_forward_bounds(&input, &gamma, &beta, eps);

    assert!(verify_layernorm_containment(
        &[1.0, 2.0],
        &output_bounds,
        &gamma,
        &beta,
        eps
    ));
    assert!(verify_layernorm_containment(
        &[3.0, 4.0],
        &output_bounds,
        &gamma,
        &beta,
        eps
    ));
    assert!(verify_layernorm_containment(
        &[1.0, 4.0],
        &output_bounds,
        &gamma,
        &beta,
        eps
    ));
    assert!(verify_layernorm_containment(
        &[3.0, 2.0],
        &output_bounds,
        &gamma,
        &beta,
        eps
    ));
}

#[test]
fn test_containment_outside_bounds_fails() {
    let input = vec![(1.0, 1.0), (3.0, 3.0)];
    let gamma = vec![1.0, 1.0];
    let beta = vec![0.0, 0.0];
    let eps = TEST_EPS;
    let output_bounds = layernorm_forward_bounds(&input, &gamma, &beta, eps);

    let far_input = vec![100.0, -100.0];
    assert!(
        !verify_layernorm_containment(&far_input, &output_bounds, &gamma, &beta, eps),
        "input far outside bounds should fail containment"
    );
}

#[test]
fn test_containment_with_gamma_beta() {
    let input = vec![(0.0, 2.0), (4.0, 6.0), (8.0, 10.0)];
    let gamma = vec![2.0, 0.5, -1.0];
    let beta = vec![1.0, -1.0, 3.0];
    let eps = 1e-3;
    let output_bounds = layernorm_forward_bounds(&input, &gamma, &beta, eps);

    let concrete = vec![1.0, 5.0, 9.0];
    assert!(
        verify_layernorm_containment(&concrete, &output_bounds, &gamma, &beta, eps),
        "concrete input in range should be contained"
    );
}

#[test]
fn test_containment_single_element() {
    let input = vec![(2.0, 8.0)];
    let gamma = vec![3.0];
    let beta = vec![5.0];
    let eps = TEST_EPS;
    let output_bounds = layernorm_forward_bounds(&input, &gamma, &beta, eps);

    let concrete = vec![4.0];
    assert!(
        verify_layernorm_containment(&concrete, &output_bounds, &gamma, &beta, eps),
        "single element should produce output=beta"
    );
}

#[test]
fn test_containment_random_sampling() {
    let input_bounds = vec![(0.0, 5.0), (1.0, 6.0), (2.0, 7.0)];
    let gamma = vec![1.5, -0.5, 2.0];
    let beta = vec![0.0, 1.0, -1.0];
    let eps = TEST_EPS;
    let output_bounds = layernorm_forward_bounds(&input_bounds, &gamma, &beta, eps);

    let mut rng: u64 = 31415;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };

    for _ in 0..200 {
        let x: Vec<f64> = input_bounds
            .iter()
            .map(|&(lo, hi)| lo + lcg(&mut rng) * (hi - lo))
            .collect();
        assert!(
            verify_layernorm_containment(&x, &output_bounds, &gamma, &beta, eps),
            "random input within bounds must pass containment"
        );
    }
}

// --- End-to-end pipeline consistency test ---

#[test]
fn test_pipeline_consistency_mean_center_variance() {
    let bounds = vec![(1.0, 3.0), (2.0, 5.0), (0.0, 4.0)];
    let mean = compute_mean_interval(&bounds);
    let centered = compute_centered_bounds(&bounds, mean);
    let var = compute_variance_interval(&centered);

    assert!(mean.0 <= mean.1 + 1e-10);
    for &(lo, hi) in &centered {
        assert!(lo <= hi + 1e-10);
    }
    assert!(var.0 >= -1e-10);
    assert!(var.1 >= var.0 - 1e-10);
}
