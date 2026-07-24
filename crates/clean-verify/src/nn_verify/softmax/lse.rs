// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Log-Sum-Exp (LSE) decomposition for softmax analysis.
//!
//! The key identity: `softmax(x)_i = exp(x_i - LSE(x))` where
//! `LSE(x) = log(sum_j exp(x_j))`. This decomposition is central to
//! deriving tight convex relaxations because:
//!
//! 1. LSE is convex (log of sum of convex functions)
//! 2. LSE is monotone in each coordinate
//! 3. `max(x) <= LSE(x) <= max(x) + log(n)` (range-based tightness)
//!
//! ## Numerical stability
//!
//! We use the shifted formulation: `LSE(x) = m + log(sum_j exp(x_j - m))`
//! where `m = max(x)`. This avoids overflow in exp().
//!
//! ## References
//!
//! - Boyd & Vandenberghe, "Convex Optimization" (2004), Section 3.1.5
//! - Shi et al., "Robustness Verification for Transformers" (ICLR 2020)

/// Compute `softmax(x)` with numerical stability via max-shift.
///
/// `softmax(x)_i = exp(x_i - max(x)) / sum_j exp(x_j - max(x))`
///
/// # Panics
///
/// Panics if `x` is empty.
#[must_use]
pub(crate) fn softmax(x: &[f64]) -> Vec<f64> {
    assert!(!x.is_empty(), "softmax requires non-empty input");

    let max_x = x.iter().copied().fold(f64::NEG_INFINITY, f64::max);
    let exps: Vec<f64> = x.iter().map(|&xi| (xi - max_x).exp()).collect();
    let sum_exp: f64 = exps.iter().sum();

    exps.iter().map(|&e| e / sum_exp).collect()
}

/// Compute `log-sum-exp(x)` with numerical stability.
///
/// `LSE(x) = max(x) + log(sum_j exp(x_j - max(x)))`
///
/// This is the normalization constant of softmax in log-space:
/// `LSE(x) = log(sum_j exp(x_j))`.
///
/// # Properties (all provable)
///
/// - **Convexity:** LSE is convex (Hessian = diag(softmax) - softmax * softmax^T is PSD)
/// - **Monotonicity:** LSE is monotonically increasing in each coordinate
/// - **Squeeze:** `max(x) <= LSE(x) <= max(x) + ln(n)`
/// - **Translation invariance:** `LSE(x + c*1) = LSE(x) + c`
///
/// # Panics
///
/// Panics if `x` is empty.
#[must_use]
pub(crate) fn log_sum_exp(x: &[f64]) -> f64 {
    assert!(!x.is_empty(), "LSE requires non-empty input");

    let max_x = x.iter().copied().fold(f64::NEG_INFINITY, f64::max);
    if max_x == f64::NEG_INFINITY {
        return f64::NEG_INFINITY;
    }

    let sum_shifted: f64 = x.iter().map(|&xi| (xi - max_x).exp()).sum();
    max_x + sum_shifted.ln()
}

/// Compute the gradient of LSE at point `x`, which is `softmax(x)`.
///
/// `nabla LSE(x) = softmax(x)`
///
/// This is used for tangent-plane linear bounds on LSE.
///
/// # Panics
///
/// Panics if `x` is empty.
#[must_use]
pub(crate) fn lse_gradient(x: &[f64]) -> Vec<f64> {
    softmax(x)
}

/// Verify the LSE squeeze property: `max(x) <= LSE(x) <= max(x) + ln(n)`.
///
/// Returns `(lower_gap, upper_gap)` where both should be non-negative
/// if the property holds. The lower gap is `LSE(x) - max(x)` and the
/// upper gap is `max(x) + ln(n) - LSE(x)`.
#[must_use]
pub(crate) fn verify_lse_squeeze(x: &[f64]) -> (f64, f64) {
    let lse = log_sum_exp(x);
    let max_x = x.iter().copied().fold(f64::NEG_INFINITY, f64::max);
    let n = x.len() as f64;

    let lower_gap = lse - max_x;
    let upper_gap = max_x + n.ln() - lse;

    (lower_gap, upper_gap)
}

/// Compute the range of a vector: `max(x) - min(x)`.
///
/// The range controls the tightness of softmax convex relaxation.
/// When range is small, softmax approaches uniform distribution (1/n),
/// making bounds tight. When range is large, softmax concentrates on
/// the argmax, and bounds are looser (but still O(range)).
///
/// # Panics
///
/// Panics if `x` is empty.
#[must_use]
pub(crate) fn input_range(x: &[f64]) -> f64 {
    assert!(!x.is_empty(), "range requires non-empty input");

    let max_x = x.iter().copied().fold(f64::NEG_INFINITY, f64::max);
    let min_x = x.iter().copied().fold(f64::INFINITY, f64::min);

    max_x - min_x
}

/// Compute softmax via LSE decomposition: `softmax(x)_i = exp(x_i - LSE(x))`.
///
/// This is mathematically equivalent to [`softmax`] but makes the LSE
/// decomposition explicit, which is useful for analysis.
///
/// # Panics
///
/// Panics if `x` is empty.
#[must_use]
pub(crate) fn softmax_via_lse(x: &[f64]) -> Vec<f64> {
    let lse = log_sum_exp(x);
    x.iter().map(|&xi| (xi - lse).exp()).collect()
}

/// Compute the Jacobian of softmax at point `x`.
///
/// `J_ij = softmax(x)_i * (delta_ij - softmax(x)_j)`
///
/// where `delta_ij` is the Kronecker delta. This Jacobian is the
/// Hessian of LSE, and its positive semidefiniteness proves LSE convexity.
///
/// Returns a row-major `n x n` matrix as `Vec<Vec<f64>>`.
///
/// # Panics
///
/// Panics if `x` is empty.
#[must_use]
pub(crate) fn softmax_jacobian(x: &[f64]) -> Vec<Vec<f64>> {
    let s = softmax(x);
    let n = s.len();
    let mut jac = vec![vec![0.0; n]; n];

    for i in 0..n {
        for j in 0..n {
            if i == j {
                jac[i][j] = s[i] * (1.0 - s[j]);
            } else {
                jac[i][j] = -s[i] * s[j];
            }
        }
    }

    jac
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-10;

    #[test]
    fn test_softmax_uniform_input() {
        let x = vec![1.0, 1.0, 1.0];
        let s = softmax(&x);
        for &si in &s {
            assert!(
                (si - 1.0 / 3.0).abs() < EPS,
                "uniform input -> uniform softmax"
            );
        }
    }

    #[test]
    fn test_softmax_sums_to_one() {
        let x = vec![1.0, 2.0, 3.0, 4.0];
        let s = softmax(&x);
        let sum: f64 = s.iter().sum();
        assert!((sum - 1.0).abs() < EPS, "softmax must sum to 1, got {sum}");
    }

    #[test]
    fn test_softmax_monotonicity() {
        let x = vec![1.0, 2.0, 3.0];
        let s = softmax(&x);
        assert!(s[0] < s[1], "softmax must be monotone");
        assert!(s[1] < s[2], "softmax must be monotone");
    }

    #[test]
    fn test_softmax_all_positive() {
        let x = vec![-100.0, 0.0, 100.0];
        let s = softmax(&x);
        for &si in &s {
            assert!(si >= 0.0, "softmax outputs must be non-negative");
            assert!(si <= 1.0, "softmax outputs must be at most 1");
        }
    }

    #[test]
    fn test_lse_squeeze_property() {
        let test_cases: Vec<Vec<f64>> = vec![
            vec![1.0, 2.0, 3.0],
            vec![0.0, 0.0, 0.0],
            vec![-5.0, 0.0, 5.0],
            vec![100.0, 100.0],
        ];

        for x in &test_cases {
            let (lower_gap, upper_gap) = verify_lse_squeeze(x);
            assert!(
                lower_gap >= -EPS,
                "LSE squeeze lower violated for {x:?}: gap = {lower_gap}"
            );
            assert!(
                upper_gap >= -EPS,
                "LSE squeeze upper violated for {x:?}: gap = {upper_gap}"
            );
        }
    }

    #[test]
    fn test_lse_translation_invariance() {
        let x = vec![1.0, 2.0, 3.0];
        let c = 5.0;
        let x_shifted: Vec<f64> = x.iter().map(|&xi| xi + c).collect();

        let lse_x = log_sum_exp(&x);
        let lse_shifted = log_sum_exp(&x_shifted);

        assert!(
            (lse_shifted - lse_x - c).abs() < EPS,
            "LSE must be translation invariant"
        );
    }

    #[test]
    fn test_softmax_via_lse_equals_direct() {
        let x = vec![1.0, 3.0, 5.0, 2.0];
        let direct = softmax(&x);
        let via_lse = softmax_via_lse(&x);

        for (d, l) in direct.iter().zip(via_lse.iter()) {
            assert!(
                (d - l).abs() < EPS,
                "softmax_via_lse must match softmax: {d} vs {l}"
            );
        }
    }

    #[test]
    fn test_lse_gradient_is_softmax() {
        let x = vec![1.0, 2.0, 3.0];
        let grad = lse_gradient(&x);
        let s = softmax(&x);

        for (g, si) in grad.iter().zip(s.iter()) {
            assert!((g - si).abs() < EPS, "LSE gradient must equal softmax");
        }
    }

    #[test]
    fn test_softmax_jacobian_row_sums_zero() {
        // Each row of the Jacobian sums to zero because softmax sums to 1
        // (differentiating sum(softmax(x)) = 1 w.r.t. x_j gives 0)
        let x = vec![1.0, 2.0, 3.0];
        let jac = softmax_jacobian(&x);

        for (i, row) in jac.iter().enumerate() {
            let row_sum: f64 = row.iter().sum();
            assert!(
                row_sum.abs() < EPS,
                "Jacobian row {i} should sum to 0, got {row_sum}"
            );
        }
    }

    #[test]
    fn test_softmax_jacobian_psd() {
        // The Jacobian = diag(s) - s*s^T is positive semidefinite
        // (it's the Hessian of LSE, and LSE is convex)
        // Test: v^T J v >= 0 for random v
        let x = vec![1.0, 2.0, 3.0];
        let jac = softmax_jacobian(&x);

        let test_vectors = vec![
            vec![1.0, 0.0, 0.0],
            vec![0.0, 1.0, 0.0],
            vec![1.0, -1.0, 0.0],
            vec![1.0, 1.0, 1.0],
            vec![3.0, -1.0, 2.0],
        ];

        for v in &test_vectors {
            let mut quadratic = 0.0;
            for i in 0..3 {
                for j in 0..3 {
                    quadratic += v[i] * jac[i][j] * v[j];
                }
            }
            assert!(
                quadratic >= -EPS,
                "Jacobian must be PSD, got v^T J v = {quadratic} for v = {v:?}"
            );
        }
    }

    #[test]
    fn test_input_range_uniform() {
        let x = vec![5.0, 5.0, 5.0];
        assert!(input_range(&x).abs() < EPS);
    }

    #[test]
    fn test_input_range_spread() {
        let x = vec![1.0, 5.0, 3.0];
        assert!((input_range(&x) - 4.0).abs() < EPS);
    }

    #[test]
    fn test_softmax_numerical_stability_large_values() {
        // Should not overflow or produce NaN for large inputs
        let x = vec![1000.0, 1001.0, 999.0];
        let s = softmax(&x);
        let sum: f64 = s.iter().sum();
        assert!((sum - 1.0).abs() < 1e-8, "must handle large values");
        assert!(s.iter().all(|si| si.is_finite()), "no NaN/Inf");
    }

    #[test]
    fn test_softmax_numerical_stability_large_negative() {
        let x = vec![-1000.0, -1001.0, -999.0];
        let s = softmax(&x);
        let sum: f64 = s.iter().sum();
        assert!(
            (sum - 1.0).abs() < 1e-8,
            "must handle large negative values"
        );
        assert!(s.iter().all(|si| si.is_finite()), "no NaN/Inf");
    }
}
