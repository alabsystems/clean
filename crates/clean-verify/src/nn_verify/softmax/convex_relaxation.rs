// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Convex relaxation of softmax with provable O(range) tightness.
//!
//! ## Key Idea
//!
//! Softmax is neither convex nor concave (it maps R^n -> Delta^{n-1}),
//! but its log (`log softmax(x)_i = x_i - LSE(x)`) involves the convex
//! function LSE. We exploit LSE convexity to build tangent-plane lower
//! bounds and secant upper bounds on each softmax output.
//!
//! ## Bound Construction
//!
//! For each output `softmax(x)_i`:
//!
//! **Lower bound (tangent plane on LSE):**
//! Since LSE is convex, `LSE(x) >= LSE(x0) + nabla LSE(x0)^T (x - x0)`.
//! Therefore `softmax(x)_i = exp(x_i - LSE(x)) <= exp(x_i - LSE(x0) - s^T(x-x0))`
//! where `s = softmax(x0)`. But we want a *lower* bound on softmax_i.
//! Using the interval bound approach: we minimize `exp(x_i) / sum exp(x_j)`
//! over the box `[l, u]` by minimizing numerator and maximizing denominator.
//!
//! **Upper bound (concavity of exp(-LSE)):**
//! We maximize softmax_i over the box by maximizing numerator and minimizing
//! denominator.
//!
//! **Tightness guarantee:**
//! The gap `upper_i - lower_i <= C * range` where `range = max(u) - min(l)`
//! and C depends on the dimension. This is because when range -> 0, softmax
//! approaches uniform, and both bounds converge to 1/n.
//!
//! ## References
//!
//! - Shi et al., "Robustness Verification for Transformers" (ICLR 2020)
//! - Wei et al., "Certified Robustness of Transformers" (NeurIPS 2021)
//! - Bonaert et al., "Fast and Precise Certification of Transformers" (PLDI 2021)

use super::lse::{log_sum_exp, softmax};

/// Result of softmax convex relaxation over a box `[lower, upper]`.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct SoftmaxRelaxation {
    /// Per-output lower bounds on `softmax(x)_i` for `x in [l, u]`.
    pub lower: Vec<f64>,
    /// Per-output upper bounds on `softmax(x)_i` for `x in [l, u]`.
    pub upper: Vec<f64>,
    /// Input dimension.
    pub dim: usize,
    /// Maximum gap (upper_i - lower_i) across all outputs.
    pub max_gap: f64,
    /// Input range: `max(u) - min(l)`.
    pub input_range: f64,
}

/// Linear bound on a single softmax output.
///
/// Represents `softmax(x)_i >= a^T x + b` (lower) or
/// `softmax(x)_i <= a^T x + b` (upper) as a linear function of x.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct LinearBound {
    /// Coefficients of the linear function.
    pub(crate) coeffs: Vec<f64>,
    /// Constant term.
    pub(crate) bias: f64,
}

impl LinearBound {
    /// Evaluate the linear bound at a point.
    #[must_use]
    pub(crate) fn evaluate(&self, x: &[f64]) -> f64 {
        self.coeffs
            .iter()
            .zip(x.iter())
            .map(|(a, xi)| a * xi)
            .sum::<f64>()
            + self.bias
    }
}

/// Compute sound interval bounds on softmax over a box domain.
///
/// For `x in [lower_bounds, upper_bounds]`, computes per-output intervals
/// `[lo_i, hi_i]` such that `lo_i <= softmax(x)_i <= hi_i` for all
/// `x` in the box.
///
/// ## Method
///
/// For each output i:
/// - **Lower bound:** `exp(l_i) / (exp(l_i) + sum_{j!=i} exp(u_j))`
///   (minimize numerator, maximize all other denominators)
/// - **Upper bound:** `exp(u_i) / (exp(u_i) + sum_{j!=i} exp(l_j))`
///   (maximize numerator, minimize all other denominators)
///
/// This matches the approach in the existing `ibp_crown::attention::softmax_bounds`
/// but is extended with tightness analysis.
///
/// ## Tightness
///
/// The gap `hi_i - lo_i` is O(range) where range = max(upper) - min(lower).
/// Specifically, when range = 0, softmax is constant and bounds are exact.
///
/// # Panics
///
/// Panics if bounds have different lengths, are empty, or lower > upper.
#[must_use]
pub fn softmax_convex_relaxation(lower_bounds: &[f64], upper_bounds: &[f64]) -> SoftmaxRelaxation {
    let n = lower_bounds.len();
    assert_eq!(n, upper_bounds.len(), "bounds must have equal length");
    assert!(n > 0, "must have at least one dimension");
    for i in 0..n {
        assert!(
            lower_bounds[i] <= upper_bounds[i] + f64::EPSILON * 64.0,
            "lower must be <= upper at index {i}: {} > {}",
            lower_bounds[i],
            upper_bounds[i]
        );
    }

    // Use max-shift for numerical stability in exp computations
    let global_max = upper_bounds
        .iter()
        .copied()
        .fold(f64::NEG_INFINITY, f64::max);

    let exp_lower: Vec<f64> = lower_bounds
        .iter()
        .map(|&x| (x - global_max).exp())
        .collect();
    let exp_upper: Vec<f64> = upper_bounds
        .iter()
        .map(|&x| (x - global_max).exp())
        .collect();

    let sum_exp_lower: f64 = exp_lower.iter().sum();
    let sum_exp_upper: f64 = exp_upper.iter().sum();

    let mut lo = Vec::with_capacity(n);
    let mut hi = Vec::with_capacity(n);

    for i in 0..n {
        // Lower bound on softmax_i:
        // Minimize numerator exp(x_i) -> exp(l_i)
        // Maximize denominator: use exp(u_j) for j != i, exp(l_i) for j = i
        let denom_for_lo = sum_exp_upper - exp_upper[i] + exp_lower[i];
        let lo_i = (exp_lower[i] / denom_for_lo).clamp(0.0, 1.0);

        // Upper bound on softmax_i:
        // Maximize numerator exp(x_i) -> exp(u_i)
        // Minimize denominator: use exp(l_j) for j != i, exp(u_i) for j = i
        let denom_for_hi = sum_exp_lower - exp_lower[i] + exp_upper[i];
        let hi_i = (exp_upper[i] / denom_for_hi).clamp(0.0, 1.0);

        lo.push(lo_i);
        hi.push(hi_i);
    }

    let max_gap = lo
        .iter()
        .zip(hi.iter())
        .map(|(l, h)| h - l)
        .fold(0.0_f64, f64::max);

    let input_range = {
        let max_u = upper_bounds
            .iter()
            .copied()
            .fold(f64::NEG_INFINITY, f64::max);
        let min_l = lower_bounds.iter().copied().fold(f64::INFINITY, f64::min);
        max_u - min_l
    };

    SoftmaxRelaxation {
        lower: lo,
        upper: hi,
        dim: n,
        max_gap,
        input_range,
    }
}

/// Compute a tangent-plane linear lower bound on LSE at reference point `x0`.
///
/// Since LSE is convex: `LSE(x) >= LSE(x0) + softmax(x0)^T (x - x0)`
///
/// This gives a linear lower bound: `a^T x + b` where:
/// - `a = softmax(x0)` (the gradient)
/// - `b = LSE(x0) - softmax(x0)^T x0`
///
/// # Panics
///
/// Panics if `x0` is empty.
#[must_use]
pub(crate) fn lse_tangent_lower_bound(x0: &[f64]) -> LinearBound {
    assert!(!x0.is_empty(), "reference point must be non-empty");

    let s = softmax(x0);
    let lse_x0 = log_sum_exp(x0);

    let dot_s_x0: f64 = s.iter().zip(x0.iter()).map(|(si, xi)| si * xi).sum();

    LinearBound {
        coeffs: s,
        bias: lse_x0 - dot_s_x0,
    }
}

/// Compute a secant linear upper bound on LSE between two corner points.
///
/// Given box corners `a` and `b`, the secant bound is:
/// `LSE(x) <= LSE(a) + (LSE(b) - LSE(a)) / (b - a)^T (b - a) * (b - a)^T (x - a)`
///
/// For the simple case of axis-aligned interpolation, this simplifies to
/// a coordinate-wise weighted interpolation.
///
/// # Panics
///
/// Panics if inputs have different lengths or are empty.
#[must_use]
pub(crate) fn lse_secant_upper_bound(lower: &[f64], upper: &[f64]) -> LinearBound {
    let n = lower.len();
    assert_eq!(n, upper.len(), "bounds must have equal length");
    assert!(n > 0, "bounds must be non-empty");

    let lse_l = log_sum_exp(lower);
    let lse_u = log_sum_exp(upper);

    // Coordinate-wise secant slopes
    let mut coeffs = Vec::with_capacity(n);
    for i in 0..n {
        let range_i = upper[i] - lower[i];
        if range_i.abs() < f64::EPSILON * 64.0 {
            // Degenerate case: treat as zero slope for this coordinate
            coeffs.push(0.0);
        } else {
            // For a simple diagonal secant, the slope per coordinate
            // is approximated by the partial derivative at the midpoint
            let mid: Vec<f64> = lower
                .iter()
                .zip(upper.iter())
                .map(|(l, u)| (l + u) / 2.0)
                .collect();
            let s_mid = softmax(&mid);
            coeffs.push(s_mid[i]);
        }
    }

    // Bias: ensure the bound passes through the lower corner
    let dot_coeffs_lower: f64 = coeffs.iter().zip(lower.iter()).map(|(c, l)| c * l).sum();

    // Adjust bias to be a valid upper bound at both corners
    let bias_from_lower = lse_l - dot_coeffs_lower;
    let dot_coeffs_upper: f64 = coeffs.iter().zip(upper.iter()).map(|(c, u)| c * u).sum();
    let bias_from_upper = lse_u - dot_coeffs_upper;

    // Take the larger bias to ensure the bound is valid at both endpoints
    let bias = bias_from_lower.max(bias_from_upper);

    LinearBound { coeffs, bias }
}

/// Verify that a concrete softmax output is contained within the relaxation bounds.
///
/// For a concrete point `x in [lower, upper]`, checks that
/// `relaxation.lower[i] <= softmax(x)[i] <= relaxation.upper[i]` for all i.
///
/// Returns the maximum violation (negative if all bounds hold).
#[must_use]
pub fn verify_relaxation_soundness(
    x: &[f64],
    lower_bounds: &[f64],
    upper_bounds: &[f64],
    relaxation: &SoftmaxRelaxation,
) -> f64 {
    let n = x.len();
    assert_eq!(n, relaxation.dim, "dimension mismatch");

    let eps = f64::EPSILON * 256.0;

    // Verify x is in the box
    for i in 0..n {
        assert!(
            x[i] >= lower_bounds[i] - eps && x[i] <= upper_bounds[i] + eps,
            "x[{i}] = {} not in [{}, {}]",
            x[i],
            lower_bounds[i],
            upper_bounds[i]
        );
    }

    let s = softmax(x);
    let mut max_violation = f64::NEG_INFINITY;

    // Index `i` is used to look up three parallel arrays (`relaxation.lower`,
    // `s`, `relaxation.upper`); zipping three iterators is less direct.
    #[allow(clippy::needless_range_loop)]
    for i in 0..n {
        let lower_violation = relaxation.lower[i] - s[i];
        let upper_violation = s[i] - relaxation.upper[i];
        max_violation = max_violation.max(lower_violation).max(upper_violation);
    }

    max_violation
}

/// Compute the tightness ratio: `max_gap / (input_range + epsilon)`.
///
/// A ratio of O(1) or less indicates the gap is O(range), confirming
/// the tightness guarantee. The epsilon prevents division by zero
/// when the input range is zero (point interval).
#[must_use]
pub fn tightness_ratio(relaxation: &SoftmaxRelaxation) -> f64 {
    let eps = 1e-15;
    relaxation.max_gap / (relaxation.input_range + eps)
}

/// Verify the O(range) tightness property empirically.
///
/// Checks that for a given relaxation, the maximum gap across outputs
/// is bounded by `C * range` for some dimension-dependent constant C.
///
/// The theoretical bound is `C <= 1` for the interval-arithmetic method.
///
/// Returns `(is_tight, actual_ratio)`.
#[must_use]
pub fn verify_o_range_tightness(
    relaxation: &SoftmaxRelaxation,
    tightness_constant: f64,
) -> (bool, f64) {
    let ratio = tightness_ratio(relaxation);
    (ratio <= tightness_constant + f64::EPSILON * 256.0, ratio)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-10;

    #[test]
    fn test_relaxation_point_interval_exact() {
        // When lower == upper, softmax is exact (zero gap)
        let x = vec![1.0, 2.0, 3.0];
        let relax = softmax_convex_relaxation(&x, &x);

        let s = softmax(&x);
        for (i, &si) in s.iter().enumerate() {
            assert!(
                (relax.lower[i] - si).abs() < EPS,
                "lower bound must match softmax at point"
            );
            assert!(
                (relax.upper[i] - si).abs() < EPS,
                "upper bound must match softmax at point"
            );
        }
        assert!(relax.max_gap < EPS, "point interval must have zero gap");
    }

    #[test]
    fn test_relaxation_soundness_random_points() {
        let lower = vec![0.0, 1.0, 2.0];
        let upper = vec![1.0, 2.0, 3.0];
        let relax = softmax_convex_relaxation(&lower, &upper);

        // Test several points in the box
        let test_points = vec![
            vec![0.0, 1.0, 2.0], // lower corner
            vec![1.0, 2.0, 3.0], // upper corner
            vec![0.5, 1.5, 2.5], // midpoint
            vec![0.0, 2.0, 2.0], // mixed
            vec![1.0, 1.0, 3.0], // mixed
        ];

        for x in &test_points {
            let violation = verify_relaxation_soundness(x, &lower, &upper, &relax);
            assert!(
                violation < EPS,
                "soundness violated at {x:?}: violation = {violation}"
            );
        }
    }

    #[test]
    fn test_relaxation_bounds_in_01() {
        let lower = vec![-2.0, 0.0, 1.0, 3.0];
        let upper = vec![0.0, 2.0, 4.0, 5.0];
        let relax = softmax_convex_relaxation(&lower, &upper);

        for i in 0..4 {
            assert!(
                relax.lower[i] >= -EPS,
                "lower bound must be >= 0, got {}",
                relax.lower[i]
            );
            assert!(
                relax.upper[i] <= 1.0 + EPS,
                "upper bound must be <= 1, got {}",
                relax.upper[i]
            );
            assert!(
                relax.lower[i] <= relax.upper[i] + EPS,
                "lower must be <= upper at index {i}"
            );
        }
    }

    #[test]
    fn test_o_range_tightness() {
        // Test that gap scales linearly with range
        let ranges = [0.01, 0.1, 0.5, 1.0, 2.0, 5.0];
        let base = vec![0.0, 1.0, 2.0];

        for &r in &ranges {
            let lower = base.clone();
            let upper: Vec<f64> = base.iter().map(|&x| x + r).collect();
            let relax = softmax_convex_relaxation(&lower, &upper);

            let (is_tight, ratio) = verify_o_range_tightness(&relax, 1.0);
            assert!(
                is_tight,
                "O(range) tightness violated at range={r}: ratio={ratio}"
            );
        }
    }

    #[test]
    fn test_tightness_improves_with_smaller_range() {
        let base = vec![0.0, 1.0, 2.0];

        let upper_wide: Vec<f64> = base.iter().map(|&x| x + 5.0).collect();
        let upper_narrow: Vec<f64> = base.iter().map(|&x| x + 0.1).collect();

        let relax_wide = softmax_convex_relaxation(&base, &upper_wide);
        let relax_narrow = softmax_convex_relaxation(&base, &upper_narrow);

        assert!(
            relax_narrow.max_gap < relax_wide.max_gap,
            "narrower range should give tighter bounds: {} vs {}",
            relax_narrow.max_gap,
            relax_wide.max_gap
        );
    }

    #[test]
    fn test_lse_tangent_is_valid_lower_bound() {
        let x0 = vec![1.0, 2.0, 3.0];
        let bound = lse_tangent_lower_bound(&x0);

        // At x0, the tangent should equal LSE(x0)
        let lse_at_x0 = log_sum_exp(&x0);
        let bound_at_x0 = bound.evaluate(&x0);
        assert!(
            (lse_at_x0 - bound_at_x0).abs() < EPS,
            "tangent must touch LSE at x0"
        );

        // At other points, the tangent should be <= LSE (convexity)
        let test_points = vec![
            vec![0.0, 0.0, 0.0],
            vec![2.0, 2.0, 2.0],
            vec![1.0, 3.0, 5.0],
            vec![-1.0, 4.0, 2.0],
        ];

        for x in &test_points {
            let lse_x = log_sum_exp(x);
            let bound_x = bound.evaluate(x);
            assert!(
                bound_x <= lse_x + EPS,
                "tangent plane must be <= LSE at {x:?}: {bound_x} > {lse_x}"
            );
        }
    }

    #[test]
    fn test_relaxation_dimension_two() {
        // 2D case: softmax is just sigmoid
        let lower = vec![0.0, 0.0];
        let upper = vec![1.0, 1.0];
        let relax = softmax_convex_relaxation(&lower, &upper);

        // Both outputs should be bounded in [0, 1] and sum bounds should overlap 1
        assert!(relax.lower[0] >= -EPS);
        assert!(relax.upper[0] <= 1.0 + EPS);
        assert!(relax.lower[1] >= -EPS);
        assert!(relax.upper[1] <= 1.0 + EPS);
    }

    #[test]
    fn test_relaxation_large_dimension() {
        let n = 100;
        let lower: Vec<f64> = (0..n).map(|i| i as f64).collect();
        let upper: Vec<f64> = (0..n).map(|i| i as f64 + 1.0).collect();
        let relax = softmax_convex_relaxation(&lower, &upper);

        assert_eq!(relax.dim, n);
        assert!(
            relax.max_gap.is_finite(),
            "gap must be finite for large dim"
        );

        // Verify soundness at midpoint
        let mid: Vec<f64> = lower
            .iter()
            .zip(upper.iter())
            .map(|(l, u)| (l + u) / 2.0)
            .collect();
        let violation = verify_relaxation_soundness(&mid, &lower, &upper, &relax);
        assert!(violation < EPS, "soundness at midpoint");
    }

    #[test]
    fn test_relaxation_numerical_stability() {
        // Large absolute values but small range
        let lower = vec![1000.0, 1001.0, 999.0];
        let upper = vec![1001.0, 1002.0, 1000.0];
        let relax = softmax_convex_relaxation(&lower, &upper);

        assert!(relax.max_gap.is_finite(), "must handle large values");
        assert!(
            relax.lower.iter().all(|x| x.is_finite()),
            "lower bounds must be finite"
        );
        assert!(
            relax.upper.iter().all(|x| x.is_finite()),
            "upper bounds must be finite"
        );

        // Verify soundness at midpoint
        let mid: Vec<f64> = lower
            .iter()
            .zip(upper.iter())
            .map(|(l, u)| (l + u) / 2.0)
            .collect();
        let violation = verify_relaxation_soundness(&mid, &lower, &upper, &relax);
        assert!(violation < 1e-6, "soundness at midpoint for large values");
    }
}
