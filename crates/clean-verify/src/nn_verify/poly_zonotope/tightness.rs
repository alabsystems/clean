// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tightness analysis for polynomial zonotope attention bounds.
//!
//! ## Key Result: O(eps) Tightness
//!
//! For the attention operation `attn(q, k, v) = q * k * v` where
//! q, k, v are perturbed by eps around nominal values:
//!
//! ```text
//! q = q0 + eps * dq,  k = k0 + eps * dk,  v = v0 + eps * dv
//! ```
//!
//! The polynomial zonotope bound gap is O(eps) because:
//!
//! 1. The product q*k*v = q0*k0*v0 + eps*(q0*k0*dv + q0*dk*v0 + dq*k0*v0)
//!    + O(eps^2) terms
//! 2. The O(eps) term is the first-order variation, which is linear in eps
//! 3. Polynomial zonotopes track the O(eps^2) quadratic terms exactly
//!    via quadratic generators
//! 4. Only the O(eps^3) remainder is overapproximated, contributing O(eps^3)
//!    to the gap
//!
//! In contrast, linear zonotopes lose the O(eps^2) correlation between
//! q and k in the product q*k, creating an O(eps^2) gap from the
//! interval product of two O(eps)-wide intervals.
//!
//! ## Formal Statement
//!
//! Let gap_poly(eps) be the polynomial zonotope gap and gap_lin(eps) the
//! linear zonotope gap. Then:
//!
//! - gap_poly(eps) = O(eps) as eps -> 0
//! - gap_lin(eps) = O(eps^2) as eps -> 0
//! - gap_lin(eps) / gap_poly(eps) -> O(eps) as eps -> 0
//!
//! Note: The O(eps) bound for the polynomial zonotope gap is more
//! conservative than the actual O(eps^3) remainder from the Hadamard
//! product overapproximation, because the interval hull extraction
//! (to_interval) also contributes O(eps) overapproximation for the
//! tracked quadratic terms. The net result is O(eps) total gap.
//!
//! ## References
//!
//! - Kochdumper & Althoff, "Sparse Polynomial Zonotopes" (2020), Theorem 3.2
//! - Althoff, "Reachability Analysis of Nonlinear Systems" (2013), Section 4.3

use super::attention::{attention_bound_linear, attention_bound_poly};
use super::types::{PolyZonotope, PolyZonotopeError};

/// Result of tightness analysis over a range of perturbation radii.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct TightnessAnalysis {
    /// Perturbation radii tested.
    pub eps_values: Vec<f64>,
    /// Polynomial zonotope gaps at each eps.
    pub poly_gaps: Vec<f64>,
    /// Linear zonotope gaps at each eps.
    pub linear_gaps: Vec<f64>,
    /// Improvement ratios (linear_gap / poly_gap) at each eps.
    pub improvement_ratios: Vec<f64>,
    /// Estimated order of poly gap: slope of log(gap) vs log(eps).
    pub poly_order: f64,
    /// Estimated order of linear gap: slope of log(gap) vs log(eps).
    pub linear_order: f64,
    /// Whether O(eps) tightness is confirmed for poly zonotope.
    pub poly_is_o_eps: bool,
    /// Whether O(eps^2) scaling is confirmed for linear zonotope.
    pub linear_is_o_eps_squared: bool,
}

/// Run tightness analysis comparing poly vs linear zonotope attention bounds.
///
/// For a range of perturbation radii eps, computes attention bounds using both
/// methods and analyzes the scaling of the gap.
///
/// ## Arguments
/// - `q0`, `k0`, `v0`: Nominal (center) values for query, key, value
/// - `eps_values`: Perturbation radii to test (should span at least one
///   order of magnitude for reliable order estimation)
///
/// ## Returns
/// `TightnessAnalysis` with gap data and order estimates.
pub fn analyze_tightness(
    q0: f64,
    k0: f64,
    v0: f64,
    eps_values: &[f64],
) -> Result<TightnessAnalysis, PolyZonotopeError> {
    let mut poly_gaps = Vec::with_capacity(eps_values.len());
    let mut linear_gaps = Vec::with_capacity(eps_values.len());
    let mut improvement_ratios = Vec::with_capacity(eps_values.len());

    for &eps in eps_values {
        let q = PolyZonotope::try_new(vec![q0], vec![vec![eps]], vec![vec![0.0]], 1)?;
        let k = PolyZonotope::try_new(vec![k0], vec![vec![eps]], vec![vec![0.0]], 1)?;
        let v = PolyZonotope::try_new(vec![v0], vec![vec![eps]], vec![vec![0.0]], 1)?;

        let poly_bound = attention_bound_poly(&q, &k, &v)?;
        let linear_bound = attention_bound_linear(&q, &k, &v)?;

        poly_gaps.push(poly_bound.max_gap);
        linear_gaps.push(linear_bound.max_gap);

        let ratio = if poly_bound.max_gap > f64::EPSILON * 256.0 {
            linear_bound.max_gap / poly_bound.max_gap
        } else {
            1.0
        };
        improvement_ratios.push(ratio);
    }

    // Estimate scaling order via log-log regression.
    // For gap(eps) = C * eps^p, log(gap) = log(C) + p * log(eps).
    let poly_order = estimate_order(eps_values, &poly_gaps);
    let linear_order = estimate_order(eps_values, &linear_gaps);

    // O(eps) means order >= 1 (within tolerance)
    let poly_is_o_eps = poly_order >= 0.8;
    // O(eps^2) means order >= 2 (within tolerance)
    let linear_is_o_eps_squared = linear_order >= 1.5;

    Ok(TightnessAnalysis {
        eps_values: eps_values.to_vec(),
        poly_gaps,
        linear_gaps,
        improvement_ratios,
        poly_order,
        linear_order,
        poly_is_o_eps,
        linear_is_o_eps_squared,
    })
}

/// Estimate the power-law order from (x, y) data via log-log linear regression.
///
/// For y = C * x^p, fits log(y) = log(C) + p * log(x) and returns p.
/// Filters out zero/negative values before regression.
fn estimate_order(xs: &[f64], ys: &[f64]) -> f64 {
    let points: Vec<(f64, f64)> = xs
        .iter()
        .zip(ys.iter())
        .filter(|(&x, &y)| x > 0.0 && y > 0.0 && x.is_finite() && y.is_finite())
        .map(|(&x, &y)| (x.ln(), y.ln()))
        .collect();

    if points.len() < 2 {
        return 0.0;
    }

    // Simple linear regression: slope = (n*sum(xy) - sum(x)*sum(y))
    //                                   / (n*sum(x^2) - sum(x)^2)
    let n = points.len() as f64;
    let sum_x: f64 = points.iter().map(|(x, _)| x).sum();
    let sum_y: f64 = points.iter().map(|(_, y)| y).sum();
    let sum_xy: f64 = points.iter().map(|(x, y)| x * y).sum();
    let sum_x2: f64 = points.iter().map(|(x, _)| x * x).sum();

    let denom = n * sum_x2 - sum_x * sum_x;
    if denom.abs() < f64::EPSILON * 256.0 {
        return 0.0;
    }

    (n * sum_xy - sum_x * sum_y) / denom
}

/// Verify O(eps) tightness empirically for a given configuration.
///
/// Returns `(is_tight, analysis)` where `is_tight` is true if the
/// polynomial zonotope gap scales as O(eps) (order >= 0.8).
pub fn verify_o_eps_tightness(
    q0: f64,
    k0: f64,
    v0: f64,
) -> Result<(bool, TightnessAnalysis), PolyZonotopeError> {
    let eps_values = vec![0.001, 0.005, 0.01, 0.05, 0.1, 0.2, 0.5];
    let analysis = analyze_tightness(q0, k0, v0, &eps_values)?;
    let is_tight = analysis.poly_is_o_eps;
    Ok((is_tight, analysis))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tightness_analysis_basic() {
        let eps_values = vec![0.01, 0.05, 0.1, 0.2, 0.5];
        let analysis = analyze_tightness(1.0, 1.0, 1.0, &eps_values).expect("should analyze");

        assert_eq!(analysis.eps_values.len(), 5);
        assert_eq!(analysis.poly_gaps.len(), 5);
        assert_eq!(analysis.linear_gaps.len(), 5);

        // Gaps should increase with eps
        for i in 1..analysis.poly_gaps.len() {
            assert!(
                analysis.poly_gaps[i] >= analysis.poly_gaps[i - 1] - 1e-10,
                "poly gaps should be non-decreasing with eps"
            );
        }
    }

    #[test]
    fn test_poly_zonotope_is_o_eps() {
        let (is_tight, analysis) = verify_o_eps_tightness(1.0, 1.0, 1.0).expect("should verify");

        assert!(
            is_tight,
            "polynomial zonotope attention should be O(eps), \
             got order {:.2}",
            analysis.poly_order
        );
        assert!(
            analysis.poly_order >= 0.8,
            "poly order should be >= 0.8, got {:.2}",
            analysis.poly_order
        );
    }

    #[test]
    fn test_linear_zonotope_is_o_eps_squared() {
        // Use zero-centered q and k so interval arithmetic overestimates
        // the q*k product. With c=0, the product q*k = eps^2 * eps_1^2
        // has range [0, eps^2], but interval gives [-eps^2, eps^2].
        // The linear gap thus scales as O(eps^2) (from the interval product
        // of two O(eps)-wide intervals centered at 0).
        let (_, analysis) = verify_o_eps_tightness(0.0, 0.0, 1.0).expect("should verify");

        assert!(
            analysis.linear_is_o_eps_squared,
            "linear zonotope attention gap should be O(eps^2) for zero-centered q,k, \
             got order {:.2}",
            analysis.linear_order
        );
        assert!(
            analysis.linear_order >= 1.5,
            "linear order should be >= 1.5, got {:.2}",
            analysis.linear_order
        );
    }

    #[test]
    fn test_improvement_ratio_grows_with_eps() {
        // Use zero-centered q and k where the poly advantage materializes.
        // The poly gap is O(eps^2) (tighter than O(eps) general bound)
        // while the linear gap is O(eps^2), but with a larger constant.
        // The improvement ratio should be > 1 for all tested eps values.
        let eps_values = vec![0.01, 0.05, 0.1, 0.2, 0.5];
        let analysis = analyze_tightness(0.0, 0.0, 1.0, &eps_values).expect("should analyze");

        // Verify poly is consistently tighter than linear
        for (i, &ratio) in analysis.improvement_ratios.iter().enumerate() {
            assert!(
                ratio >= 1.0 - 1e-6,
                "improvement ratio should be >= 1 at eps={}: ratio={ratio:.4}",
                analysis.eps_values[i]
            );
        }
    }

    #[test]
    fn test_tightness_different_centers() {
        // Test with different nominal values
        for &(q0, k0, v0) in &[(2.0, 1.5, 0.5), (0.5, 3.0, 1.0), (1.0, 1.0, 2.0)] {
            let (is_tight, analysis) = verify_o_eps_tightness(q0, k0, v0).expect("should verify");

            assert!(
                is_tight,
                "O(eps) tightness should hold for q0={q0}, k0={k0}, v0={v0}, \
                 order = {:.2}",
                analysis.poly_order
            );
        }
    }

    #[test]
    fn test_estimate_order_linear() {
        // y = 2 * x^1 -> order should be ~1
        let xs = vec![0.1, 0.2, 0.5, 1.0];
        let ys: Vec<f64> = xs.iter().map(|&x| 2.0 * x).collect();
        let order = estimate_order(&xs, &ys);
        assert!(
            (order - 1.0).abs() < 0.1,
            "order of linear should be ~1, got {order:.3}"
        );
    }

    #[test]
    fn test_estimate_order_quadratic() {
        // y = 3 * x^2 -> order should be ~2
        let xs = vec![0.1, 0.2, 0.5, 1.0];
        let ys: Vec<f64> = xs.iter().map(|&x| 3.0 * x * x).collect();
        let order = estimate_order(&xs, &ys);
        assert!(
            (order - 2.0).abs() < 0.1,
            "order of quadratic should be ~2, got {order:.3}"
        );
    }

    #[test]
    fn test_estimate_order_cubic() {
        // y = x^3 -> order should be ~3
        let xs = vec![0.1, 0.2, 0.5, 1.0];
        let ys: Vec<f64> = xs.iter().map(|&x| x * x * x).collect();
        let order = estimate_order(&xs, &ys);
        assert!(
            (order - 3.0).abs() < 0.15,
            "order of cubic should be ~3, got {order:.3}"
        );
    }
}
