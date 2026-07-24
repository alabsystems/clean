// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LayerNorm Bound Propagation
//!
//! LayerNorm(x) = gamma * (x - mean(x)) / sqrt(var(x) + eps) + beta
//!
//! Propagating interval bounds through LayerNorm is non-trivial because:
//! 1. The mean and variance depend on all elements jointly (not element-wise).
//! 2. The division by sqrt(var + eps) requires reasoning about rational
//!    arithmetic, and sqrt over Rat is not exact.
//!
//! ## Theorems (all `DerivedPending`, Phase 3)
//!
//! - **T20 (LayerNorm centering):** Bounding x - mean(x) when x is in
//!   an interval. The key insight: mean(x) is a linear function of x,
//!   so interval arithmetic applies directly to the centered value.
//!
//! - **T21 (LayerNorm scaling):** Bounding the division by sqrt(var + eps).
//!   This is the hard part: variance is quadratic in x, and sqrt introduces
//!   irrationality over Rat.
//!
//! - **T22 (LayerNorm full):** Composition of centering, scaling, and
//!   affine transform (gamma * . + beta).
//!
//! ## AI Model Finding: sqrt Domain Issue
//!
//! When working over rational arithmetic (Rat), sqrt(var + eps) is
//! irrational for most inputs. The proof must either:
//! - Work over Real (requires real-closed field axioms)
//! - Use rational approximation bounds on sqrt
//! - Use the squared form: bound var(x) directly and derive output
//!   bounds without computing sqrt explicitly
//!
//! The third approach is most promising for formalization. All functions
//! in this module work with variance (sigma-squared) directly and never
//! compute sqrt. This is intentional: sqrt(Var) is irrational over Rat,
//! so the design doc demotes sqrt-based normalization to Phase 3+.
//!
//! ## AI Model Finding: Operator Order
//!
//! The correct order is scale AFTER center:
//!   LayerNorm(x) = gamma * normalize(x) + beta
//! where normalize(x) = (x - mean(x)) / sqrt(var(x) + eps).
//! NOT: normalize(gamma * x + beta). This matters for bound computation
//! because the affine transform is applied to already-normalized values.

use crate::spec::ProofStatus;

/// Default epsilon for LayerNorm numerical stability.
const DEFAULT_EPS: f64 = 1e-5;

// ---------------------------------------------------------------------------
// LayerNormBounds: result of LayerNorm bound propagation
// ---------------------------------------------------------------------------

/// Bounds on LayerNorm output for each element.
///
/// Each element i has bounds [lower[i], upper[i]] on the LayerNorm output.
/// Also stores intermediate bounds (mean, variance) for verification.
///
/// **Important:** Variance bounds are on sigma-squared, NOT sigma. We never
/// compute sqrt(variance) because sqrt over Rat is irrational.
#[derive(Debug, Clone, PartialEq)]
pub struct LayerNormBounds {
    /// Per-element lower bounds on LayerNorm output.
    pub lower: Vec<f64>,
    /// Per-element upper bounds on LayerNorm output.
    pub upper: Vec<f64>,
    /// Bounds on the mean: (mean_lower, mean_upper).
    pub mean_bounds: (f64, f64),
    /// Bounds on the variance (sigma-squared): (var_lower, var_upper).
    /// Never take sqrt of this -- work with variance directly.
    pub variance_bounds: (f64, f64),
}

// ---------------------------------------------------------------------------
// Mean bounds
// ---------------------------------------------------------------------------

/// Compute bounds on the mean: mean(x) = (1/d) * sum(x_i).
///
/// Since the mean is a linear function of x, interval arithmetic applies
/// directly: the minimum mean occurs when each x_i is at its lower bound,
/// and the maximum mean occurs when each x_i is at its upper bound.
///
/// # Panics
///
/// Debug-asserts that the slices have equal, nonzero length.
#[must_use]
pub fn compute_mean_bounds(input_lower: &[f64], input_upper: &[f64]) -> (f64, f64) {
    let d = input_lower.len();
    debug_assert_eq!(d, input_upper.len(), "input bounds must have equal length");
    debug_assert!(d > 0, "input dimension must be nonzero");

    let inv_d = 1.0 / d as f64;
    let sum_lower: f64 = input_lower.iter().sum();
    let sum_upper: f64 = input_upper.iter().sum();
    (sum_lower * inv_d, sum_upper * inv_d)
}

// ---------------------------------------------------------------------------
// Variance bounds (sigma-squared, no sqrt)
// ---------------------------------------------------------------------------

/// Compute bounds on variance: var(x) = (1/d) * sum((x_i - mean)^2).
///
/// This is conservative: we bound (x_i - mean)^2 for each element using
/// the widest possible range of (x_i - mean), then sum.
///
/// The variance lower bound is 0 when all inputs can be equal (their
/// intervals overlap). The upper bound uses the maximum possible squared
/// deviation from the mean.
///
/// **Key constraint:** We work with variance (sigma-squared) directly
/// and never compute sqrt. sqrt(Var) is irrational over Rat; the design
/// doc demotes this to Phase 3+.
///
/// # Panics
///
/// Debug-asserts that slices have equal, nonzero length.
#[must_use]
pub fn compute_variance_bounds(
    input_lower: &[f64],
    input_upper: &[f64],
    mean_bounds: (f64, f64),
) -> (f64, f64) {
    let d = input_lower.len();
    debug_assert_eq!(d, input_upper.len(), "input bounds must have equal length");
    debug_assert!(d > 0, "input dimension must be nonzero");

    let inv_d = 1.0 / d as f64;

    // Upper bound on variance: maximize sum of (x_i - mean)^2.
    // For each element, the deviation (x_i - mean) is maximized when x_i
    // and mean are as far apart as possible.
    // Worst-case squared deviation for element i:
    //   max( (x_i_upper - mean_lower)^2, (x_i_lower - mean_upper)^2 )
    let mut sum_sq_upper = 0.0;
    for i in 0..d {
        let dev_a = input_upper[i] - mean_bounds.0; // max x_i minus min mean
        let dev_b = input_lower[i] - mean_bounds.1; // min x_i minus max mean
        let max_sq = dev_a.abs().max(dev_b.abs());
        sum_sq_upper += max_sq * max_sq;
    }
    let var_upper = sum_sq_upper * inv_d;

    // Lower bound on variance: can be 0 when all intervals share a common point
    // (i.e., all elements could be the same value). Otherwise, compute the
    // minimum possible variance.
    //
    // A simple conservative lower bound: if all intervals share an overlap,
    // variance can be 0. We check if there is a common point in all intervals.
    let max_of_lowers = input_lower
        .iter()
        .copied()
        .fold(f64::NEG_INFINITY, f64::max);
    let min_of_uppers = input_upper.iter().copied().fold(f64::INFINITY, f64::min);

    let var_lower = if max_of_lowers <= min_of_uppers + f64::EPSILON {
        // All intervals overlap at some point => variance can be 0
        0.0
    } else {
        // Not all intervals overlap. The minimum variance occurs when elements
        // are packed as tightly as possible. Conservative lower bound:
        // each (x_i - mean) has a minimum absolute deviation from the centroid.
        // For soundness, we use 0.0 here as a safe conservative lower bound.
        // A tighter bound requires solving a constrained optimization problem.
        0.0
    };

    (var_lower, var_upper)
}

// ---------------------------------------------------------------------------
// Full LayerNorm forward pass bounds
// ---------------------------------------------------------------------------

/// Compute conservative bounds on LayerNorm output.
///
/// LayerNorm(x)_i = gamma_i * (x_i - mean(x)) / sqrt(var(x) + eps) + beta_i
///
/// **Operator order:** centering first (x_i - mean), then scaling (divide by
/// sqrt(var + eps)), then affine (gamma * . + beta). This is the correct
/// order per the design doc.
///
/// **Variance formulation:** We work with variance (sigma-squared) directly.
/// To bound the division by sqrt(var + eps), we use:
///   1/sqrt(var + eps) is in [1/sqrt(var_upper + eps), 1/sqrt(var_lower + eps)]
/// since 1/sqrt is monotonically decreasing for positive arguments.
///
/// Note: This function does use sqrt for the concrete numerical computation
/// of the scaling factor bounds, but the proof-level formalization will
/// work with squared forms. For the concrete verifier, sqrt of f64 is fine.
///
/// # Panics
///
/// Debug-asserts that all slices have equal length and gamma/beta match.
#[must_use]
pub fn verify_layernorm_forward(
    input_lower: &[f64],
    input_upper: &[f64],
    gamma: &[f64],
    beta: &[f64],
) -> LayerNormBounds {
    let d = input_lower.len();
    debug_assert_eq!(d, input_upper.len());
    debug_assert_eq!(d, gamma.len());
    debug_assert_eq!(d, beta.len());
    debug_assert!(d > 0, "dimension must be nonzero");

    // Step 1: Mean bounds (linear, exact interval arithmetic)
    let mean_bounds = compute_mean_bounds(input_lower, input_upper);

    // Step 2: Variance bounds (quadratic, conservative)
    let variance_bounds = compute_variance_bounds(input_lower, input_upper, mean_bounds);

    // Step 3: Scaling factor bounds.
    // scale = 1 / sqrt(var + eps).
    // Since 1/sqrt is decreasing on (0, inf):
    //   scale_lower = 1 / sqrt(var_upper + eps)
    //   scale_upper = 1 / sqrt(var_lower + eps)
    let scale_lower = 1.0 / (variance_bounds.1 + DEFAULT_EPS).sqrt();
    let scale_upper = 1.0 / (variance_bounds.0 + DEFAULT_EPS).sqrt();

    // Step 4: For each element, compute output bounds.
    // centered_i = x_i - mean
    // normalized_i = centered_i * scale
    // output_i = gamma_i * normalized_i + beta_i
    let mut out_lower = Vec::with_capacity(d);
    let mut out_upper = Vec::with_capacity(d);

    for i in 0..d {
        // Centering: bounds on (x_i - mean)
        let centered_lo = input_lower[i] - mean_bounds.1; // min x_i - max mean
        let centered_hi = input_upper[i] - mean_bounds.0; // max x_i - min mean

        // Scaling: multiply centered by scale (interval multiplication)
        let products = [
            centered_lo * scale_lower,
            centered_lo * scale_upper,
            centered_hi * scale_lower,
            centered_hi * scale_upper,
        ];
        let norm_lo = products.iter().copied().fold(f64::INFINITY, f64::min);
        let norm_hi = products.iter().copied().fold(f64::NEG_INFINITY, f64::max);

        // Affine: gamma_i * normalized_i + beta_i
        let g = gamma[i];
        let (af_lo, af_hi) = if g >= 0.0 {
            (g * norm_lo + beta[i], g * norm_hi + beta[i])
        } else {
            (g * norm_hi + beta[i], g * norm_lo + beta[i])
        };

        out_lower.push(af_lo);
        out_upper.push(af_hi);
    }

    LayerNormBounds {
        lower: out_lower,
        upper: out_upper,
        mean_bounds,
        variance_bounds,
    }
}

// ---------------------------------------------------------------------------
// Proof spec stubs (Phase 3 theorem tracking)
// ---------------------------------------------------------------------------

/// Proof specification for T20: LayerNorm centering bound.
///
/// Tracks formal verification that interval arithmetic on the centering
/// step (x - mean(x)) is sound. The concrete computation is in
/// [`compute_mean_bounds`].
#[derive(Debug)]
pub struct LayerNormCenterSpec {
    status: ProofStatus,
}

impl LayerNormCenterSpec {
    #[must_use]
    pub fn new() -> Self {
        Self {
            status: ProofStatus::DerivedPending,
        }
    }

    #[must_use]
    pub fn status(&self) -> ProofStatus {
        self.status
    }
}

impl Default for LayerNormCenterSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// Proof specification for T21: LayerNorm scaling bound.
///
/// Tracks formal verification of bounds on division by sqrt(var + eps).
/// The concrete computation uses variance (sigma-squared) directly.
#[derive(Debug)]
pub struct LayerNormScaleSpec {
    status: ProofStatus,
}

impl LayerNormScaleSpec {
    #[must_use]
    pub fn new() -> Self {
        Self {
            status: ProofStatus::DerivedPending,
        }
    }

    #[must_use]
    pub fn status(&self) -> ProofStatus {
        self.status
    }
}

impl Default for LayerNormScaleSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// Proof specification for T22: LayerNorm full pipeline bound.
///
/// Tracks formal verification of the composed pipeline: centering,
/// scaling, and affine transform. The concrete computation is in
/// [`verify_layernorm_forward`].
#[derive(Debug)]
pub struct LayerNormFullSpec {
    status: ProofStatus,
}

impl LayerNormFullSpec {
    #[must_use]
    pub fn new() -> Self {
        Self {
            status: ProofStatus::DerivedPending,
        }
    }

    #[must_use]
    pub fn status(&self) -> ProofStatus {
        self.status
    }
}

impl Default for LayerNormFullSpec {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_layernorm_specs_exist_as_derived_pending() {
        let center = LayerNormCenterSpec::new();
        let scale = LayerNormScaleSpec::new();
        let full = LayerNormFullSpec::new();
        assert_eq!(center.status(), ProofStatus::DerivedPending);
        assert_eq!(scale.status(), ProofStatus::DerivedPending);
        assert_eq!(full.status(), ProofStatus::DerivedPending);
    }
}
