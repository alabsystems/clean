// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! McCormick Envelope Relaxations
//!
//! McCormick envelopes provide the tightest convex/concave relaxation of
//! a bilinear term w = x * y when x in [x_l, x_u] and y in [y_l, y_u].
//! These are fundamental building blocks for attention mechanism verification
//! (Q*K^T involves bilinear products).
//!
//! ## Theorems (all `DerivedPending`, Phase 3)
//!
//! - **T50 (McCormick envelope soundness):** The four McCormick inequalities
//!   are valid: for x in [x_l, x_u], y in [y_l, y_u], and w = x*y:
//!   w >= x_l*y + x*y_l - x_l*y_l
//!   w >= x_u*y + x*y_u - x_u*y_u
//!   w <= x_u*y + x*y_l - x_u*y_l
//!   w <= x_l*y + x*y_u - x_l*y_u
//!
//! - **T51 (McCormick convex underestimator):** The lower bound from T50
//!   is the tightest convex underestimator of x*y on the box domain.
//!
//! - **T52 (McCormick concave overestimator):** The upper bound from T50
//!   is the tightest concave overestimator of x*y on the box domain.
//!
//! ## AI Model Finding: `cases` before `linarith`
//!
//! The formal proof of the McCormick inequalities requires explicit
//! `cases` (case split) on the sign of (x - x_l), (x - x_u), (y - y_l),
//! (y - y_u) before `linarith` can close the goals. Without the case
//! split, `linarith` cannot derive the needed product-of-differences
//! non-negativity from the interval membership hypotheses alone.
//!
//! The key identity is:
//!   x*y - x_l*y - x*y_l + x_l*y_l = (x - x_l) * (y - y_l) >= 0
//! which requires knowing that both factors are non-negative.

use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// BilinearBounds: result of McCormick envelope computation
// ---------------------------------------------------------------------------

/// Bounds on the product x*y given x in [x_l, x_u], y in [y_l, y_u].
///
/// Computed from the four McCormick inequalities. The `lower` and `upper`
/// fields give the tightest interval [lower, upper] containing all possible
/// values of x*y for x in [x_l, x_u] and y in [y_l, y_u].
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BilinearBounds {
    /// Tight lower bound on x*y (minimum of the four corner products).
    pub lower: f64,
    /// Tight upper bound on x*y (maximum of the four corner products).
    pub upper: f64,
    /// x interval lower bound (stored for soundness verification).
    pub(crate) x_lower: f64,
    /// x interval upper bound.
    pub(crate) x_upper: f64,
    /// y interval lower bound.
    pub(crate) y_lower: f64,
    /// y interval upper bound.
    pub(crate) y_upper: f64,
}

impl BilinearBounds {
    /// Width of the product interval.
    #[must_use]
    pub fn width(&self) -> f64 {
        self.upper - self.lower
    }
}

// ---------------------------------------------------------------------------
// Core McCormick functions
// ---------------------------------------------------------------------------

/// Compute McCormick envelope bounds on x*y given box constraints.
///
/// The four McCormick inequalities define the tightest convex/concave
/// relaxation of the bilinear term x*y on the box [x_l, x_u] x [y_l, y_u].
///
/// The tight interval is the min/max of the four corner products:
///   x_l*y_l, x_l*y_u, x_u*y_l, x_u*y_u
///
/// This is exact because x*y is bilinear and attains its extrema at the
/// corners of the box domain.
#[must_use]
pub fn mccormick_envelope(
    x_lower: f64,
    x_upper: f64,
    y_lower: f64,
    y_upper: f64,
) -> BilinearBounds {
    debug_assert!(
        x_lower <= x_upper,
        "x_lower must not exceed x_upper: {x_lower} > {x_upper}"
    );
    debug_assert!(
        y_lower <= y_upper,
        "y_lower must not exceed y_upper: {y_lower} > {y_upper}"
    );

    // Four corner products
    let c1 = x_lower * y_lower;
    let c2 = x_lower * y_upper;
    let c3 = x_upper * y_lower;
    let c4 = x_upper * y_upper;

    let lower = c1.min(c2).min(c3).min(c4);
    let upper = c1.max(c2).max(c3).max(c4);

    BilinearBounds {
        lower,
        upper,
        x_lower,
        x_upper,
        y_lower,
        y_upper,
    }
}

/// Check that x*y is within the computed McCormick bounds.
///
/// Returns `true` if x*y falls within [bounds.lower, bounds.upper]
/// (with floating-point tolerance) and x, y are within their declared ranges.
#[must_use]
pub fn verify_mccormick_sound(x: f64, y: f64, bounds: &BilinearBounds) -> bool {
    let eps = f64::EPSILON * 16.0;
    // Check x in [x_l, x_u]
    if x < bounds.x_lower - eps || x > bounds.x_upper + eps {
        return false;
    }
    // Check y in [y_l, y_u]
    if y < bounds.y_lower - eps || y > bounds.y_upper + eps {
        return false;
    }
    // Check x*y in [lower, upper]
    let product = x * y;
    product >= bounds.lower - eps && product <= bounds.upper + eps
}

/// Compute the tightest interval containing x*y for x in x_bounds, y in y_bounds.
///
/// This is equivalent to the [lower, upper] fields of [`mccormick_envelope`]
/// but presented as a simple tuple for callers that only need the product interval.
#[must_use]
pub fn mccormick_product_interval(x_bounds: (f64, f64), y_bounds: (f64, f64)) -> (f64, f64) {
    let bounds = mccormick_envelope(x_bounds.0, x_bounds.1, y_bounds.0, y_bounds.1);
    (bounds.lower, bounds.upper)
}

// ---------------------------------------------------------------------------
// Proof spec stubs (Phase 3 theorem tracking)
// ---------------------------------------------------------------------------

/// Proof specification for T50: McCormick envelope soundness.
///
/// Tracks the formal proof that the four McCormick inequalities hold.
/// The concrete computation in [`mccormick_envelope`] implements the
/// sound relaxation; this spec tracks the formal verification status.
#[derive(Debug)]
pub struct McCormickEnvelopeSpec {
    status: ProofStatus,
}

impl McCormickEnvelopeSpec {
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

impl Default for McCormickEnvelopeSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// Proof specification for T51: McCormick convex underestimator tightness.
#[derive(Debug)]
pub struct McCormickConvexSpec {
    status: ProofStatus,
}

impl McCormickConvexSpec {
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

impl Default for McCormickConvexSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// Proof specification for T52: McCormick concave overestimator tightness.
#[derive(Debug)]
pub struct McCormickConcaveSpec {
    status: ProofStatus,
}

impl McCormickConcaveSpec {
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

impl Default for McCormickConcaveSpec {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Extended McCormick relaxation functions
// ---------------------------------------------------------------------------

/// Compute tight interval bounds on x*y using McCormick envelope.
///
/// For a bilinear term x*y with x in [x_lo, x_hi] and y in [y_lo, y_hi],
/// the tightest interval is the min/max of the four corner products. This
/// is tighter than naive interval arithmetic when both intervals cross zero,
/// because naive IA overestimates by treating the factors independently.
///
/// Returns `(lower, upper)` of the product interval.
#[must_use]
pub fn mccormick_tight_bounds(x_lo: f64, x_hi: f64, y_lo: f64, y_hi: f64) -> (f64, f64) {
    debug_assert!(x_lo <= x_hi, "x_lo must not exceed x_hi: {x_lo} > {x_hi}");
    debug_assert!(y_lo <= y_hi, "y_lo must not exceed y_hi: {y_lo} > {y_hi}");

    let c1 = x_lo * y_lo;
    let c2 = x_lo * y_hi;
    let c3 = x_hi * y_lo;
    let c4 = x_hi * y_hi;

    (c1.min(c2).min(c3).min(c4), c1.max(c2).max(c3).max(c4))
}

/// Bound on the product of n intervals using iterative pairwise McCormick.
///
/// Given intervals [(a1_lo, a1_hi), (a2_lo, a2_hi), ...], computes a bound
/// on a1 * a2 * ... * an by iteratively applying McCormick to pairs:
///   bound(a1*a2) -> bound((a1*a2)*a3) -> ...
///
/// Returns `(lower, upper)` of the product interval. For an empty slice,
/// returns `(1.0, 1.0)` (multiplicative identity).
#[must_use]
pub fn multi_term_product_bound(intervals: &[(f64, f64)]) -> (f64, f64) {
    if intervals.is_empty() {
        return (1.0, 1.0);
    }

    let mut acc = intervals[0];
    for &(lo, hi) in &intervals[1..] {
        acc = mccormick_tight_bounds(acc.0, acc.1, lo, hi);
    }
    acc
}

/// Bounds on x/y via McCormick on x * (1/y).
///
/// Computes interval bounds on x/y by first bounding 1/y on [y_lo, y_hi]
/// (which requires y_lo > 0 or y_hi < 0, i.e., the y interval must not
/// contain zero), then applying McCormick to x * (1/y).
///
/// Returns `None` if the y interval contains zero (division undefined).
#[must_use]
pub fn mccormick_division_bounds(x_lo: f64, x_hi: f64, y_lo: f64, y_hi: f64) -> Option<(f64, f64)> {
    debug_assert!(x_lo <= x_hi, "x_lo must not exceed x_hi: {x_lo} > {x_hi}");
    debug_assert!(y_lo <= y_hi, "y_lo must not exceed y_hi: {y_lo} > {y_hi}");

    // y interval must not contain zero
    if y_lo <= 0.0 && y_hi >= 0.0 {
        return None;
    }

    // Bound 1/y on [y_lo, y_hi]. Since 1/x is monotone decreasing on
    // intervals not containing zero, the bounds swap:
    //   if y_lo > 0: 1/y in [1/y_hi, 1/y_lo]
    //   if y_hi < 0: 1/y in [1/y_hi, 1/y_lo]  (both negative, 1/y_hi > 1/y_lo)
    let inv_lo = (1.0 / y_hi).min(1.0 / y_lo);
    let inv_hi = (1.0 / y_hi).max(1.0 / y_lo);

    Some(mccormick_tight_bounds(x_lo, x_hi, inv_lo, inv_hi))
}

/// Verify that McCormick gives tighter bounds than naive interval multiplication.
///
/// Naive interval arithmetic computes:
///   lo = min(x_lo*y_lo, x_lo*y_hi, x_hi*y_lo, x_hi*y_hi)
///   hi = max(x_lo*y_lo, x_lo*y_hi, x_hi*y_lo, x_hi*y_hi)
///
/// For bilinear products, McCormick and naive IA yield the same bounds
/// (both are exact for corner products). This function returns `true` when
/// the McCormick width is less than or equal to the naive width (within
/// floating-point tolerance), which should always be the case.
#[must_use]
pub fn verify_mccormick_tighter_than_naive(x_bounds: (f64, f64), y_bounds: (f64, f64)) -> bool {
    let (mc_lo, mc_hi) = mccormick_tight_bounds(x_bounds.0, x_bounds.1, y_bounds.0, y_bounds.1);
    let mc_width = mc_hi - mc_lo;

    // Naive interval arithmetic: all four endpoint combinations
    let (x_lo, x_hi) = x_bounds;
    let (y_lo, y_hi) = y_bounds;
    let products = [x_lo * y_lo, x_lo * y_hi, x_hi * y_lo, x_hi * y_hi];
    let naive_lo = products.iter().copied().fold(f64::INFINITY, f64::min);
    let naive_hi = products.iter().copied().fold(f64::NEG_INFINITY, f64::max);
    let naive_width = naive_hi - naive_lo;

    let eps = f64::EPSILON * 64.0;
    mc_width <= naive_width + eps
}

/// Tight bound on x^2 using convexity.
///
/// Since x^2 is convex, we can compute tighter bounds than naive interval
/// arithmetic when the interval crosses zero:
///   - If x_lo >= 0: x^2 in [x_lo^2, x_hi^2]
///   - If x_hi <= 0: x^2 in [x_hi^2, x_lo^2]
///   - If x_lo < 0 < x_hi: x^2 in [0, max(x_lo^2, x_hi^2)]
///
/// This is tighter than McCormick on x*x (which treats the two factors as
/// independent) when the interval crosses zero.
#[must_use]
pub fn mccormick_quadratic_bound(x_lo: f64, x_hi: f64) -> (f64, f64) {
    debug_assert!(x_lo <= x_hi, "x_lo must not exceed x_hi: {x_lo} > {x_hi}");

    if x_lo >= 0.0 {
        // Entirely non-negative: x^2 is monotone increasing
        (x_lo * x_lo, x_hi * x_hi)
    } else if x_hi <= 0.0 {
        // Entirely non-positive: x^2 is monotone decreasing
        (x_hi * x_hi, x_lo * x_lo)
    } else {
        // Crosses zero: minimum is 0, maximum at the endpoint farther from 0
        (0.0, (x_lo * x_lo).max(x_hi * x_hi))
    }
}

/// Bound on the dot product q^T * k using pairwise McCormick on each q_i * k_i.
///
/// For attention score computation, we bound sum_i(q_i * k_i) by bounding
/// each q_i * k_i with McCormick and summing the individual bounds.
///
/// This is sound because interval addition is exact:
///   [a, b] + [c, d] = [a+c, b+d]
///
/// Returns `(lower, upper)` of the dot product bound.
///
/// # Panics
///
/// Panics if `q_bounds` and `k_bounds` have different lengths.
#[must_use]
pub fn softmax_attention_bound(q_bounds: &[(f64, f64)], k_bounds: &[(f64, f64)]) -> (f64, f64) {
    assert_eq!(
        q_bounds.len(),
        k_bounds.len(),
        "q_bounds and k_bounds must have the same length"
    );

    let mut total_lo = 0.0;
    let mut total_hi = 0.0;

    for (&(q_lo, q_hi), &(k_lo, k_hi)) in q_bounds.iter().zip(k_bounds.iter()) {
        let (prod_lo, prod_hi) = mccormick_tight_bounds(q_lo, q_hi, k_lo, k_hi);
        total_lo += prod_lo;
        total_hi += prod_hi;
    }

    (total_lo, total_hi)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mccormick_specs_exist_as_derived_pending() {
        let envelope = McCormickEnvelopeSpec::new();
        let convex = McCormickConvexSpec::new();
        let concave = McCormickConcaveSpec::new();
        assert_eq!(envelope.status(), ProofStatus::DerivedPending);
        assert_eq!(convex.status(), ProofStatus::DerivedPending);
        assert_eq!(concave.status(), ProofStatus::DerivedPending);
    }
}
