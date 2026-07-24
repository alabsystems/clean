// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C005: McCormick bilinear relaxation linear error growth formalization.
//!
//! This module tracks the quantitative error of the McCormick lower envelope
//! for a bilinear term `x * y` over a box `[x_l, x_u] x [y_l, y_u]`.
//! At a point `(x, y)`, the lower-envelope gap is
//! `x * y - max(x_l * y + x * y_l - x_l * y_l, x_u * y + x * y_u - x_u * y_u)`.
//! The maximum gap over the box is `(x_u - x_l) * (y_u - y_l) / 4`, achieved
//! at the midpoint.
//!
//! C005 also records the shared-input attention case `Q = w_q * x`,
//! `K = w_k * x` with `x in [c - eps, c + eps]`. The induced McCormick box
//! has widths `2 * |w_q| * eps` and `2 * |w_k| * eps`, so the worst-case gap
//! is `|w_q| * |w_k| * eps^2`. Normalizing by either interval width yields an
//! `O(eps)` growth rate, which is the linear normalized-error claim.

use crate::spec::ProofStatus;

use super::{Phase, TheoremEntry};

const FLOAT_TOLERANCE: f64 = 1e-12;
const GAP_GRID_STEPS: usize = 8;

#[must_use]
pub(crate) fn approx_eq(lhs: f64, rhs: f64, tolerance: f64) -> bool {
    (lhs - rhs).abs() <= tolerance
}

#[must_use]
pub(crate) fn scaled_tolerance(scale: f64) -> f64 {
    FLOAT_TOLERANCE * scale.abs().max(1.0)
}

#[must_use]
pub(crate) fn interval_width(lower: f64, upper: f64) -> f64 {
    debug_assert!(
        lower <= upper,
        "interval lower bound must not exceed upper bound: {lower} > {upper}"
    );
    (upper - lower).max(0.0)
}

#[must_use]
pub(crate) fn shared_input_interval(weight: f64, center: f64, eps: f64) -> (f64, f64) {
    debug_assert!(eps >= 0.0, "eps must be non-negative: {eps}");

    let radius = eps.max(0.0);
    let x_lower = center - radius;
    let x_upper = center + radius;
    let endpoint_a = weight * x_lower;
    let endpoint_b = weight * x_upper;
    (endpoint_a.min(endpoint_b), endpoint_a.max(endpoint_b))
}

/// McCormick relaxation gap at a specific point `(x, y)` within the box.
#[must_use]
pub fn mccormick_gap_at_point(x: f64, y: f64, xl: f64, xu: f64, yl: f64, yu: f64) -> f64 {
    debug_assert!(xl <= xu, "x bounds must satisfy xl <= xu: {xl} > {xu}");
    debug_assert!(yl <= yu, "y bounds must satisfy yl <= yu: {yl} > {yu}");
    debug_assert!(
        x >= xl - FLOAT_TOLERANCE && x <= xu + FLOAT_TOLERANCE,
        "x must lie inside the box: x={x}, box=[{xl}, {xu}]"
    );
    debug_assert!(
        y >= yl - FLOAT_TOLERANCE && y <= yu + FLOAT_TOLERANCE,
        "y must lie inside the box: y={y}, box=[{yl}, {yu}]"
    );

    let lower_env_a = xl * y + x * yl - xl * yl;
    let lower_env_b = xu * y + x * yu - xu * yu;
    let lower_env = lower_env_a.max(lower_env_b);
    let raw_gap = x.mul_add(y, -lower_env);
    let gap = if raw_gap.is_sign_negative() && raw_gap.abs() <= FLOAT_TOLERANCE {
        0.0
    } else {
        raw_gap.max(0.0)
    };

    let gap_from_lower_left = (x - xl) * (y - yl);
    let gap_from_upper_right = (xu - x) * (yu - y);
    let equivalent_gap = gap_from_lower_left.min(gap_from_upper_right);
    debug_assert!(
        approx_eq(gap, equivalent_gap, scaled_tolerance(equivalent_gap)),
        "McCormick gap closed forms should agree: direct={gap}, closed_form={equivalent_gap}"
    );

    gap
}

/// Worst-case McCormick relaxation gap over the entire box domain.
///
/// Returns `(xu - xl) * (yu - yl) / 4`.
#[must_use]
pub fn mccormick_worst_case_gap(xl: f64, xu: f64, yl: f64, yu: f64) -> f64 {
    debug_assert!(xl <= xu, "x bounds must satisfy xl <= xu: {xl} > {xu}");
    debug_assert!(yl <= yu, "y bounds must satisfy yl <= yu: {yl} > {yu}");

    0.25 * interval_width(xl, xu) * interval_width(yl, yu)
}

/// Verify the box-domain McCormick bound `gap <= width_x * width_y / 4`.
#[must_use]
pub fn verify_gap_bound(xl: f64, xu: f64, yl: f64, yu: f64) -> bool {
    if !xl.is_finite() || !xu.is_finite() || !yl.is_finite() || !yu.is_finite() {
        return false;
    }
    if xl > xu || yl > yu {
        return false;
    }

    let worst_case = mccormick_worst_case_gap(xl, xu, yl, yu);
    let tolerance = scaled_tolerance(worst_case);
    let x_width = interval_width(xl, xu);
    let y_width = interval_width(yl, yu);
    let x_mid = 0.5 * (xl + xu);
    let y_mid = 0.5 * (yl + yu);

    if !approx_eq(
        mccormick_gap_at_point(x_mid, y_mid, xl, xu, yl, yu),
        worst_case,
        tolerance,
    ) {
        return false;
    }

    for &(x, y) in &[(xl, yl), (xl, yu), (xu, yl), (xu, yu)] {
        if mccormick_gap_at_point(x, y, xl, xu, yl, yu) > tolerance {
            return false;
        }
    }

    for i in 0..=GAP_GRID_STEPS {
        let x = xl + x_width * (i as f64) / (GAP_GRID_STEPS as f64);
        for j in 0..=GAP_GRID_STEPS {
            let y = yl + y_width * (j as f64) / (GAP_GRID_STEPS as f64);
            if mccormick_gap_at_point(x, y, xl, xu, yl, yu) > worst_case + tolerance {
                return false;
            }
        }
    }

    true
}

/// Shared-input McCormick gap for `Q = w_q * x`, `K = w_k * x`,
/// with `x in [center - eps, center + eps]`.
///
/// This is the worst-case McCormick gap over the induced `(Q, K)` box.
#[must_use]
pub fn shared_input_mccormick_gap(w_q: f64, w_k: f64, center: f64, eps: f64) -> f64 {
    debug_assert!(eps >= 0.0, "eps must be non-negative: {eps}");

    let (q_lower, q_upper) = shared_input_interval(w_q, center, eps);
    let (k_lower, k_upper) = shared_input_interval(w_k, center, eps);
    mccormick_worst_case_gap(q_lower, q_upper, k_lower, k_upper)
}

/// Verify the shared-input linear normalized growth law.
///
/// The absolute gap is `|w_q| * |w_k| * eps^2`, while
/// `gap / width_Q = |w_k| * eps / 2` and `gap / width_K = |w_q| * eps / 2`.
#[must_use]
pub fn verify_shared_input_linear_growth(w_q: f64, w_k: f64, center: f64, eps: f64) -> bool {
    if !w_q.is_finite() || !w_k.is_finite() || !center.is_finite() || !eps.is_finite() {
        return false;
    }
    if eps < 0.0 {
        return false;
    }

    let gap = shared_input_mccormick_gap(w_q, w_k, center, eps);
    let expected_gap = w_q.abs() * w_k.abs() * eps * eps;
    if !approx_eq(gap, expected_gap, scaled_tolerance(expected_gap)) {
        return false;
    }

    let (q_lower, q_upper) = shared_input_interval(w_q, center, eps);
    let (k_lower, k_upper) = shared_input_interval(w_k, center, eps);
    let q_width = interval_width(q_lower, q_upper);
    let k_width = interval_width(k_lower, k_upper);
    let zero_gap_ok = gap <= scaled_tolerance(gap);
    let q_ratio = if q_width <= FLOAT_TOLERANCE {
        0.0
    } else {
        gap / q_width
    };
    let k_ratio = if k_width <= FLOAT_TOLERANCE {
        0.0
    } else {
        gap / k_width
    };
    let expected_q_ratio = 0.5 * w_k.abs() * eps;
    let expected_k_ratio = 0.5 * w_q.abs() * eps;

    let q_ratio_ok = if q_width <= FLOAT_TOLERANCE {
        zero_gap_ok
    } else {
        approx_eq(
            q_ratio,
            expected_q_ratio,
            scaled_tolerance(expected_q_ratio),
        )
    };
    let k_ratio_ok = if k_width <= FLOAT_TOLERANCE {
        zero_gap_ok
    } else {
        approx_eq(
            k_ratio,
            expected_k_ratio,
            scaled_tolerance(expected_k_ratio),
        )
    };

    q_ratio_ok && k_ratio_ok
}

/// C005 proof specification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct McCormickLinearErrorSpec {
    status: ProofStatus,
}

impl McCormickLinearErrorSpec {
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

    #[must_use]
    pub fn verify_gap_bound(&self, xl: f64, xu: f64, yl: f64, yu: f64) -> bool {
        verify_gap_bound(xl, xu, yl, yu)
    }

    #[must_use]
    pub fn verify_linear_growth(&self, w_q: f64, w_k: f64, center: f64, eps: f64) -> bool {
        self.verify_shared_input(w_q, w_k, center, eps)
            && verify_shared_input_linear_growth(w_q, w_k, center, eps)
    }

    #[must_use]
    pub fn verify_shared_input(&self, w_q: f64, w_k: f64, center: f64, eps: f64) -> bool {
        if !w_q.is_finite() || !w_k.is_finite() || !center.is_finite() || !eps.is_finite() {
            return false;
        }
        if eps < 0.0 {
            return false;
        }

        let gap = shared_input_mccormick_gap(w_q, w_k, center, eps);
        let expected_gap = w_q.abs() * w_k.abs() * eps * eps;
        approx_eq(gap, expected_gap, scaled_tolerance(expected_gap))
    }
}

impl Default for McCormickLinearErrorSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// Return the theorem registry entry for C005.
#[must_use]
pub(crate) fn c005_theorem_entry() -> TheoremEntry {
    TheoremEntry {
        id: "C005",
        description: "McCormick bilinear relaxation normalized error grows linearly",
        status: ProofStatus::DerivedPending,
        phase: Phase::Phase3,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_close(lhs: f64, rhs: f64) {
        assert!(
            approx_eq(lhs, rhs, scaled_tolerance(rhs)),
            "left={lhs}, right={rhs}"
        );
    }

    #[test]
    fn test_mccormick_gap_at_point_midpoint_is_maximum() {
        let gap = mccormick_gap_at_point(1.0, 3.0, 0.0, 2.0, 1.0, 5.0);
        assert_close(gap, 2.0);
        assert_close(gap, mccormick_worst_case_gap(0.0, 2.0, 1.0, 5.0));
        assert!(gap > mccormick_gap_at_point(0.5, 2.0, 0.0, 2.0, 1.0, 5.0));
    }

    #[test]
    fn test_mccormick_gap_at_corners_is_zero() {
        for &(x, y) in &[(-2.0, -1.0), (-2.0, 4.0), (3.0, -1.0), (3.0, 4.0)] {
            assert_close(mccormick_gap_at_point(x, y, -2.0, 3.0, -1.0, 4.0), 0.0);
        }
    }

    #[test]
    fn test_worst_case_gap_sign_patterns() {
        assert_close(mccormick_worst_case_gap(1.0, 3.0, 2.0, 6.0), 2.0);
        assert_close(mccormick_worst_case_gap(-5.0, -1.0, -4.0, -2.0), 2.0);
        assert_close(mccormick_worst_case_gap(-2.0, 2.0, -3.0, 1.0), 4.0);
    }

    #[test]
    fn test_worst_case_gap_point_interval_is_zero() {
        assert_close(mccormick_worst_case_gap(2.0, 2.0, -1.0, 5.0), 0.0);
        assert_close(mccormick_worst_case_gap(-3.0, 4.0, 7.0, 7.0), 0.0);
    }

    #[test]
    fn test_verify_gap_bound_holds_for_representative_boxes() {
        assert!(verify_gap_bound(1.0, 3.0, 2.0, 6.0));
        assert!(verify_gap_bound(-5.0, -1.0, -4.0, -2.0));
        assert!(verify_gap_bound(-2.0, 2.0, -3.0, 1.0));
        assert!(verify_gap_bound(0.0, 0.0, -3.0, 5.0));
    }

    #[test]
    fn test_shared_input_gap_scales_quadratically_with_eps() {
        let gap_small = shared_input_mccormick_gap(2.0, -3.0, 1.5, 0.25);
        let gap_large = shared_input_mccormick_gap(2.0, -3.0, 1.5, 0.5);
        assert_close(gap_small, 0.375);
        assert_close(gap_large, 1.5);
        assert_close(gap_large / gap_small, 4.0);
    }

    #[test]
    fn test_shared_input_normalized_gap_scales_linearly() {
        let center = -0.75;
        let gap_small = shared_input_mccormick_gap(3.0, 5.0, center, 0.1);
        let gap_large = shared_input_mccormick_gap(3.0, 5.0, center, 0.2);
        let (q_lower_small, q_upper_small) = shared_input_interval(3.0, center, 0.1);
        let (q_lower_large, q_upper_large) = shared_input_interval(3.0, center, 0.2);
        let ratio_small = gap_small / interval_width(q_lower_small, q_upper_small);
        let ratio_large = gap_large / interval_width(q_lower_large, q_upper_large);

        assert_close(ratio_small, 0.25);
        assert_close(ratio_large, 0.5);
        assert_close(ratio_large / ratio_small, 2.0);
        assert!(verify_shared_input_linear_growth(3.0, 5.0, center, 0.2));
    }

    #[test]
    fn test_shared_input_gap_zero_eps_is_zero() {
        assert_close(shared_input_mccormick_gap(4.0, -7.0, 2.0, 0.0), 0.0);
        assert!(verify_shared_input_linear_growth(4.0, -7.0, 2.0, 0.0));
    }

    #[test]
    fn test_shared_input_gap_negative_weights() {
        let gap = shared_input_mccormick_gap(-2.0, -3.0, 1.0, 0.5);
        assert_close(gap, 1.5);
        assert!(verify_shared_input_linear_growth(-2.0, -3.0, 1.0, 0.5));
    }

    #[test]
    fn test_shared_input_gap_zero_center() {
        assert_close(shared_input_mccormick_gap(2.0, 5.0, 0.0, 0.25), 0.625);
        assert!(verify_shared_input_linear_growth(2.0, 5.0, 0.0, 0.25));
    }

    #[test]
    fn test_c005_spec_status_is_pending() {
        let spec = McCormickLinearErrorSpec::new();
        assert_eq!(spec.status(), ProofStatus::DerivedPending);
    }

    #[test]
    fn test_c005_spec_verifiers_succeed() {
        let spec = McCormickLinearErrorSpec::new();
        assert!(spec.verify_gap_bound(-2.0, 2.0, -3.0, 1.0));
        assert!(spec.verify_shared_input(-2.0, 5.0, 0.5, 0.25));
        assert!(spec.verify_linear_growth(-2.0, 5.0, 0.5, 0.25));
    }

    #[test]
    fn test_c005_theorem_entry() {
        let entry = c005_theorem_entry();
        assert_eq!(entry.id, "C005");
        assert_eq!(entry.status, ProofStatus::DerivedPending);
        assert_eq!(entry.phase, Phase::Phase3);
    }
}
