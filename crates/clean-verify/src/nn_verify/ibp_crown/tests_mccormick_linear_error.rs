// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C005 McCormick bilinear relaxation linear error growth

use crate::spec::ProofStatus;

use super::mccormick_linear_error::*;
use super::Phase;

const FLOAT_TOLERANCE: f64 = 1e-10;
const COARSE_GRID_STEP: f64 = 0.1;
const FINE_GRID_STEP: f64 = 0.05;

fn assert_abs_diff_eq(actual: f64, expected: f64) {
    let abs_diff = (actual - expected).abs();
    assert!(
        abs_diff <= FLOAT_TOLERANCE,
        "actual={actual}, expected={expected}, abs_diff={abs_diff}"
    );
}

fn assert_gap_bound_on_grid(
    xl: f64,
    xu: f64,
    yl: f64,
    yu: f64,
    step: f64,
    include_boundary: bool,
) -> f64 {
    let bound = mccormick_worst_case_gap(xl, xu, yl, yu);
    let x_steps = ((xu - xl) / step).round() as usize;
    let y_steps = ((yu - yl) / step).round() as usize;
    let mut max_gap: f64 = 0.0;

    for i in 0..=x_steps {
        if !include_boundary && (i == 0 || i == x_steps) {
            continue;
        }
        let x = xl + step * i as f64;
        for j in 0..=y_steps {
            if !include_boundary && (j == 0 || j == y_steps) {
                continue;
            }
            let y = yl + step * j as f64;
            let gap = mccormick_gap_at_point(x, y, xl, xu, yl, yu);
            assert!(
                gap >= -FLOAT_TOLERANCE,
                "gap must be non-negative: gap={gap}, x={x}, y={y}, box=[{xl}, {xu}]x[{yl}, {yu}]"
            );
            assert!(
                gap <= bound + FLOAT_TOLERANCE,
                "gap exceeds worst-case bound: gap={gap}, bound={bound}, x={x}, y={y}, box=[{xl}, {xu}]x[{yl}, {yu}]"
            );
            max_gap = max_gap.max(gap);
        }
    }

    max_gap
}

#[test]
fn test_mccormick_gap_at_point_midpoint_is_maximum() {
    let (xl, xu, yl, yu) = (0.0, 2.0, 0.0, 4.0);
    let midpoint_gap = mccormick_gap_at_point(1.0, 2.0, xl, xu, yl, yu);
    let expected_gap = (xu - xl) * (yu - yl) / 4.0;
    let max_gap = assert_gap_bound_on_grid(xl, xu, yl, yu, COARSE_GRID_STEP, true);

    assert_abs_diff_eq(midpoint_gap, expected_gap);
    assert_abs_diff_eq(midpoint_gap, mccormick_worst_case_gap(xl, xu, yl, yu));
    assert_abs_diff_eq(midpoint_gap, max_gap);
}

#[test]
fn test_mccormick_gap_at_point_corners_is_zero() {
    let corners = [(-2.0, -1.0), (-2.0, 4.0), (3.0, -1.0), (3.0, 4.0)];
    for (x, y) in corners {
        let gap = mccormick_gap_at_point(x, y, -2.0, 3.0, -1.0, 4.0);
        assert_abs_diff_eq(gap, 0.0);
    }
}

#[test]
fn test_worst_case_gap_both_positive() {
    assert_abs_diff_eq(mccormick_worst_case_gap(1.0, 3.0, 2.0, 4.0), 1.0);
}

#[test]
fn test_worst_case_gap_both_negative() {
    assert_abs_diff_eq(mccormick_worst_case_gap(-4.0, -1.0, -3.0, -2.0), 0.75);
}

#[test]
fn test_worst_case_gap_crossing_zero() {
    assert_abs_diff_eq(mccormick_worst_case_gap(-2.0, 3.0, -1.0, 4.0), 6.25);
}

#[test]
fn test_worst_case_gap_symmetric() {
    let a = 2.5;
    let b = 1.2;
    assert_abs_diff_eq(mccormick_worst_case_gap(-a, a, -b, b), a * b);
}

#[test]
fn test_worst_case_gap_point_interval_is_zero() {
    assert_abs_diff_eq(mccormick_worst_case_gap(2.0, 2.0, 3.0, 3.0), 0.0);
}

#[test]
fn test_verify_gap_bound_holds_for_all_sign_patterns() {
    let boxes = [
        (1.0, 3.0, 2.0, 4.0),
        (-4.0, -1.0, -3.0, -2.0),
        (-4.0, -1.0, 2.0, 5.0),
        (1.0, 4.0, -5.0, -2.0),
        (-2.0, 3.0, 1.0, 4.0),
        (1.0, 4.0, -2.0, 3.0),
    ];

    for (xl, xu, yl, yu) in boxes {
        let midpoint_x = 0.5 * (xl + xu);
        let midpoint_y = 0.5 * (yl + yu);
        let bound = mccormick_worst_case_gap(xl, xu, yl, yu);
        let max_gap = assert_gap_bound_on_grid(xl, xu, yl, yu, COARSE_GRID_STEP, true);

        assert!(verify_gap_bound(xl, xu, yl, yu));
        assert_abs_diff_eq(
            mccormick_gap_at_point(midpoint_x, midpoint_y, xl, xu, yl, yu),
            bound,
        );
        assert_abs_diff_eq(max_gap, bound);
    }
}

#[test]
fn test_verify_gap_bound_grid_scan_interior() {
    let (xl, xu, yl, yu) = (-2.0, 3.0, -1.0, 4.0);
    let bound = mccormick_worst_case_gap(xl, xu, yl, yu);
    let midpoint_gap = mccormick_gap_at_point(0.5, 1.5, xl, xu, yl, yu);
    let max_gap = assert_gap_bound_on_grid(xl, xu, yl, yu, FINE_GRID_STEP, false);

    assert!(verify_gap_bound(xl, xu, yl, yu));
    assert_abs_diff_eq(midpoint_gap, bound);
    assert_abs_diff_eq(max_gap, bound);
}

#[test]
fn test_shared_input_gap_scales_quadratically_with_eps() {
    let gap_eps = shared_input_mccormick_gap(2.0, -3.0, 1.5, 0.25);
    let gap_double_eps = shared_input_mccormick_gap(2.0, -3.0, 1.5, 0.5);

    assert_abs_diff_eq(gap_eps, 0.375);
    assert_abs_diff_eq(gap_double_eps, 1.5);
    assert_abs_diff_eq(gap_double_eps / gap_eps, 4.0);
}

#[test]
fn test_shared_input_normalized_gap_linear_in_eps() {
    let w_q: f64 = 3.0;
    let w_k: f64 = 5.0;
    let center = -0.75;
    let eps_large: f64 = 0.2;
    let eps_small: f64 = 0.1;

    let gap_large = shared_input_mccormick_gap(w_q, w_k, center, eps_large);
    let gap_small = shared_input_mccormick_gap(w_q, w_k, center, eps_small);
    let width_large = 2.0 * w_q.abs() * eps_large;
    let width_small = 2.0 * w_q.abs() * eps_small;
    let ratio_large = gap_large / width_large;
    let ratio_small = gap_small / width_small;

    assert_abs_diff_eq(ratio_large, 0.5);
    assert_abs_diff_eq(ratio_small, 0.25);
    assert_abs_diff_eq(ratio_large / ratio_small, 2.0);
    assert!(verify_shared_input_linear_growth(
        w_q, w_k, center, eps_large
    ));
    assert!(verify_shared_input_linear_growth(
        w_q, w_k, center, eps_small
    ));
}

#[test]
fn test_shared_input_gap_zero_eps_is_zero() {
    let gap = shared_input_mccormick_gap(4.0, -7.0, 2.0, 0.0);
    assert_abs_diff_eq(gap, 0.0);
    assert!(verify_shared_input_linear_growth(4.0, -7.0, 2.0, 0.0));
}

#[test]
fn test_shared_input_gap_negative_weights() {
    let gap = shared_input_mccormick_gap(-2.0, -3.0, 1.0, 0.5);
    let expected_gap = 2.0 * 3.0 * 0.5 * 0.5;

    assert_abs_diff_eq(gap, expected_gap);
    assert!(verify_shared_input_linear_growth(-2.0, -3.0, 1.0, 0.5));
}

#[test]
fn test_shared_input_gap_zero_center() {
    let gap = shared_input_mccormick_gap(2.0, 5.0, 0.0, 0.25);
    assert_abs_diff_eq(gap, 0.625);
    assert!(verify_shared_input_linear_growth(2.0, 5.0, 0.0, 0.25));
}

#[test]
fn test_verify_shared_input_linear_growth_various_configs() {
    let configs = [
        (2.0, 3.0, 1.0, 0.1),
        (-1.5, 4.0, -0.75, 0.2),
        (2.0, -5.0, 0.0, 0.3),
        (-3.0, -2.0, 1.5, 0.05),
    ];

    for (w_q, w_k, center, eps) in configs {
        let gap = shared_input_mccormick_gap(w_q, w_k, center, eps);
        let expected_gap = w_q.abs() * w_k.abs() * eps * eps;
        let q_width = 2.0 * w_q.abs() * eps;
        let k_width = 2.0 * w_k.abs() * eps;
        let q_ratio = gap / q_width;
        let k_ratio = gap / k_width;

        assert!(verify_shared_input_linear_growth(w_q, w_k, center, eps));
        assert_abs_diff_eq(gap, expected_gap);
        assert_abs_diff_eq(q_ratio, 0.5 * w_k.abs() * eps);
        assert_abs_diff_eq(k_ratio, 0.5 * w_q.abs() * eps);
    }
}

#[test]
fn test_c005_spec_status_is_pending() {
    let spec = McCormickLinearErrorSpec::new();
    assert_eq!(spec.status(), ProofStatus::DerivedPending);
}

#[test]
fn test_c005_spec_verify_gap_bound_unit_interval_succeeds() {
    let spec = McCormickLinearErrorSpec::new();
    assert!(spec.verify_gap_bound(0.0, 1.0, 0.0, 1.0));
    assert_abs_diff_eq(mccormick_worst_case_gap(0.0, 1.0, 0.0, 1.0), 0.25);
}

#[test]
fn test_c005_spec_verify_linear_growth_succeeds() {
    let spec = McCormickLinearErrorSpec::new();
    assert!(spec.verify_linear_growth(-2.0, 5.0, 0.5, 0.25));
}

#[test]
fn test_c005_spec_verify_shared_input_succeeds() {
    let spec = McCormickLinearErrorSpec::new();
    assert!(spec.verify_shared_input(-2.0, 5.0, 0.5, 0.25));
    assert_abs_diff_eq(shared_input_mccormick_gap(-2.0, 5.0, 0.5, 0.25), 0.625);
}

#[test]
fn test_c005_theorem_entry_fields() {
    let entry = c005_theorem_entry();

    assert_eq!(entry.id, "C005");
    assert_eq!(
        entry.description,
        "McCormick bilinear relaxation normalized error grows linearly"
    );
    assert_eq!(entry.status, ProofStatus::DerivedPending);
    assert_eq!(entry.phase, Phase::Phase3);
}
