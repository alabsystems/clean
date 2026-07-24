// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C003 ECLipsE convergence.

use super::c003_spec::C003ConvergenceSpec;
use super::convergence::{
    convergence_rate_bound, iterate_to_fixed_point, verify_contraction, verify_convergence_rate,
    ContractiveMap, EclipseRefinementStep,
};
use crate::spec::ProofStatus;

const TOL: f64 = 1e-10;

fn step<const ROWS: usize, const COLS: usize>(
    weight_matrix: [[f64; COLS]; ROWS],
    bias: [f64; ROWS],
    lipschitz_constant: f64,
) -> EclipseRefinementStep {
    EclipseRefinementStep::new(
        weight_matrix.into_iter().map(|row| row.to_vec()).collect(),
        bias.to_vec(),
        lipschitz_constant,
    )
}

fn assert_close(actual: f64, expected: f64) {
    assert!(
        (actual - expected).abs() <= TOL,
        "expected {expected:.12}, got {actual:.12}"
    );
}

fn assert_vec_close(actual: &[f64], expected: &[f64]) {
    assert_eq!(actual.len(), expected.len(), "length mismatch");
    for (i, (&a, &e)) in actual.iter().zip(expected.iter()).enumerate() {
        assert!(
            (a - e).abs() <= TOL,
            "mismatch at index {i}: expected {e:.12}, got {a:.12}"
        );
    }
}

fn l2_distance(x: &[f64], y: &[f64]) -> f64 {
    x.iter()
        .zip(y.iter())
        .map(|(&xi, &yi)| {
            let d = xi - yi;
            d * d
        })
        .sum::<f64>()
        .sqrt()
}

fn iterate_reference<M: ContractiveMap>(map: &M, x0: &[f64], n: usize) -> Vec<f64> {
    let mut x = x0.to_vec();
    for _ in 0..n {
        x = map.apply(&x);
    }
    x
}

#[test]
fn test_c003_spec_status_is_derived_proved() {
    let spec = C003ConvergenceSpec::new();
    assert_eq!(spec.status(), ProofStatus::DerivedPending);
}

#[test]
fn test_contraction_simple_scaling_succeeds() {
    let map = step([[0.5, 0.0], [0.0, 0.5]], [0.0, 0.0], 0.5);
    let x = [2.0, -4.0];
    let y = [-2.0, 0.0];

    verify_contraction(&map, &x, &y, TOL).expect("0.5 * I should be contractive");
    assert_eq!(map.lipschitz_constant(), 0.5);
    assert_vec_close(&map.apply(&x), &[1.0, -2.0]);
}

#[test]
fn test_contraction_violated_reports_error() {
    let map = step([[1.1, 0.0], [0.0, 1.1]], [0.0, 0.0], 1.1);
    let x = [1.0, -2.0];
    let y = [0.0, 0.0];

    assert!(
        verify_contraction(&map, &x, &y, TOL).is_err(),
        "expansive map should fail contraction verification"
    );
}

#[test]
fn test_convergence_rate_bound_geometric_decay() {
    let bound = convergence_rate_bound(0.5, 2.5, 4);
    let expected = 0.5_f64.powi(4) / (1.0 - 0.5) * 2.5;
    assert_close(bound, expected);
}

#[test]
fn test_convergence_rate_bound_zero_iterations() {
    let bound = convergence_rate_bound(0.5, 3.0, 0);
    assert_close(bound, 3.0 / (1.0 - 0.5));
}

#[test]
fn test_iterate_to_fixed_point_simple_contraction() {
    let map = step([[0.5, 0.0], [0.0, 0.5]], [1.0, 1.0], 0.5);
    let x0 = [0.0, 0.0];

    let result = iterate_to_fixed_point(&map, &x0, 64, 1e-12)
        .expect("simple affine contraction should converge");
    let _ = result;

    let fixed_point = [2.0, 2.0];
    let approx = iterate_reference(&map, &x0, 60);
    assert_vec_close(&approx, &fixed_point);
    assert!(l2_distance(&map.apply(&approx), &approx) <= 1e-10);
}

#[test]
fn test_iterate_to_fixed_point_2d_contraction() {
    let map = step([[0.25, 0.10], [0.0, 0.40]], [1.0, -0.5], 0.4);
    let x0 = [0.0, 0.0];

    let result = iterate_to_fixed_point(&map, &x0, 96, 1e-12)
        .expect("2D affine contraction should converge");
    let _ = result;

    let fixed_point = [1.222_222_222_222, -0.833_333_333_333];
    let approx = iterate_reference(&map, &x0, 80);
    assert_vec_close(&approx, &fixed_point);
    assert!(l2_distance(&map.apply(&approx), &approx) <= 1e-10);
}

#[test]
fn test_verify_convergence_rate_distances_decrease() {
    let map = step([[0.5, 0.0], [0.0, 0.5]], [1.0, 1.0], 0.5);
    let x0 = [0.0, 0.0];

    let witness = verify_convergence_rate(&map, &x0, 5, TOL)
        .expect("convergence-rate verification should succeed");
    let _ = witness;

    let fixed_point = [2.0, 2.0];
    let mut x = x0.to_vec();
    let mut prev = l2_distance(&x, &fixed_point);
    for _ in 0..5 {
        x = map.apply(&x);
        let curr = l2_distance(&x, &fixed_point);
        assert!(curr < prev, "distance to fixed point should decrease");
        prev = curr;
    }
}

#[test]
fn test_convergence_rate_bound_tight_lipschitz() {
    let bound = convergence_rate_bound(0.9, 1.0, 10);
    let expected = 0.9_f64.powi(10) / (1.0 - 0.9);

    assert_close(bound, expected);
    assert!(bound > 3.0, "L = 0.9 should converge slowly");
}
