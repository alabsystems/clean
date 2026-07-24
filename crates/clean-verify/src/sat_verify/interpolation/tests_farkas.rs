// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for Farkas-based LRA interpolation.

use super::farkas::{
    extract_lra_interpolant, farkas_to_prop_formula, verify_farkas_craig_property, FarkasError,
    LinearInequality,
};
use super::PropFormula;
use std::collections::{HashMap, HashSet};

fn make_ineq(coeffs: &[(u32, f64)], bound: f64) -> LinearInequality {
    LinearInequality::new(coeffs.iter().copied().collect(), bound)
}

#[test]
fn test_farkas_basic_extraction() {
    // A: x1 + x2 <= 5 (x1 is A-local, x2 is shared)
    // B: -x2 + x3 <= -6 (x3 is B-local, x2 is shared)
    // Farkas: lambda=[1], mu=[1]
    // Interpolant restricted to shared vars: x2 <= 5
    let a = vec![make_ineq(&[(1, 1.0), (2, 1.0)], 5.0)];
    let b = vec![make_ineq(&[(2, -1.0), (3, 1.0)], -6.0)];
    let shared: HashSet<u32> = [2].into_iter().collect();

    let result = extract_lra_interpolant(&a, &b, &[1.0], &[1.0], &shared)
        .expect("basic extraction should succeed");

    assert!(result.interpolant.coeffs.contains_key(&2));
    assert!(
        !result.interpolant.coeffs.contains_key(&1),
        "x1 should be projected"
    );
    assert!(
        !result.interpolant.coeffs.contains_key(&3),
        "x3 should not appear"
    );
    assert!(result.a_projected_vars.contains(&1));
    assert!(result.b_projected_vars.contains(&3));
}

#[test]
fn test_farkas_weighted_combination() {
    // A: 2*x1 + x2 <= 10, x2 <= 3
    // B: -x2 <= -15
    // Farkas: lambda=[1.0, 2.0], mu=[1.0]
    // A-combination on shared (x2):
    //   1.0 * x2 + 2.0 * x2 = 3*x2
    //   bound: 1.0*10 + 2.0*3 = 16
    let a = vec![
        make_ineq(&[(1, 2.0), (2, 1.0)], 10.0),
        make_ineq(&[(2, 1.0)], 3.0),
    ];
    let b = vec![make_ineq(&[(2, -1.0)], -15.0)];
    let shared: HashSet<u32> = [2].into_iter().collect();

    let result = extract_lra_interpolant(&a, &b, &[1.0, 2.0], &[1.0], &shared)
        .expect("weighted extraction should succeed");

    assert!((result.interpolant.coeffs[&2] - 3.0).abs() < f64::EPSILON);
    assert!((result.interpolant.bound - 16.0).abs() < f64::EPSILON);
}

#[test]
fn test_farkas_zero_coefficient_skipped() {
    // A: x1 <= 5 (no shared vars)
    // B: -x2 <= -6
    // Farkas: lambda=[0.0], mu=[1.0]  -- zero lambda skips A-literal
    let a = vec![make_ineq(&[(1, 1.0)], 5.0)];
    let b = vec![make_ineq(&[(2, -1.0)], -6.0)];
    let shared: HashSet<u32> = HashSet::new();

    let result = extract_lra_interpolant(&a, &b, &[0.0], &[1.0], &shared)
        .expect("zero-coeff extraction should succeed");

    assert!(result.interpolant.coeffs.is_empty());
    assert!((result.interpolant.bound - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_farkas_negative_coefficient_rejected() {
    let a = vec![make_ineq(&[(1, 1.0)], 0.0)];
    let b = vec![make_ineq(&[(1, -1.0)], -1.0)];
    let shared: HashSet<u32> = [1].into_iter().collect();

    let err = extract_lra_interpolant(&a, &b, &[-1.0], &[1.0], &shared)
        .expect_err("negative coefficient should fail");
    assert!(matches!(
        err,
        FarkasError::NegativeCoefficient { index: 0, .. }
    ));
}

#[test]
fn test_farkas_length_mismatch_a() {
    let a = vec![make_ineq(&[(1, 1.0)], 0.0)];
    let b = vec![make_ineq(&[(1, -1.0)], -1.0)];
    let shared: HashSet<u32> = [1].into_iter().collect();

    let err = extract_lra_interpolant(&a, &b, &[1.0, 2.0], &[1.0], &shared)
        .expect_err("length mismatch should fail");
    assert!(matches!(
        err,
        FarkasError::LengthMismatch {
            coeff_count: 2,
            lit_count: 1
        }
    ));
}

#[test]
fn test_farkas_length_mismatch_b() {
    let a = vec![make_ineq(&[(1, 1.0)], 0.0)];
    let b = vec![make_ineq(&[(1, -1.0)], -1.0)];
    let shared: HashSet<u32> = [1].into_iter().collect();

    let err = extract_lra_interpolant(&a, &b, &[1.0], &[], &shared)
        .expect_err("B length mismatch should fail");
    assert!(matches!(err, FarkasError::LengthMismatch { .. }));
}

#[test]
fn test_farkas_craig_verification() {
    let a = vec![make_ineq(&[(1, 1.0), (2, 1.0)], 5.0)];
    let b = vec![make_ineq(&[(2, -1.0), (3, 1.0)], -6.0)];
    let shared: HashSet<u32> = [2].into_iter().collect();

    let result = extract_lra_interpolant(&a, &b, &[1.0], &[1.0], &shared)
        .expect("extraction should succeed");

    let verification = verify_farkas_craig_property(&a, &b, &result);
    assert!(verification.variable_restriction_holds);
    assert!(verification.coefficients_non_negative);
    assert!(verification.variable_violations.is_empty());
}

#[test]
fn test_farkas_to_prop_empty_coeffs() {
    use super::farkas::FarkasInterpolationResult;

    let result = FarkasInterpolationResult {
        interpolant: LinearInequality::new(HashMap::new(), 5.0),
        shared_vars: HashSet::new(),
        a_projected_vars: HashSet::new(),
        b_projected_vars: HashSet::new(),
        a_farkas_coefficients: vec![],
        b_farkas_coefficients: vec![],
    };
    assert_eq!(farkas_to_prop_formula(&result), PropFormula::True);
}

#[test]
fn test_farkas_to_prop_negative_bound() {
    use super::farkas::FarkasInterpolationResult;

    let result = FarkasInterpolationResult {
        interpolant: LinearInequality::new(HashMap::new(), -5.0),
        shared_vars: HashSet::new(),
        a_projected_vars: HashSet::new(),
        b_projected_vars: HashSet::new(),
        a_farkas_coefficients: vec![],
        b_farkas_coefficients: vec![],
    };
    assert_eq!(farkas_to_prop_formula(&result), PropFormula::False);
}

#[test]
fn test_farkas_to_prop_single_variable() {
    use super::farkas::FarkasInterpolationResult;

    let mut coeffs = HashMap::new();
    coeffs.insert(5, 1.0);
    let result = FarkasInterpolationResult {
        interpolant: LinearInequality::new(coeffs, 3.0),
        shared_vars: [5].into_iter().collect(),
        a_projected_vars: HashSet::new(),
        b_projected_vars: HashSet::new(),
        a_farkas_coefficients: vec![1.0],
        b_farkas_coefficients: vec![1.0],
    };
    assert_eq!(farkas_to_prop_formula(&result), PropFormula::Var(5));
}

#[test]
fn test_farkas_to_prop_multiple_variables_sorted() {
    use super::farkas::FarkasInterpolationResult;

    let mut coeffs = HashMap::new();
    coeffs.insert(3, 1.0);
    coeffs.insert(1, 2.0);
    let result = FarkasInterpolationResult {
        interpolant: LinearInequality::new(coeffs, 5.0),
        shared_vars: [1, 3].into_iter().collect(),
        a_projected_vars: HashSet::new(),
        b_projected_vars: HashSet::new(),
        a_farkas_coefficients: vec![1.0],
        b_farkas_coefficients: vec![1.0],
    };
    let formula = farkas_to_prop_formula(&result);
    // Variables should be sorted: AndType(Var(1), Var(3))
    assert_eq!(
        formula,
        PropFormula::AndType(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(3)))
    );
}

#[test]
fn test_linear_inequality_satisfaction() {
    // 2*x1 + 3*x2 <= 12
    let ineq = make_ineq(&[(1, 2.0), (2, 3.0)], 12.0);

    let mut asgn = HashMap::new();
    asgn.insert(1, 3.0);
    asgn.insert(2, 2.0);
    // 2*3 + 3*2 = 12 <= 12
    assert!(ineq.is_satisfied(&asgn));

    asgn.insert(2, 3.0);
    // 2*3 + 3*3 = 15 > 12
    assert!(!ineq.is_satisfied(&asgn));
}

#[test]
fn test_linear_inequality_missing_var_defaults_zero() {
    let ineq = make_ineq(&[(1, 5.0), (2, 3.0)], 10.0);
    let mut asgn = HashMap::new();
    asgn.insert(1, 2.0);
    // Missing x2 defaults to 0: 5*2 + 3*0 = 10 <= 10
    assert!(ineq.is_satisfied(&asgn));
}
