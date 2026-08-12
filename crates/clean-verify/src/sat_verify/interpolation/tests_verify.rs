// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the unified Craig property verification module.

use super::extract::{ExtractionAlgorithm, InterpolantExtractor};
use super::verify::{quick_check_variable_restriction, verify_craig_property, CraigVerifyError};
use super::PropFormula;

#[test]
fn test_verify_craig_valid_simple() {
    // A = {x1}, B = {!x1}, Interpolant = x1
    let result = verify_craig_property(&[vec![1]], &[vec![-1]], &PropFormula::Var(1))
        .expect("valid interpolant should pass");
    assert!(result.all_valid);
    assert!(result.implication_holds);
    assert!(result.contradiction_holds);
    assert!(result.variable_restriction_holds);
    assert!(result.violating_variables.is_empty());
    assert_eq!(result.num_vars, 1);
    assert!(result.shared_variables.contains(&1));
}

#[test]
fn test_verify_craig_valid_negated() {
    // A = {!x1}, B = {x1}, Interpolant = !x1
    let result = verify_craig_property(
        &[vec![-1]],
        &[vec![1]],
        &PropFormula::Not(Box::new(PropFormula::Var(1))),
    )
    .expect("negated interpolant should pass");
    assert!(result.all_valid);
}

#[test]
fn test_verify_craig_true_interpolant_fails_contradiction() {
    let err = verify_craig_property(&[vec![1]], &[vec![-1]], &PropFormula::True)
        .expect_err("True fails contradiction");
    assert!(matches!(
        err,
        CraigVerifyError::ContradictionViolated { .. }
    ));
}

#[test]
fn test_verify_craig_false_interpolant_fails_implication() {
    let err = verify_craig_property(&[vec![1]], &[vec![-1]], &PropFormula::False)
        .expect_err("False fails implication");
    assert!(matches!(err, CraigVerifyError::ImplicationViolated { .. }));
}

#[test]
fn test_verify_craig_variable_restriction_only_violation() {
    // A = {x1}, B = {!x1}
    // Interpolant uses x2 (not in A or B at all)
    // Note: x2 not in either set, so A |= x2 might fail too.
    // Actually x2 defaults to false, so A (x1=true) doesn't imply x2(false).
    // So this is a multiple violation.
    let err = verify_craig_property(&[vec![1]], &[vec![-1]], &PropFormula::Var(2))
        .expect_err("x2 not in shared vars should fail");
    match err {
        CraigVerifyError::MultipleViolations { detail } => {
            assert!(!detail.variable_restriction_holds);
            assert!(detail.violating_variables.contains(&2));
        }
        CraigVerifyError::VariableRestrictionViolated(vars) => {
            assert!(vars.contains(&2));
        }
        other => panic!("unexpected error: {other:?}"),
    }
}

#[test]
fn test_verify_craig_multi_clause_valid() {
    // A = {x1, x2}, {x1, !x2}  (equivalent to x1)
    // B = {!x1, x3}, {!x1, !x3}  (equivalent to !x1)
    // Shared: {x1}
    // Interpolant: x1
    let a = vec![vec![1, 2], vec![1, -2]];
    let b = vec![vec![-1, 3], vec![-1, -3]];
    let result =
        verify_craig_property(&a, &b, &PropFormula::Var(1)).expect("x1 is valid interpolant");
    assert!(result.all_valid);
}

#[test]
fn test_verify_craig_multi_clause_not_x1() {
    // Same A, B as above, but interpolant = !x1
    // A = {x1, x2}, {x1, !x2} -- forces x1=true
    // !x1 = false when x1=true, so A does NOT imply !x1
    let a = vec![vec![1, 2], vec![1, -2]];
    let b = vec![vec![-1, 3], vec![-1, -3]];
    let err = verify_craig_property(&a, &b, &PropFormula::Not(Box::new(PropFormula::Var(1))))
        .expect_err("!x1 should fail implication");
    match err {
        CraigVerifyError::ImplicationViolated { counterexample } => {
            // x1 must be true in the counterexample
            assert_eq!(counterexample.get(&1), Some(&true));
        }
        CraigVerifyError::MultipleViolations { detail } => {
            assert!(!detail.implication_holds);
        }
        other => panic!("unexpected error: {other:?}"),
    }
}

#[test]
fn test_verify_craig_extracted_interpolant() {
    // Use the extractor to build a refutation, then verify the result.
    let mut ext = InterpolantExtractor::new();
    let a0 = ext.add_a_clause(vec![1, 2]);
    let a1 = ext.add_a_clause(vec![1, -2]);
    let b0 = ext.add_b_clause(vec![-1, 3]);
    let b1 = ext.add_b_clause(vec![-1, -3]);
    let r0 = ext.add_resolution(a0, a1, 2);
    let r1 = ext.add_resolution(b0, b1, 3);
    ext.add_resolution(r0, r1, 1);

    let extraction = ext
        .extract(ExtractionAlgorithm::McMillan)
        .expect("extraction should succeed");

    let a_clauses = vec![vec![1, 2], vec![1, -2]];
    let b_clauses = vec![vec![-1, 3], vec![-1, -3]];
    let result = verify_craig_property(&a_clauses, &b_clauses, &extraction.interpolant)
        .expect("extracted interpolant should satisfy Craig property");
    assert!(result.all_valid);
}

#[test]
fn test_quick_check_variable_restriction_pass() {
    assert!(quick_check_variable_restriction(
        &[vec![1, 2]],
        &[vec![-2, 3]],
        &PropFormula::Var(2),
    ));
}

#[test]
fn test_quick_check_variable_restriction_fail() {
    assert!(!quick_check_variable_restriction(
        &[vec![1, 2]],
        &[vec![-2, 3]],
        &PropFormula::Var(1), // A-local
    ));
}

#[test]
fn test_verify_craig_counterexample_structure() {
    // A = {x1}, B = {!x1}
    // Interpolant = False -> fails implication
    let err = verify_craig_property(&[vec![1]], &[vec![-1]], &PropFormula::False)
        .expect_err("should fail");
    if let CraigVerifyError::ImplicationViolated { counterexample } = err {
        // x1=true satisfies A but not False
        assert_eq!(counterexample.get(&1), Some(&true));
    } else {
        panic!("expected ImplicationViolated");
    }
}

#[test]
fn test_verify_craig_witness_structure() {
    // A = {x1}, B = {!x1}
    // Interpolant = True -> fails contradiction
    let err = verify_craig_property(&[vec![1]], &[vec![-1]], &PropFormula::True)
        .expect_err("should fail");
    if let CraigVerifyError::ContradictionViolated { witness } = err {
        // x1=false satisfies True and also !x1
        assert_eq!(witness.get(&1), Some(&false));
    } else {
        panic!("expected ContradictionViolated");
    }
}

#[test]
fn test_verify_craig_or_interpolant() {
    // A = {x1, x2}, {!x1, x2} (implies x2)
    // B = {!x2}
    // Shared: {x2}
    // Interpolant: x2
    let a = vec![vec![1, 2], vec![-1, 2]];
    let b = vec![vec![-2]];
    let result = verify_craig_property(&a, &b, &PropFormula::Var(2)).expect("x2 should be valid");
    assert!(result.all_valid);
}

#[test]
fn test_verify_craig_shared_variables_computed() {
    let a = vec![vec![1, 2, 3]];
    let b = vec![vec![-2, -3, 4]];
    // Shared = {2, 3}
    // Note: x2 alone is not a valid interpolant for this pair (A doesn't
    // imply x2), so verify_craig_property returns an Err. Extract
    // shared_variables from whichever variant we get.
    let shared = match verify_craig_property(&a, &b, &PropFormula::Var(2)) {
        Ok(result) => result.shared_variables,
        Err(CraigVerifyError::MultipleViolations { detail }) => detail.shared_variables,
        Err(CraigVerifyError::ImplicationViolated { .. })
        | Err(CraigVerifyError::ContradictionViolated { .. })
        | Err(CraigVerifyError::VariableRestrictionViolated(_)) => {
            panic!("expected Ok or MultipleViolations for this formula pair");
        }
    };
    assert!(shared.contains(&2));
    assert!(shared.contains(&3));
    assert!(!shared.contains(&1));
    assert!(!shared.contains(&4));
}
