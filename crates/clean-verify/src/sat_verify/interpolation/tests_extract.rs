// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the high-level interpolant extraction API.

use super::extract::{
    extract_interpolant_from_parts, ExtractionAlgorithm, ExtractionError, InterpolantExtractor,
};
use super::property::verify_all_properties;
use super::PropFormula;

/// Build a simple refutation: A = {x}, B = {!x}, resolve on x.
fn simple_refutation() -> InterpolantExtractor {
    let mut ext = InterpolantExtractor::new();
    let a = ext.add_a_clause(vec![1]);
    let b = ext.add_b_clause(vec![-1]);
    ext.add_resolution(a, b, 1);
    ext
}

/// Build a multi-step refutation with A-local, B-local, and shared variables.
///
/// A = {x1, x2}, {x1, !x2}  (x2 is A-local; after resolution gives {x1})
/// B = {!x1, x3}, {!x1, !x3}  (x3 is B-local; after resolution gives {!x1})
/// Resolve {x1} and {!x1} on x1 -> empty clause
fn multi_step_refutation() -> InterpolantExtractor {
    let mut ext = InterpolantExtractor::new();
    let a0 = ext.add_a_clause(vec![1, 2]);
    let a1 = ext.add_a_clause(vec![1, -2]);
    let b0 = ext.add_b_clause(vec![-1, 3]);
    let b1 = ext.add_b_clause(vec![-1, -3]);
    let r0 = ext.add_resolution(a0, a1, 2); // {x1}
    let r1 = ext.add_resolution(b0, b1, 3); // {!x1}
    ext.add_resolution(r0, r1, 1); // empty
    ext
}

#[test]
fn test_extract_simple_refutation_mcmillan() {
    let ext = simple_refutation();
    let result = ext
        .extract(ExtractionAlgorithm::McMillan)
        .expect("simple refutation should succeed");

    assert!(result.shared_vars.contains(&1));
    assert!(result.a_local_vars.is_empty());
    assert!(result.b_local_vars.is_empty());

    // Verify Craig property on the result.
    let verify = verify_all_properties(&[vec![1]], &[vec![-1]], &result.interpolant, 1);
    assert!(
        verify.all_valid,
        "McMillan interpolant must satisfy Craig property"
    );
}

#[test]
fn test_extract_simple_refutation_pudlak() {
    let ext = simple_refutation();
    let result = ext
        .extract(ExtractionAlgorithm::Pudlak)
        .expect("Pudlak extraction should succeed");

    let verify = verify_all_properties(&[vec![1]], &[vec![-1]], &result.interpolant, 1);
    assert!(
        verify.all_valid,
        "Pudlak interpolant must satisfy Craig property"
    );
}

#[test]
fn test_extract_simple_refutation_both() {
    let ext = simple_refutation();
    let result = ext
        .extract(ExtractionAlgorithm::Both)
        .expect("both extraction should succeed");

    assert!(result.pudlak_interpolant.is_some());

    // Both interpolants should satisfy Craig property.
    let verify_m = verify_all_properties(&[vec![1]], &[vec![-1]], &result.interpolant, 1);
    assert!(verify_m.all_valid, "McMillan interpolant");

    let verify_p = verify_all_properties(
        &[vec![1]],
        &[vec![-1]],
        result.pudlak_interpolant.as_ref().expect("present"),
        1,
    );
    assert!(verify_p.all_valid, "Pudlak interpolant");
}

#[test]
fn test_extract_multi_step_variable_classification() {
    let ext = multi_step_refutation();
    let result = ext
        .extract(ExtractionAlgorithm::McMillan)
        .expect("multi-step should succeed");

    assert!(result.shared_vars.contains(&1), "x1 is shared");
    assert!(result.a_local_vars.contains(&2), "x2 is A-local");
    assert!(result.b_local_vars.contains(&3), "x3 is B-local");

    // Interpolant should only use shared vars.
    let interp_vars = result.interpolant.variables();
    for v in &interp_vars {
        assert!(
            result.shared_vars.contains(v),
            "variable {v} in interpolant but not shared"
        );
    }
}

#[test]
fn test_extract_multi_step_craig_property() {
    let ext = multi_step_refutation();
    let result = ext
        .extract(ExtractionAlgorithm::McMillan)
        .expect("extraction should succeed");

    let a_clauses = vec![vec![1, 2], vec![1, -2]];
    let b_clauses = vec![vec![-1, 3], vec![-1, -3]];
    let verify = verify_all_properties(&a_clauses, &b_clauses, &result.interpolant, 3);
    assert!(
        verify.all_valid,
        "multi-step interpolant must satisfy Craig property"
    );
}

#[test]
fn test_extract_empty_dag_error() {
    let ext = InterpolantExtractor::new();
    let result = ext.extract(ExtractionAlgorithm::McMillan);
    assert!(
        matches!(result, Err(ExtractionError::EmptyDag)),
        "empty DAG should error"
    );
}

#[test]
fn test_extract_not_a_refutation_error() {
    let mut ext = InterpolantExtractor::new();
    ext.add_a_clause(vec![1, 2]);
    ext.add_b_clause(vec![-2, 3]);
    // No resolution to derive empty clause.
    let result = ext.extract(ExtractionAlgorithm::McMillan);
    assert!(
        matches!(result, Err(ExtractionError::NotARefutation)),
        "non-refutation should error"
    );
}

#[test]
fn test_extract_from_parts_convenience() {
    let result = extract_interpolant_from_parts(&[vec![1]], &[vec![-1]], &[(0, 1, 1)])
        .expect("parts extraction should succeed");
    assert!(result.shared_vars.contains(&1));
}

#[test]
fn test_extract_counts() {
    let ext = multi_step_refutation();
    let result = ext
        .extract(ExtractionAlgorithm::McMillan)
        .expect("should succeed");
    assert_eq!(result.a_clause_count, 2);
    assert_eq!(result.b_clause_count, 2);
    assert_eq!(result.resolution_step_count, 3);
}

#[test]
fn test_extract_both_interpolants_satisfy_craig() {
    let ext = multi_step_refutation();
    let result = ext
        .extract(ExtractionAlgorithm::Both)
        .expect("both extraction should succeed");

    let a_clauses = vec![vec![1, 2], vec![1, -2]];
    let b_clauses = vec![vec![-1, 3], vec![-1, -3]];

    let verify_m = verify_all_properties(&a_clauses, &b_clauses, &result.interpolant, 3);
    assert!(verify_m.all_valid, "McMillan: {verify_m:?}");

    if let Some(pud) = &result.pudlak_interpolant {
        let verify_p = verify_all_properties(&a_clauses, &b_clauses, pud, 3);
        assert!(verify_p.all_valid, "Pudlak: {verify_p:?}");
    }
}
