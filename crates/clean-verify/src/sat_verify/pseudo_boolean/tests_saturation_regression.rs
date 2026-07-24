// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for issue #3348 — PB saturation unsound with negative
//! coefficients.
//!
//! The soundness fix (in `rules.rs`) rejects applying the saturation rule to
//! any constraint that contains a negative coefficient. These tests pin the
//! exact scenario from the issue body so the rule cannot silently regress
//! against the reported example.
//!
//! Issue text (paraphrased):
//!   `10*x - 5*y >= 5`, model (x=1, y=1) satisfies (5 >= 5). An unsound
//!   saturation that caps the positive coefficient at the degree (5) would
//!   produce `5*x - 5*y >= 5`, under which (1, 1) gives 0 < 5 (UNSAT).

use super::rules::{verify_rule, PbRule};
use super::types::{PbConstraint, PbFormula};
use super::PbError;

/// Evaluate a PB constraint under a variable -> bool assignment.
///
/// Returns the LHS sum so the caller can check whether `sum >= degree`.
fn evaluate(constraint: &PbConstraint, assignment: &[(u32, bool)]) -> i64 {
    constraint
        .terms
        .iter()
        .map(|&(coeff, lit)| {
            let var = lit.unsigned_abs();
            let value = assignment
                .iter()
                .find(|&&(v, _)| v == var)
                .map(|&(_, b)| b)
                .expect("assignment must cover all variables in constraint");
            let effective = if lit > 0 { value } else { !value };
            if effective {
                coeff
            } else {
                0
            }
        })
        .sum()
}

/// The exact scenario named in issue #3348.
///
/// `10*x1 + (-5)*x2 >= 5` with model (x1=1, x2=1):
/// - Original LHS = 10 - 5 = 5, degree = 5 → SAT.
/// - Unsound saturation would rewrite to `5*x1 + (-5)*x2 >= 5`:
///   LHS under (1,1) = 5 - 5 = 0, degree = 5 → UNSAT (model lost).
///
/// The fixed rule rejects the saturation application.
#[test]
fn saturation_issue_3348_10x_minus_5y_rejected() {
    let formula = PbFormula::new(2);
    let input = PbConstraint::new(vec![(10, 1), (-5, 2)], 5);
    let derived = vec![input.clone()];

    // Model (x1=1, x2=1) must satisfy the original constraint.
    let assignment = [(1u32, true), (2u32, true)];
    let original_lhs = evaluate(&input, &assignment);
    assert_eq!(original_lhs, 5);
    assert!(
        original_lhs >= input.degree,
        "precondition: (1,1) must satisfy 10*x1 - 5*x2 >= 5"
    );

    // Applying saturation must be rejected.
    let err = verify_rule(&derived, &formula, &PbRule::Saturation(0))
        .expect_err("saturation must reject constraints with any negative coefficient");

    match err {
        PbError::NegativeCoefficientInSaturation { coeff, literal } => {
            assert_eq!(coeff, -5, "rejected coefficient should be -5");
            assert_eq!(literal, 2, "rejected literal should be x2 (+2)");
        }
        other => panic!("expected NegativeCoefficientInSaturation, got {other:?}"),
    }
}

/// Exhaustive model-preservation sanity check.
///
/// For every 2^2 assignment, if the model satisfies the original
/// `10*x1 - 5*x2 >= 5`, the unsound saturated `5*x1 - 5*x2 >= 5` must not
/// lose it. This is a direct check of the soundness property the rule was
/// violating; the test confirms the unsound rewrite would indeed drop a
/// model, and the fixed code refuses to produce that rewrite.
#[test]
fn saturation_issue_3348_model_preservation_counterexample() {
    let original = PbConstraint::new(vec![(10, 1), (-5, 2)], 5);
    // The forbidden saturated form — we never construct it via verify_rule;
    // we only use it to exhibit the concrete soundness violation that would
    // exist without the guard.
    let unsound_saturated = PbConstraint::new(vec![(5, 1), (-5, 2)], 5);

    let mut lost_models: Vec<(bool, bool)> = Vec::new();
    for &x1 in &[false, true] {
        for &x2 in &[false, true] {
            let assignment = [(1u32, x1), (2u32, x2)];
            let orig_lhs = evaluate(&original, &assignment);
            let sat_lhs = evaluate(&unsound_saturated, &assignment);

            let orig_sat = orig_lhs >= original.degree;
            let sat_sat = sat_lhs >= unsound_saturated.degree;

            if orig_sat && !sat_sat {
                lost_models.push((x1, x2));
            }
        }
    }

    assert!(
        lost_models.contains(&(true, true)),
        "unsound saturation must drop model (1,1): lost={lost_models:?}"
    );

    // AndType verify the rule guard actually prevents the unsound derivation.
    let formula = PbFormula::new(2);
    let derived = vec![original];
    assert!(
        verify_rule(&derived, &formula, &PbRule::Saturation(0)).is_err(),
        "rule must not produce the unsound saturated form"
    );
}

/// Companion sanity check: saturation on the all-positive form still works
/// and preserves the single model where x1=1 (the only one that can satisfy
/// `10*x1 >= 5`).
#[test]
fn saturation_all_positive_preserves_models() {
    let formula = PbFormula::new(2);
    let input = PbConstraint::new(vec![(10, 1), (3, 2)], 5);
    let derived = vec![input.clone()];

    let saturated = verify_rule(&derived, &formula, &PbRule::Saturation(0))
        .expect("saturation on non-negative coefficients must succeed");

    for &x1 in &[false, true] {
        for &x2 in &[false, true] {
            let a = [(1u32, x1), (2u32, x2)];
            let orig_sat = evaluate(&input, &a) >= input.degree;
            let sat_sat = evaluate(&saturated, &a) >= saturated.degree;
            assert!(
                !orig_sat || sat_sat,
                "saturation lost model ({x1},{x2}) on all-positive constraint"
            );
        }
    }
}
