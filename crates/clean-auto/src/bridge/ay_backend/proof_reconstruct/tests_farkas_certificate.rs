// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct unit tests for Farkas certificate extraction and validation.
//!
//! Part of #2891: cover `farkas_certificate.rs` without requiring full LRA
//! reconstruction.

use ay::Sort;
use ay_core::{FarkasAnnotation, Proof, ProofId, TermStore};
use num_bigint::BigInt;
use num_rational::Rational64;

use crate::bridge::ay_backend::proof_reconstruct::farkas_certificate::FarkasCertificate;
use crate::bridge::ay_backend::proof_reconstruct::trace::{FarkasView, ProofTrace, StepView};
use crate::bridge::ay_backend::proof_reconstruct::ReconstructionError;

/// Build a negated arithmetic conflict clause of `len` literals.
///
/// Returns `[¬(x ≤ base), ¬(x ≤ base+1), ..., ¬(x ≤ base+len-1)]` and
/// uses the same variable `x` throughout. For semantic validation, only
/// subsets with coefficients that eliminate `x` will pass the Farkas checker.
fn negated_le_clause(terms: &mut TermStore, len: usize) -> Vec<ay_core::TermId> {
    let x = terms.mk_var("x", Sort::Int);
    (0..len)
        .map(|idx| {
            let rhs = terms.mk_int(BigInt::from(idx as i64));
            let le = terms.mk_le(x, rhs);
            terms.mk_not(le)
        })
        .collect()
}

/// Build a 2-literal Farkas conflict: `[¬(x ≤ 5), ¬(x ≥ 10)]`.
///
/// With coefficients [1, 1] this is a valid Farkas conflict:
/// 1*(x − 5 ≤ 0) + 1*(10 − x ≤ 0) = 5 > 0.
fn valid_arith_conflict_2(terms: &mut TermStore) -> Vec<ay_core::TermId> {
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));
    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);
    vec![terms.mk_not(x_le_5), terms.mk_not(x_ge_10)]
}

fn build_farkas_trace(
    coefficients: Vec<Rational64>,
) -> (TermStore, Proof, Vec<ay_core::TermId>, ProofId, FarkasView) {
    let mut terms = TermStore::new();
    let clause = negated_le_clause(&mut terms, coefficients.len());

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::new(coefficients),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let StepView::TheoryLemma {
        farkas: Some(view), ..
    } = trace.step(step_id.0 as usize)
    else {
        panic!("expected an LRA theory lemma with a Farkas annotation");
    };

    (terms, proof, clause, step_id, view)
}

#[test]
fn test_from_trace_with_valid_farkas() {
    // Use a proper arithmetic conflict instead of non-negated terms.
    let mut terms = TermStore::new();
    let clause = valid_arith_conflict_2(&mut terms);

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 1]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let StepView::TheoryLemma {
        farkas: Some(view), ..
    } = trace.step(step_id.0 as usize)
    else {
        panic!("expected theory lemma");
    };

    let cert = FarkasCertificate::from_trace(Some(view), &clause, step_id, &trace)
        .expect("valid Farkas certificate should be accepted");

    assert_eq!(cert.active_indices(), &[0, 1]);
    assert!(cert.all_unit());
    assert_eq!(cert.coefficient_for(0), Some(Rational64::from_integer(1)));
    assert_eq!(cert.coefficient_for(1), Some(Rational64::from_integer(1)));
}

#[test]
fn test_from_trace_none_gives_all_unit_fallback() {
    let mut terms = TermStore::new();
    let clause = negated_le_clause(&mut terms, 4);
    let trace = ProofTrace::without_proof(&terms);

    let cert = FarkasCertificate::from_trace(None, &clause, ProofId(0), &trace)
        .expect("missing annotation should fall back to all-unit");

    assert_eq!(cert.active_indices(), &[0, 1, 2, 3]);
    assert!(cert.all_unit());
    for idx in 0..4 {
        assert_eq!(cert.coefficient_for(idx), Some(Rational64::from_integer(1)));
    }
}

#[test]
fn test_from_trace_length_mismatch_errors() {
    let (terms, proof, clause, step_id, view) = build_farkas_trace(vec![
        Rational64::from_integer(1),
        Rational64::from_integer(2),
    ]);
    let trace = ProofTrace::new(&proof, &terms);

    // Pass a 3-element clause to trigger mismatch with 2-coefficient view.
    let mut longer_clause = clause.clone();
    longer_clause.push(clause[0]);

    let err = FarkasCertificate::from_trace(Some(view), &longer_clause, step_id, &trace)
        .expect_err("coefficient-count mismatch should fail closed");

    match err {
        ReconstructionError::UnsupportedStep {
            step_index,
            description,
        } => {
            assert_eq!(step_index, step_id.0);
            assert!(description.contains("length"));
        }
        other => panic!("expected UnsupportedStep, got {other:?}"),
    }
}

#[test]
fn test_from_trace_negative_coefficient_errors() {
    let (terms, proof, clause, step_id, view) = build_farkas_trace(vec![
        Rational64::from_integer(1),
        Rational64::from_integer(-1),
    ]);
    let trace = ProofTrace::new(&proof, &terms);

    let err = FarkasCertificate::from_trace(Some(view), &clause, step_id, &trace)
        .expect_err("negative coefficients should fail closed");

    match err {
        ReconstructionError::UnsupportedStep {
            step_index,
            description,
        } => {
            assert_eq!(step_index, step_id.0);
            assert!(description.contains("negative"));
        }
        other => panic!("expected UnsupportedStep, got {other:?}"),
    }
}

#[test]
fn test_all_unit_fallback_empty() {
    let terms = TermStore::new();
    let trace = ProofTrace::without_proof(&terms);

    let cert = FarkasCertificate::from_trace(None, &[], ProofId(0), &trace)
        .expect("empty missing annotation should still succeed");

    assert!(cert.active_indices().is_empty());
    assert!(cert.all_unit());
    assert_eq!(cert.coefficient_for(0), None);
}

#[test]
fn test_coefficient_for_not_found() {
    let mut terms = TermStore::new();
    let clause = valid_arith_conflict_2(&mut terms);

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 1]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let StepView::TheoryLemma {
        farkas: Some(view), ..
    } = trace.step(step_id.0 as usize)
    else {
        panic!("expected theory lemma");
    };

    let cert = FarkasCertificate::from_trace(Some(view), &clause, step_id, &trace)
        .expect("valid Farkas certificate should be accepted");

    assert_eq!(cert.coefficient_for(99), None);
}

#[test]
fn test_from_trace_all_unit_coefficients_flag() {
    // All-unit: valid [1, 1] conflict.
    let mut terms = TermStore::new();
    let clause = valid_arith_conflict_2(&mut terms);

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 1]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let StepView::TheoryLemma {
        farkas: Some(view), ..
    } = trace.step(step_id.0 as usize)
    else {
        panic!("expected theory lemma");
    };

    let unit_cert = FarkasCertificate::from_trace(Some(view), &clause, step_id, &trace)
        .expect("all-unit certificate should be accepted");
    assert!(unit_cert.all_unit());

    // Non-unit: [1, 2] won't cancel x, triggering TrustBoundary, which is
    // correct semantic behavior — non-unit coefficients that don't form a
    // valid conflict are rejected.
    let mut terms2 = TermStore::new();
    let clause2 = valid_arith_conflict_2(&mut terms2);
    let mut proof2 = Proof::new();
    let step_id2 = proof2.add_theory_lemma_with_farkas(
        "LRA",
        clause2.clone(),
        FarkasAnnotation::from_ints(&[1, 2]),
    );
    let trace2 = ProofTrace::new(&proof2, &terms2);
    let StepView::TheoryLemma {
        farkas: Some(view2),
        ..
    } = trace2.step(step_id2.0 as usize)
    else {
        panic!("expected theory lemma");
    };

    let result = FarkasCertificate::from_trace(Some(view2), &clause2, step_id2, &trace2);
    assert!(
        matches!(result, Err(ReconstructionError::TrustBoundary { .. })),
        "non-unit [1,2] should trigger TrustBoundary: {:?}",
        result,
    );
}

#[test]
fn test_from_trace_zero_coefficient_excluded() {
    // 4-literal clause: [¬(x≤5), ¬(y≤3), ¬(z≤7), ¬(x≥10)] with [1, 0, 0, 1].
    // Active subset: {x≤5, x≥10} is a valid conflict.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let three = terms.mk_int(BigInt::from(3));
    let seven = terms.mk_int(BigInt::from(7));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let y_le_3 = terms.mk_le(y, three);
    let z_le_7 = terms.mk_le(z, seven);
    let x_ge_10 = terms.mk_ge(x, ten);
    let clause = vec![
        terms.mk_not(x_le_5),
        terms.mk_not(y_le_3),
        terms.mk_not(z_le_7),
        terms.mk_not(x_ge_10),
    ];

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 0, 0, 1]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let StepView::TheoryLemma {
        farkas: Some(view), ..
    } = trace.step(step_id.0 as usize)
    else {
        panic!("expected theory lemma");
    };

    let cert = FarkasCertificate::from_trace(Some(view), &clause, step_id, &trace)
        .expect("zero-coefficient certificate should be accepted");

    assert_eq!(cert.active_indices(), &[0, 3]);
}
