// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{FarkasAnnotation, ProofId, TermId, TheoryLemmaKind};
use num_bigint::BigInt;
use num_rational::Rational64;

use super::super::farkas_certificate::FarkasCertificate;
use super::super::trace::{FarkasView, StepView};

/// Build a 2-literal arithmetic conflict clause: [¬(x ≤ 5), ¬(x ≥ 10)].
///
/// With coefficients [1, 1] (or any equal pair), this is a valid Farkas
/// conflict: 1*(x − 5) + 1*(10 − x) = 5 > 0.
fn mk_arith_conflict_2(terms: &mut TermStore) -> Vec<TermId> {
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);

    vec![not_x_le_5, not_x_ge_10]
}

/// Build a 3-literal clause with a dummy middle element:
/// [¬(x ≤ 5), ¬(y ≤ 3), ¬(x ≥ 10)].
///
/// With coefficients [1, 0, 1], the active subset {x ≤ 5, x ≥ 10} is a
/// valid Farkas conflict. The middle literal is inactive (zero coefficient).
fn mk_arith_conflict_3(terms: &mut TermStore) -> Vec<TermId> {
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let y_le_3 = terms.mk_le(y, three);
    let x_ge_10 = terms.mk_ge(x, ten);

    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_y_le_3 = terms.mk_not(y_le_3);
    let not_x_ge_10 = terms.mk_not(x_ge_10);

    vec![not_x_le_5, not_y_le_3, not_x_ge_10]
}

/// Build a 4-literal clause with two zero-coefficient middle elements:
/// [¬(x ≤ 5), ¬(y ≤ 3), ¬(z ≤ 7), ¬(x ≥ 10)].
fn mk_arith_conflict_4(terms: &mut TermStore) -> Vec<TermId> {
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));
    let seven = terms.mk_int(BigInt::from(7));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let y_le_3 = terms.mk_le(y, three);
    let z_le_7 = terms.mk_le(z, seven);
    let x_ge_10 = terms.mk_ge(x, ten);

    vec![
        terms.mk_not(x_le_5),
        terms.mk_not(y_le_3),
        terms.mk_not(z_le_7),
        terms.mk_not(x_ge_10),
    ]
}

fn farkas_view_from_step(trace: &ProofTrace<'_>, step_id: ProofId) -> Option<FarkasView> {
    match trace.step(step_id.0 as usize) {
        StepView::TheoryLemma { farkas, .. } => farkas,
        other => panic!("expected theory lemma step, got {:?}", other),
    }
}

#[test]
fn test_from_trace_extracts_active_indices_and_coefficients() {
    let mut terms = TermStore::new();
    let clause = mk_arith_conflict_3(&mut terms);

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 0, 1]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let certificate = FarkasCertificate::from_trace(
        farkas_view_from_step(&trace, step_id),
        &clause,
        step_id,
        &trace,
    )
    .expect("valid Farkas annotation should build a certificate");

    assert_eq!(certificate.active_indices(), &[0, 2]);
    assert!(certificate.all_unit());
    assert_eq!(
        certificate.coefficient_for(0),
        Some(Rational64::from_integer(1))
    );
    assert_eq!(certificate.coefficient_for(1), None);
    assert_eq!(
        certificate.coefficient_for(2),
        Some(Rational64::from_integer(1))
    );
}

#[test]
fn test_from_trace_none_uses_all_unit_fallback() {
    let mut terms = TermStore::new();
    // Clause content doesn't matter for None path (all-unit fallback).
    let clause = mk_arith_conflict_2(&mut terms);
    let dummy_clause: Vec<TermId> = (0..4).map(|_| clause[0]).collect();
    let trace = ProofTrace::without_proof(&terms);

    let certificate = FarkasCertificate::from_trace(None, &dummy_clause, ProofId(0), &trace)
        .expect("missing annotation should fall back to all-unit certificate");

    assert_eq!(certificate.active_indices(), &[0, 1, 2, 3]);
    assert!(certificate.all_unit());
    for idx in 0..4 {
        assert_eq!(
            certificate.coefficient_for(idx),
            Some(Rational64::from_integer(1))
        );
    }
}

#[test]
fn test_from_trace_rejects_length_mismatch() {
    let mut terms = TermStore::new();
    let clause = mk_arith_conflict_3(&mut terms);
    let trace = ProofTrace::without_proof(&terms);

    let result = FarkasCertificate::from_trace(
        Some(FarkasView {
            coefficient_count: 2,
            is_valid: true,
            all_unit_coefficients: false,
        }),
        &clause,
        ProofId(7),
        &trace,
    );

    match result {
        Err(ReconstructionError::UnsupportedStep {
            step_index,
            description,
        }) => {
            assert_eq!(step_index, 7);
            assert!(description.contains("length"));
        }
        other => panic!("expected length-mismatch error, got {:?}", other),
    }
}

#[test]
fn test_from_trace_rejects_negative_coefficients() {
    let mut terms = TermStore::new();
    let clause = mk_arith_conflict_2(&mut terms);
    let trace = ProofTrace::without_proof(&terms);

    let result = FarkasCertificate::from_trace(
        Some(FarkasView {
            coefficient_count: 2,
            is_valid: false,
            all_unit_coefficients: false,
        }),
        &clause,
        ProofId(11),
        &trace,
    );

    match result {
        Err(ReconstructionError::UnsupportedStep {
            step_index,
            description,
        }) => {
            assert_eq!(step_index, 11);
            assert!(description.contains("negative"));
        }
        other => panic!("expected negative-coefficient error, got {:?}", other),
    }
}

#[test]
fn test_all_unit_fallback_handles_empty_clause() {
    let terms = TermStore::new();
    let trace = ProofTrace::without_proof(&terms);

    let certificate = FarkasCertificate::from_trace(None, &[], ProofId(0), &trace)
        .expect("empty fallback certificate should still construct");

    assert!(certificate.active_indices().is_empty());
    assert!(certificate.all_unit());
    assert_eq!(certificate.coefficient_for(0), None);
}

#[test]
fn test_from_trace_all_unit_tracks_active_coefficients() {
    let mut terms = TermStore::new();
    let clause = mk_arith_conflict_3(&mut terms);

    let mut proof = Proof::new();
    // [1, 1, 1] — all active. But the middle literal (y ≤ 3) makes the
    // combined Farkas sum fail to eliminate y, so this will trigger a
    // semantic validation failure. Use [1, 0, 1] for the valid all-unit test.
    let unit_step = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 0, 1]),
    );
    let zero_tail_step = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 0, 1]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let unit_certificate = FarkasCertificate::from_trace(
        farkas_view_from_step(&trace, unit_step),
        &clause,
        unit_step,
        &trace,
    )
    .expect("all-unit Farkas annotation should build a certificate");
    let zero_tail_certificate = FarkasCertificate::from_trace(
        farkas_view_from_step(&trace, zero_tail_step),
        &clause,
        zero_tail_step,
        &trace,
    )
    .expect("zero-tail unit Farkas annotation should build a certificate");

    assert!(unit_certificate.all_unit());
    assert!(zero_tail_certificate.all_unit());
}

#[test]
fn test_coefficient_for_out_of_range_index_returns_none() {
    let mut terms = TermStore::new();
    let clause = mk_arith_conflict_2(&mut terms);

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 1]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let certificate = FarkasCertificate::from_trace(
        farkas_view_from_step(&trace, step_id),
        &clause,
        step_id,
        &trace,
    )
    .expect("valid Farkas annotation should build a certificate");

    assert_eq!(certificate.coefficient_for(99), None);
}

#[test]
fn test_zero_coefficients_are_not_active() {
    let mut terms = TermStore::new();
    let clause = mk_arith_conflict_4(&mut terms);

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 0, 0, 1]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let certificate = FarkasCertificate::from_trace(
        farkas_view_from_step(&trace, step_id),
        &clause,
        step_id,
        &trace,
    )
    .expect("zero coefficients should still produce a valid certificate");

    assert_eq!(certificate.active_indices(), &[0, 3]);
    assert_eq!(certificate.coefficient_for(1), None);
    assert_eq!(certificate.coefficient_for(2), None);
}

// --- New tests for #2902: semantic validation ---

#[test]
fn test_semantic_validation_rejects_invalid_active_subset() {
    // Build a clause where the active subset cannot form a valid Farkas
    // conflict (coefficients don't eliminate variables).
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);

    let clause = vec![not_x_le_5, not_x_ge_10];

    // Coefficients [1, 2] don't eliminate x:
    // 1*(x - 5) + 2*(10 - x) = -x + 15, variable not eliminated.
    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 2]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let result = FarkasCertificate::from_trace(
        farkas_view_from_step(&trace, step_id),
        &clause,
        step_id,
        &trace,
    );

    match result {
        Err(ReconstructionError::TrustBoundary {
            step_index: _,
            subsystem,
            description,
        }) => {
            assert_eq!(subsystem, "LRA");
            assert!(
                description.starts_with("Farkas semantic validation failed:"),
                "unexpected description: {description}"
            );
        }
        other => panic!(
            "expected TrustBoundary from semantic validation, got {:?}",
            other
        ),
    }
}

#[test]
fn test_semantic_validation_passes_valid_conflict() {
    let mut terms = TermStore::new();
    let clause = mk_arith_conflict_2(&mut terms);

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 1]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let certificate = FarkasCertificate::from_trace(
        farkas_view_from_step(&trace, step_id),
        &clause,
        step_id,
        &trace,
    )
    .expect("valid [1,1] conflict on x≤5, x≥10 should pass semantic validation");

    assert!(certificate.all_unit());
    assert_eq!(certificate.active_indices(), &[0, 1]);
}

#[test]
fn test_lia_generic_uses_same_constructor_path() {
    let mut terms = TermStore::new();
    let clause = mk_arith_conflict_2(&mut terms);

    let mut proof = Proof::new();
    // LiaGeneric with explicit Farkas annotation goes through from_view,
    // not the all_unit_fallback (which only fires for None annotations).
    let step_id = proof.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 1]),
        TheoryLemmaKind::LiaGeneric,
    );

    let trace = ProofTrace::new(&proof, &terms);
    let certificate = FarkasCertificate::from_trace(
        farkas_view_from_step(&trace, step_id),
        &clause,
        step_id,
        &trace,
    )
    .expect("LiaGeneric with valid Farkas should pass the same validation");

    assert!(certificate.all_unit());
    assert_eq!(certificate.active_indices(), &[0, 1]);
}

#[test]
fn test_zero_tail_preservation_with_semantic_validation() {
    // [1, 0, 1] on a 3-element clause: the zero-tail (middle element) is
    // ignored for both validation and replay.
    let mut terms = TermStore::new();
    let clause = mk_arith_conflict_3(&mut terms);

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 0, 1]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let certificate = FarkasCertificate::from_trace(
        farkas_view_from_step(&trace, step_id),
        &clause,
        step_id,
        &trace,
    )
    .expect("zero-tail [1,0,1] should pass semantic validation on active subset");

    assert!(certificate.all_unit());
    assert_eq!(certificate.active_indices(), &[0, 2]);
    // Middle element has no coefficient.
    assert_eq!(certificate.coefficient_for(1), None);
}

// =========================================================================
// Boundary tests: algorithm audit for off-by-one and edge cases
// Part of #2917 algorithm audit (iter 1514)
// =========================================================================

#[test]
fn test_all_zero_coefficients_through_from_view_produces_empty_active_set() {
    // All-zero coefficients [0, 0]: FarkasView has coefficient_count=2,
    // is_valid=true (no negatives). Active indices should be empty, all_unit
    // should be vacuously true. Semantic validation with an empty active set
    // should hit TrustBoundary (can't form a contradiction from 0 literals).
    let mut terms = TermStore::new();
    let clause = mk_arith_conflict_2(&mut terms);

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[0, 0]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let view = farkas_view_from_step(&trace, step_id);

    // All-zero coefficients should produce a valid view (no negatives).
    assert!(view.is_some(), "all-zero annotation should produce a view");
    let view = view.unwrap();
    assert!(view.is_valid, "all-zero coefficients have no negatives");
    assert_eq!(view.coefficient_count, 2);

    // The certificate should either succeed with empty active set or
    // fail at semantic validation. Either way, it must not panic.
    let result = FarkasCertificate::from_trace(Some(view), &clause, step_id, &trace);
    match &result {
        Ok(cert) => {
            // If it succeeds, active set must be empty and all_unit vacuously true.
            assert!(
                cert.active_indices().is_empty(),
                "all-zero coefficients must yield empty active set"
            );
            assert!(
                cert.all_unit(),
                "empty active set must report all_unit as vacuously true"
            );
        }
        Err(ReconstructionError::TrustBoundary { .. }) => {
            // Semantic validation rejects empty active set — this is also correct.
        }
        Err(other) => {
            panic!("unexpected error for all-zero coefficients: {other:?}");
        }
    }
}

#[test]
fn test_single_literal_clause_boundary() {
    // A 1-literal clause with coefficient [1]: the active index should be [0],
    // and hypothesis() computes bvar(clause_len - 1 - 0) = bvar(0). This is
    // the minimum clause size boundary.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let x_le_5 = terms.mk_le(x, five);
    let clause = vec![terms.mk_not(x_le_5)];

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let view = farkas_view_from_step(&trace, step_id);

    // Single-literal Farkas with coefficient 1 can't form a proper conflict
    // (no variable cancellation possible with just one literal), so this
    // should hit TrustBoundary or succeed depending on the ay-core validator.
    let result = FarkasCertificate::from_trace(view, &clause, step_id, &trace);
    // Must not panic — that's the key boundary check.
    match &result {
        Ok(cert) => {
            assert_eq!(cert.active_indices(), &[0]);
            assert!(cert.all_unit());
        }
        Err(_) => {
            // Semantic validation rejection is acceptable for a single literal.
        }
    }
}

#[test]
fn test_coefficient_for_at_max_clause_index() {
    // Verify coefficient_for works at the maximum valid index (clause_len - 1).
    let mut terms = TermStore::new();
    let clause = mk_arith_conflict_4(&mut terms);

    let mut proof = Proof::new();
    let step_id = proof.add_theory_lemma_with_farkas(
        "LRA",
        clause.clone(),
        FarkasAnnotation::from_ints(&[1, 0, 0, 1]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    let certificate = FarkasCertificate::from_trace(
        farkas_view_from_step(&trace, step_id),
        &clause,
        step_id,
        &trace,
    )
    .expect("valid [1,0,0,1] should construct");

    // Max valid index is clause_len - 1 = 3
    assert_eq!(
        certificate.coefficient_for(3),
        Some(Rational64::from_integer(1)),
        "coefficient_for at max clause index must return the coefficient"
    );
    // Just past the max: should return None, not panic.
    assert_eq!(
        certificate.coefficient_for(4),
        None,
        "coefficient_for past max clause index must return None"
    );
    // Way past the max: should return None, not panic.
    assert_eq!(
        certificate.coefficient_for(usize::MAX),
        None,
        "coefficient_for at usize::MAX must return None"
    );
}
