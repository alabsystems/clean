// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What a REFUSED certificate means at verification tier 1.
//!
//! `extract_proof_and_quality` reports a refusal as `proof: None`. It used to
//! report it as `Some("(error ...)")` — a document no checker can parse. This
//! pins the consequence: at tier 1 the two are the SAME outcome class, so
//! nothing that used to succeed on a refusal now fails.
//!
//! `verify_proof_if_required` is the only reader of the proof field in the
//! crate, and it reads it only when the native quality is absent or incomplete.

use super::AyProofBackend;
use crate::bridge::ay_backend::{AyBackendConfig, AyError, AyLogic, ProofProfile};
use ay::ProofQuality;

fn tier_one_backend() -> AyProofBackend {
    AyProofBackend::with_config(
        AyBackendConfig::new(AyLogic::QfLia).proof_profile(ProofProfile::carcara_verified()),
    )
}

/// The refusal that the loud exporter used to hand back, verbatim.
fn refusal_document() -> String {
    "; UNVERIFIABLE PROOF — ay refused to emit :rule trust fallback (#8821)\n\
     ; context: export_alethe_with_problem_scope_and_overrides\n\
     (error \"UNVERIFIABLE PROOF: reachable assume t0 uses non-problem term t11; \
     preprocessing-derived formulas are not proof authority\")\n"
        .to_string()
}

#[test]
fn tier_one_treats_an_absent_certificate_exactly_as_it_treated_a_refusal_document() {
    let backend = tier_one_backend();
    let mut incomplete = ProofQuality::default();
    incomplete.total_steps = 3;
    incomplete.trust_count = 1;

    for quality in [None, Some(incomplete)] {
        // Pre-change shape: the refusal dressed as a document.
        let before = backend.verify_proof_if_required(&Some(refusal_document()), &quality);
        // Post-change shape: the refusal reported as absence.
        let after = backend.verify_proof_if_required(&None, &quality);

        assert!(
            matches!(before, Err(AyError::VerificationFailed(_))),
            "anti-vacuity: an `(error ...)` s-expression never verified either, got {before:?}"
        );
        assert!(
            matches!(after, Err(AyError::VerificationFailed(_))),
            "a refusal must stay a refusal at tier 1, got {after:?}"
        );
    }
}

#[test]
fn tier_one_never_reads_the_certificate_when_the_native_check_is_complete() {
    let backend = tier_one_backend();
    let complete = ProofQuality::default();
    assert!(complete.is_complete(), "anti-vacuity");

    assert!(
        backend
            .verify_proof_if_required(&None, &Some(complete))
            .expect("tier 1 accepts a complete native check"),
        "a complete native check verifies the PROOF OBJECT, not its rendering, so an \
         unrenderable certificate must not withdraw the verdict"
    );
}

#[test]
fn tier_zero_never_reads_the_certificate_at_all() {
    // Every `AyProofBackend::new_with_proofs` consumer — all four trust-certify
    // call sites and `datatype_no_confusion::ay_refutes` — lands here.
    let backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
    assert!(
        backend.config.profile().is_none(),
        "anti-vacuity: `new_with_proofs` must stay tier 0"
    );
    assert!(
        !backend
            .verify_proof_if_required(&None, &None)
            .expect("tier 0 never fails"),
        "tier 0 must not verify, and must not care that no certificate was rendered"
    );
}
