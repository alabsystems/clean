// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! D7 conformance at the tier-1 Carcara fallback.
//!
//! ay (owner decision D7, 2026-09-22) renders every UNSAT proof its strict
//! checker accepted and DISCLOSES whether the pinned Carcara can parse the
//! document (`Executor::last_unsat_proof_carcara_surface`). A consumer that
//! CLAIMS an external Carcara check must read that disclosure and refuse an
//! unsupported document with its reason before the round-trip, never hand
//! Carcara a document it cannot parse and report the parse failure as a
//! verdict. The fallback in `verify_proof_if_required` is such a consumer.

use super::{AyProofBackend, AyProofResult};
use crate::bridge::ay_backend::{AyBackendConfig, AyError, AyLogic, ProofProfile};

/// The marker every D7 refusal carries; the Carcara round-trip's own
/// failures (`no checker available`, `rejected proof`, `Carcara verification
/// error`) never do.
const D7_MARKER: &str = "ay D7 disclosure";

/// Assert `message` is a D7 refusal carrying `needle` and none of the Carcara
/// round-trip's own failure texts — i.e. it was raised before Carcara ran.
fn assert_refused_before_carcara(message: &str, needle: &str) {
    assert!(
        message.contains(D7_MARKER) && message.contains(needle),
        "the refusal must carry the D7 marker and `{needle}`, got {message}"
    );
    assert!(
        !message.contains("no checker available")
            && !message.contains("rejected proof")
            && !message.contains("Carcara verification error"),
        "the refusal must precede the Carcara round-trip, got {message}"
    );
}

fn tier_one_backend(logic: AyLogic) -> AyProofBackend {
    AyProofBackend::with_config(
        AyBackendConfig::new(logic).proof_profile(ProofProfile::carcara_verified()),
    )
}

#[test]
fn seq_sorted_unsat_is_refused_with_the_disclosed_reason_before_carcara() {
    let mut backend = tier_one_backend(AyLogic::All);
    backend.add_raw_declaration("(declare-const s (Seq Int))");
    backend.assert_formula("(= (seq.len s) 1)");
    backend.assert_formula("(= (seq.len s) 2)");

    let outcome = backend.check_sat();
    let surface = backend
        .executor
        .last_unsat_proof_carcara_surface()
        .expect("anti-vacuity: ay retains the Seq UNSAT proof");
    let reason = surface
        .unsupported_reason()
        .expect("anti-vacuity: the Seq surface is disclosed as unsupported")
        .to_string();
    assert!(reason.contains("(Seq Int)"), "{reason}");

    // Whether ay's native proof quality is complete decides which call
    // produces the fallback's verdict; both paths yield it, and it is checked
    // once below, so neither path skips the subject.
    let fallback = match outcome {
        // Complete native quality: `check_sat` returned without the fallback,
        // so force it on the returned document (no complete native verdict).
        Ok(AyProofResult::Unsat { proof, .. }) => backend.verify_proof_if_required(&proof, &None),
        // Incomplete native quality: `check_sat` itself reached the fallback,
        // and its refusal is the verdict under test. Re-driving the fallback
        // without a document would stop at "proof required" before the D7
        // read, so this refusal is the one checked.
        Err(refusal @ AyError::VerificationFailed(_)) => Err(refusal),
        other => panic!("seq length pinned twice must be UNSAT, got {other:?}"),
    };
    match fallback {
        Err(AyError::VerificationFailed(message)) => {
            assert_refused_before_carcara(&message, &reason);
        }
        other => panic!("D7: an unsupported surface must be refused at the claim, got {other:?}"),
    }
}

#[test]
fn int_unsat_with_a_supported_surface_still_goes_to_carcara() {
    let mut backend = tier_one_backend(AyLogic::QfLia);
    let x = backend.fresh_int("x");
    backend.assert_formula(&format!("(> {x} 0)"));
    backend.assert_formula(&format!("(< {x} 0)"));
    let proof = match backend.check_sat() {
        Ok(AyProofResult::Unsat { proof, .. }) => proof,
        other => panic!("x > 0 and x < 0 must be UNSAT, got {other:?}"),
    };
    assert!(proof.is_some(), "anti-vacuity: the Int document renders");
    let surface = backend
        .executor
        .last_unsat_proof_carcara_surface()
        .expect("anti-vacuity: ay retains the Int UNSAT proof");
    assert!(surface.is_supported(), "{surface}");

    match backend.verify_proof_if_required(&proof, &None) {
        // `carcara-verify` on: Carcara's own verdict, whichever it is.
        Ok(_) => {}
        // `carcara-verify` off: the round-trip's own refusal, reached.
        Err(AyError::VerificationFailed(message)) => assert!(
            !message.contains(D7_MARKER),
            "a supported surface must reach Carcara, got the D7 refusal: {message}"
        ),
        other => panic!("unexpected outcome for a supported surface: {other:?}"),
    }
}

#[test]
fn a_certificate_with_no_disclosure_is_refused_before_carcara() {
    // No `check_sat` ran, so no retained UNSAT proof discloses a surface for
    // the document handed in. Nothing vouches for its surface, so the claim is
    // refused on the absent disclosure, never handed to Carcara.
    let backend = tier_one_backend(AyLogic::QfLia);
    assert!(
        backend
            .executor
            .last_unsat_proof_carcara_surface()
            .is_none(),
        "anti-vacuity: a fresh executor retains no UNSAT proof"
    );
    let document = Some("(step t1 (cl) :rule hole)\n".to_string());
    match backend.verify_proof_if_required(&document, &None) {
        Err(AyError::VerificationFailed(message)) => {
            assert_refused_before_carcara(&message, "no retained UNSAT proof");
        }
        other => panic!("D7: an undisclosed surface must be refused at the claim, got {other:?}"),
    }
}
