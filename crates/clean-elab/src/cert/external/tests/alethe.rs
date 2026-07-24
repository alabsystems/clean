// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
#[cfg(feature = "carcara-verify")]
use clean_auto::bridge::ay_contract::{AyLogic, AyProofBackend, AyProofResult};

#[cfg(feature = "carcara-verify")]
fn sample_valid_alethe_cert() -> ExternalAletheCert {
    ExternalAletheCert {
        version: "1.0".to_string(),
        problem: "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n"
            .to_string(),
        proof: "(assume t0 p)\n(assume t1 (not p))\n(step t2 (cl) :rule resolution :premises (t1 t0))\n"
            .to_string(),
    }
}

#[cfg(feature = "carcara-verify")]
fn sample_holey_alethe_cert() -> ExternalAletheCert {
    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
    let x = backend.fresh_int("x");
    backend.assert_formula(&format!("(> {x} 0)"));
    backend.assert_formula(&format!("(< {x} 0)"));

    let problem = format!(
        "(set-logic QF_LIA)\n(declare-const {x} Int)\n(assert (> {x} 0))\n(assert (< {x} 0))\n(check-sat)\n"
    );
    let proof = match backend
        .check_sat()
        .expect("simple contradiction should produce an UNSAT proof")
    {
        AyProofResult::Unsat {
            proof: Some(proof), ..
        } => proof,
        other => panic!("expected UNSAT proof result, got {other:?}"),
    };

    // Replace the first proof rule with a valid `hole` step so this fixture
    // deterministically exercises the non-error `Ok(false)` path.
    let marker = ":rule ";
    let start = proof
        .find(marker)
        .map(|i| i + marker.len())
        .expect("generated Alethe proof should contain a rule marker");
    let end = proof[start..]
        .find(|c: char| c.is_whitespace() || c == ')')
        .map(|i| start + i)
        .expect("generated Alethe proof rule should terminate");
    assert_ne!(
        &proof[start..end],
        "hole",
        "proof mutation must change the rule name"
    );
    let proof = format!("{}hole{}", &proof[..start], &proof[end..]);

    ExternalAletheCert {
        version: "1.0".to_string(),
        problem,
        proof,
    }
}

#[test]
fn test_alethe_cert_serde_roundtrip() {
    let json = r#"{
        "type": "alethe_certificate",
        "version": "1.0",
        "problem": "(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (> x 0))\n(assert (< x 0))\n(check-sat)",
        "proof": "(assume h1 (> x 0))\n(assume h2 (< x 0))\n(step t1 (cl (not (> x 0)) (not (< x 0))) :rule la_generic :args (1 1))"
    }"#;
    let cert: ExternalCertificate = serde_json::from_str(json).unwrap();
    match &cert {
        ExternalCertificate::Alethe(alethe) => {
            assert_eq!(alethe.version, "1.0");
            assert!(alethe.problem.contains("QF_LIA"));
            assert!(alethe.proof.contains("la_generic"));
        }
        _ => panic!("expected Alethe variant"),
    }

    let serialized = serde_json::to_string(&cert).unwrap();
    assert!(serialized.contains("alethe_certificate"));
}

#[test]
fn test_alethe_cert_bad_version() {
    let cert = ExternalAletheCert {
        version: "2.0".to_string(),
        problem: "(check-sat)".to_string(),
        proof: "(step t1 (cl) :rule true)".to_string(),
    };
    let err = verify_alethe_certificate(&cert).unwrap_err();
    assert_eq!(err.code, ExternalCertErrorCode::InvalidSchema);
}

#[test]
fn test_alethe_cert_empty_problem() {
    let cert = ExternalAletheCert {
        version: "1.0".to_string(),
        problem: String::new(),
        proof: "(step t1 (cl) :rule true)".to_string(),
    };
    let err = verify_alethe_certificate(&cert).unwrap_err();
    assert_eq!(err.code, ExternalCertErrorCode::InvalidSchema);
    assert!(err.detail.contains("problem"));
}

#[test]
fn test_alethe_cert_empty_proof() {
    let cert = ExternalAletheCert {
        version: "1.0".to_string(),
        problem: "(check-sat)".to_string(),
        proof: String::new(),
    };
    let err = verify_alethe_certificate(&cert).unwrap_err();
    assert_eq!(err.code, ExternalCertErrorCode::InvalidSchema);
    assert!(err.detail.contains("proof"));
}

#[cfg(feature = "carcara-verify")]
#[test]
fn test_alethe_cert_valid_proof_returns_true() {
    let valid = verify_alethe_certificate(&sample_valid_alethe_cert())
        .expect("complete Alethe proof should return Ok(true)");
    assert!(
        valid,
        "complete Alethe proof should count as fully verified"
    );
}

#[cfg(feature = "carcara-verify")]
#[test]
fn test_alethe_cert_holey_proof_returns_false() {
    let valid = verify_alethe_certificate(&sample_holey_alethe_cert())
        .expect("holey Alethe proof should return Ok(false), not a verifier transport error");
    assert!(
        !valid,
        "holey Alethe proof should not count as fully verified"
    );
}

/// Regression test for #2701: raw ay QF_LIA Alethe proofs must never hard-fail
/// on Carcara transport anymore. Missing `la_generic :args` still degrades to
/// the holey `Ok(false)` path, but newer ay pins may also emit proofs that do
/// not use `la_generic` at all or already include the required coefficients.
#[cfg(feature = "carcara-verify")]
#[test]
fn test_alethe_cert_raw_ay_lia_tracks_la_generic_args_contract() {
    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
    let x = backend.fresh_int("x");
    backend.assert_formula(&format!("(> {x} 0)"));
    backend.assert_formula(&format!("(< {x} 0)"));

    let problem = format!(
        "(set-logic QF_LIA)\n(declare-const {x} Int)\n(assert (> {x} 0))\n(assert (< {x} 0))\n(check-sat)\n"
    );
    let proof = match backend
        .check_sat()
        .expect("simple contradiction should produce an UNSAT proof")
    {
        AyProofResult::Unsat {
            proof: Some(proof), ..
        } => proof,
        other => panic!("expected UNSAT proof result, got {other:?}"),
    };

    let missing_la_generic_args = proof
        .lines()
        .any(|line| line.contains(":rule la_generic") && !line.contains(":args"));
    let raw_proof_is_already_holey = proof.contains(":rule hole") || proof.contains(":rule trust");

    let cert = ExternalAletheCert {
        version: "1.0".to_string(),
        problem,
        proof,
    };

    let valid = verify_alethe_certificate(&cert)
        .expect("raw ay QF_LIA proof should verify or degrade cleanly, not error (Part of #2701)");
    if missing_la_generic_args || raw_proof_is_already_holey {
        assert!(
            !valid,
            "raw ay QF_LIA proof should stay holey when it carries missing la_generic :args or explicit hole/trust steps"
        );
    } else {
        assert!(
            valid,
            "raw ay QF_LIA proof with no missing la_generic :args and no explicit hole/trust steps should count as fully verified"
        );
    }
}
