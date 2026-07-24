// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![cfg(feature = "carcara-verify")]

use crate::handlers::*;
use clean_auto::bridge::ay_contract::{AyLogic, AyProofBackend, AyProofResult};
use clean_elab::cert::external::{ExternalAletheCert, ExternalCertificate};

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

#[tokio::test]
async fn test_verify_alethe_certificate_holey_proof_returns_valid_false() {
    let state = ServerState::new();
    let params = VerifyExternalCertParams {
        certificate: ExternalCertificate::Alethe(sample_holey_alethe_cert()),
        timeout_ms: None,
    };

    let response = handle_verify_alethe_certificate(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected RPC error: {:?}",
        response.error
    );
    let result: VerifyAletheCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        !result.valid,
        "holey Alethe proof should not count as fully verified"
    );
    assert_eq!(
        result.error, None,
        "single-certificate handler should surface holey proofs as valid=false"
    );
    assert_eq!(
        result.detail, None,
        "single-certificate handler should not reclassify holey proofs as handler errors"
    );
}

#[tokio::test]
async fn test_verify_external_certificates_batch_alethe_holey_proof() {
    let state = ServerState::new();
    let params = BatchVerifyExternalCertParams {
        certificates: vec![BatchExternalCertItem {
            id: "alethe-bad".to_string(),
            certificate: ExternalCertificate::Alethe(sample_holey_alethe_cert()),
        }],
        threads: 0,
        timeout_ms: None,
    };

    let response = handle_verify_certificates_batch(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected RPC error: {:?}",
        response.error
    );
    let result: BatchVerifyExternalCertResult =
        serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.stats.total, 1);
    assert_eq!(result.stats.valid, 0);
    assert_eq!(result.stats.invalid, 1);

    let item = result
        .results
        .iter()
        .find(|item| item.id == "alethe-bad")
        .expect("batch result should include the holey Alethe proof");
    assert!(
        !item.valid,
        "batch verifier should mark holey Alethe proofs invalid"
    );
    assert_eq!(
        item.error.as_deref(),
        Some("proof_verification_failed"),
        "batch handler should translate valid=false into a proof verification error"
    );
    assert_eq!(
        item.detail.as_deref(),
        Some("proof was holey or not fully verified")
    );
}
