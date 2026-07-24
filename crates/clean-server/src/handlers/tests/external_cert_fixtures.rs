// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Handler-level fixture replay tests for external certificates (Part of #1195).
//!
//! These tests load the canonical JSON fixtures from `tests/fixtures/external_certificates/`
//! and route them through the server handler functions, validating the full
//! deserialization → handler → response path. This catches schema drift between
//! the shipped fixture wire format and the handler's expected param shape.

use crate::handlers::*;
use clean_elab::cert::external::ExternalCertificate;

fn fixture_path(name: &str) -> std::path::PathBuf {
    let workspace_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    workspace_root
        .join("tests/fixtures/external_certificates")
        .join(name)
}

fn load_fixture(name: &str) -> ExternalCertificate {
    let json =
        std::fs::read_to_string(fixture_path(name)).expect("fixture file should be readable");
    serde_json::from_str(&json).expect("fixture should deserialize into ExternalCertificate")
}

#[tokio::test]
async fn test_handler_fixture_farkas_valid() {
    let cert = load_fixture("gamma_crown_farkas_valid.json");
    assert!(
        matches!(&cert, ExternalCertificate::Farkas(_)),
        "farkas fixture should deserialize as Farkas variant"
    );

    let state = ServerState::new();
    let params = VerifyExternalCertParams {
        certificate: cert,
        timeout_ms: None,
    };

    let response = handle_verify_farkas_certificate(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected RPC error: {:?}",
        response.error
    );

    let result: VerifyFarkasCertResult =
        serde_json::from_value(response.result.expect("response should have result")).unwrap();
    assert!(result.valid, "farkas fixture should verify as valid");
    assert!(
        result.contradiction_value.is_some(),
        "valid farkas should include contradiction_value"
    );
    assert!(result.error.is_none());
    assert!(result.detail.is_none());
    assert!(result.time_us > 0, "timing should be recorded");
}

#[tokio::test]
async fn test_handler_fixture_entailment_valid() {
    let cert = load_fixture("gamma_crown_entailment_valid.json");
    assert!(
        matches!(&cert, ExternalCertificate::Entailment(_)),
        "entailment fixture should deserialize as Entailment variant"
    );

    let state = ServerState::new();
    let params = VerifyExternalCertParams {
        certificate: cert,
        timeout_ms: None,
    };

    let response = handle_verify_entailment_certificate(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected RPC error: {:?}",
        response.error
    );

    let result: VerifyEntailmentCertResult =
        serde_json::from_value(response.result.expect("response should have result")).unwrap();
    assert!(result.valid, "entailment fixture should verify as valid");
    assert!(
        result.derived_bound.is_some(),
        "valid entailment should include derived_bound"
    );
    assert!(
        result.claimed_bound.is_some(),
        "valid entailment should include claimed_bound"
    );
    assert!(result.error.is_none());
    assert!(result.detail.is_none());
    assert!(result.time_us > 0, "timing should be recorded");
}

#[tokio::test]
async fn test_handler_fixture_batch_valid() {
    let json = std::fs::read_to_string(fixture_path("gamma_crown_batch_valid.json"))
        .expect("batch fixture should be readable");
    let certs: Vec<ExternalCertificate> =
        serde_json::from_str(&json).expect("batch fixture should deserialize");
    assert_eq!(
        certs.len(),
        2,
        "batch fixture should contain 2 certificates"
    );

    let items: Vec<BatchExternalCertItem> = certs
        .into_iter()
        .enumerate()
        .map(|(i, cert)| BatchExternalCertItem {
            id: format!("fixture-{i}"),
            certificate: cert,
        })
        .collect();

    let state = ServerState::new();
    let params = BatchVerifyExternalCertParams {
        certificates: items,
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
        serde_json::from_value(response.result.expect("response should have result")).unwrap();
    assert_eq!(result.stats.total, 2);
    assert_eq!(result.stats.valid, 2);
    assert_eq!(result.stats.invalid, 0);
    assert!(result.stats.total_time_us > 0, "timing should be recorded");
    assert_eq!(result.results.len(), 2);
    for item in &result.results {
        assert!(item.valid, "batch fixture item {} should be valid", item.id);
    }
}

#[tokio::test]
async fn test_handler_fixture_alethe_valid_when_verifier_available() {
    let cert = load_fixture("ay_alethe_envelope.json");
    assert!(
        matches!(&cert, ExternalCertificate::Alethe(_)),
        "alethe fixture should deserialize as Alethe variant"
    );

    let state = ServerState::new();
    let params = VerifyExternalCertParams {
        certificate: cert,
        timeout_ms: None,
    };

    let response = handle_verify_alethe_certificate(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "alethe fixture should not produce an RPC error: {:?}",
        response.error
    );

    let result: VerifyAletheCertResult =
        serde_json::from_value(response.result.expect("response should have result")).unwrap();
    #[cfg(feature = "carcara-verify")]
    {
        assert!(result.valid, "Alethe fixture should verify as valid");
        assert_eq!(
            result.error, None,
            "verified Alethe fixture should not return an error code"
        );
        assert_eq!(
            result.detail, None,
            "verified Alethe fixture should not return an error detail"
        );
    }
    #[cfg(not(feature = "carcara-verify"))]
    {
        assert!(
            !result.valid,
            "without carcara-verify the handler should stay invalid on the tier-1 verifier gate"
        );
        assert_eq!(result.error.as_deref(), Some("proof_verification_failed"));
        assert_eq!(
            result.detail.as_deref(),
            Some("carcara-verify feature required for tier 1 verification")
        );
    }
    assert!(result.time_us > 0, "timing should be recorded");
}

#[tokio::test]
async fn test_handler_fixture_farkas_type_mismatch_through_entailment() {
    // Load a Farkas fixture and send it through the entailment handler.
    // This exercises the type-mismatch path using real fixture data.
    let cert = load_fixture("gamma_crown_farkas_valid.json");

    let state = ServerState::new();
    let params = VerifyExternalCertParams {
        certificate: cert,
        timeout_ms: None,
    };

    let response = handle_verify_entailment_certificate(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "type mismatch should not be an RPC error: {:?}",
        response.error
    );

    let result: VerifyEntailmentCertResult =
        serde_json::from_value(response.result.expect("response should have result")).unwrap();
    assert!(!result.valid);
    assert_eq!(result.error.as_deref(), Some("invalid_schema"));
    assert_eq!(
        result.detail.as_deref(),
        Some("expected entailment_certificate")
    );
}
