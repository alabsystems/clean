// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;
use clean_elab::cert::external::{
    ConstraintKind, ExternalCertificate, ExternalEntailmentCert, ExternalFarkasCert,
    ExternalLinearConstraint, ExternalRational,
};
use clean_kernel::cert::ProofCert;
use std::collections::BTreeMap;

fn sample_farkas_cert() -> ExternalFarkasCert {
    ExternalFarkasCert {
        version: "1.0".to_string(),
        constraints: vec![
            ExternalLinearConstraint {
                kind: ConstraintKind::Le,
                coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
                constant: ExternalRational::from_int(5),
            },
            ExternalLinearConstraint {
                kind: ConstraintKind::Le,
                coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(-1))]),
                constant: ExternalRational::from_int(-6),
            },
        ],
        multipliers: vec![ExternalRational::ONE, ExternalRational::ONE],
        conclusion: "contradiction".to_string(),
    }
}

pub(super) fn sample_entailment_cert() -> ExternalEntailmentCert {
    ExternalEntailmentCert {
        version: "1.0".to_string(),
        premises: vec![ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
            constant: ExternalRational::from_int(5),
        }],
        multipliers: vec![ExternalRational::ONE],
        conclusion: ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
            constant: ExternalRational::from_int(6),
        },
    }
}

#[tokio::test]
async fn test_verify_farkas_certificate_valid() {
    let state = ServerState::new();
    let params = VerifyExternalCertParams {
        certificate: ExternalCertificate::Farkas(sample_farkas_cert()),
        timeout_ms: None,
    };

    let response = handle_verify_farkas_certificate(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let result: VerifyFarkasCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.valid);
    assert!(
        result.contradiction_value.is_some(),
        "valid farkas cert should have contradiction value"
    );
}

#[tokio::test]
async fn test_verify_farkas_certificate_invalid_multiplier() {
    let state = ServerState::new();
    let mut cert = sample_farkas_cert();
    cert.multipliers = vec![ExternalRational::from_int(-1), ExternalRational::ONE];

    let params = VerifyExternalCertParams {
        certificate: ExternalCertificate::Farkas(cert),
        timeout_ms: None,
    };

    let response = handle_verify_farkas_certificate(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let result: VerifyFarkasCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.valid);
    assert_eq!(result.error.as_deref(), Some("multiplier_negative"));
}

#[tokio::test]
async fn test_verify_farkas_certificate_type_mismatch() {
    let state = ServerState::new();
    let params = VerifyExternalCertParams {
        certificate: ExternalCertificate::Entailment(sample_entailment_cert()),
        timeout_ms: None,
    };

    let response = handle_verify_farkas_certificate(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let result: VerifyFarkasCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.valid);
    assert_eq!(result.error.as_deref(), Some("invalid_schema"));
    assert_eq!(
        result.detail.as_deref(),
        Some("expected farkas_certificate")
    );
}

#[tokio::test]
async fn test_verify_entailment_certificate_valid() {
    let state = ServerState::new();
    let params = VerifyExternalCertParams {
        certificate: ExternalCertificate::Entailment(sample_entailment_cert()),
        timeout_ms: None,
    };

    let response = handle_verify_entailment_certificate(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let result: VerifyEntailmentCertResult =
        serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.valid);
    assert!(
        result.derived_bound.is_some(),
        "valid entailment should have derived_bound"
    );
    assert!(
        result.claimed_bound.is_some(),
        "valid entailment should have claimed_bound"
    );
}

#[tokio::test]
async fn test_verify_entailment_certificate_invalid() {
    let state = ServerState::new();
    let mut cert = sample_entailment_cert();
    cert.conclusion = ExternalLinearConstraint {
        kind: ConstraintKind::Le,
        coefficients: BTreeMap::from([("y".to_string(), ExternalRational::from_int(1))]),
        constant: ExternalRational::from_int(6),
    };

    let params = VerifyExternalCertParams {
        certificate: ExternalCertificate::Entailment(cert),
        timeout_ms: None,
    };

    let response = handle_verify_entailment_certificate(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let result: VerifyEntailmentCertResult =
        serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.valid);
    assert_eq!(result.error.as_deref(), Some("entailment_failed"));
    assert!(
        result.derived_bound.is_none(),
        "failed entailment should not have derived_bound, got: {:?}",
        result.derived_bound
    );
    assert!(
        result.claimed_bound.is_none(),
        "failed entailment should not have claimed_bound, got: {:?}",
        result.claimed_bound
    );
}

#[tokio::test]
async fn test_verify_external_certificates_batch_mixed() {
    let state = ServerState::new();
    let mut invalid_farkas = sample_farkas_cert();
    invalid_farkas.multipliers = vec![ExternalRational::from_int(-1), ExternalRational::ONE];

    let mut invalid_entailment = sample_entailment_cert();
    invalid_entailment.conclusion = ExternalLinearConstraint {
        kind: ConstraintKind::Le,
        coefficients: BTreeMap::from([("y".to_string(), ExternalRational::from_int(1))]),
        constant: ExternalRational::from_int(6),
    };

    let params = BatchVerifyExternalCertParams {
        certificates: vec![
            BatchExternalCertItem {
                id: "farkas-ok".to_string(),
                certificate: ExternalCertificate::Farkas(sample_farkas_cert()),
            },
            BatchExternalCertItem {
                id: "farkas-bad".to_string(),
                certificate: ExternalCertificate::Farkas(invalid_farkas),
            },
            BatchExternalCertItem {
                id: "entailment-ok".to_string(),
                certificate: ExternalCertificate::Entailment(sample_entailment_cert()),
            },
            BatchExternalCertItem {
                id: "entailment-bad".to_string(),
                certificate: ExternalCertificate::Entailment(invalid_entailment),
            },
        ],
        threads: 0,
        timeout_ms: None,
    };

    let response = handle_verify_certificates_batch(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let result: BatchVerifyExternalCertResult =
        serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.stats.total, 4);
    assert_eq!(result.stats.valid, 2);
    assert_eq!(result.stats.invalid, 2);
    assert!(result
        .results
        .iter()
        .any(|item| item.id == "farkas-bad" && !item.valid));
    assert!(result
        .results
        .iter()
        .any(|item| item.id == "entailment-bad" && !item.valid));
    assert!(result
        .results
        .iter()
        .any(|item| item.id == "farkas-ok" && item.valid));
    assert!(result
        .results
        .iter()
        .any(|item| item.id == "entailment-ok" && item.valid));
}

#[tokio::test]
async fn test_verify_external_certificates_batch_empty() {
    let state = ServerState::new();
    let params = BatchVerifyExternalCertParams {
        certificates: Vec::new(),
        threads: 0,
        timeout_ms: None,
    };

    let response = handle_verify_certificates_batch(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let result: BatchVerifyExternalCertResult =
        serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.results.is_empty());
    assert_eq!(result.stats.total, 0);
    assert_eq!(result.stats.valid, 0);
    assert_eq!(result.stats.invalid, 0);
}

#[tokio::test]
async fn test_verify_entailment_certificate_type_mismatch() {
    let state = ServerState::new();
    let params = VerifyExternalCertParams {
        certificate: ExternalCertificate::Farkas(sample_farkas_cert()),
        timeout_ms: None,
    };

    let response = handle_verify_entailment_certificate(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let result: VerifyEntailmentCertResult =
        serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.valid);
    assert_eq!(result.error.as_deref(), Some("invalid_schema"));
    assert_eq!(
        result.detail.as_deref(),
        Some("expected entailment_certificate")
    );
}

// ========================================================================
// External Certificate Timeout Tests
// ========================================================================

#[tokio::test]
async fn test_verify_farkas_certificate_timeout() {
    use crate::handlers::external_cert::TEST_DELAY_MS;
    use std::sync::atomic::Ordering;

    // Reset first for parallel test safety
    TEST_DELAY_MS.store(0, Ordering::Relaxed);
    // Set a 100ms delay in the handler
    TEST_DELAY_MS.store(100, Ordering::Relaxed);

    let state = ServerState::new();
    let params = VerifyExternalCertParams {
        certificate: ExternalCertificate::Farkas(sample_farkas_cert()),
        timeout_ms: Some(10), // 10ms timeout, will be exceeded by 100ms delay
    };

    let response = handle_verify_farkas_certificate(&state, RequestId::Number(1), params).await;

    // Reset delay for other tests
    TEST_DELAY_MS.store(0, Ordering::Relaxed);

    // Should return timeout error
    assert!(response.error.is_some(), "Expected timeout error");
    let err = response.error.unwrap();
    assert_eq!(err.code, -32004); // TIMEOUT error code
}

#[tokio::test]
async fn test_verify_entailment_certificate_timeout() {
    use crate::handlers::external_cert::TEST_DELAY_MS;
    use std::sync::atomic::Ordering;

    // Reset first for parallel test safety
    TEST_DELAY_MS.store(0, Ordering::Relaxed);
    // Set a 100ms delay in the handler
    TEST_DELAY_MS.store(100, Ordering::Relaxed);

    let state = ServerState::new();
    let params = VerifyExternalCertParams {
        certificate: ExternalCertificate::Entailment(sample_entailment_cert()),
        timeout_ms: Some(10), // 10ms timeout, will be exceeded by 100ms delay
    };

    let response = handle_verify_entailment_certificate(&state, RequestId::Number(1), params).await;

    // Reset delay for other tests
    TEST_DELAY_MS.store(0, Ordering::Relaxed);

    // Should return timeout error
    assert!(response.error.is_some(), "Expected timeout error");
    let err = response.error.unwrap();
    assert_eq!(err.code, -32004); // TIMEOUT error code
}

#[tokio::test]
async fn test_verify_certificates_batch_timeout() {
    use crate::handlers::external_cert::TEST_DELAY_MS;
    use std::sync::atomic::Ordering;

    // Reset first for parallel test safety
    TEST_DELAY_MS.store(0, Ordering::Relaxed);
    // Set a 100ms delay in the handler
    TEST_DELAY_MS.store(100, Ordering::Relaxed);

    let state = ServerState::new();
    let params = BatchVerifyExternalCertParams {
        certificates: vec![BatchExternalCertItem {
            id: "test".to_string(),
            certificate: ExternalCertificate::Farkas(sample_farkas_cert()),
        }],
        threads: 0,
        timeout_ms: Some(10), // 10ms timeout, will be exceeded by 100ms delay
    };

    let response = handle_verify_certificates_batch(&state, RequestId::Number(1), params).await;

    // Reset delay for other tests
    TEST_DELAY_MS.store(0, Ordering::Relaxed);

    // Should return timeout error
    assert!(response.error.is_some(), "Expected timeout error");
    let err = response.error.unwrap();
    assert_eq!(err.code, -32004); // TIMEOUT error code
}

// ========================================================================
// Dictionary Compression Tests
// ========================================================================

/// Helper to create sample certificates for dictionary training
pub(super) fn create_sample_certs(count: usize) -> Vec<ProofCert> {
    use clean_kernel::Level;

    (0..count)
        .map(|i| {
            // Create varied certificates with different universe levels
            let level = if i % 3 == 0 {
                Level::zero()
            } else if i % 3 == 1 {
                Level::succ(Level::zero())
            } else {
                Level::succ(Level::succ(Level::zero()))
            };
            ProofCert::Sort { level }
        })
        .collect()
}
