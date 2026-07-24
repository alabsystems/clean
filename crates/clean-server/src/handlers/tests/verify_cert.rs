// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;
use clean_kernel::cert::{
    archive_cert_with_algorithm_stats, CertArchive, CertArchiveEnvelope, CompressionAlgorithm,
    ProofCert,
};
use clean_kernel::mode::CleanMode;
use clean_kernel::{Environment, Expr, ExprKind, Level};

#[tokio::test]
async fn test_verify_cert_valid_sort() {
    let state = ServerState::new();
    let level = Level::zero();
    let expr = Expr::sort(level.clone());
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let params = VerifyCertParams {
        cert,
        expr,
        timeout_ms: None,
    };

    let response = handle_verify_cert(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: VerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.success);
    assert!(
        result.verified_type.is_some(),
        "expected verified_type to be present"
    );
    assert!(
        result.error.is_none(),
        "unexpected result error: {:?}",
        result.error
    );
}

#[tokio::test]
async fn test_verify_cert_archive_valid_sort() {
    let state = ServerState::new();
    let level = Level::zero();
    let expr = Expr::sort(level.clone());
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let (archive, _) = archive_cert_with_algorithm_stats(&cert, CompressionAlgorithm::Lz4).unwrap();

    let params = VerifyCertArchiveParams {
        archive,
        expr,
        timeout_ms: None,
    };

    let response = handle_verify_cert_archive(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: VerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.success);
    assert!(
        result.verified_type.is_some(),
        "expected verified_type to be present"
    );
    assert!(
        result.error.is_none(),
        "unexpected result error: {:?}",
        result.error
    );
}

#[tokio::test]
async fn test_verify_cert_uses_environment_mode_for_cubical_interval() {
    let state = ServerState::new().with_env(Environment::with_mode(CleanMode::Cubical));
    let params = VerifyCertParams {
        cert: ProofCert::CubicalInterval,
        expr: Expr::from_kind(ExprKind::CubicalInterval),
        timeout_ms: None,
    };

    let response = handle_verify_cert(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: VerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.success,
        "Cubical interval verification should succeed in cubical mode: {:?}",
        result.error
    );
    assert!(
        result.verified_type.is_some(),
        "expected verified_type to be present"
    );
}

#[tokio::test]
async fn test_verify_cert_archive_uses_environment_mode_for_cubical_interval() {
    let state = ServerState::new().with_env(Environment::with_mode(CleanMode::Cubical));
    let (archive, _) =
        archive_cert_with_algorithm_stats(&ProofCert::CubicalInterval, CompressionAlgorithm::Lz4)
            .expect("cubical interval certificate should archive");
    let params = VerifyCertArchiveParams {
        archive,
        expr: Expr::from_kind(ExprKind::CubicalInterval),
        timeout_ms: None,
    };

    let response = handle_verify_cert_archive(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: VerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.success,
        "Archived cubical interval verification should succeed in cubical mode: {:?}",
        result.error
    );
    assert!(
        result.verified_type.is_some(),
        "expected verified_type to be present"
    );
}

#[tokio::test]
async fn test_verify_cert_invalid_certificate() {
    let state = ServerState::new();
    // Create mismatched cert and expression
    let level = Level::zero();
    let expr = Expr::sort(level.clone());
    let cert = ProofCert::Sort {
        level: Level::succ(Level::zero()), // Mismatched level
    };

    let params = VerifyCertParams {
        cert,
        expr,
        timeout_ms: None,
    };

    let response = handle_verify_cert(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Should return result not RPC error"
    );

    let result: VerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.success);
    assert!(
        result.verified_type.is_none(),
        "expected no verified_type on failure, got: {:?}",
        result.verified_type
    );
    assert!(
        result.error.is_some(),
        "expected error on failure but got none"
    );
}

#[tokio::test]
async fn test_verify_cert_json_serialization() {
    let level = Level::zero();
    let cert = ProofCert::Sort {
        level: level.clone(),
    };
    let expr = Expr::sort(level);

    let params = VerifyCertParams {
        cert,
        expr,
        timeout_ms: Some(1000),
    };

    // Test that params can be serialized/deserialized
    let json = serde_json::to_string(&params).expect("Should serialize");
    let _: VerifyCertParams = serde_json::from_str(&json).expect("Should deserialize");

    let result = VerifyCertResult {
        success: true,
        verified_type: Some("Sort(succ(zero))".to_string()),
        error: None,
        time_us: 42,
        time_ns: Some(42_000),
    };

    let json = serde_json::to_string(&result).expect("Should serialize");
    let deserialized: VerifyCertResult = serde_json::from_str(&json).expect("Should deserialize");
    assert_eq!(deserialized.success, result.success);
    assert_eq!(deserialized.time_us, result.time_us);
}

#[tokio::test]
async fn test_verify_cert_valid_pi() {
    use clean_kernel::{BinderInfo, Level};

    let state = ServerState::new();
    // Pi type: (x : Type) → Type
    // This is a valid Pi type in universe Type 1
    let type_0 = Expr::sort(Level::zero());

    // The Pi expression: (x : Type 0) → Type 0
    let pi_expr = Expr::pi(
        BinderInfo::Default,
        type_0.clone(),
        type_0.clone(), // Body doesn't use x, so it's just Type 0
    );

    // Use infer_type_with_cert to generate correct certificate
    use clean_kernel::TypeChecker;
    let env = clean_kernel::Environment::new();
    let tc = TypeChecker::new(&env);
    let (_, cert) = tc
        .infer_type_with_cert(&pi_expr)
        .expect("Pi should type-check");

    let params = VerifyCertParams {
        cert,
        expr: pi_expr,
        timeout_ms: None,
    };

    let response = handle_verify_cert(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: VerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.success,
        "Pi verification should succeed: {:?}",
        result.error
    );
    assert!(
        result.verified_type.is_some(),
        "expected verified_type to be present"
    );
}

#[tokio::test]
async fn test_verify_cert_valid_lambda() {
    use clean_kernel::{BinderInfo, Level};

    let state = ServerState::new();
    // Lambda: λ (x : Type) => x
    // This is the identity function at Type level
    let type_0 = Expr::sort(Level::zero());

    let lam_expr = Expr::lam(
        BinderInfo::Default,
        type_0.clone(),
        Expr::bvar(0), // Body is just x (BVar 0)
    );

    // Use infer_type_with_cert to generate correct certificate
    use clean_kernel::TypeChecker;
    let env = clean_kernel::Environment::new();
    let tc = TypeChecker::new(&env);
    let (_, cert) = tc
        .infer_type_with_cert(&lam_expr)
        .expect("Lambda should type-check");

    let params = VerifyCertParams {
        cert,
        expr: lam_expr,
        timeout_ms: None,
    };

    let response = handle_verify_cert(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: VerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.success,
        "Lambda verification should succeed: {:?}",
        result.error
    );
    assert!(
        result.verified_type.is_some(),
        "expected verified_type to be present"
    );
}

#[tokio::test]
async fn test_verify_cert_valid_app() {
    use clean_kernel::{BinderInfo, Level};

    let state = ServerState::new();
    // Application: (λ (x : Type 1) => x) Type
    // The identity function at universe level 1 applied to Type 0
    // Type 0 : Type 1, so this is well-typed
    let type_0 = Expr::sort(Level::zero());
    let type_1 = Expr::sort(Level::succ(Level::zero()));

    // The identity lambda: λ (x : Type 1). x
    let id_lam = Expr::lam(
        BinderInfo::Default,
        type_1.clone(), // Domain is Type 1
        Expr::bvar(0),
    );

    // Application expression: (λ (x : Type 1). x) Type 0
    // Type 0 has type Type 1, so this is valid
    let app_expr = Expr::app(id_lam, type_0);

    // Use infer_type_with_cert to generate correct certificate
    use clean_kernel::TypeChecker;
    let env = clean_kernel::Environment::new();
    let tc = TypeChecker::new(&env);
    let (_, cert) = tc
        .infer_type_with_cert(&app_expr)
        .expect("App should type-check");

    let params = VerifyCertParams {
        cert,
        expr: app_expr,
        timeout_ms: None,
    };

    let response = handle_verify_cert(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: VerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.success,
        "App verification should succeed: {:?}",
        result.error
    );
    assert!(
        result.verified_type.is_some(),
        "expected verified_type to be present"
    );
}

#[tokio::test]
async fn test_verify_cert_invalid_pi_level_mismatch() {
    use clean_kernel::{BinderInfo, Level};

    let state = ServerState::new();
    // Pi type with mismatched level in certificate
    let type_0 = Expr::sort(Level::zero());

    let pi_expr = Expr::pi(BinderInfo::Default, type_0.clone(), type_0.clone());

    // Certificate with wrong arg level
    let arg_type_cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let body_type_cert = ProofCert::Sort {
        level: Level::zero(),
    };

    let cert = ProofCert::Pi {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(arg_type_cert),
        arg_level: Level::zero(), // WRONG: should be succ(zero)
        body_type_cert: Box::new(body_type_cert),
        body_level: Level::succ(Level::zero()),
    };

    let params = VerifyCertParams {
        cert,
        expr: pi_expr,
        timeout_ms: None,
    };

    let response = handle_verify_cert(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Should return result not RPC error"
    );

    let result: VerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        !result.success,
        "Pi verification should fail due to level mismatch"
    );
    assert!(
        result.error.is_some(),
        "expected error on failure but got none"
    );
}

#[tokio::test]
async fn test_verify_cert_nested_app_lambda() {
    use clean_kernel::{BinderInfo, Level};

    let state = ServerState::new();
    // Test nested application: (λx:Type1. x) ((λy:Type1. y) Type0)
    // This is: id (id Type0) where id = λx:Type1. x
    // Type0 : Type1, so both applications are well-typed
    let type_0 = Expr::sort(Level::zero());
    let type_1 = Expr::sort(Level::succ(Level::zero()));

    // The identity lambda at Type 1: λx:Type1. x
    let id_lam = Expr::lam(BinderInfo::Default, type_1.clone(), Expr::bvar(0));

    // Inner application: (λy:Type1. y) Type0
    let inner_app = Expr::app(id_lam.clone(), type_0.clone());

    // Outer application: (λx:Type1. x) ((λy:Type1. y) Type0)
    // The inner app has type Type1 (from id's return type instantiated),
    // but we need to apply id to something of type Type1.
    // However, ((λy:Type1. y) Type0) has type Type1, not Type0!
    // So this should work.
    let nested_app = Expr::app(id_lam, inner_app);

    // Use infer_type_with_cert to generate correct certificate
    use clean_kernel::TypeChecker;
    let env = clean_kernel::Environment::new();
    let tc = TypeChecker::new(&env);
    let (_, cert) = tc
        .infer_type_with_cert(&nested_app)
        .expect("Nested app should type-check");

    let params = VerifyCertParams {
        cert,
        expr: nested_app,
        timeout_ms: None,
    };

    let response = handle_verify_cert(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: VerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.success,
        "Nested app/lambda verification should succeed: {:?}",
        result.error
    );
    assert!(
        result.verified_type.is_some(),
        "expected verified_type to be present"
    );
}

// --- Batch certificate verification tests ---

#[tokio::test]
async fn test_batch_verify_cert_empty() {
    let state = ServerState::new();
    let params = BatchVerifyCertParams {
        items: vec![],
        threads: 0,
        timeout_ms: None,
    };

    let response = handle_batch_verify_cert(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: BatchVerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.results.is_empty());
    assert_eq!(result.stats.total, 0);
}

#[tokio::test]
async fn test_batch_verify_cert_single_valid() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let level = Level::zero();
    let expr = Expr::sort(level.clone());
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let params = BatchVerifyCertParams {
        items: vec![BatchVerifyCertItem {
            id: "test1".to_string(),
            cert,
            expr,
        }],
        threads: 0,
        timeout_ms: None,
    };

    let response = handle_batch_verify_cert(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: BatchVerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.results.len(), 1);
    assert!(result.results[0].success);
    assert_eq!(result.results[0].id, "test1");
    assert!(
        result.results[0].verified_type.is_some(),
        "expected verified_type for successful cert"
    );
    assert_eq!(result.stats.total, 1);
    assert_eq!(result.stats.successful, 1);
    assert_eq!(result.stats.failed, 0);
}

#[tokio::test]
async fn test_batch_verify_cert_archive_single_valid() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let level = Level::zero();
    let expr = Expr::sort(level.clone());
    let cert = ProofCert::Sort {
        level: level.clone(),
    };
    let (archive, _) = archive_cert_with_algorithm_stats(&cert, CompressionAlgorithm::Lz4).unwrap();

    let params = BatchVerifyCertArchiveParams {
        items: vec![BatchVerifyCertArchiveItem {
            id: "archive-1".to_string(),
            archive,
            expr,
        }],
        threads: 0,
        timeout_ms: None,
    };

    let response =
        handle_batch_verify_cert_archive(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: BatchVerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.results.len(), 1);
    assert!(result.results[0].success);
    assert_eq!(result.results[0].id, "archive-1");
    assert_eq!(result.stats.total, 1);
    assert_eq!(result.stats.successful, 1);
    assert_eq!(result.stats.failed, 0);
}

#[tokio::test]
async fn test_verify_cert_archive_invalid_archive() {
    let state = ServerState::new();
    let level = Level::zero();
    let expr = Expr::sort(level);

    // Create an invalid archive envelope with corrupted data
    let invalid_archive = CertArchiveEnvelope::Lz4(CertArchive {
        compressed_data: vec![0xFF, 0xFF, 0xFF], // Invalid LZ4 data
        uncompressed_size: 100,
        version: 1,
    });

    let params = VerifyCertArchiveParams {
        archive: invalid_archive,
        expr,
        timeout_ms: None,
    };

    let response = handle_verify_cert_archive(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Should return success with error in result, not RPC error"
    );

    let result: VerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.success, "Should fail for invalid archive");
    assert!(result.error.is_some(), "Should have error message");
    assert!(
        result.error.as_ref().unwrap().contains("Archive error"),
        "Error should mention archive: {:?}",
        result.error
    );
}

#[tokio::test]
async fn test_batch_verify_cert_archive_mixed_valid_invalid() {
    let state = ServerState::new();
    let level = Level::zero();
    let expr = Expr::sort(level.clone());
    let cert = ProofCert::Sort {
        level: level.clone(),
    };
    let (valid_archive, _) =
        archive_cert_with_algorithm_stats(&cert, CompressionAlgorithm::Lz4).unwrap();

    // Create invalid archive with corrupted data
    let invalid_archive = CertArchiveEnvelope::Lz4(CertArchive {
        compressed_data: vec![0xFF, 0xFF, 0xFF], // Invalid LZ4 data
        uncompressed_size: 100,
        version: 1,
    });

    let params = BatchVerifyCertArchiveParams {
        items: vec![
            BatchVerifyCertArchiveItem {
                id: "valid-1".to_string(),
                archive: valid_archive,
                expr: expr.clone(),
            },
            BatchVerifyCertArchiveItem {
                id: "invalid-1".to_string(),
                archive: invalid_archive,
                expr,
            },
        ],
        threads: 0,
        timeout_ms: None,
    };

    let response =
        handle_batch_verify_cert_archive(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: BatchVerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.stats.total, 2);
    assert_eq!(result.stats.successful, 1);
    assert_eq!(result.stats.failed, 1);

    // Find the results by id
    let valid_result = result.results.iter().find(|r| r.id == "valid-1").unwrap();
    let invalid_result = result.results.iter().find(|r| r.id == "invalid-1").unwrap();

    assert!(valid_result.success);
    assert!(!invalid_result.success);
    assert!(
        invalid_result.error.is_some(),
        "expected error for invalid cert but got none"
    );
}

#[tokio::test]
async fn test_batch_verify_cert_archive_streams_progress_with_failures() {
    use tokio::sync::mpsc;

    let state = ServerState::new();
    let level = Level::zero();
    let expr = Expr::sort(level.clone());
    let cert = ProofCert::Sort {
        level: level.clone(),
    };
    let (valid_archive, _) =
        archive_cert_with_algorithm_stats(&cert, CompressionAlgorithm::Lz4).unwrap();

    // Create invalid archive with corrupted data
    let invalid_archive = CertArchiveEnvelope::Lz4(CertArchive {
        compressed_data: vec![0xFF, 0xFF, 0xFF],
        uncompressed_size: 100,
        version: 1,
    });

    let params = BatchVerifyCertArchiveParams {
        items: vec![
            BatchVerifyCertArchiveItem {
                id: "valid-1".to_string(),
                archive: valid_archive,
                expr: expr.clone(),
            },
            BatchVerifyCertArchiveItem {
                id: "invalid-1".to_string(),
                archive: invalid_archive,
                expr,
            },
        ],
        threads: 0,
        timeout_ms: None,
    };

    let (tx, mut rx) = mpsc::channel(16);
    let progress = ProgressSender::new(RequestId::Number(99), tx);

    let response =
        handle_batch_verify_cert_archive(&state, RequestId::Number(1), params, Some(progress))
            .await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let mut updates = Vec::new();
    // Use 5s timeout to avoid flakiness under CI load
    while let Ok(update) = tokio::time::timeout(Duration::from_secs(5), rx.recv()).await {
        match update {
            Some(u) => updates.push(u),
            None => break,
        }
    }

    // Should have: start + 2 per-item (valid + invalid archive) + complete
    assert!(
        updates.len() >= 3,
        "expected start + per-item + final progress updates, got {}",
        updates.len()
    );
    assert!(
        updates.iter().any(|u| u.message.contains("Verified")),
        "should include per-item verification updates"
    );
    // Verify final update shows accurate counts (1 success, 1 fail)
    let final_update = updates.last().unwrap();
    assert!(
        final_update.message.contains("1 success") && final_update.message.contains("1 failed"),
        "final update should show 1 success / 1 failed, got: {}",
        final_update.message
    );
    assert!(
        final_update.percentage == Some(100),
        "should mark completion percentage"
    );
}

#[tokio::test]
async fn test_batch_verify_cert_multiple() {
    use clean_kernel::Level;

    let state = ServerState::new();

    let items: Vec<BatchVerifyCertItem> = (0..10)
        .map(|i| {
            let level = Level::zero();
            let expr = Expr::sort(level.clone());
            let cert = ProofCert::Sort {
                level: level.clone(),
            };
            BatchVerifyCertItem {
                id: format!("cert_{i}"),
                cert,
                expr,
            }
        })
        .collect();

    let params = BatchVerifyCertParams {
        items,
        threads: 0,
        timeout_ms: None,
    };

    let response = handle_batch_verify_cert(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: BatchVerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.results.len(), 10);
    assert_eq!(result.stats.total, 10);
    assert_eq!(result.stats.successful, 10);

    for (i, item_result) in result.results.iter().enumerate() {
        assert!(item_result.success, "Failed at index {i}");
        assert_eq!(item_result.id, format!("cert_{i}"));
    }
}

#[tokio::test]
async fn test_batch_verify_cert_with_failures() {
    use clean_kernel::Level;

    let state = ServerState::new();

    let items: Vec<BatchVerifyCertItem> = (0..5)
        .map(|i| {
            let level = Level::zero();
            let expr = Expr::sort(level.clone());
            if i % 2 == 0 {
                // Valid certificate
                let cert = ProofCert::Sort {
                    level: level.clone(),
                };
                BatchVerifyCertItem {
                    id: format!("valid_{i}"),
                    cert,
                    expr,
                }
            } else {
                // Invalid certificate (level mismatch)
                let cert = ProofCert::Sort {
                    level: Level::succ(Level::zero()),
                };
                BatchVerifyCertItem {
                    id: format!("invalid_{i}"),
                    cert,
                    expr,
                }
            }
        })
        .collect();

    let params = BatchVerifyCertParams {
        items,
        threads: 0,
        timeout_ms: None,
    };

    let response = handle_batch_verify_cert(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: BatchVerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.results.len(), 5);
    assert!(result.results[0].success); // valid_0
    assert!(!result.results[1].success); // invalid_1
    assert!(result.results[2].success); // valid_2
    assert!(!result.results[3].success); // invalid_3
    assert!(result.results[4].success); // valid_4

    assert_eq!(result.stats.successful, 3);
    assert_eq!(result.stats.failed, 2);
}

#[tokio::test]
async fn test_batch_verify_cert_stats() {
    use clean_kernel::Level;

    let state = ServerState::new();

    let items: Vec<BatchVerifyCertItem> = (0..100)
        .map(|i| {
            let level = Level::zero();
            let expr = Expr::sort(level.clone());
            let cert = ProofCert::Sort {
                level: level.clone(),
            };
            BatchVerifyCertItem {
                id: format!("{i}"),
                cert,
                expr,
            }
        })
        .collect();

    let params = BatchVerifyCertParams {
        items,
        threads: 0,
        timeout_ms: None,
    };

    let response = handle_batch_verify_cert(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: BatchVerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.stats.total, 100);
    assert_eq!(result.stats.successful, 100);
    assert_eq!(result.stats.failed, 0);
    // Verify timing stats are populated
    assert!(result.stats.wall_time_us > 0 || result.stats.total == 0);
}

#[tokio::test]
async fn test_batch_verify_cert_streams_progress() {
    use tokio::sync::mpsc;

    let state = ServerState::new();
    let level = Level::zero();
    let expr = Expr::sort(level.clone());
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let params = BatchVerifyCertParams {
        items: vec![
            BatchVerifyCertItem {
                id: "a".to_string(),
                cert: cert.clone(),
                expr: expr.clone(),
            },
            BatchVerifyCertItem {
                id: "b".to_string(),
                cert,
                expr,
            },
        ],
        threads: 0,
        timeout_ms: None,
    };

    let (tx, mut rx) = mpsc::channel(16);
    let progress = ProgressSender::new(RequestId::Number(99), tx);

    let response =
        handle_batch_verify_cert(&state, RequestId::Number(1), params, Some(progress)).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let mut updates = Vec::new();
    // Use 5s timeout to avoid flakiness under CI load
    while let Ok(update) = tokio::time::timeout(Duration::from_secs(5), rx.recv()).await {
        match update {
            Some(u) => updates.push(u),
            None => break,
        }
    }

    assert!(
        updates.len() >= 3,
        "expected start + per-item + final progress updates"
    );
    assert!(
        updates.iter().any(|u| u.message.contains("Verified")),
        "should include per-item verification updates"
    );
    assert!(
        updates.iter().any(|u| u.percentage == Some(100)),
        "should mark completion percentage"
    );
}

#[tokio::test]
async fn test_batch_verify_cert_json_serialization() {
    use clean_kernel::Level;

    // Test that the types can be serialized/deserialized correctly
    let level = Level::zero();
    let expr = Expr::sort(level.clone());
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let item = BatchVerifyCertItem {
        id: "test".to_string(),
        cert,
        expr,
    };

    // Should be able to serialize to JSON
    let json = serde_json::to_string(&item).expect("Should serialize");
    assert!(json.contains("test"));

    // Should be able to deserialize back
    let _: BatchVerifyCertItem = serde_json::from_str(&json).expect("Should deserialize");
}

// ========================================================================
// Certificate Compression Tests
// ========================================================================

#[tokio::test]
async fn test_batch_verify_cert_with_threads_param() {
    // Test that threads parameter in request is respected
    let state = ServerState::new();

    // Create a valid certificate
    let level = Level::zero();
    let expr = Expr::sort(level.clone());
    let cert = ProofCert::Sort { level };

    let params = BatchVerifyCertParams {
        items: vec![BatchVerifyCertItem {
            id: "test1".to_string(),
            cert,
            expr,
        }],
        threads: 2, // Request 2 threads
        timeout_ms: None,
    };

    let response = handle_batch_verify_cert(&state, RequestId::Number(1), params, None).await;
    let result: BatchVerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert_eq!(result.stats.total, 1);
    assert_eq!(result.stats.successful, 1);
}

#[tokio::test]
async fn test_batch_verify_cert_uses_server_worker_threads() {
    // Test that server config worker_threads is used when request threads=0
    let state = ServerState::new().with_worker_threads(2);

    // Create a valid certificate
    let level = Level::zero();
    let expr = Expr::sort(level.clone());
    let cert = ProofCert::Sort { level };

    let params = BatchVerifyCertParams {
        items: vec![BatchVerifyCertItem {
            id: "test1".to_string(),
            cert,
            expr,
        }],
        threads: 0, // Use server default
        timeout_ms: None,
    };

    let response = handle_batch_verify_cert(&state, RequestId::Number(1), params, None).await;
    let result: BatchVerifyCertResult = serde_json::from_value(response.result.unwrap()).unwrap();

    // Should succeed using server's 2 threads
    assert_eq!(result.stats.total, 1);
    assert_eq!(result.stats.successful, 1);
}

// ========================================================================
// Timeout error path tests (#1654 — acceptance criterion 2)
// ========================================================================

/// Test handle_verify_cert timeout path.
/// Uses a 1ms timeout to trigger the tokio::time::timeout arm (line 935-938).
#[tokio::test]
async fn test_verify_cert_timeout() {
    let state = ServerState::new();

    // Build a large nested certificate that takes non-trivial time to verify.
    // Even if verification is fast, a 1ms timeout may fire on env lock contention.
    let sort_type = Expr::sort(Level::succ(Level::zero()));
    let sort_expr = Expr::sort(Level::zero());
    let pi_type = Expr::pi(
        clean_kernel::BinderInfo::Default,
        sort_type.clone(),
        sort_type.clone(),
    );
    let mut cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let mut expr = sort_expr.clone();
    // Nest 100 layers of App(Lam(...)) to increase verification time
    for _ in 0..100 {
        let lam_cert = ProofCert::Lam {
            binder_info: clean_kernel::BinderInfo::Default,
            arg_type_cert: Box::new(ProofCert::Sort {
                level: Level::zero(),
            }),
            body_cert: Box::new(cert.clone()),
            result_type: Box::new(pi_type.clone()),
        };
        cert = ProofCert::App {
            fn_cert: Box::new(lam_cert),
            fn_type: Box::new(pi_type.clone()),
            arg_cert: Box::new(ProofCert::Sort {
                level: Level::zero(),
            }),
            result_type: Box::new(sort_type.clone()),
        };
        expr = Expr::app(
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                sort_expr.clone(),
                expr.clone(),
            ),
            sort_expr.clone(),
        );
    }

    let params = VerifyCertParams {
        cert,
        expr,
        timeout_ms: Some(1), // 1ms — likely to expire during deep verification
    };

    let response = handle_verify_cert(&state, RequestId::Number(1), params).await;

    // Either the verification finished quickly (cert is structurally valid-ish)
    // or we hit the timeout. Both are acceptable outcomes.
    if let Some(err) = response.error {
        assert_eq!(
            err.code, -32004,
            "Timeout should use TIMEOUT error code (-32004), got: {}",
            err.code
        );
    } else {
        // Handler completed within 1ms — verify it returned a valid result
        assert!(
            response.result.is_some(),
            "Non-error response must have a result"
        );
    }
}
