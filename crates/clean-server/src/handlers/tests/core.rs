// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;

/// Helper: create a `ServerState` pre-loaded with the kernel prelude (Nat, Bool, Eq, List, …).
fn prelude_state() -> ServerState {
    let env =
        clean_kernel::Environment::try_with_prelude().expect("try_with_prelude should succeed");
    ServerState::new().with_env(env)
}

#[tokio::test]
async fn test_check_simple_expr() {
    let state = ServerState::new();
    // Use fully-typed expression (no metavariables needed)
    let params = CheckParams {
        code: "fun (A : Type) (x : A) => x".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );
    let result: CheckResult = serde_json::from_value(
        response
            .result
            .expect("check response should have a result"),
    )
    .unwrap();
    assert!(
        result.valid,
        "Check result should be valid, got errors: {:?}",
        result.errors
    );
}

#[tokio::test]
async fn test_check_invalid_syntax() {
    let state = ServerState::new();
    let params = CheckParams {
        // Use undefined identifier that will fail type checking
        code: "unknownIdent123".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    // Should fail because unknownIdent123 is not defined
    assert!(
        !result.valid,
        "Expected invalid result for undefined identifier"
    );
    assert!(
        !result.errors.is_empty(),
        "Expected errors for undefined identifier"
    );
}

#[tokio::test]
async fn test_server_info() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(info.name, "clean-server");
    assert!(info.methods.contains(&"check".to_string()));
}

#[tokio::test]
async fn test_batch_check() {
    let state = ServerState::new();
    let params = BatchCheckParams {
        items: vec![
            BatchCheckItem {
                id: "1".to_string(),
                // Use fully-typed expression
                code: "fun (A : Type) (x : A) => x".to_string(),
            },
            BatchCheckItem {
                id: "2".to_string(),
                code: "Type".to_string(),
            },
        ],
        use_gpu: false,
        timeout_ms: None,
    };

    let response = handle_batch_check(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: BatchCheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.results.len(), 2);
    assert!(
        result.results[0].valid,
        "First item should be valid: {:?}",
        result.results[0]
    );
    assert!(
        result.results[1].valid,
        "Second item should be valid: {:?}",
        result.results[1]
    );
    // When use_gpu=false, no warnings should be present
    assert!(
        result.warnings.is_empty(),
        "No warnings expected when use_gpu=false"
    );
}

#[tokio::test]
async fn test_batch_check_use_gpu_warning() {
    let state = ServerState::new();
    let params = BatchCheckParams {
        items: vec![BatchCheckItem {
            id: "1".to_string(),
            code: "Type".to_string(),
        }],
        use_gpu: true, // Request GPU acceleration
        timeout_ms: None,
    };

    let response = handle_batch_check(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: BatchCheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.results.len(), 1);
    assert!(result.results[0].valid);
    // GPU is not available, so we expect a warning
    assert!(
        !result.warnings.is_empty(),
        "Expected warning when use_gpu=true"
    );
    assert!(
        result.warnings[0].contains("GPU"),
        "Warning should mention GPU: {:?}",
        result.warnings[0]
    );
    assert!(
        !result.gpu_used,
        "gpu_used should be false since GPU is unavailable"
    );
}

#[tokio::test]
async fn test_get_type() {
    let state = ServerState::new();
    let params = GetTypeParams {
        expr: "fun (x : Type) => x".to_string(),
    };

    let response = handle_get_type(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: GetTypeResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.type_.is_empty());
}

#[tokio::test]
async fn test_server_info_includes_verify_c() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        info.methods.contains(&"verifyC".to_string()),
        "serverInfo should include verifyC method"
    );
}

#[tokio::test]
async fn test_server_info_includes_batch_verify_cert() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        info.methods.contains(&"batchVerifyCert".to_string()),
        "serverInfo should include batchVerifyCert method"
    );
}

#[tokio::test]
async fn test_server_info_includes_verify_cert_archive() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        info.methods.contains(&"verifyCertArchive".to_string()),
        "serverInfo should include verifyCertArchive method"
    );
}

#[tokio::test]
async fn test_server_info_includes_batch_verify_cert_archive() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        info.methods.contains(&"batchVerifyCertArchive".to_string()),
        "serverInfo should include batchVerifyCertArchive method"
    );
}

// --- Single certificate verification tests (verifyCert) ---

#[tokio::test]
async fn test_server_info_includes_verify_cert() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        info.methods.contains(&"verifyCert".to_string()),
        "serverInfo should include verifyCert method"
    );
}

#[tokio::test]
async fn test_server_info_includes_cert_methods() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();

    // Verify all certificate methods are listed
    assert!(
        info.methods
            .contains(&"verify_alethe_certificate".to_string()),
        "serverInfo should include verify_alethe_certificate"
    );
    assert!(
        info.methods
            .contains(&"verify_farkas_certificate".to_string()),
        "serverInfo should include verify_farkas_certificate"
    );
    assert!(
        info.methods
            .contains(&"verify_entailment_certificate".to_string()),
        "serverInfo should include verify_entailment_certificate"
    );
    assert!(
        info.methods
            .contains(&"verify_certificates_batch".to_string()),
        "serverInfo should include verify_certificates_batch"
    );
    assert!(
        info.methods.contains(&"compressCert".to_string()),
        "serverInfo should include compressCert"
    );
    assert!(
        info.methods.contains(&"decompressCert".to_string()),
        "serverInfo should include decompressCert"
    );
    assert!(
        info.methods.contains(&"archiveCert".to_string()),
        "serverInfo should include archiveCert"
    );
    assert!(
        info.methods.contains(&"unarchiveCert".to_string()),
        "serverInfo should include unarchiveCert"
    );
}

/// serverInfo advertises canonical names only, not aliases (Part of #1380).
///
/// This is the tested policy: API discovery and API acceptance are different
/// contracts by design. serverInfo returns canonical names; dispatch accepts
/// both canonical and alias names.
#[tokio::test]
async fn test_server_info_excludes_aliases() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();

    for (alias, canonical) in crate::registry::all_aliases() {
        assert!(
            !info.methods.contains(&alias.to_string()),
            "serverInfo should NOT include alias '{}' (canonical: '{}'). \
             Policy: serverInfo advertises canonical names only.",
            alias,
            canonical
        );
    }
}

#[tokio::test]
async fn test_server_info_includes_dict_methods() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();

    // Verify dictionary methods are listed
    assert!(
        info.methods.contains(&"trainDict".to_string()),
        "serverInfo should include trainDict"
    );
    assert!(
        info.methods.contains(&"archiveCertWithDict".to_string()),
        "serverInfo should include archiveCertWithDict"
    );
    assert!(
        info.methods.contains(&"unarchiveCertWithDict".to_string()),
        "serverInfo should include unarchiveCertWithDict"
    );
}

#[tokio::test]
async fn test_server_info_includes_get_config() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(info.methods.contains(&"getConfig".to_string()));
}

#[tokio::test]
async fn test_server_info_includes_get_metrics() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(info.methods.contains(&"getMetrics".to_string()));
}

#[tokio::test]
async fn test_server_info_includes_get_cache_metrics() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(info.methods.contains(&"getCacheMetrics".to_string()));
}

#[tokio::test]
async fn test_server_info_includes_environment_methods() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        info.methods.contains(&"saveEnvironment".to_string()),
        "serverInfo should include saveEnvironment"
    );
    assert!(
        info.methods.contains(&"loadEnvironment".to_string()),
        "serverInfo should include loadEnvironment"
    );
    assert!(
        info.methods.contains(&"getEnvironment".to_string()),
        "serverInfo should include getEnvironment"
    );
}

// ========================================================================
// LLM Integration API Tests
// ========================================================================

#[tokio::test]
async fn test_server_info_includes_llm_api_methods() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        info.methods.contains(&"initProofState".to_string()),
        "serverInfo should include initProofState"
    );
    assert!(
        info.methods
            .contains(&"proofState.openObligation".to_string()),
        "serverInfo should include proofState.openObligation"
    );
    assert!(
        info.methods.contains(&"applyTactic".to_string()),
        "serverInfo should include applyTactic"
    );
    assert!(
        info.methods.contains(&"getProofState".to_string()),
        "serverInfo should include getProofState"
    );
    assert!(
        info.methods.contains(&"extractProof".to_string()),
        "serverInfo should include extractProof"
    );
    assert!(
        info.methods.contains(&"verifyProof".to_string()),
        "serverInfo should include verifyProof"
    );
    assert!(
        info.methods.contains(&"verifyProofBatch".to_string()),
        "serverInfo should include verifyProofBatch"
    );
    assert!(
        info.methods.contains(&"verifyFile".to_string()),
        "serverInfo should include verifyFile"
    );
    assert!(
        info.methods.contains(&"fillSorries".to_string()),
        "serverInfo should include fillSorries"
    );
    assert!(
        info.methods.contains(&"composeProof".to_string()),
        "serverInfo should include composeProof"
    );
}

#[tokio::test]
async fn test_server_info_includes_batch_apply_tactic() {
    let state = ServerState::new();
    let response = handle_server_info(&state, RequestId::Number(1)).await;

    let info: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        info.methods.contains(&"batchApplyTactic".to_string()),
        "serverInfo should include batchApplyTactic"
    );
}

// =========================================================================
// Error-path and edge-case tests for core handlers (#1654)
// =========================================================================

/// Test handle_get_type with an invalid expression returns an RPC error.
#[tokio::test]
async fn test_get_type_invalid_expr_returns_rpc_error() {
    let state = ServerState::new();
    let params = GetTypeParams {
        expr: "@@#$ invalid syntax".to_string(),
    };

    let response = handle_get_type(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_some(),
        "Invalid expression should produce RPC error, got result: {:?}",
        response.result
    );
    let err = response.error.unwrap();
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("parse"),
        "Error should mention parse failure, got: {}",
        err.message
    );
}

/// Test handle_get_type with an undefined identifier returns an error.
#[tokio::test]
async fn test_get_type_undefined_ident_returns_error() {
    let state = ServerState::new();
    let params = GetTypeParams {
        expr: "unknownIdent999".to_string(),
    };

    let response = handle_get_type(&state, RequestId::Number(1), params).await;
    // Should produce an RPC error because elaboration or type checking fails
    assert!(
        response.error.is_some(),
        "Undefined identifier should produce RPC error, got result: {:?}",
        response.result
    );
}

/// Test handle_check records metrics on success.
#[tokio::test]
async fn test_check_records_metrics_on_success() {
    let state = ServerState::new();
    let params = CheckParams {
        code: "Type".to_string(),
        timeout_ms: None,
    };

    let _response = handle_check(&state, RequestId::Number(1), params).await;

    assert!(
        state
            .metrics
            .total_requests
            .load(std::sync::atomic::Ordering::Relaxed)
            > 0,
        "Metrics should record the check request"
    );
}

/// Test handle_check records metrics on failure.
#[tokio::test]
async fn test_check_records_metrics_on_failure() {
    let state = ServerState::new();
    let params = CheckParams {
        code: "unknownIdent123".to_string(),
        timeout_ms: None,
    };

    let _response = handle_check(&state, RequestId::Number(1), params).await;

    assert!(
        state
            .metrics
            .total_requests
            .load(std::sync::atomic::Ordering::Relaxed)
            > 0,
        "Metrics should record the check request even on failure"
    );
}

/// Test handle_batch_check with mixed valid and invalid items.
#[tokio::test]
async fn test_batch_check_mixed_valid_invalid() {
    let state = ServerState::new();
    let params = BatchCheckParams {
        items: vec![
            BatchCheckItem {
                id: "valid".to_string(),
                code: "fun (A : Type) (x : A) => x".to_string(),
            },
            BatchCheckItem {
                id: "invalid".to_string(),
                code: "unknownIdent123".to_string(),
            },
            BatchCheckItem {
                id: "also_valid".to_string(),
                code: "Type".to_string(),
            },
        ],
        use_gpu: false,
        timeout_ms: None,
    };

    let response = handle_batch_check(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "Batch should succeed even with individual failures: {:?}",
        response.error
    );

    let result: BatchCheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.results.len(), 3, "Should have 3 results");
    assert_eq!(result.results[0].id, "valid");
    assert!(result.results[0].valid, "First item should be valid");
    assert_eq!(result.results[1].id, "invalid");
    assert!(!result.results[1].valid, "Second item should be invalid");
    assert_eq!(result.results[2].id, "also_valid");
    assert!(result.results[2].valid, "Third item should be valid");
}

/// Test handle_batch_check with empty items list.
#[tokio::test]
async fn test_batch_check_empty() {
    let state = ServerState::new();
    let params = BatchCheckParams {
        items: vec![],
        use_gpu: false,
        timeout_ms: None,
    };

    let response = handle_batch_check(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "Empty batch should succeed: {:?}",
        response.error
    );

    let result: BatchCheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.results.is_empty(), "No results for empty batch");
}

/// Test handle_batch_check with progress sender receives progress updates.
#[tokio::test]
async fn test_batch_check_progress_updates() {
    use crate::progress::ProgressSender;
    use std::time::Duration;
    use tokio::sync::mpsc;

    let state = ServerState::new();
    let params = BatchCheckParams {
        items: vec![
            BatchCheckItem {
                id: "a".to_string(),
                code: "Type".to_string(),
            },
            BatchCheckItem {
                id: "b".to_string(),
                code: "Type".to_string(),
            },
        ],
        use_gpu: false,
        timeout_ms: None,
    };

    let (tx, mut rx) = mpsc::channel(50);
    let progress = ProgressSender::new(RequestId::Number(99), tx);

    let response = handle_batch_check(&state, RequestId::Number(1), params, Some(progress)).await;
    assert!(
        response.error.is_none(),
        "Batch with progress should succeed: {:?}",
        response.error
    );

    // Collect progress updates
    let mut updates = Vec::new();
    while let Ok(update) = tokio::time::timeout(Duration::from_secs(2), rx.recv()).await {
        match update {
            Some(u) => updates.push(u),
            None => break,
        }
    }

    // Should have received at least a "started" message
    assert!(
        !updates.is_empty(),
        "Should receive at least one progress update"
    );
    assert!(
        updates.iter().any(|u| u.message.contains("started")),
        "Should have a 'started' progress message"
    );
}

/// Test handle_check with explicit timeout parameter.
#[tokio::test]
async fn test_check_with_explicit_timeout() {
    let state = ServerState::new();
    let params = CheckParams {
        code: "fun (x : Type) => x".to_string(),
        timeout_ms: Some(30000), // generous timeout
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Check with timeout should succeed: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.valid);
    assert!(
        result.time_ms < 30000,
        "Should complete well within timeout"
    );
}

/// Test handle_check result includes inferred_type for valid expressions.
#[tokio::test]
async fn test_check_valid_expr_has_inferred_type() {
    let state = ServerState::new();
    let params = CheckParams {
        code: "fun (A : Type) (x : A) => x".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.valid);
    assert!(
        result.inferred_type.is_some(),
        "Valid expression should have an inferred type"
    );
    let ty = result.inferred_type.unwrap();
    assert!(!ty.is_empty(), "Inferred type should be non-empty");
}

/// Test handle_check with an expression that fails elaboration.
/// An undefined identifier should produce valid:false with errors.
#[tokio::test]
async fn test_check_declaration_elaboration_error() {
    let state = ServerState::new();
    // Use an undefined identifier that fails elaboration
    let params = CheckParams {
        code: "UndefinedType".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Elaboration error should return result, not RPC error: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.valid, "Undefined identifier should fail check");
    assert!(
        !result.errors.is_empty(),
        "Should have errors for undefined identifier"
    );
}

/// Test handle_check with an expression that type-checks but has a type error.
/// E.g., applying Nat.zero to an argument (Nat.zero is not a function).
#[tokio::test]
async fn test_check_type_error_application() {
    let state = ServerState::new();
    // Nat.zero applied to something — Nat.zero is not a function
    let params = CheckParams {
        code: "Nat.zero Nat.zero".to_string(),
        timeout_ms: None,
    };

    let response = handle_check(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Type error should return result, not RPC error: {:?}",
        response.error
    );

    let result: CheckResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        !result.valid,
        "Applying non-function should produce type error"
    );
    assert!(
        !result.errors.is_empty(),
        "Should have errors for type mismatch"
    );
}

// =========================================================================
// Additional get_type tests (#1654)
// =========================================================================

/// Test handle_get_type with Type returns its universe type.
#[tokio::test]
async fn test_get_type_of_type() {
    let state = ServerState::new();
    let params = GetTypeParams {
        expr: "Type".to_string(),
    };

    let response = handle_get_type(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "getType of Type should succeed: {:?}",
        response.error
    );

    let result: GetTypeResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.type_.is_empty(), "Type of Type should be non-empty");
    // Type : Type 1 (or Sort (succ (succ zero)))
    assert!(
        result.type_.contains("Type") || result.type_.contains("Sort"),
        "Type of Type should mention Type or Sort, got: {}",
        result.type_
    );
}

/// Test handle_get_type with a lambda expression returns its Pi type.
/// Requires prelude for Nat.
#[tokio::test]
async fn test_get_type_lambda_returns_pi() {
    let state = prelude_state();
    let params = GetTypeParams {
        expr: "fun (x : Nat) => x".to_string(),
    };

    let response = handle_get_type(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "getType of lambda should succeed: {:?}",
        response.error
    );

    let result: GetTypeResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.type_.is_empty(), "Should have a type");
    // The type of (fun x : Nat => x) should be Nat → Nat or similar Pi type
    assert!(
        result.type_.contains("Nat"),
        "Type of identity on Nat should mention Nat, got: {}",
        result.type_
    );
}

/// Test handle_get_type with an empty string returns error.
#[tokio::test]
async fn test_get_type_empty_string_returns_error() {
    let state = ServerState::new();
    let params = GetTypeParams {
        expr: String::new(),
    };

    let response = handle_get_type(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_some(),
        "Empty expression should produce RPC error, got result: {:?}",
        response.result
    );
}
