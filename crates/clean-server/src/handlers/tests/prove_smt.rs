// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `handle_prove` (SMT bridge) handler.
//!
//! Covers happy path, parse errors, hypothesis handling, and not-found cases.

use crate::handlers::*;

fn prelude_state() -> ServerState {
    let env =
        clean_kernel::Environment::try_with_prelude().expect("try_with_prelude should succeed");
    ServerState::new().with_env(env)
}

fn assert_verified_prove_result(result: &ProveResult) {
    assert!(result.found, "verified prove results must set found=true");
    assert!(
        result.proof_term.is_some(),
        "verified prove results must include a proof_term"
    );
    assert_eq!(result.method.as_deref(), Some("smt"));
    assert!(
        result.reason.is_none(),
        "verified prove results must omit reason"
    );
    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("verified prove results must include trust_summary");
    assert!(
        trust_summary.sorry_provenance.is_some(),
        "verified prove results must expose closed-proof sorry provenance"
    );
}

fn assert_unverified_prove_result(result: &ProveResult) {
    assert!(result.found, "unverified prove results must set found=true");
    assert!(
        result.proof_term.is_none(),
        "unverified prove results must omit proof_term"
    );
    assert_eq!(result.method.as_deref(), Some("smt_unverified"));
    assert!(
        result
            .reason
            .as_deref()
            .is_some_and(|reason| !reason.is_empty()),
        "unverified prove results must preserve a non-empty reason"
    );
    assert!(
        result.trust_summary.is_none(),
        "unverified prove results must omit trust_summary"
    );
}

fn assert_refuted_prove_result(result: &ProveResult) {
    assert!(!result.found, "refuted prove results must set found=false");
    assert!(
        result.proof_term.is_none(),
        "refuted prove results must omit proof_term"
    );
    assert!(
        result.reason.is_none(),
        "refuted prove results must omit reason"
    );
    assert!(
        result.trust_summary.is_none(),
        "refuted prove results must omit trust_summary"
    );
}

fn assert_unknown_prove_result(result: &ProveResult) {
    assert!(!result.found, "unknown prove results must set found=false");
    assert!(
        result.proof_term.is_none(),
        "unknown prove results must omit proof_term"
    );
    assert!(
        result
            .reason
            .as_deref()
            .is_some_and(|reason| !reason.is_empty()),
        "unknown prove results must preserve a non-empty reason"
    );
    assert!(
        result.trust_summary.is_none(),
        "unknown prove results must omit trust_summary"
    );
}

fn assert_prove_status_invariants(result: &ProveResult) {
    match result.status {
        ProveStatus::Verified => assert_verified_prove_result(result),
        ProveStatus::Unverified => assert_unverified_prove_result(result),
        ProveStatus::KernelRejected => {
            assert!(
                result.found,
                "kernel-rejected results still found a candidate term"
            );
            assert!(
                result.proof_term.is_some(),
                "kernel-rejected results must surface the rejected proof_term"
            );
            assert!(
                result.reason.is_some(),
                "kernel-rejected results must explain the rejection"
            );
            assert!(
                result
                    .trust_summary
                    .as_ref()
                    .is_some_and(|ts| !ts.fully_verified),
                "kernel-rejected results carry a non-fully_verified trust_summary"
            );
        }
        ProveStatus::Refuted => assert_refuted_prove_result(result),
        ProveStatus::Unknown => assert_unknown_prove_result(result),
    }
}

/// Test handle_prove with a simple goal the SMT bridge can reason about.
/// Even if the bridge can't fully prove it, the handler should return a
/// well-formed response with timing and method info.
#[tokio::test]
async fn test_prove_simple_goal_response_structure() {
    let state = ServerState::new();

    let params = ProveParams {
        goal: "Prop".to_string(),
        hypotheses: vec![],
        timeout_ms: Some(5000),
        strategy: None,
    };

    let response = handle_prove(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "RPC-level error: {:?}",
        response.error
    );

    let result: ProveResult = serde_json::from_value(response.result.unwrap()).unwrap();
    // Whether or not a proof is found, the response should have timing
    assert!(result.time_ms < 5000, "Should not timeout on simple goal");
    assert_prove_status_invariants(&result);
}

/// Test handle_prove with a goal that has a parse error.
/// The handler should return an RPC error (not crash).
#[tokio::test]
async fn test_prove_parse_error_returns_rpc_error() {
    let state = ServerState::new();

    let params = ProveParams {
        goal: "@@#$ invalid syntax !!".to_string(),
        hypotheses: vec![],
        timeout_ms: Some(5000),
        strategy: None,
    };

    let response = handle_prove(&state, RequestId::Number(1), params).await;
    // Parse errors in prove_impl go through RpcError path
    assert!(
        response.error.is_some(),
        "Invalid goal should produce RPC error, got result: {:?}",
        response.result
    );
    let err = response.error.unwrap();
    // Error message should reference parsing
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("parse"),
        "Error should mention parse failure, got: {}",
        err.message
    );
}

/// Test handle_prove with a hypothesis that has a parse error.
#[tokio::test]
async fn test_prove_hypothesis_parse_error() {
    let state = ServerState::new();

    let params = ProveParams {
        goal: "Prop".to_string(),
        hypotheses: vec!["@@invalid_hyp".to_string()],
        timeout_ms: Some(5000),
        strategy: None,
    };

    let response = handle_prove(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_some(),
        "Invalid hypothesis should produce RPC error, got result: {:?}",
        response.result
    );
    let err = response.error.unwrap();
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("hypothesis") || msg.contains("parse"),
        "Error should mention hypothesis or parse failure, got: {}",
        err.message
    );
}

/// Test handle_prove with empty hypotheses and a goal the bridge likely can't prove.
/// Verifies the not-found path returns found=false.
#[tokio::test]
async fn test_prove_not_found() {
    let state = ServerState::new();

    // A Pi type that SMT won't prove without tactics
    let params = ProveParams {
        goal: "(A : Type) -> A".to_string(),
        hypotheses: vec![],
        timeout_ms: Some(5000),
        strategy: None,
    };

    let response = handle_prove(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "RPC-level error: {:?}",
        response.error
    );

    let result: ProveResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        !result.found,
        "SMT bridge should not be able to prove (A : Type) -> A"
    );
    assert!(result.method.is_none(), "No method when proof not found");
    assert!(
        result.proof_term.is_none(),
        "No proof_term when proof not found"
    );
    assert!(
        matches!(result.status, ProveStatus::Refuted | ProveStatus::Unknown),
        "not-found prove responses must report refuted/unknown status, got {:?}",
        result.status
    );
    assert_prove_status_invariants(&result);
}

/// Test handle_prove records metrics.
#[tokio::test]
async fn test_prove_records_metrics() {
    let state = ServerState::new();

    let params = ProveParams {
        goal: "Prop".to_string(),
        hypotheses: vec![],
        timeout_ms: Some(5000),
        strategy: None,
    };

    let _response = handle_prove(&state, RequestId::Number(1), params).await;

    // Check that the prove handler incremented the request counter
    assert!(
        state
            .metrics
            .total_requests
            .load(std::sync::atomic::Ordering::Relaxed)
            > 0,
        "Metrics should record the prove request"
    );
}

/// Test handle_prove JSON serialization roundtrip for ProveParams.
#[test]
fn test_prove_params_json_roundtrip() {
    let params = ProveParams {
        goal: "1 = 1".to_string(),
        hypotheses: vec!["True".to_string()],
        timeout_ms: Some(3000),
        strategy: None,
    };

    let json = serde_json::to_string(&params).unwrap();
    let deserialized: ProveParams = serde_json::from_str(&json).unwrap();

    assert_eq!(deserialized.goal, "1 = 1");
    assert_eq!(deserialized.hypotheses.len(), 1);
    assert_eq!(deserialized.timeout_ms, Some(3000));
}

// =========================================================================
// Error-path and edge-case tests for handle_prove (#1654)
// =========================================================================

/// Test handle_prove with empty goal string.
#[tokio::test]
async fn test_prove_empty_goal_returns_error() {
    let state = ServerState::new();

    let params = ProveParams {
        goal: String::new(),
        hypotheses: vec![],
        timeout_ms: Some(5000),
        strategy: None,
    };

    let response = handle_prove(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_some(),
        "Empty goal should produce RPC error, got result: {:?}",
        response.result
    );
}

/// Test handle_prove with multiple hypotheses where the second fails to parse.
/// Error message should reference the failing hypothesis index.
#[tokio::test]
async fn test_prove_multi_hypothesis_second_fails() {
    let state = ServerState::new();

    let params = ProveParams {
        goal: "Prop".to_string(),
        hypotheses: vec![
            "Prop".to_string(),         // valid
            "@@#$ invalid".to_string(), // invalid
        ],
        timeout_ms: Some(5000),
        strategy: None,
    };

    let response = handle_prove(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_some(),
        "Invalid hypothesis should produce RPC error, got result: {:?}",
        response.result
    );
    let err = response.error.unwrap();
    let msg = err.message.to_lowercase();
    // The error should reference "hypothesis" and ideally the index
    assert!(
        msg.contains("hypothesis") || msg.contains("parse"),
        "Error should mention hypothesis parse failure, got: {}",
        err.message
    );
}

/// Test handle_prove with multiple valid hypotheses returns well-formed response.
#[tokio::test]
async fn test_prove_multiple_valid_hypotheses() {
    let state = ServerState::new();

    let params = ProveParams {
        goal: "Prop".to_string(),
        hypotheses: vec!["Prop".to_string(), "Type".to_string()],
        timeout_ms: Some(5000),
        strategy: None,
    };

    let response = handle_prove(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Multiple valid hypotheses should not produce RPC error: {:?}",
        response.error
    );

    let result: ProveResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.time_ms < 5000, "Should not timeout");
    assert_prove_status_invariants(&result);
}

#[tokio::test]
async fn test_prove_true_goal_reports_verified_or_unverified_status() {
    let state = prelude_state();
    let params = ProveParams {
        goal: "True".to_string(),
        hypotheses: vec![],
        timeout_ms: Some(5000),
        strategy: None,
    };

    let response = handle_prove(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "RPC-level error: {:?}",
        response.error
    );

    let result: ProveResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        matches!(
            result.status,
            ProveStatus::Verified | ProveStatus::Unverified
        ),
        "True should map to a successful prove status, got {:?}",
        result.status
    );
    assert_prove_status_invariants(&result);
}

#[tokio::test]
async fn test_prove_false_goal_reports_refuted_status() {
    let state = prelude_state();
    let params = ProveParams {
        goal: "False".to_string(),
        hypotheses: vec![],
        timeout_ms: Some(5000),
        strategy: None,
    };

    let response = handle_prove(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "RPC-level error: {:?}",
        response.error
    );

    let result: ProveResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.status, ProveStatus::Refuted);
    assert_prove_status_invariants(&result);
}

/// Test handle_prove with undefined identifier as goal (elaboration failure path).
#[tokio::test]
async fn test_prove_elaboration_failure() {
    let state = ServerState::new();

    // This should parse but fail during elaboration (unknown constant)
    let params = ProveParams {
        goal: "undefinedConst123".to_string(),
        hypotheses: vec![],
        timeout_ms: Some(5000),
        strategy: None,
    };

    let response = handle_prove(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_some(),
        "Undefined constant should produce RPC error, got result: {:?}",
        response.result
    );
    let err = response.error.unwrap();
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("elaborate") || msg.contains("parse") || msg.contains("unknown"),
        "Error should mention elaboration or parse failure, got: {}",
        err.message
    );
}

/// Test ProveParams JSON deserialization with missing hypotheses field
/// (serde default should provide empty vec).
#[test]
fn test_prove_params_missing_hypotheses_defaults_to_empty() {
    let json = r#"{"goal": "Prop", "timeout_ms": 1000}"#;
    let params: ProveParams = serde_json::from_str(json).unwrap();

    assert_eq!(params.goal, "Prop");
    assert!(
        params.hypotheses.is_empty(),
        "Missing hypotheses should default to empty vec"
    );
    assert_eq!(params.timeout_ms, Some(1000));
}

/// Test ProveParams JSON deserialization with missing timeout_ms
/// (Option should be None).
#[test]
fn test_prove_params_missing_timeout_defaults_to_none() {
    let json = r#"{"goal": "Prop"}"#;
    let params: ProveParams = serde_json::from_str(json).unwrap();

    assert_eq!(params.goal, "Prop");
    assert!(params.hypotheses.is_empty());
    assert!(
        params.timeout_ms.is_none(),
        "Missing timeout_ms should default to None"
    );
}

// =========================================================================
// Error-path gap coverage (#1654 — acceptance criterion 2)
// =========================================================================

/// Test handle_prove with a hypothesis that parses but fails elaboration.
/// This covers the error path at prove_impl line 510-512:
///   "Failed to elaborate hypothesis {i}"
#[tokio::test]
async fn test_prove_hypothesis_elaboration_failure() {
    let state = ServerState::new();

    // "undefinedConst123" parses as an identifier but fails elaboration
    // because it's not in the environment.
    let params = ProveParams {
        goal: "Prop".to_string(),
        hypotheses: vec!["undefinedConst123".to_string()],
        timeout_ms: Some(5000),
        strategy: None,
    };

    let response = handle_prove(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_some(),
        "Hypothesis elaboration failure should produce RPC error, got result: {:?}",
        response.result
    );
    let err = response.error.unwrap();
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("hypothesis") || msg.contains("elaborate"),
        "Error should mention hypothesis or elaboration, got: {}",
        err.message
    );
}

/// Test handle_prove timeout path.
/// Uses a 1ms timeout to trigger the tokio::time::timeout arm.
#[tokio::test]
async fn test_prove_timeout_returns_rpc_error() {
    let state = ServerState::new();

    // Use a trivially provable goal but with a near-zero timeout.
    // The handler wraps prove_impl in tokio::time::timeout (line 467)
    // and returns RpcError::timeout on expiry.
    let params = ProveParams {
        goal: "(A B C D E F G : Type) -> (A -> B) -> (B -> C) -> (C -> D) -> (D -> E) -> (E -> F) -> (F -> G) -> A -> G".to_string(),
        hypotheses: vec![],
        timeout_ms: Some(1), // 1ms — virtually guaranteed to expire
        strategy: None,
    };

    let response = handle_prove(&state, RequestId::Number(1), params).await;
    // Either the handler finishes in time (unlikely but possible) or
    // it returns a timeout error. Both are valid outcomes.
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
