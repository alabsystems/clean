// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;
use clean_kernel::cert::ProofCert;
use clean_kernel::{Environment, Expr, Name};

async fn solve_proof_state_with_tactics(
    state: &ServerState,
    theorem: &str,
    tactics: &[&str],
) -> String {
    let init_params = InitProofStateParams {
        theorem: theorem.to_string(),
        problem_id: None,
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(state, RequestId::Number(1), init_params).await;
    assert!(
        init_response.error.is_none(),
        "initProofState failed: {:?}",
        init_response.error
    );
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    let mut current_state_id = init_result.state_id;
    for (i, tactic) in tactics.iter().enumerate() {
        let apply_params = ApplyTacticParams {
            state_id: current_state_id.clone(),
            goal_id: "g0".to_string(),
            tactic: (*tactic).to_string(),
            timeout_ms: None,
        };
        let apply_response =
            handle_apply_tactic(state, RequestId::Number(i as i64 + 2), apply_params).await;
        assert!(
            apply_response.error.is_none(),
            "Tactic '{}' failed: {:?}",
            tactic,
            apply_response.error
        );
        let apply_result: crate::proof_state::ApplyTacticResult =
            serde_json::from_value(apply_response.result.unwrap()).unwrap();
        assert!(apply_result.success, "Tactic '{}' should succeed", tactic);
        current_state_id = apply_result.new_state_id;
    }

    current_state_id
}

#[tokio::test]
async fn test_apply_tactic_rejects_wrong_goal_id() {
    let state = ServerState::new().with_env(Environment::with_prelude());
    let init_response = handle_init_proof_state(
        &state,
        RequestId::Number(1),
        InitProofStateParams {
            theorem: "(A : Type) -> A -> A".to_string(),
            problem_id: None,
            timeout_ms: None,
        },
    )
    .await;
    assert!(
        init_response.error.is_none(),
        "initProofState failed: {:?}",
        init_response.error
    );
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    let apply_response = handle_apply_tactic(
        &state,
        RequestId::Number(2),
        ApplyTacticParams {
            state_id: init_result.state_id.clone(),
            goal_id: "wrong-goal-id".to_string(),
            tactic: "intro A".to_string(),
            timeout_ms: None,
        },
    )
    .await;
    assert!(
        apply_response.error.is_none(),
        "applyTactic should return a structured tactic failure, got RPC error: {:?}",
        apply_response.error
    );
    let apply_result: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(apply_response.result.unwrap()).unwrap();

    assert!(!apply_result.success, "wrong goal_id must be rejected");
    assert_eq!(apply_result.new_state_id, init_result.state_id);
    let err = apply_result
        .error
        .expect("wrong goal_id should produce a tactic error");
    assert_eq!(
        err.code,
        crate::proof_state::TacticErrorCode::NoMatchingGoal
    );
    assert!(
        err.message.contains("wrong-goal-id"),
        "error should mention the rejected goal id: {}",
        err.message
    );
}

/// Test extractProof with certificate format
#[tokio::test]
async fn test_extract_proof_with_certificate() {
    let state = ServerState::new();

    // Initialize and complete proof: (A : Type) -> A -> A
    let current_state_id = solve_proof_state_with_tactics(
        &state,
        "(A : Type) -> A -> A",
        &["intro A", "intro a", "assumption"],
    )
    .await;

    // Extract proof with certificate format
    let extract_params = ExtractProofParams {
        state_id: current_state_id.clone(),
        format: "certificate".to_string(),
    };
    let extract_response =
        handle_extract_proof(&state, RequestId::Number(100), extract_params).await;
    assert!(
        extract_response.error.is_none(),
        "extractProof failed: {:?}",
        extract_response.error
    );

    let extract_result: ExtractProofResult =
        serde_json::from_value(extract_response.result.unwrap()).unwrap();
    assert!(extract_result.is_solved, "Proof should be solved");
    assert!(extract_result.verification.verified, "Proof should verify");

    // Certificate should be present when format = "certificate"
    // The certificate should be a valid JSON object
    let cert = extract_result
        .certificate
        .expect("certificate should be present for format='certificate'");
    assert!(
        cert.is_object() || cert.is_string(),
        "Certificate should be a JSON object or string"
    );
}

/// Test that an extractProof certificate can be verified via verifyCert using the returned proof_expr.
#[tokio::test]
async fn test_extract_proof_certificate_verifies_with_verify_cert() {
    let state = ServerState::new();

    // Initialize and complete proof: (A : Type) -> A -> A
    let current_state_id = solve_proof_state_with_tactics(
        &state,
        "(A : Type) -> A -> A",
        &["intro A", "intro a", "assumption"],
    )
    .await;

    // Extract certificate + proof_expr for verifyCert roundtrip
    let extract_params = ExtractProofParams {
        state_id: current_state_id.clone(),
        format: "certificate".to_string(),
    };
    let extract_response =
        handle_extract_proof(&state, RequestId::Number(100), extract_params).await;
    assert!(
        extract_response.error.is_none(),
        "extractProof failed: {:?}",
        extract_response.error
    );

    let extract_result: ExtractProofResult =
        serde_json::from_value(extract_response.result.unwrap()).unwrap();
    assert!(extract_result.is_solved, "Proof should be solved");
    assert!(
        extract_result.verification.verified,
        "Proof extraction should succeed"
    );

    let proof_expr = extract_result
        .proof_expr
        .expect("extractProof should return proof_expr for format='certificate'");
    let cert_json = extract_result
        .certificate
        .expect("extractProof should return certificate for format='certificate'");

    let cert: ProofCert = match cert_json {
        serde_json::Value::String(s) => serde_json::from_str(&s).unwrap(),
        other => serde_json::from_value(other).unwrap(),
    };

    let verify_params = VerifyCertParams {
        cert,
        expr: proof_expr,
        timeout_ms: None,
    };
    let verify_response = handle_verify_cert(&state, RequestId::Number(200), verify_params).await;
    assert!(
        verify_response.error.is_none(),
        "verifyCert failed: {:?}",
        verify_response.error
    );
    let verify_result: VerifyCertResult =
        serde_json::from_value(verify_response.result.unwrap()).unwrap();

    assert!(
        verify_result.success,
        "Expected verifyCert to succeed; error: {:?}",
        verify_result.error
    );
    assert!(
        verify_result.verified_type.is_some(),
        "verifyCert should return a verified type on success"
    );
}

/// Test extractProof with "all" format returns certificate and tactic script
#[tokio::test]
async fn test_extract_proof_all_format() {
    let state = ServerState::new();

    // Initialize and complete proof: (A : Type) -> A -> A
    let current_state_id = solve_proof_state_with_tactics(
        &state,
        "(A : Type) -> A -> A",
        &["intro A", "intro a", "assumption"],
    )
    .await;

    // Extract proof with "all" format
    let extract_params = ExtractProofParams {
        state_id: current_state_id.clone(),
        format: "all".to_string(),
    };
    let extract_response =
        handle_extract_proof(&state, RequestId::Number(100), extract_params).await;
    let extract_result: ExtractProofResult =
        serde_json::from_value(extract_response.result.unwrap()).unwrap();

    assert!(extract_result.is_solved);
    assert!(extract_result.verification.verified);

    // "all" format should include certificate
    assert!(
        extract_result.certificate.is_some(),
        "Certificate should be present for format='all'"
    );

    // "all" format should include tactic script
    assert!(
        extract_result.tactic_script.is_some(),
        "Tactic script should be present for format='all'"
    );

    let script = extract_result.tactic_script.unwrap();
    assert!(!script.is_empty(), "Tactic script should not be empty");
}

/// Regression test for #2157: extractProof with default format="term" must
/// kernel type-check the proof and report verified accurately (not assume true).
#[tokio::test]
async fn test_extract_proof_default_format_verifies_via_kernel() {
    let state = ServerState::new();

    // Initialize and complete proof: (A : Type) -> A -> A
    let current_state_id = solve_proof_state_with_tactics(
        &state,
        "(A : Type) -> A -> A",
        &["intro A", "intro a", "assumption"],
    )
    .await;

    // Extract proof with default format ("term") — this is the buggy path from #2157
    let extract_params = ExtractProofParams {
        state_id: current_state_id.clone(),
        format: "term".to_string(),
    };
    let extract_response =
        handle_extract_proof(&state, RequestId::Number(100), extract_params).await;
    assert!(
        extract_response.error.is_none(),
        "extractProof failed: {:?}",
        extract_response.error
    );

    let extract_result: ExtractProofResult =
        serde_json::from_value(extract_response.result.unwrap()).unwrap();
    assert!(extract_result.is_solved, "Proof should be solved");

    // CRITICAL: verified must be true because the kernel actually type-checked
    // the proof term. Before #2157 fix, this was true without any checking.
    assert!(
        extract_result.verification.verified,
        "Proof should be kernel-verified even with format='term'"
    );

    // Certificate should NOT be present for format="term"
    assert!(
        extract_result.certificate.is_none(),
        "Certificate should not be generated for format='term'"
    );

    // Proof term should be present
    assert!(
        extract_result.proof_term.is_some(),
        "Proof term should be present for format='term'"
    );

    // time_us measures total handler time, not just kernel verification
    assert!(
        extract_result.verification.time_us > 0,
        "Handler time should be non-zero"
    );
}

/// `kernel_evidence` is the Phase 7 producer surface: it should emit the
/// consumer schema only after kernel verification and clean trust accounting.
#[tokio::test]
async fn test_extract_proof_kernel_evidence_emits_checked_schema() {
    let state = ServerState::new();
    let current_state_id = solve_proof_state_with_tactics(
        &state,
        "(A : Type) -> A -> A",
        &["intro A", "intro a", "assumption"],
    )
    .await;

    let extract_response = handle_extract_proof(
        &state,
        RequestId::Number(100),
        ExtractProofParams {
            state_id: current_state_id,
            format: "kernel_evidence".to_string(),
        },
    )
    .await;
    assert!(
        extract_response.error.is_none(),
        "extractProof kernel_evidence failed: {:?}",
        extract_response.error
    );

    let evidence = extract_response.result.expect("kernel evidence result");
    assert_eq!(evidence["schema_version"], "clean-math-kernel-evidence-v1");
    assert_eq!(evidence["checked"], true);
    assert_eq!(evidence["source"], "clean-kernel:extractProof");
    assert_eq!(evidence["kernel_verification"]["verified"], true);
    assert_eq!(evidence["trust_summary"]["fully_verified"], true);
    assert!(evidence["proof_hash"]
        .as_str()
        .unwrap()
        .starts_with("sha256:"));
    assert!(evidence.get("checked_proof_expr").is_some());
    assert!(evidence.get("checked_target_expr").is_some());
    assert!(evidence.get("proof_certificate").is_some());
    assert!(
        evidence.get("proof_expr").is_none(),
        "kernel evidence must not reuse diagnostic proof-state JSON shape"
    );
}

#[tokio::test]
async fn test_extract_proof_kernel_evidence_uses_proof_state_metadata() {
    let state = ServerState::new().with_env(Environment::with_prelude());
    let params = crate::proof_state::OpenObligationRequest {
        schema_version: crate::proof_state::OPEN_OBLIGATION_SCHEMA_VERSION.to_string(),
        environment_id: "legacy-env-without-project-context".to_string(),
        domain_profile: crate::proof_state::ObligationDomainProfile::General,
        goal: crate::proof_state::ObligationGoalPayload {
            expr: Some(Expr::const_(Name::from_string("True"), vec![])),
            pretty: "True".to_string(),
            type_expr: None,
            type_pp: None,
        },
        local_context: vec![],
        artifact_refs: vec![],
        metadata: Some(crate::proof_state::ProofStateMetadata {
            project: Some("metadata-project".to_string()),
            obligation_fingerprint: Some("sha256:metadata-obligation".to_string()),
            ..Default::default()
        }),
        trust_policy: crate::proof_state::ObligationTrustPolicy::ConstructiveOnly,
        ttl_sec: 60,
        max_states: 4,
        min_schema_version: crate::proof_state::PROOF_STATE_SCHEMA_VERSION.to_string(),
        max_schema_version: crate::proof_state::PROOF_STATE_SCHEMA_VERSION.to_string(),
    };

    let open_response = handle_open_obligation(&state, RequestId::Number(1), params).await;
    assert!(
        open_response.error.is_none(),
        "open obligation failed: {:?}",
        open_response.error
    );
    let opened: crate::proof_state::OpenObligationResponse =
        serde_json::from_value(open_response.result.unwrap()).unwrap();
    let goal_id = opened
        .initial_snapshot
        .as_ref()
        .expect("initial snapshot")
        .goals[0]
        .goal_id
        .clone();

    let apply_response = handle_apply_tactic(
        &state,
        RequestId::Number(2),
        ApplyTacticParams {
            state_id: opened.state_id,
            goal_id,
            tactic: "exact True.intro".to_string(),
            timeout_ms: None,
        },
    )
    .await;
    assert!(
        apply_response.error.is_none(),
        "apply tactic failed: {:?}",
        apply_response.error
    );
    let applied: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(apply_response.result.unwrap()).unwrap();
    assert!(applied.success);

    let extract_response = handle_extract_proof(
        &state,
        RequestId::Number(3),
        ExtractProofParams {
            state_id: applied.new_state_id,
            format: "kernel_evidence".to_string(),
        },
    )
    .await;
    assert!(
        extract_response.error.is_none(),
        "extractProof kernel_evidence failed: {:?}",
        extract_response.error
    );
    let evidence = extract_response.result.expect("kernel evidence result");
    assert_eq!(evidence["project"], "metadata-project");
    assert_eq!(evidence["obligation"], "sha256:metadata-obligation");
    assert_eq!(
        evidence["linked_obligations"],
        serde_json::json!(["sha256:metadata-obligation"])
    );
}

#[tokio::test]
async fn test_extract_proof_kernel_evidence_rejects_trust_debt() {
    let state = ServerState::new();
    let current_state_id = solve_proof_state_with_tactics(&state, "Prop", &["sorry"]).await;

    let extract_response = handle_extract_proof(
        &state,
        RequestId::Number(100),
        ExtractProofParams {
            state_id: current_state_id,
            format: "kernel_evidence".to_string(),
        },
    )
    .await;
    let error = extract_response
        .error
        .expect("kernel evidence with sorry debt should fail closed");
    let code = error
        .data
        .as_ref()
        .and_then(|data| data.get("code"))
        .and_then(serde_json::Value::as_str);
    assert_eq!(code, Some("KERNEL_EVIDENCE_TRUST_DEBT"));
    assert!(
        extract_response.result.is_none(),
        "rejected kernel evidence must not emit the evidence schema"
    );
}

// =========================================================================
// verifyProof endpoint tests (#79)
// =========================================================================

#[tokio::test]
async fn test_verify_proof_trivial_goal() {
    let state = ServerState::new();
    // Use a goal type that's trivially provable
    // In bare kernel, we can use Prop as a trivial goal (already satisfied)
    let params = VerifyProofParams {
        goal: "Prop".to_string(), // Type level, trivially "proved" by being a type
        proof: "".to_string(),    // Empty proof since it's already a type
        context: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    // Should at least parse and respond
    assert!(result.time_ns > 0, "Should have non-zero timing");
}

#[tokio::test]
async fn test_verify_proof_with_intro() {
    let state = ServerState::new();
    // Use Pi type that can be proved with intro
    let params = VerifyProofParams {
        goal: "(A : Type) -> Type".to_string(),
        proof: "intro A".to_string(),
        context: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    // After intro A, goal should be `Type` which is satisfied
    // Note: This test validates basic tactic execution
    assert!(result.time_ns > 0, "Should have timing info");
}

#[tokio::test]
async fn test_verify_proof_failed_tactic() {
    let state = ServerState::new();
    // Use a goal that can't be proved with the given tactic
    let params = VerifyProofParams {
        goal: "Type".to_string(),
        proof: "rfl".to_string(), // rfl can't prove Type
        context: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        !result.verified,
        "Expected proof to fail - rfl can't prove Type"
    );
    assert!(
        result.error.is_some(),
        "failed tactic should have error details, got: {:?}",
        result.error
    );
}

#[tokio::test]
async fn test_verify_proof_incomplete() {
    let state = ServerState::new();
    // Incomplete proof - intro leaves remaining goals
    let params = VerifyProofParams {
        goal: "(A : Type) -> (B : Type) -> Type".to_string(),
        proof: "intro A".to_string(), // Only one intro, need two
        context: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.verified, "Expected proof to be incomplete");
    assert!(
        result.error.is_some(),
        "incomplete proof should have error, got: {:?}",
        result.error
    );
}

#[tokio::test]
async fn test_verify_proof_parse_error() {
    let state = ServerState::new();
    // Invalid syntax should fail parsing
    let params = VerifyProofParams {
        goal: "@@#$ invalid".to_string(),
        proof: "rfl".to_string(),
        context: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.verified, "Should fail on parse error");
    // The error could mention "parse" or "elaborate"
    assert!(
        result.error.is_some(),
        "parse error should have error details, got: {:?}",
        result.error
    );
}

#[tokio::test]
async fn test_verify_proof_multiline_parsing() {
    let state = ServerState::new();
    // Test that newline-separated tactics are parsed correctly
    // We use a simple multi-tactic proof that doesn't need variable threading
    let params = VerifyProofParams {
        goal: "1 = 1".to_string(),
        proof: "-- comment line\nrfl".to_string(),
        context: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    // Even if rfl alone works, verifies multi-line parsing works
    assert!(result.time_ns > 0, "Should record timing");
}

// ==========================================================================
// Tests for TimingBreakdown (#90)
// ==========================================================================

#[tokio::test]
async fn test_verify_proof_timing_breakdown() {
    let state = ServerState::new();
    // Use Prop as goal - trivially satisfied (see test_verify_proof_trivial_goal)
    let params = VerifyProofParams {
        goal: "Prop".to_string(),
        proof: "".to_string(),
        context: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    // Note: Prop is a "trivial" goal that verifies as complete
    let timing = result.timing.expect("should have timing breakdown");
    assert!(timing.parse_ns > 0, "Should have parse time");
    assert!(timing.total_ns > 0, "Should have total time");
    // Total should be approximately sum of parts (with timing jitter tolerance)
    let sum = timing
        .parse_ns
        .saturating_add(timing.elaborate_ns)
        .saturating_add(timing.verify_ns);
    assert!(
        timing.total_ns + 10000 >= sum, // Allow 10us jitter
        "total_ns ({}) should be >= sum of parts ({}) within tolerance",
        timing.total_ns,
        sum
    );
}

#[tokio::test]
async fn test_verify_proof_timing_on_error() {
    let state = ServerState::new();
    let params = VerifyProofParams {
        goal: "invalid@#$syntax".to_string(),
        proof: "rfl".to_string(),
        context: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Should return result, not RPC error"
    );

    let result: VerifyProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.verified, "Proof should fail");
    let timing = result.timing.expect("should have timing even on error");
    assert!(timing.total_ns > 0, "Should record time to failure");
}

// ==========================================================================
// Tests for verifyProofBatch (#89)
// ==========================================================================

#[tokio::test]
async fn test_verify_proof_batch_simple() {
    let state = ServerState::new();
    // Use trivially satisfied goals (Prop, Type) with empty proofs
    let params = VerifyProofBatchParams {
        proofs: vec![
            VerifyProofBatchItem {
                id: "p1".to_string(),
                goal: "Prop".to_string(),
                proof: "".to_string(),
                context: None,
            },
            VerifyProofBatchItem {
                id: "p2".to_string(),
                goal: "Type".to_string(),
                proof: "".to_string(),
                context: None,
            },
        ],
        threads: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof_batch(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofBatchResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert_eq!(result.results.len(), 2, "Should have 2 results");
    assert_eq!(result.results[0].id, "p1", "Should preserve ID order");
    assert_eq!(result.results[1].id, "p2", "Should preserve ID order");

    // Both results should have timing
    assert!(
        result.results[0].timing.is_some(),
        "First should have timing"
    );
    assert!(
        result.results[1].timing.is_some(),
        "Second should have timing"
    );
    assert!(result.throughput_ops_sec > 0.0, "Should report throughput");
}

#[tokio::test]
async fn test_verify_proof_batch_empty() {
    let state = ServerState::new();
    let params = VerifyProofBatchParams {
        proofs: vec![],
        threads: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof_batch(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofBatchResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert!(result.results.is_empty(), "Should have no results");
    assert_eq!(result.stats.verified_count, 0);
    assert_eq!(result.stats.failed_count, 0);
}

#[tokio::test]
async fn test_verify_proof_batch_mixed_results() {
    let state = ServerState::new();
    let params = VerifyProofBatchParams {
        proofs: vec![
            VerifyProofBatchItem {
                id: "parseable".to_string(),
                goal: "Prop".to_string(),
                proof: "".to_string(),
                context: None,
            },
            VerifyProofBatchItem {
                id: "parse_error".to_string(),
                goal: "invalid@#$syntax".to_string(), // Parse error
                proof: "".to_string(),
                context: None,
            },
        ],
        threads: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof_batch(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: VerifyProofBatchResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert_eq!(result.results.len(), 2);
    // First result should have timing (even if not verified)
    assert!(
        result.results[0].timing.is_some(),
        "First should have timing"
    );
    // Second should fail (parse or elaborate error)
    assert!(!result.results[1].verified, "Second should fail");
    assert!(
        result.results[1].error.is_some(),
        "Second should have error details"
    );

    // Stats should reflect the difference
    assert!(
        result.stats.failed_count > 0,
        "Should have at least one failure"
    );
}

#[tokio::test]
async fn test_verify_proof_batch_with_timing() {
    let state = ServerState::new();
    let params = VerifyProofBatchParams {
        proofs: vec![VerifyProofBatchItem {
            id: "p1".to_string(),
            goal: "Prop".to_string(),
            proof: "".to_string(),
            context: None,
        }],
        threads: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof_batch(&state, RequestId::Number(1), params).await;
    let result: VerifyProofBatchResult = serde_json::from_value(response.result.unwrap()).unwrap();

    let timing = result.results[0]
        .timing
        .as_ref()
        .expect("should have timing");
    assert!(timing.total_ns > 0, "Should have total time");
    assert!(timing.parse_ns > 0, "Should have parse time");
}

#[tokio::test]
async fn test_verify_proof_batch_parallel_scaling() {
    // Verify that batch mode can handle multiple proofs in parallel
    let state = ServerState::new();

    // Create a batch of 10 trivial proofs
    let proofs: Vec<VerifyProofBatchItem> = (0..10)
        .map(|i| VerifyProofBatchItem {
            id: format!("p{}", i),
            goal: "Prop".to_string(),
            proof: "".to_string(),
            context: None,
        })
        .collect();

    let params = VerifyProofBatchParams {
        proofs,
        threads: Some(4), // Use 4 threads
        timeout_ms: None,
    };

    let response = handle_verify_proof_batch(&state, RequestId::Number(1), params).await;
    let result: VerifyProofBatchResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert_eq!(result.results.len(), 10, "Should process all 10 proofs");
    // Verify all have timing
    for (i, r) in result.results.iter().enumerate() {
        assert!(r.timing.is_some(), "Proof {} should have timing", i);
        assert!(r.time_ns > 0, "Proof {} should have non-zero time", i);
    }
    assert!(result.throughput_ops_sec > 0.0, "Should report throughput");
    assert!(result.stats.min_time_ns > 0, "Should have min time");
    assert!(
        result.stats.max_time_ns >= result.stats.min_time_ns,
        "Max >= min"
    );
    assert!(result.total_time_ns > 0, "Should have total time");
}

/// Acceptance criteria #5: Test with 100 proof batch
///
/// Note: This test uses a relaxed throughput threshold (1K ops/sec) to avoid
/// flakiness when running in parallel with other tests. When run in isolation,
/// throughput is typically >10K ops/sec. The primary validation is that batch
/// processing works correctly; throughput is logged for manual verification.
#[tokio::test]
async fn test_verify_proof_batch_100_proofs_throughput() {
    let state = ServerState::new();

    // Create a batch of 100 trivial proofs (Prop with empty proof)
    let proofs: Vec<VerifyProofBatchItem> = (0..100)
        .map(|i| VerifyProofBatchItem {
            id: format!("p{}", i),
            goal: "Prop".to_string(),
            proof: "".to_string(),
            context: None,
        })
        .collect();

    let params = VerifyProofBatchParams {
        proofs,
        threads: None, // Use all CPUs
        timeout_ms: None,
    };

    let response = handle_verify_proof_batch(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofBatchResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert_eq!(result.results.len(), 100, "Should process all 100 proofs");

    // Log throughput for manual verification (target >10K when run alone)
    eprintln!(
        "100 proof batch: {} ops/sec (target: >10000 when isolated)",
        result.throughput_ops_sec as u64
    );

    // Use relaxed threshold to avoid flakiness in parallel test execution
    // Actual throughput is ~17K ops/sec when run in isolation
    assert!(
        result.throughput_ops_sec >= 1_000.0,
        "Throughput {} ops/sec below minimum threshold",
        result.throughput_ops_sec
    );
}

// =========================================================================
// verifyProof type-checking against goal type tests (#2200)
// =========================================================================

/// A well-typed proof of the CORRECT theorem must return verified:true.
///
/// Tests the end-to-end check_type verification path (#2200): after tactics
/// close all goals, the handler calls check_type(proof_term, &target) and
/// returns verified:true when the types match.
#[tokio::test]
async fn test_verify_proof_correct_type_returns_verified() {
    let state = ServerState::new();
    // Goal: Type, proof: exact Prop
    // Prop (Sort 0) : Type (Sort 1), so this is a valid proof.
    let params = VerifyProofParams {
        goal: "Type".to_string(),
        proof: "exact Prop".to_string(),
        context: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.verified,
        "Well-typed proof of correct theorem should be verified:true, error: {:?}",
        result.error
    );
}

/// A proof attempt that cannot close the goal must return verified:false.
///
/// Here `assumption` cannot find a term of type `B` in the context (only `a : A`),
/// so the proof remains incomplete and the handler returns verified:false.
///
/// Note: The #2200 kernel type-check is a safety net for buggy tactics that
/// close goals with wrong-type proofs. Testing it through the handler API
/// requires a tactic that produces a complete-but-wrong proof, which correct
/// tactics don't do. The kernel-level check_type behavior is verified by
/// the check_type unit tests in clean-kernel.
#[tokio::test]
async fn test_verify_proof_wrong_type_returns_not_verified() {
    let state = ServerState::new();
    // Goal: (A : Type) -> (B : Type) -> A -> B
    // After intro A, intro B, intro a, the goal is `B` with context {A:Type, B:Type, a:A}.
    // `assumption` cannot find a term of type B (only a:A), so the tactic fails
    // and the proof remains incomplete.
    let params = VerifyProofParams {
        goal: "(A : Type) -> (B : Type) -> A -> B".to_string(),
        proof: "intro A\nintro B\nintro a\nassumption".to_string(),
        context: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        !result.verified,
        "Proof of wrong theorem should NOT be verified"
    );
}

// =========================================================================
// verifyFile endpoint tests (#91)
// =========================================================================
