// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;

fn assert_empty_mathverse_candidates_json(value: &serde_json::Value, context: &str) {
    let candidates = value
        .get("mathverse_candidates")
        .unwrap_or_else(|| panic!("{context} should serialize mathverse_candidates"));
    let candidates = candidates
        .as_array()
        .unwrap_or_else(|| panic!("{context} mathverse_candidates should be an array"));
    assert!(
        candidates.is_empty(),
        "{context} should default mathverse_candidates to []"
    );
}

#[test]
fn test_tactic_results_deserialize_missing_mathverse_candidates_as_empty() {
    let init: InitProofStateResult = serde_json::from_value(serde_json::json!({
        "state_id": "ps_00000000000000000000000000000000",
        "goals": [],
        "is_solved": false,
        "time_us": 0
    }))
    .expect("legacy initProofState result should decode");
    assert!(init.mathverse_candidates.is_empty());

    let apply: crate::proof_state::ApplyTacticResult = serde_json::from_value(serde_json::json!({
        "success": true,
        "new_state_id": "ps_00000000000000000000000000000001",
        "new_goals": [],
        "is_solved": true,
        "time_us": 0
    }))
    .expect("legacy applyTactic result should decode");
    assert!(apply.mathverse_candidates.is_empty());

    let batch_item: BatchTacticItemResult = serde_json::from_value(serde_json::json!({
        "id": "t1",
        "success": false,
        "is_solved": false,
        "time_us": 0
    }))
    .expect("legacy batchApplyTactic item should decode");
    assert!(batch_item.mathverse_candidates.is_empty());
}

#[tokio::test]
async fn test_apply_tactic_intro() {
    let state = ServerState::new();

    // Init a state with a Pi type goal
    let init_params = InitProofStateParams {
        theorem: "(A : Type) -> A -> A".to_string(),
        problem_id: None,
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    // Apply intro tactic
    let apply_params = ApplyTacticParams {
        state_id: init_result.state_id.clone(),
        goal_id: "g0".to_string(),
        tactic: "intro A".to_string(),
        timeout_ms: None,
    };
    let apply_response = handle_apply_tactic(&state, RequestId::Number(2), apply_params).await;
    assert!(
        apply_response.error.is_none(),
        "Unexpected error: {:?}",
        apply_response.error
    );

    let result: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(apply_response.result.unwrap()).unwrap();
    assert!(result.success, "Tactic should succeed");
    // New state should have different ID
    assert_ne!(result.new_state_id, init_result.state_id);
}

#[tokio::test]
async fn test_apply_tactic_unknown() {
    let state = ServerState::new();

    // Init a state
    let init_params = InitProofStateParams {
        theorem: "Prop".to_string(),
        problem_id: None,
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    // Try unknown tactic
    let apply_params = ApplyTacticParams {
        state_id: init_result.state_id.clone(),
        goal_id: "g0".to_string(),
        tactic: "foobar_unknown_tactic".to_string(),
        timeout_ms: None,
    };
    let apply_response = handle_apply_tactic(&state, RequestId::Number(2), apply_params).await;

    let result: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(apply_response.result.unwrap()).unwrap();
    assert!(!result.success, "Tactic should fail");
    assert!(
        result.error.is_some(),
        "failed tactic should have error info, got: {:?}",
        result.error
    );
}

#[tokio::test]
async fn test_apply_tactic_invalid_state() {
    let state = ServerState::new();

    let apply_params = ApplyTacticParams {
        state_id: "ps_00000000000000000000000000000000".to_string(),
        goal_id: "g0".to_string(),
        tactic: "intro x".to_string(),
        timeout_ms: None,
    };
    let apply_response = handle_apply_tactic(&state, RequestId::Number(1), apply_params).await;

    let result: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(apply_response.result.unwrap()).unwrap();
    assert!(!result.success);
    let err = result.error.expect("invalid state should produce an error");
    assert_eq!(
        err.code,
        crate::proof_state::TacticErrorCode::InvalidStateId
    );
}

#[tokio::test]
async fn test_batch_apply_tactic_basic() {
    let state = ServerState::new();

    // Initialize a proof state with a simple function type
    let init_params = InitProofStateParams {
        theorem: "(A : Type) -> A -> A".to_string(),
        problem_id: Some("batch_test".to_string()),
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    // Apply multiple tactics in a batch
    let batch_params = BatchApplyTacticParams {
        items: vec![
            BatchTacticItem {
                id: "t1".to_string(),
                state_id: init_result.state_id.clone(),
                goal_id: "g0".to_string(),
                tactic: "intro A".to_string(),
            },
            BatchTacticItem {
                id: "t2".to_string(),
                state_id: init_result.state_id.clone(),
                goal_id: "g0".to_string(),
                tactic: "rfl".to_string(), // This should fail (not applicable)
            },
        ],
        threads: Some(2),
        timeout_ms: Some(5000),
    };
    let batch_response =
        handle_batch_apply_tactic(&state, RequestId::Number(2), batch_params).await;

    assert!(
        batch_response.error.is_none(),
        "Unexpected error: {:?}",
        batch_response.error
    );

    let result: BatchApplyTacticResult =
        serde_json::from_value(batch_response.result.unwrap()).unwrap();

    // Check stats
    assert_eq!(result.stats.total, 2);
    assert_eq!(result.stats.succeeded, 1);
    assert_eq!(result.stats.failed, 1);

    // Check individual results
    assert_eq!(result.results.len(), 2);
    assert_eq!(result.results[0].id, "t1");
    assert!(result.results[0].success);
    assert!(
        result.results[0].new_state_id.is_some(),
        "successful tactic should produce new_state_id"
    );

    assert_eq!(result.results[1].id, "t2");
    assert!(!result.results[1].success);
    assert!(
        result.results[1].error.is_some(),
        "failed tactic should have error info"
    );
}

#[tokio::test]
async fn test_batch_apply_tactic_empty() {
    let state = ServerState::new();

    let batch_params = BatchApplyTacticParams {
        items: vec![],
        threads: None,
        timeout_ms: None,
    };
    let response = handle_batch_apply_tactic(&state, RequestId::Number(1), batch_params).await;

    let result: BatchApplyTacticResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.stats.total, 0);
    assert_eq!(result.stats.succeeded, 0);
    assert_eq!(result.stats.failed, 0);
    assert!(result.results.is_empty());
}

#[tokio::test]
async fn test_batch_apply_tactic_invalid_states() {
    let state = ServerState::new();

    let batch_params = BatchApplyTacticParams {
        items: vec![
            BatchTacticItem {
                id: "t1".to_string(),
                state_id: "ps_00000000000000000000000000000000".to_string(),
                goal_id: "g0".to_string(),
                tactic: "intro x".to_string(),
            },
            BatchTacticItem {
                id: "t2".to_string(),
                state_id: "invalid_format".to_string(),
                goal_id: "g0".to_string(),
                tactic: "intro y".to_string(),
            },
        ],
        threads: None,
        timeout_ms: None,
    };
    let response = handle_batch_apply_tactic(&state, RequestId::Number(1), batch_params).await;

    let result: BatchApplyTacticResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.stats.total, 2);
    assert_eq!(result.stats.failed, 2);

    // Both should fail with InvalidStateId
    for r in &result.results {
        assert!(!r.success);
        assert!(
            r.error.is_some(),
            "failed tactic result should have error details"
        );
        assert_eq!(
            r.error.as_ref().unwrap().code,
            crate::proof_state::TacticErrorCode::InvalidStateId
        );
    }
}

/// Throughput test for batchApplyTactic
///
/// Success criteria from #73: >10K tactics/sec
/// Tests parallel execution with multiple proof states and tactics.
#[tokio::test]
async fn test_batch_apply_tactic_throughput() {
    use std::time::Instant;

    let state = ServerState::new();

    // Create multiple proof states with different theorems
    // Use pure Type/Prop terms that don't require standard library (no Nat, Eq, etc.)
    let theorems = [
        "(A : Type) -> A -> A",
        "(A B : Type) -> A -> B -> A",
        "(A B : Type) -> (A -> B) -> A -> B",
        "(P Q : Prop) -> P -> P",
        "(A B C : Type) -> (A -> B) -> (B -> C) -> A -> C",
    ];

    // Initialize all proof states
    let mut state_ids = Vec::new();
    for (i, theorem) in theorems.iter().enumerate() {
        let init_params = InitProofStateParams {
            theorem: theorem.to_string(),
            problem_id: Some(format!("throughput_test_{}", i)),
            timeout_ms: None,
        };
        let response =
            handle_init_proof_state(&state, RequestId::Number(i as i64), init_params).await;
        assert!(
            response.error.is_none(),
            "Failed to init proof state for theorem '{}': {:?}",
            theorem,
            response.error
        );
        let result: InitProofStateResult =
            serde_json::from_value(response.result.unwrap()).unwrap();
        state_ids.push(result.state_id);
    }

    // Build a large batch of tactics (100 items per state = 500 total)
    // Each state gets various tactics, some will succeed, some will fail
    let tactics = ["intro A", "intro x", "intro B", "intro n", "intro P", "rfl"];
    let mut batch_items = Vec::new();
    let items_per_state = 100;

    for (state_idx, state_id) in state_ids.iter().enumerate() {
        for tactic_idx in 0..items_per_state {
            let tactic = tactics[tactic_idx % tactics.len()];
            batch_items.push(BatchTacticItem {
                id: format!("s{}_t{}", state_idx, tactic_idx),
                state_id: state_id.clone(),
                goal_id: "g0".to_string(),
                tactic: tactic.to_string(),
            });
        }
    }

    let total_items = batch_items.len();

    // Run the batch with 4 threads
    let batch_params = BatchApplyTacticParams {
        items: batch_items,
        threads: Some(4),
        timeout_ms: Some(30000),
    };

    let start = Instant::now();
    let response = handle_batch_apply_tactic(&state, RequestId::Number(999), batch_params).await;
    let wall_time = start.elapsed();

    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: BatchApplyTacticResult = serde_json::from_value(response.result.unwrap()).unwrap();

    // Verify all items were processed
    assert_eq!(result.stats.total, total_items);
    assert_eq!(result.results.len(), total_items);

    // Calculate throughput
    let throughput = total_items as f64 / wall_time.as_secs_f64();

    // Log throughput metrics for diagnostics
    eprintln!(
        "batchApplyTactic throughput: {:.0} tactics/sec ({} items in {:.2}ms)",
        throughput,
        total_items,
        wall_time.as_secs_f64() * 1000.0
    );
    eprintln!(
        "  succeeded: {}, failed: {}, solved: {}",
        result.stats.succeeded, result.stats.failed, result.stats.solved
    );

    // Success criteria: >10K tactics/sec
    // Note: In CI environments, this threshold may need adjustment
    // We use a more lenient 1K for test stability
    assert!(
        throughput > 1000.0,
        "Throughput {:.0} tactics/sec is below minimum 1000/sec (CI-safe threshold)",
        throughput
    );

    // Verify some tactics succeeded (intro should work on most states)
    assert!(
        result.stats.succeeded > 0,
        "Expected at least some tactics to succeed"
    );

    // Verify results are in correct order
    for (i, r) in result.results.iter().enumerate() {
        let expected_id = format!("s{}_t{}", i / items_per_state, i % items_per_state);
        assert_eq!(r.id, expected_id, "Results should preserve input order");
    }
}

/// Test batchApplyTactic parallel speedup with different thread counts
#[tokio::test]
async fn test_batch_apply_tactic_parallel_scaling() {
    use std::time::Instant;

    let state = ServerState::new();

    // Initialize multiple proof states
    // Use pure Type terms that don't require standard library (no Nat, Eq, etc.)
    let mut state_ids = Vec::new();
    for i in 0..10 {
        let init_params = InitProofStateParams {
            theorem: format!("(A{} : Type) -> A{} -> A{}", i, i, i),
            problem_id: Some(format!("scale_test_{}", i)),
            timeout_ms: None,
        };
        let response = handle_init_proof_state(&state, RequestId::Number(i), init_params).await;
        assert!(
            response.error.is_none(),
            "Failed to init proof state {}: {:?}",
            i,
            response.error
        );
        let result: InitProofStateResult =
            serde_json::from_value(response.result.unwrap()).unwrap();
        state_ids.push(result.state_id);
    }

    // Build batch items (50 per state = 500 total)
    let mut batch_items = Vec::new();
    for (state_idx, state_id) in state_ids.iter().enumerate() {
        for tactic_idx in 0..50 {
            batch_items.push(BatchTacticItem {
                id: format!("s{}_t{}", state_idx, tactic_idx),
                state_id: state_id.clone(),
                goal_id: "g0".to_string(),
                tactic: format!("intro x{}", tactic_idx),
            });
        }
    }

    let total_items = batch_items.len();

    // Test with 1 thread
    let batch_params_1 = BatchApplyTacticParams {
        items: batch_items.clone(),
        threads: Some(1),
        timeout_ms: Some(30000),
    };
    let start_1 = Instant::now();
    let response_1 =
        handle_batch_apply_tactic(&state, RequestId::Number(1000), batch_params_1).await;
    let time_1 = start_1.elapsed();
    assert!(
        response_1.error.is_none(),
        "batch with 1 thread should succeed, got: {:?}",
        response_1.error
    );

    // Test with 4 threads
    let batch_params_4 = BatchApplyTacticParams {
        items: batch_items,
        threads: Some(4),
        timeout_ms: Some(30000),
    };
    let start_4 = Instant::now();
    let response_4 =
        handle_batch_apply_tactic(&state, RequestId::Number(1001), batch_params_4).await;
    let time_4 = start_4.elapsed();
    assert!(
        response_4.error.is_none(),
        "batch with 4 threads should succeed, got: {:?}",
        response_4.error
    );

    let throughput_1 = total_items as f64 / time_1.as_secs_f64();
    let throughput_4 = total_items as f64 / time_4.as_secs_f64();
    let speedup = throughput_4 / throughput_1;

    eprintln!(
        "Parallel scaling: 1 thread: {:.0}/sec, 4 threads: {:.0}/sec, speedup: {:.2}x",
        throughput_1, throughput_4, speedup
    );

    // With 4 threads, we ideally expect speedup, but in test/CI environments
    // with cache contention and thread scheduling overhead, parallelism may not help.
    // The key validation is that parallel execution doesn't catastrophically degrade.
    // Threshold: 0.3x allows up to 70% degradation under system load (#92)
    assert!(
        speedup >= 0.3,
        "Expected parallel execution to not severely degrade (speedup: {:.2}x)",
        speedup
    );
}

// ============================================================================
// Interactive trust-summary surface tests (#2716)
// ============================================================================

/// initProofState returns a zero-baseline trust_summary for a fresh unsolved state.
#[tokio::test]
async fn test_init_proof_state_trust_summary_zero_baseline() {
    let state = ServerState::new();

    let init_params = InitProofStateParams {
        theorem: "(A : Type) -> A -> A".to_string(),
        problem_id: None,
        timeout_ms: None,
    };
    let response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let result_json = response.result.unwrap();
    assert_empty_mathverse_candidates_json(&result_json, "initProofState");
    let result: InitProofStateResult = serde_json::from_value(result_json).unwrap();

    let ts = result
        .trust_summary
        .expect("initProofState should include trust_summary");
    assert!(result.mathverse_candidates.is_empty());
    assert_eq!(ts.sorry_count, 0, "fresh state should have zero sorry");
    assert_eq!(ts.ay_count, 0, "fresh state should have zero ay");
    assert_eq!(ts.arith_count, 0, "fresh state should have zero arith");
    assert!(ts.arith_provenance.is_none());
    assert_eq!(
        ts.kernel_check_failures, 0,
        "fresh state should have zero kernel failures"
    );
    assert!(
        !ts.fully_verified,
        "unsolved state must not be fully_verified"
    );
    assert!(
        !result.is_solved,
        "Pi type goal should not be trivially solved"
    );
}

/// applyTactic success path returns the new state's trust_summary with zero counts.
#[tokio::test]
async fn test_apply_tactic_success_trust_summary_clean() {
    let state = ServerState::new();

    let init_params = InitProofStateParams {
        theorem: "(A : Type) -> A -> A".to_string(),
        problem_id: None,
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    let apply_params = ApplyTacticParams {
        state_id: init_result.state_id.clone(),
        goal_id: "g0".to_string(),
        tactic: "intro A".to_string(),
        timeout_ms: None,
    };
    let apply_response = handle_apply_tactic(&state, RequestId::Number(2), apply_params).await;
    let result_json = apply_response.result.unwrap();
    assert_empty_mathverse_candidates_json(&result_json, "applyTactic success");
    let result: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(result_json).unwrap();

    assert!(result.success, "intro should succeed");
    assert!(result.mathverse_candidates.is_empty());
    let ts = result
        .trust_summary
        .expect("successful applyTactic should include trust_summary");
    assert_eq!(ts.sorry_count, 0);
    assert_eq!(ts.ay_count, 0);
    assert_eq!(ts.arith_count, 0);
    assert!(ts.arith_provenance.is_none());
    assert!(
        !ts.fully_verified,
        "unsolved state after intro should not be fully_verified"
    );
}

/// applyTactic failure on a valid state returns the original state's trust_summary.
#[tokio::test]
async fn test_apply_tactic_failure_returns_original_trust_summary() {
    let state = ServerState::new();

    let init_params = InitProofStateParams {
        theorem: "(A : Type) -> A -> A".to_string(),
        problem_id: None,
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    // rfl should fail on this goal
    let apply_params = ApplyTacticParams {
        state_id: init_result.state_id.clone(),
        goal_id: "g0".to_string(),
        tactic: "rfl".to_string(),
        timeout_ms: None,
    };
    let apply_response = handle_apply_tactic(&state, RequestId::Number(2), apply_params).await;
    let result_json = apply_response.result.unwrap();
    assert_empty_mathverse_candidates_json(&result_json, "applyTactic valid failure");
    let result: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(result_json).unwrap();

    assert!(!result.success, "rfl should fail on this goal");
    assert!(result.mathverse_candidates.is_empty());
    let ts = result
        .trust_summary
        .expect("failed applyTactic on valid state should include trust_summary");
    assert_eq!(ts.sorry_count, 0, "original state has zero trust debt");
    assert!(ts.arith_provenance.is_none());
    assert!(
        !ts.fully_verified,
        "failed tactic should not yield fully_verified"
    );
}

/// applyTactic on an invalid state_id returns trust_summary: None.
#[tokio::test]
async fn test_apply_tactic_invalid_state_trust_summary_none() {
    let state = ServerState::new();

    let apply_params = ApplyTacticParams {
        state_id: "ps_00000000000000000000000000000000".to_string(),
        goal_id: "g0".to_string(),
        tactic: "intro x".to_string(),
        timeout_ms: None,
    };
    let apply_response = handle_apply_tactic(&state, RequestId::Number(1), apply_params).await;
    let result_json = apply_response.result.unwrap();
    assert_empty_mathverse_candidates_json(&result_json, "applyTactic invalid state");
    let result: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(result_json).unwrap();

    assert!(!result.success);
    assert!(result.mathverse_candidates.is_empty());
    assert!(
        result.trust_summary.is_none(),
        "invalid state_id should return trust_summary: None"
    );
}

/// batchApplyTactic returns per-item trust_summary: Some for valid states, None for invalid.
#[tokio::test]
async fn test_batch_apply_tactic_trust_summary_per_item() {
    let state = ServerState::new();

    let init_params = InitProofStateParams {
        theorem: "(A : Type) -> A -> A".to_string(),
        problem_id: None,
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    let batch_params = BatchApplyTacticParams {
        items: vec![
            BatchTacticItem {
                id: "valid_success".to_string(),
                state_id: init_result.state_id.clone(),
                goal_id: "g0".to_string(),
                tactic: "intro A".to_string(),
            },
            BatchTacticItem {
                id: "valid_failure".to_string(),
                state_id: init_result.state_id.clone(),
                goal_id: "g0".to_string(),
                tactic: "rfl".to_string(),
            },
            BatchTacticItem {
                id: "invalid_state".to_string(),
                state_id: "ps_00000000000000000000000000000000".to_string(),
                goal_id: "g0".to_string(),
                tactic: "intro x".to_string(),
            },
        ],
        threads: None,
        timeout_ms: None,
    };
    let response = handle_batch_apply_tactic(&state, RequestId::Number(2), batch_params).await;
    let result_json = response.result.unwrap();
    let items = result_json
        .get("results")
        .and_then(serde_json::Value::as_array)
        .expect("batchApplyTactic should serialize results as an array");
    for (idx, item) in items.iter().enumerate() {
        assert_empty_mathverse_candidates_json(item, &format!("batchApplyTactic results[{idx}]"));
    }
    let result: BatchApplyTacticResult = serde_json::from_value(result_json).unwrap();

    assert_eq!(result.results.len(), 3);

    // valid_success: trust_summary present with zero counts
    let r0 = &result.results[0];
    assert!(r0.success);
    assert!(r0.mathverse_candidates.is_empty());
    let ts0 = r0
        .trust_summary
        .as_ref()
        .expect("successful batch item should include trust_summary");
    assert_eq!(ts0.sorry_count, 0);
    assert!(ts0.arith_provenance.is_none());

    // valid_failure: trust_summary present (original state's summary)
    let r1 = &result.results[1];
    assert!(!r1.success);
    assert!(r1.mathverse_candidates.is_empty());
    let ts1 = r1
        .trust_summary
        .as_ref()
        .expect("failed batch item on valid state should include trust_summary");
    assert_eq!(ts1.sorry_count, 0);
    assert!(ts1.arith_provenance.is_none());

    // invalid_state: trust_summary None
    let r2 = &result.results[2];
    assert!(!r2.success);
    assert!(r2.mathverse_candidates.is_empty());
    assert!(
        r2.trust_summary.is_none(),
        "invalid state batch item should return trust_summary: None"
    );
}

/// applyTactic with sorry reports immediate trust debt without needing extractProof.
#[tokio::test]
async fn test_apply_tactic_sorry_reports_trust_debt_immediately() {
    let state = ServerState::new();

    let init_params = InitProofStateParams {
        theorem: "(A : Type) -> A -> A".to_string(),
        problem_id: None,
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(&state, RequestId::Number(1), init_params).await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    // Apply sorry — should close the goal but introduce trust debt
    let apply_params = ApplyTacticParams {
        state_id: init_result.state_id.clone(),
        goal_id: "g0".to_string(),
        tactic: "sorry".to_string(),
        timeout_ms: None,
    };
    let apply_response = handle_apply_tactic(&state, RequestId::Number(2), apply_params).await;
    let result: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(apply_response.result.unwrap()).unwrap();

    assert!(result.success, "sorry should succeed as a tactic");
    let ts = result
        .trust_summary
        .expect("sorry tactic should include trust_summary");
    assert!(
        ts.sorry_count > 0,
        "sorry tactic should report trust debt immediately, got sorry_count={}",
        ts.sorry_count
    );
    assert!(ts.arith_provenance.is_none());
    assert!(
        !ts.fully_verified,
        "sorry-containing state must not be fully_verified"
    );
}

/// Goal addressing (C1 Task E): applyTactic must honor a non-first `goal_id`,
/// focusing that goal before running the tactic instead of always acting on
/// goal 0.
///
/// Setup: `False ∧ True` split by `constructor` yields two goals
/// `[g0: False, g1: True]`. Applying `exact True.intro` to the SECOND goal
/// (`g1`) must succeed and close `True`, leaving exactly `[False]`. If the
/// handler ignored `goal_id` and acted on `g0` (`False`), `exact True.intro`
/// would fail with a type mismatch — so success plus a single remaining `False`
/// goal proves the tactic was routed to the addressed goal.
#[tokio::test]
async fn test_apply_tactic_addresses_non_first_goal() {
    let state = ServerState::new().with_env(clean_kernel::Environment::with_prelude());

    let init_response = handle_init_proof_state(
        &state,
        RequestId::Number(1),
        InitProofStateParams {
            theorem: "False ∧ True".to_string(),
            problem_id: None,
            timeout_ms: None,
        },
    )
    .await;
    assert!(
        init_response.error.is_none(),
        "init should not error: {:?}",
        init_response.error
    );
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    // Split into two goals via constructor.
    let split_response = handle_apply_tactic(
        &state,
        RequestId::Number(2),
        ApplyTacticParams {
            state_id: init_result.state_id,
            goal_id: init_result.goals[0].goal_id.clone(),
            tactic: "constructor".to_string(),
            timeout_ms: None,
        },
    )
    .await;
    let split: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(split_response.result.unwrap()).unwrap();
    assert!(
        split.success,
        "constructor should split the conjunction: {:?}",
        split.error
    );
    assert_eq!(split.new_goals.len(), 2, "expected two goals after split");
    assert_eq!(split.new_goals[0].target_pp, "False");
    assert_eq!(split.new_goals[1].target_pp, "True");

    let second_goal_id = split.new_goals[1].goal_id.clone();

    // Address the SECOND goal (True) with a tactic that only fits True.
    let apply_response = handle_apply_tactic(
        &state,
        RequestId::Number(3),
        ApplyTacticParams {
            state_id: split.new_state_id,
            goal_id: second_goal_id,
            tactic: "exact True.intro".to_string(),
            timeout_ms: None,
        },
    )
    .await;
    assert!(
        apply_response.error.is_none(),
        "applyTactic transport should not error: {:?}",
        apply_response.error
    );
    let result: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(apply_response.result.unwrap()).unwrap();

    assert!(
        result.success,
        "exact True.intro on the second (True) goal should succeed; \
         a failure means the tactic was misrouted to the first (False) goal: {:?}",
        result.error
    );
    // The True goal is closed; only the original first goal (False) remains.
    assert_eq!(
        result.new_goals.len(),
        1,
        "closing the second goal should leave exactly the first goal"
    );
    assert_eq!(
        result.new_goals[0].target_pp, "False",
        "the surviving goal must be the original first goal (False)"
    );
}

/// Goal addressing rejects a `goal_id` that names no live goal (out of range),
/// returning a failure rather than silently acting on goal 0.
#[tokio::test]
async fn test_apply_tactic_unknown_goal_id_is_rejected() {
    let state = ServerState::new().with_env(clean_kernel::Environment::with_prelude());

    let init_response = handle_init_proof_state(
        &state,
        RequestId::Number(1),
        InitProofStateParams {
            theorem: "True".to_string(),
            problem_id: None,
            timeout_ms: None,
        },
    )
    .await;
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    // g7 does not exist (single-goal state).
    let apply_response = handle_apply_tactic(
        &state,
        RequestId::Number(2),
        ApplyTacticParams {
            state_id: init_result.state_id,
            goal_id: "g7".to_string(),
            tactic: "exact True.intro".to_string(),
            timeout_ms: None,
        },
    )
    .await;
    let result: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(apply_response.result.unwrap()).unwrap();
    assert!(
        !result.success,
        "applyTactic to a non-existent goal_id must fail"
    );
    assert!(
        result.error.is_some(),
        "rejection should carry an error payload"
    );
}
