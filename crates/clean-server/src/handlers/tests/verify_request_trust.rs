// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;
use std::{future::Future, sync::Arc};

async fn run_verify_proof_request(
    state: &ServerState,
    request_id: i64,
    goal: &str,
    proof: &str,
) -> VerifyProofResult {
    let params = VerifyProofParams {
        goal: goal.to_string(),
        proof: proof.to_string(),
        context: None,
        timeout_ms: None,
    };
    let response = handle_verify_proof(state, RequestId::Number(request_id), params).await;
    assert!(
        response.error.is_none(),
        "verifyProof RPC error: {:?}",
        response.error
    );
    serde_json::from_value(response.result.unwrap()).expect("verifyProof result should decode")
}

async fn run_verify_file_request(
    state: &ServerState,
    request_id: i64,
    content: &str,
    proof: &str,
) -> VerifyFileResult {
    let params = VerifyFileParams {
        content: content.to_string(),
        proof: Some(proof.to_string()),
        timeout_ms: None,
    };
    let response = handle_verify_file(state, RequestId::Number(request_id), params).await;
    assert!(
        response.error.is_none(),
        "verifyFile RPC error: {:?}",
        response.error
    );
    serde_json::from_value(response.result.unwrap()).expect("verifyFile result should decode")
}

async fn run_concurrently<T1, T2, F1, F2>(first: F1, second: F2) -> (T1, T2)
where
    T1: Send + 'static,
    T2: Send + 'static,
    F1: Future<Output = T1> + Send + 'static,
    F2: Future<Output = T2> + Send + 'static,
{
    let start_barrier = Arc::new(tokio::sync::Barrier::new(3));
    let first_task = tokio::spawn({
        let start_barrier = Arc::clone(&start_barrier);
        async move {
            start_barrier.wait().await;
            first.await
        }
    });
    let second_task = tokio::spawn({
        let start_barrier = Arc::clone(&start_barrier);
        async move {
            start_barrier.wait().await;
            second.await
        }
    });
    start_barrier.wait().await;
    let first_result = first_task
        .await
        .expect("first concurrent task should complete");
    let second_result = second_task
        .await
        .expect("second concurrent task should complete");
    (first_result, second_result)
}

fn assert_sorry_provenance(
    summary: &TrustSummary,
    expected_explicit: bool,
    expected_synthetic: bool,
    context: &str,
) {
    let provenance = summary
        .sorry_provenance
        .as_ref()
        .expect("closed-proof trust summaries should include sorry provenance");
    assert_eq!(
        provenance.has_explicit_sorry, expected_explicit,
        "{context}: unexpected explicit sorry provenance"
    );
    assert_eq!(
        provenance.has_synthetic_sorry, expected_synthetic,
        "{context}: unexpected synthetic sorry provenance"
    );
}

fn assert_clean_trust_summary(summary: &TrustSummary, context: &str) {
    assert_eq!(summary.sorry_count, 0, "{context}: unexpected sorry_count");
    assert_sorry_provenance(summary, false, false, context);
    assert_eq!(summary.ay_count, 0, "{context}: unexpected ay_count");
    assert!(
        summary.ay_provenance.is_none(),
        "{context}: ay provenance should be omitted when ay_count is 0"
    );
    assert_eq!(summary.arith_count, 0, "{context}: unexpected arith_count");
    assert!(
        summary.arith_provenance.is_none(),
        "{context}: arith provenance should be omitted when arith_count is 0"
    );
    assert_eq!(
        summary.kernel_check_failures, 0,
        "{context}: unexpected kernel_check_failures"
    );
    assert!(
        summary.fully_verified,
        "{context}: clean proof should remain fully verified"
    );
}

fn assert_sorry_trust_summary(summary: &TrustSummary, context: &str) {
    assert_eq!(
        summary.sorry_count, 1,
        "{context}: sorry_count should be isolated"
    );
    assert_sorry_provenance(summary, true, false, context);
    assert_eq!(summary.ay_count, 0, "{context}: unexpected ay_count");
    assert!(
        summary.ay_provenance.is_none(),
        "{context}: ay provenance should be omitted when ay_count is 0"
    );
    assert_eq!(summary.arith_count, 0, "{context}: unexpected arith_count");
    assert!(
        summary.arith_provenance.is_none(),
        "{context}: arith provenance should be omitted when arith_count is 0"
    );
    assert_eq!(
        summary.kernel_check_failures, 0,
        "{context}: unexpected kernel_check_failures"
    );
    assert!(
        !summary.fully_verified,
        "{context}: sorry-backed proof must not be fully verified"
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn test_verify_proof_concurrent_requests_keep_trust_summaries_isolated() {
    const RUNS: usize = 6;

    for run in 0..RUNS {
        let trusted_state = Arc::new(ServerState::new());
        let clean_state = Arc::new(ServerState::new());
        let trusted_request_id = (run as i64) * 2 + 1;
        let clean_request_id = trusted_request_id + 1;

        let (trusted_result, clean_result) = run_concurrently(
            async move {
                run_verify_proof_request(&trusted_state, trusted_request_id, "Prop", "sorry").await
            },
            async move {
                run_verify_proof_request(
                    &clean_state,
                    clean_request_id,
                    "(A : Type) -> A -> A",
                    "intro A\nintro a\nassumption",
                )
                .await
            },
        )
        .await;

        assert!(
            trusted_result.verified,
            "verifyProof trusted request should still type-check"
        );
        assert_sorry_trust_summary(
            trusted_result
                .trust_summary
                .as_ref()
                .expect("verifyProof trusted request should include trust_summary"),
            "verifyProof trusted request",
        );

        assert!(
            clean_result.verified,
            "verifyProof clean request should verify"
        );
        assert_clean_trust_summary(
            clean_result
                .trust_summary
                .as_ref()
                .expect("verifyProof clean request should include trust_summary"),
            "verifyProof clean request",
        );
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn test_verify_file_concurrent_requests_keep_trust_summaries_isolated() {
    const RUNS: usize = 6;
    const TRUSTED_FILE: &str = r#"
theorem trusted_request_file : True := by
  exact True.intro
"#;
    const CLEAN_FILE: &str = r#"
theorem clean_request_file : True := by
  exact True.intro
"#;

    for run in 0..RUNS {
        let trusted_state = Arc::new(ServerState::new());
        let clean_state = Arc::new(ServerState::new());
        let trusted_request_id = 100 + (run as i64) * 2;
        let clean_request_id = trusted_request_id + 1;

        let (trusted_result, clean_result) = run_concurrently(
            async move {
                run_verify_file_request(&trusted_state, trusted_request_id, TRUSTED_FILE, "sorry")
                    .await
            },
            async move {
                run_verify_file_request(
                    &clean_state,
                    clean_request_id,
                    CLEAN_FILE,
                    "exact True.intro",
                )
                .await
            },
        )
        .await;

        assert!(
            trusted_result.verified,
            "verifyFile trusted request should still type-check"
        );
        assert!(
            trusted_result.sorries.is_empty(),
            "trusted file fixture must not include textual sorries"
        );
        assert_sorry_trust_summary(
            trusted_result
                .trust_summary
                .as_ref()
                .expect("verifyFile trusted request should include trust_summary"),
            "verifyFile trusted request",
        );

        assert!(
            clean_result.verified,
            "verifyFile clean request should verify"
        );
        assert!(
            clean_result.sorries.is_empty(),
            "clean file fixture must not include textual sorries"
        );
        assert_clean_trust_summary(
            clean_result
                .trust_summary
                .as_ref()
                .expect("verifyFile clean request should include trust_summary"),
            "verifyFile clean request",
        );
    }
}

#[tokio::test]
async fn test_verify_file_textual_sorries_block_fully_verified() {
    let state = ServerState::new();
    let content = r#"
theorem file_with_textual_sorry : 1 = 1 := by
  sorry
"#;

    let result = run_verify_file_request(&state, 500, content, "rfl").await;
    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("verifyFile should include trust_summary when a proof was supplied");

    assert!(
        !result.verified,
        "textual sorries in the file must keep verifyFile unverified"
    );
    assert_eq!(trust_summary.sorry_count, 0);
    assert_sorry_provenance(trust_summary, false, false, "verifyFile textual sorry");
    assert_eq!(trust_summary.ay_count, 0);
    assert_eq!(trust_summary.arith_count, 0);
    assert!(trust_summary.arith_provenance.is_none());
    assert_eq!(trust_summary.kernel_check_failures, 0);
    assert!(
        !trust_summary.fully_verified,
        "fully_verified must follow the final verifyFile verdict, including textual sorry guards"
    );
}
