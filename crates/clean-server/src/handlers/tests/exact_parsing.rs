// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;
use crate::rpc::RequestId;

#[tokio::test]
async fn test_init_proof_state_rejects_trailing_garbage() {
    let state = ServerState::new();
    let params = InitProofStateParams {
        theorem: "Prop, garbage".to_string(),
        problem_id: None,
        timeout_ms: None,
    };

    let response = handle_init_proof_state(&state, RequestId::Number(1), params).await;
    let error = response
        .error
        .expect("trailing garbage should be rejected during theorem parsing");
    assert!(
        error.message.contains("failed to parse theorem"),
        "error should identify theorem parsing failure: {error:?}"
    );
    assert!(
        error.message.contains("trailing"),
        "error should mention trailing tokens: {error:?}"
    );
}

#[tokio::test]
async fn test_get_premises_rejects_trailing_garbage_goal() {
    let state = ServerState::new();

    let params = GetPremisesParams {
        goal: "Prop, garbage".to_string(),
        method: "hybrid".to_string(),
        max_premises: 10,
        threshold: 0.0,
        timeout_ms: Some(5000),
    };

    let response = handle_get_premises(&state, RequestId::Number(1), params).await;
    let error = response
        .error
        .expect("trailing garbage should surface as an RPC parse error");
    assert!(
        error.message.contains("Failed to parse goal"),
        "error should identify goal parsing failure: {error:?}"
    );
    assert!(
        error.message.contains("trailing"),
        "error should mention trailing tokens: {error:?}"
    );
}

#[tokio::test]
async fn test_batch_get_premises_rejects_trailing_garbage_goal() {
    let state = ServerState::new();

    let params = BatchGetPremisesParams {
        items: vec![
            BatchGetPremisesItem {
                id: "valid".to_string(),
                goal: "Prop".to_string(),
            },
            BatchGetPremisesItem {
                id: "trailing".to_string(),
                goal: "Prop, garbage".to_string(),
            },
        ],
        method: "hybrid".to_string(),
        max_premises: 5,
        threshold: 0.0,
        timeout_ms: Some(10000),
    };

    let response = handle_batch_get_premises(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "batch request should return per-item failures, not RPC error: {:?}",
        response.error
    );

    let result: BatchGetPremisesResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.results[0].success, "valid goal should still succeed");
    assert!(
        !result.results[1].success,
        "trailing-garbage goal should fail"
    );
    let error = result.results[1]
        .error
        .as_ref()
        .expect("failed item should include parse error details");
    assert!(
        error.contains("trailing"),
        "item error should mention trailing tokens: {error}"
    );
}

#[tokio::test]
async fn test_verify_proof_rejects_trailing_garbage_goal() {
    let state = ServerState::new();
    let params = VerifyProofParams {
        goal: "Prop, garbage".to_string(),
        proof: "".to_string(),
        context: None,
        timeout_ms: None,
    };

    let response = handle_verify_proof(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.verified, "trailing garbage must be rejected");
    let error = result
        .error
        .expect("rejected goal should include parse error details");
    assert!(
        error.message.contains("failed to parse goal"),
        "error should identify goal parsing failure: {error:?}"
    );
    assert!(
        error.message.contains("trailing"),
        "error should mention trailing tokens: {error:?}"
    );
}

#[tokio::test]
async fn test_verify_proof_batch_rejects_trailing_garbage_goal() {
    let state = ServerState::new();
    let params = VerifyProofBatchParams {
        proofs: vec![
            VerifyProofBatchItem {
                id: "valid".to_string(),
                goal: "Prop".to_string(),
                proof: "".to_string(),
                context: None,
            },
            VerifyProofBatchItem {
                id: "trailing".to_string(),
                goal: "Prop, garbage".to_string(),
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
    assert_eq!(result.results.len(), 2, "Should preserve both batch items");
    assert_eq!(
        result.results[0].id, "valid",
        "batch item order should stay stable"
    );
    assert!(
        !result.results[0].verified,
        "empty proof for the valid goal should remain incomplete"
    );
    let valid_error = result.results[0]
        .error
        .as_ref()
        .expect("valid goal should parse and then report incomplete proof");
    assert_eq!(
        valid_error.message.as_str(),
        "proof incomplete",
        "valid item should only fail because the proof is empty: {valid_error:?}"
    );
    assert!(
        !result.results[1].verified,
        "trailing-garbage goal must not verify"
    );
    let error = result.results[1]
        .error
        .as_ref()
        .expect("failed item should include parse error details");
    assert!(
        error.message.contains("trailing"),
        "item error should mention trailing tokens: {error:?}"
    );
}

#[tokio::test]
async fn test_verify_file_rejects_trailing_garbage_goal() {
    let state = ServerState::new();

    let content = r#"
theorem bad_goal : True, garbage := by
  sorry
"#;

    let params = VerifyFileParams {
        content: content.to_string(),
        proof: Some("exact True.intro".to_string()),
        timeout_ms: Some(5000),
    };

    let response = handle_verify_file(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Trailing garbage should return a result, not RPC error: {:?}",
        response.error
    );

    let result: VerifyFileResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.verified, "trailing-garbage goal must not verify");
    let error = result
        .error
        .expect("rejected goal should include parse error details");
    assert!(
        error.message.contains("failed to parse goal"),
        "error should identify goal parsing failure: {error:?}"
    );
    assert!(
        error.message.contains("trailing"),
        "error should mention trailing tokens: {error:?}"
    );
}

#[tokio::test]
async fn test_compose_proof_rejects_trailing_garbage_goal() {
    let state = ServerState::new();

    let content = r#"
lemma malformed_goal : True, garbage := by
  sorry
"#;

    let params = ComposeProofParams {
        content: content.to_string(),
        replacements: vec![],
        timeout_ms: Some(5000),
    };

    let response = handle_compose_proof(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Trailing garbage should return a result, not RPC error: {:?}",
        response.error
    );

    let result: ComposeProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.verified, "trailing-garbage goal must not verify");
    let error = result
        .error
        .expect("rejected goal should include parse error details");
    assert!(
        error.message.contains("failed to parse goal"),
        "error should identify goal parsing failure: {error:?}"
    );
    assert!(
        error.message.contains("trailing"),
        "error should mention trailing tokens: {error:?}"
    );
}

#[tokio::test]
async fn test_fill_sorries_rejects_trailing_garbage_goal() {
    let state = ServerState::new();

    let content = r#"
lemma malformed_goal : True, garbage := by
  sorry
"#;

    let params = FillSorriesParams {
        content: content.to_string(),
        tactic_sequence: vec!["exact True.intro".to_string()],
        timeout_ms: Some(5000),
    };

    let response = handle_fill_sorries(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Trailing garbage should return a result, not RPC error: {:?}",
        response.error
    );

    let result: FillSorriesResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.verified, "trailing-garbage goal must not verify");
    let error = result
        .error
        .expect("rejected goal should include parse error details");
    assert!(
        error.message.contains("failed to parse goal"),
        "error should identify goal parsing failure: {error:?}"
    );
    assert!(
        error.message.contains("trailing"),
        "error should mention trailing tokens: {error:?}"
    );
}
