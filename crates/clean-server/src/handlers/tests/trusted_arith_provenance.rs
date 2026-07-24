// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;

#[tokio::test]
async fn test_compose_proof_omits_arith_provenance_when_count_is_zero() {
    let state = ServerState::new();

    let content = r#"
lemma compose_clean_trust_summary : True := by
  sorry
"#;

    let params = ComposeProofParams {
        content: content.to_string(),
        replacements: vec![SorryReplacement {
            sorry_index: 0,
            tactic: "exact True.intro".to_string(),
        }],
        timeout_ms: Some(5000),
    };

    let response = handle_compose_proof(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected RPC error: {:?}",
        response.error
    );

    let result: ComposeProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("composeProof should include trust_summary");

    assert!(result.verified, "composed proof should verify: {result:?}");
    assert_eq!(trust_summary.arith_count, 0);
    assert!(
        trust_summary.arith_provenance.is_none(),
        "arith provenance should stay omitted when arith_count is zero"
    );
}
