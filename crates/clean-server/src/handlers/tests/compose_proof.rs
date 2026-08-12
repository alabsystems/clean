// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;

#[tokio::test]
async fn test_compose_proof_replaces_single_sorry() {
    let state = ServerState::new();

    let content = r#"
lemma one_hole : True := by
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
    assert!(result.verified, "composed proof should verify: {result:?}");
    assert_eq!(result.replaced_count, 1);
    assert!(result.remaining_sorries.is_empty());
    assert_eq!(
        result.composed_proof.as_deref().unwrap(),
        "exact True.intro"
    );
}

#[tokio::test]
async fn test_compose_proof_replaces_multiple_sorries() {
    let state = ServerState::new();

    let content = r#"
lemma pair_true : True ∧ True := by
  constructor
  sorry
  sorry
"#;

    let params = ComposeProofParams {
        content: content.to_string(),
        replacements: vec![
            SorryReplacement {
                sorry_index: 0,
                tactic: "exact True.intro".to_string(),
            },
            SorryReplacement {
                sorry_index: 1,
                tactic: "exact True.intro".to_string(),
            },
        ],
        timeout_ms: Some(5000),
    };

    let response = handle_compose_proof(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected RPC error: {:?}",
        response.error
    );

    let result: ComposeProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.verified, "composed proof should verify: {result:?}");
    assert_eq!(result.replaced_count, 2);
    assert!(result.remaining_sorries.is_empty());
}

#[tokio::test]
async fn test_compose_proof_partial_replacement_keeps_sorry() {
    let state = ServerState::new();

    let content = r#"
lemma pair_mixed : True ∧ False := by
  constructor
  sorry
  sorry
"#;

    // Only replace sorry #0 (True goal), leave sorry #1 (False goal)
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
    assert!(
        !result.verified,
        "proof with remaining sorry should not verify"
    );
    assert_eq!(result.replaced_count, 1);
    assert!(
        !result.remaining_sorries.is_empty(),
        "should have remaining sorry from unreplaced hole"
    );
}

#[tokio::test]
async fn test_compose_proof_bad_replacement_tactic_returns_error() {
    let state = ServerState::new();

    let content = r#"
lemma false_hole : False := by
  sorry
"#;

    let params = ComposeProofParams {
        content: content.to_string(),
        replacements: vec![SorryReplacement {
            sorry_index: 0,
            tactic: "exact True.intro".to_string(), // Wrong tactic for False
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
    assert!(!result.verified);
    assert!(
        result.error.is_some(),
        "should report error for failed replacement tactic"
    );
    let error = result.error.unwrap();
    assert!(
        error
            .message
            .contains("replacement tactic for sorry #0 failed"),
        "error should identify the sorry index: {}",
        error.message
    );
}

#[tokio::test]
async fn test_compose_proof_empty_replacements_preserves_original() {
    let state = ServerState::new();

    let content = r#"
lemma simple_gap : True := by
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
        "unexpected RPC error: {:?}",
        response.error
    );

    let result: ComposeProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.replaced_count, 0);
    // Proof should still complete (sorry closes goals) but not be fully verified
    // because sorry_count > 0 in the trust summary
    assert!(!result.remaining_sorries.is_empty());
}

#[tokio::test]
async fn test_compose_proof_end_to_end_with_fill_sorries() {
    // Full Pantograph feedback loop:
    // 1. fillSorries → get unsolved sorry state_ids
    // 2. applyTactic → discover working tactic
    // 3. composeProof → splice and verify
    let state = ServerState::new();

    let content = r#"
lemma pair_true_e2e : True ∧ True := by
  constructor
  sorry
  sorry
"#;

    // Step 1: fillSorries with a tactic that is inapplicable to both True goals.
    // This leaves both holes available for the caller-driven replacement step.
    let fill_params = FillSorriesParams {
        content: content.to_string(),
        tactic_sequence: vec!["rfl".to_string()],
        timeout_ms: Some(5000),
    };
    let fill_response = handle_fill_sorries(&state, RequestId::Number(1), fill_params).await;
    assert!(fill_response.error.is_none());
    let fill_result: FillSorriesResult =
        serde_json::from_value(fill_response.result.unwrap()).unwrap();

    // Collect unsolved sorry indices
    let unsolved_indices: Vec<usize> = fill_result
        .sorry_goals
        .iter()
        .filter(|g| !g.solved)
        .map(|g| g.sorry_index)
        .collect();
    assert_eq!(
        unsolved_indices,
        vec![0, 1],
        "the setup must expose both holes to the replacement loop"
    );

    // Step 2: Build replacement list for all unsolved sorries
    let replacements: Vec<SorryReplacement> = unsolved_indices
        .iter()
        .map(|&idx| SorryReplacement {
            sorry_index: idx,
            tactic: "exact True.intro".to_string(),
        })
        .collect();

    // Step 3: composeProof with replacements
    let compose_params = ComposeProofParams {
        content: content.to_string(),
        replacements,
        timeout_ms: Some(5000),
    };

    let compose_response = handle_compose_proof(&state, RequestId::Number(2), compose_params).await;
    assert!(
        compose_response.error.is_none(),
        "unexpected RPC error: {:?}",
        compose_response.error
    );

    let compose_result: ComposeProofResult =
        serde_json::from_value(compose_response.result.unwrap()).unwrap();
    assert!(
        compose_result.verified,
        "end-to-end composed proof should verify: {compose_result:?}"
    );
    assert!(compose_result.remaining_sorries.is_empty());
}

#[tokio::test]
async fn test_compose_proof_admit_replacement_stays_unverified_with_remaining_hole() {
    let state = ServerState::new();

    let content = r#"
lemma admitted_gap : True := by
  sorry
"#;

    let params = ComposeProofParams {
        content: content.to_string(),
        replacements: vec![SorryReplacement {
            sorry_index: 0,
            tactic: "admit".to_string(),
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
    assert!(
        !result.verified,
        "composeProof should not mark an admitted proof as verified: {result:?}"
    );
    assert_eq!(result.composed_proof.as_deref(), Some("admit"));
    assert_eq!(result.remaining_sorries.len(), 1);
    let trust_summary = result
        .trust_summary
        .expect("explicit-hole composition should still return trust summary");
    assert_eq!(trust_summary.sorry_count, 1);
    assert!(
        !trust_summary.fully_verified,
        "admit-backed proofs must not be fully verified"
    );
    let provenance = trust_summary
        .sorry_provenance
        .expect("closed proof should include explicit sorry provenance");
    assert!(provenance.has_explicit_sorry);
    assert!(!provenance.has_synthetic_sorry);
}

#[tokio::test]
async fn test_compose_proof_original_admit_is_replaceable_hole() {
    let state = ServerState::new();

    let content = r#"
lemma original_admit : True := by
  admit
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
    assert!(
        result.verified,
        "replacing original admit with valid tactic should verify: {result:?}"
    );
    assert_eq!(result.replaced_count, 1);
    assert!(result.remaining_sorries.is_empty());
    assert_eq!(
        result.composed_proof.as_deref().unwrap(),
        "exact True.intro"
    );
}

#[tokio::test]
async fn test_compose_proof_unreplaced_admit_stays_unverified() {
    let state = ServerState::new();

    let content = r#"
lemma unreplaced_admit : True := by
  admit
"#;

    let params = ComposeProofParams {
        content: content.to_string(),
        replacements: vec![],
        timeout_ms: Some(5000),
    };

    let response = handle_compose_proof(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected RPC error: {:?}",
        response.error
    );

    let result: ComposeProofResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        !result.verified,
        "unreplaced admit should not verify: {result:?}"
    );
    assert_eq!(result.replaced_count, 0);
    assert!(
        !result.remaining_sorries.is_empty(),
        "admit should appear in remaining_sorries: {result:?}"
    );
}

#[tokio::test]
async fn test_compose_proof_theorem_name_with_sorry_substring_does_not_create_fake_hole() {
    let state = ServerState::new();

    let content = r#"
lemma one_sorry_name : True := by
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
    assert!(
        result.verified,
        "theorem-name substring should not leave a fake remaining hole: {result:?}"
    );
    assert!(
        result.remaining_sorries.is_empty(),
        "theorem-name substring should not be reported as a remaining hole: {result:?}"
    );
}

// Block-comment regression test (P1346 handoff)
#[tokio::test]
async fn test_compose_proof_inline_block_commented_admit_is_replaceable_hole() {
    let state = ServerState::new();

    let content = r#"
theorem block_admit : True := by
  /- note -/ admit
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
    assert!(
        result.verified,
        "admit after closed inline block comment must be replaceable and verifiable: {result:?}"
    );
}
