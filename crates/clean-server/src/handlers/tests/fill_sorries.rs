// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

pub(super) use crate::handlers::verify::SorryGoalInfo;
pub(super) use crate::handlers::*;

pub(super) fn fill_sorries_params(content: &str, tactic_sequence: &[&str]) -> FillSorriesParams {
    FillSorriesParams {
        content: content.to_string(),
        tactic_sequence: tactic_sequence
            .iter()
            .map(|tactic| (*tactic).to_string())
            .collect(),
        timeout_ms: Some(5000),
    }
}

pub(super) async fn fill_sorries_response_value(
    state: &ServerState,
    content: &str,
    tactic_sequence: &[&str],
) -> serde_json::Value {
    let response = handle_fill_sorries(
        state,
        RequestId::Number(1),
        fill_sorries_params(content, tactic_sequence),
    )
    .await;
    assert!(
        response.error.is_none(),
        "unexpected RPC error: {:?}",
        response.error
    );
    response
        .result
        .expect("fillSorries should return a JSON result payload")
}

pub(super) async fn fill_sorries_result(
    state: &ServerState,
    content: &str,
    tactic_sequence: &[&str],
) -> FillSorriesResult {
    serde_json::from_value(fill_sorries_response_value(state, content, tactic_sequence).await)
        .expect("fillSorries result should deserialize")
}

pub(super) fn assert_string_list_contains(items: &[String], expected: &str, label: &str) {
    assert!(
        items
            .iter()
            .any(|item| item == expected || item.contains(expected)),
        "expected {label} {expected:?} in {items:?}"
    );
}

pub(super) fn assert_goal_target_looks_like_equality(target: &str) {
    assert!(
        target.starts_with("Eq") || target.contains(" = "),
        "expected equality-style target, got: {target:?}"
    );
}

#[test]
fn test_fill_sorries_legacy_sorry_goals_decode_without_mathverse_candidates() {
    let result: FillSorriesResult = serde_json::from_value(serde_json::json!({
        "verified": false,
        "solved_sorries": 0,
        "time_ns": 0,
        "sorry_goals": [
            {
                "sorry_index": 0,
                "solved": false,
                "goals": []
            }
        ]
    }))
    .expect("legacy fillSorries result should decode");

    assert_eq!(result.sorry_goals.len(), 1);
    assert!(result.sorry_goals[0].mathverse_candidates.is_empty());
}

#[tokio::test]
async fn test_fill_sorries_solves_all_holes_with_custom_tactic() {
    let state = ServerState::new();
    let content = r#"
lemma pair_true : True ∧ True := by
  constructor
  sorry
  sorry
"#;

    let result = fill_sorries_result(&state, content, &["exact True.intro"]).await;
    assert!(
        result.verified,
        "filled proof should verify, got: {result:?}"
    );
    assert_eq!(
        result.solved_sorries, 2,
        "both sorry holes should be solved"
    );
    assert!(
        result.remaining_sorries.is_empty(),
        "no sorry holes should remain after solving both goals"
    );
    assert_eq!(
        result
            .filled_proof
            .as_deref()
            .expect("filled proof should be present"),
        "constructor\nexact True.intro\nexact True.intro"
    );
    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("fillSorries should include trust_summary");
    assert_eq!(trust_summary.arith_count, 0);
    assert!(trust_summary.arith_provenance.is_none());
}

#[tokio::test]
async fn test_fill_sorries_preserves_unsolved_holes() {
    let state = ServerState::new();
    let content = r#"
lemma pair_mixed : True ∧ False := by
  constructor
  sorry
  sorry
"#;

    let result = fill_sorries_result(&state, content, &["exact True.intro"]).await;
    assert!(
        !result.verified,
        "proof with a remaining sorry should not be marked verified: {result:?}"
    );
    assert_eq!(
        result.solved_sorries, 1,
        "only the True branch should be solved, got: {result:?}"
    );
    assert_eq!(
        result
            .filled_proof
            .as_deref()
            .expect("filled proof should be present"),
        "constructor\nexact True.intro\nsorry"
    );
    assert_eq!(
        result.remaining_sorries.len(),
        1,
        "one sorry should remain in the rewritten proof"
    );
    assert_eq!(result.remaining_sorries[0].line, 3);
    assert_eq!(result.remaining_sorries[0].col, 1);
    assert_eq!(
        result.remaining_sorries[0].context.as_deref(),
        Some("pair_mixed")
    );
    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("fillSorries should include trust_summary");
    assert_eq!(trust_summary.arith_count, 0);
    assert!(trust_summary.arith_provenance.is_none());
}

#[tokio::test]
async fn test_fill_sorries_replaces_sorries_with_inline_comments() {
    let state = ServerState::new();
    let content = r#"
lemma pair_true_commented : True ∧ True := by
  constructor
  sorry -- first branch
  sorry -- second branch
"#;

    let result = fill_sorries_result(&state, content, &["exact True.intro"]).await;
    assert!(
        result.verified,
        "commented sorry holes should still be replaceable, got: {result:?}"
    );
    assert_eq!(result.solved_sorries, 2);
    assert!(
        result.remaining_sorries.is_empty(),
        "all commented sorry holes should be solved"
    );
    assert_eq!(
        result
            .filled_proof
            .as_deref()
            .expect("filled proof should be present"),
        "constructor\nexact True.intro\nexact True.intro"
    );
}

#[tokio::test]
async fn test_fill_sorries_runs_aesop_candidate() {
    let state = ServerState::new();
    let content = r#"
lemma aesop_fills_true : True := by
  sorry
"#;

    let result = fill_sorries_result(&state, content, &["aesop"]).await;
    assert!(
        result.verified,
        "aesop should solve a trivial True goal, got: {result:?}"
    );
    assert_eq!(
        result.solved_sorries, 1,
        "aesop should replace the sorry hole"
    );
    assert!(
        result.remaining_sorries.is_empty(),
        "no sorry holes should remain after aesop succeeds"
    );
    assert_eq!(
        result
            .filled_proof
            .as_deref()
            .expect("filled proof should be present"),
        "aesop"
    );
}

#[tokio::test]
async fn test_fill_sorries_does_not_count_placeholder_candidate_as_solved() {
    let state = ServerState::new();
    let content = r#"
lemma placeholder_stays_unsolved : True := by
  sorry
"#;

    let result = fill_sorries_result(&state, content, &["sorry"]).await;
    assert!(
        !result.verified,
        "replaying the placeholder sorry should not count as a verified fill: {result:?}"
    );
    assert_eq!(
        result.solved_sorries, 0,
        "placeholder tactics must not be counted as solved holes"
    );
    assert_eq!(
        result
            .filled_proof
            .as_deref()
            .expect("filled proof should be present"),
        "sorry"
    );
    assert_eq!(
        result.remaining_sorries.len(),
        1,
        "the original placeholder should still be reported"
    );
}

#[tokio::test]
async fn test_fill_sorries_ignores_standalone_comments() {
    let state = ServerState::new();
    let content = r#"
lemma commented_proof : True ∧ True := by
  constructor
  -- first branch
  sorry
  -- second branch
  sorry
"#;

    let result = fill_sorries_result(&state, content, &["exact True.intro"]).await;
    assert!(
        result.verified,
        "standalone comments should be stripped during normalization: {result:?}"
    );
    assert_eq!(
        result.solved_sorries, 2,
        "both sorry holes should be solved despite interleaved comments"
    );
    assert!(
        result.remaining_sorries.is_empty(),
        "no sorry holes should remain"
    );
}
