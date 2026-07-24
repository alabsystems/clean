// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::proof_state::ApplyTacticResult;

async fn fill_unsolved_false_hole(state: &ServerState) -> serde_json::Value {
    let content = r#"
lemma false_hole : False := by
  sorry
"#;
    fill_sorries_response_value(state, content, &["trivial"]).await
}

fn extract_wire_state_id(response_value: &serde_json::Value) -> String {
    response_value["sorry_goals"][0]["state_id"]
        .as_str()
        .expect("unsolved sorry should expose a raw wire-format state_id")
        .to_string()
}

async fn replay_sorry_via_state_id(state: &ServerState, wire_state_id: &str) -> ApplyTacticResult {
    let apply_params = ApplyTacticParams {
        state_id: wire_state_id.to_string(),
        goal_id: "g0".to_string(),
        tactic: "sorry".to_string(),
        timeout_ms: None,
    };
    let apply_response = handle_apply_tactic(state, RequestId::Number(2), apply_params).await;
    assert!(
        apply_response.error.is_none(),
        "unexpected RPC error on applyTactic: {:?}",
        apply_response.error
    );
    serde_json::from_value(
        apply_response
            .result
            .expect("applyTactic should return a JSON result payload"),
    )
    .expect("applyTactic result should deserialize")
}

#[tokio::test]
async fn test_fill_sorries_unsolved_sorry_wire_state_id_replays_for_interactive_resume() {
    let state = ServerState::new();
    let response_value = fill_unsolved_false_hole(&state).await;
    let wire_state_id = extract_wire_state_id(&response_value);
    assert!(
        !wire_state_id.starts_with("ps_"),
        "fillSorries should expose the serde UUID form, got: {wire_state_id}"
    );

    let result: FillSorriesResult =
        serde_json::from_value(response_value).expect("fillSorries result should deserialize");
    assert!(!result.verified);
    assert_eq!(result.sorry_goals.len(), 1);

    let goal_info = &result.sorry_goals[0];
    assert!(!goal_info.solved, "False should not be solvable by trivial");
    assert!(
        goal_info.state_id.is_some(),
        "unsolved sorry should have a cached state_id for interactive resume"
    );

    let apply_result = replay_sorry_via_state_id(&state, &wire_state_id).await;
    assert!(
        apply_result.success,
        "applying sorry via the cached state_id should succeed: {:?}",
        apply_result.error
    );
    assert!(apply_result.is_solved, "sorry should close the proof state");
}

#[tokio::test]
async fn test_fill_sorries_fills_admit_hole_like_sorry() {
    let state = ServerState::new();
    let content = r#"
lemma admit_auto_fill : True := by
  admit
"#;

    let result = fill_sorries_result(&state, content, &["exact True.intro"]).await;
    assert!(
        result.verified,
        "admit hole should be auto-filled like sorry: {result:?}"
    );
    assert_eq!(
        result.solved_sorries, 1,
        "admit hole should be counted and solved"
    );
    assert!(
        result.remaining_sorries.is_empty(),
        "no holes should remain after auto-filling admit"
    );
    assert_eq!(
        result
            .filled_proof
            .as_deref()
            .expect("filled proof should be present"),
        "exact True.intro"
    );
}

#[tokio::test]
async fn test_fill_sorries_solved_sorry_has_no_state_id() {
    let state = ServerState::new();
    let content = r#"
lemma true_auto : True := by
  sorry
"#;

    let result = fill_sorries_result(&state, content, &["exact True.intro"]).await;
    assert!(result.verified);
    assert_eq!(result.sorry_goals.len(), 1);
    assert!(result.sorry_goals[0].solved);
    assert!(
        result.sorry_goals[0].state_id.is_none(),
        "solved sorry should not cache a state_id"
    );
}
