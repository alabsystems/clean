// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn assert_pair_true_first_sorry(goal_info: &SorryGoalInfo) {
    assert_eq!(goal_info.sorry_index, 0);
    assert!(goal_info.solved);
    assert_eq!(
        goal_info.replacement_tactic.as_deref(),
        Some("exact True.intro")
    );
    assert_eq!(
        goal_info.goals.len(),
        2,
        "both goals visible at first sorry"
    );
    assert_eq!(goal_info.goals[0].goal_id, "g0");
    assert_eq!(goal_info.goals[1].goal_id, "g1");
    assert_eq!(goal_info.goals[0].target, "True");
    assert_eq!(goal_info.goals[1].target, "True");
    assert!(
        goal_info.goals.iter().all(|goal| goal.tag.is_none()),
        "constructor goals should not invent branch tags: {:?}",
        goal_info.goals
    );
    assert!(goal_info.mathverse_candidates.is_empty());
}

fn assert_pair_true_second_sorry(goal_info: &SorryGoalInfo) {
    assert_eq!(goal_info.sorry_index, 1);
    assert!(goal_info.solved);
    assert_eq!(
        goal_info.replacement_tactic.as_deref(),
        Some("exact True.intro")
    );
    assert_eq!(goal_info.goals.len(), 1);
    assert_eq!(goal_info.goals[0].goal_id, "g0");
    assert_eq!(goal_info.goals[0].target, "True");
    assert!(goal_info.mathverse_candidates.is_empty());
}

#[tokio::test]
async fn test_fill_sorries_returns_sorry_goals_for_solved_holes() {
    let state = ServerState::new();
    let content = r#"
lemma pair_true_goals : True ∧ True := by
  constructor
  sorry
  sorry
"#;

    let result = fill_sorries_result(&state, content, &["exact True.intro"]).await;
    assert!(result.verified, "proof should verify: {result:?}");
    assert_eq!(
        result.sorry_goals.len(),
        2,
        "should have goal info for both sorry holes"
    );
    assert_pair_true_first_sorry(&result.sorry_goals[0]);
    assert_pair_true_second_sorry(&result.sorry_goals[1]);
}

#[tokio::test]
async fn test_fill_sorries_serializes_mathverse_candidates_on_sorry_goals() {
    let state = ServerState::new();
    let content = r#"
lemma true_goal_for_mathverse_wire : True := by
  sorry
"#;

    let value = fill_sorries_response_value(&state, content, &["exact True.intro"]).await;
    let candidates = value
        .get("sorry_goals")
        .and_then(serde_json::Value::as_array)
        .and_then(|goals| goals.first())
        .and_then(|goal| goal.get("mathverse_candidates"))
        .and_then(serde_json::Value::as_array)
        .expect("sorry_goals[0].mathverse_candidates should serialize as an array");
    assert!(candidates.is_empty());
}

#[tokio::test]
async fn test_fill_sorries_returns_sorry_goals_for_unsolved_holes() {
    let state = ServerState::new();
    let content = r#"
lemma mixed_goals : True ∧ False := by
  constructor
  sorry
  sorry
"#;

    let result = fill_sorries_result(&state, content, &["exact True.intro"]).await;
    assert!(
        !result.verified,
        "proof with False branch should not verify: {result:?}"
    );
    assert_eq!(
        result.sorry_goals.len(),
        2,
        "should have goal info for both sorry holes"
    );

    assert_eq!(result.sorry_goals[0].sorry_index, 0);
    assert!(result.sorry_goals[0].solved);
    assert_eq!(
        result.sorry_goals[0].replacement_tactic.as_deref(),
        Some("exact True.intro")
    );
    assert_eq!(result.sorry_goals[0].goals[0].target, "True");
    assert!(result.sorry_goals[0].mathverse_candidates.is_empty());

    assert_eq!(result.sorry_goals[1].sorry_index, 1);
    assert!(!result.sorry_goals[1].solved);
    assert!(result.sorry_goals[1].replacement_tactic.is_none());
    assert_eq!(result.sorry_goals[1].goals[0].target, "False");
    assert!(result.sorry_goals[1].mathverse_candidates.is_empty());
}

#[tokio::test]
async fn test_fill_sorries_returns_llm_guidance_for_goal_states() {
    let state = ServerState::new();
    let content = r#"
lemma nat_succ_reflexive_hole : Nat.succ Nat.zero = Nat.succ Nat.zero := by
  sorry
"#;

    let result = fill_sorries_result(&state, content, &["rfl"]).await;
    assert!(
        result.verified,
        "rfl should close a closed Nat.succ equality: {result:?}"
    );
    assert_eq!(result.sorry_goals.len(), 1);

    let goal_info = &result.sorry_goals[0];
    assert_string_list_contains(
        &goal_info.search_hints,
        "Goal is an equality",
        "search hint",
    );
    assert_string_list_contains(&goal_info.search_hints, "natural numbers", "search hint");
    assert_string_list_contains(&goal_info.suggested_tactics, "rfl", "suggested tactic");
    assert_string_list_contains(&goal_info.suggested_tactics, "simp", "suggested tactic");
    assert_string_list_contains(&goal_info.suggested_tactics, "omega", "suggested tactic");
    assert!(goal_info.mathverse_candidates.is_empty());
    assert_eq!(goal_info.goals.len(), 1);
    assert_eq!(goal_info.goals[0].goal_id, "g0");
    assert_goal_target_looks_like_equality(&goal_info.goals[0].target);
    assert!(
        goal_info.goals[0].target.contains("Nat.succ Nat.zero"),
        "target should mention both Nat.succ Nat.zero sides: {:?}",
        goal_info.goals[0].target
    );
    assert!(
        goal_info.goals[0].hypotheses.is_empty(),
        "closed Nat equality should not introduce local hypotheses"
    );
}
