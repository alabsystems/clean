// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Helper functions for fillSorries: sorry position collection and goal snapshot.

use super::parse_lean::{explicit_hole_token_at, parse_lean_file};
use super::types::*;
use crate::proof_state::{convert_goals, llm_guidance_for_state, LlmStateGuidance};
use clean_elab::tactic::ProofState as InternalProofState;

pub(crate) fn wrap_theorem_proof(theorem: &ExtractedTheorem, proof: &str) -> String {
    let indented_proof = if proof.is_empty() {
        String::new()
    } else {
        proof
            .lines()
            .map(|line| format!("  {line}"))
            .collect::<Vec<_>>()
            .join("\n")
    };
    if indented_proof.is_empty() {
        format!("theorem {} : {} := by", theorem.name, theorem.goal)
    } else {
        format!(
            "theorem {} : {} := by\n{}",
            theorem.name, theorem.goal, indented_proof
        )
    }
}

pub(crate) fn collect_explicit_sorry_positions(
    theorem: &ExtractedTheorem,
    proof: &str,
) -> Vec<SorryLocation> {
    let wrapped = wrap_theorem_proof(theorem, proof);
    let wrapped_lines: Vec<&str> = wrapped.lines().collect();
    parse_lean_file(&wrapped)
        .map(|(_, positions)| {
            positions
                .into_iter()
                .filter_map(|position| {
                    let line = wrapped_lines.get(position.line.checked_sub(1)?)?;
                    let column = position.col.checked_sub(1)?;
                    if explicit_hole_token_at(line, column).is_some() {
                        Some(SorryLocation {
                            line: position.line.saturating_sub(1),
                            col: position.col.saturating_sub(2),
                            context: position.context,
                        })
                    } else {
                        None
                    }
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Snapshot the current proof state goals into lightweight `SorryGoal` structs.
pub(crate) fn snapshot_sorry_goals(
    proof_state: &InternalProofState,
    env: &clean_kernel::Environment,
) -> Vec<SorryGoal> {
    let raw_goals = proof_state.goals();
    convert_goals(proof_state, env)
        .into_iter()
        .zip(raw_goals.iter())
        .map(|(api_goal, raw_goal)| SorryGoal {
            goal_id: api_goal.goal_id,
            target: api_goal.target_pp,
            tag: raw_goal.tag.clone(),
            hypotheses: api_goal
                .hypotheses
                .into_iter()
                .map(|h| SorryHypothesis {
                    name: h.name,
                    type_pp: h.type_pp,
                    value_pp: h.value_pp,
                })
                .collect(),
        })
        .collect()
}

/// Snapshot LLM-facing guidance for the currently focused sorry goal.
pub(crate) fn snapshot_sorry_guidance(
    proof_state: &InternalProofState,
    env: &clean_kernel::Environment,
) -> LlmStateGuidance {
    llm_guidance_for_state(proof_state, env)
}
