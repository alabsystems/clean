// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Handler for fillSorries: SorryHammer-style automatic hole filling.

use super::fill_sorries_support::{
    collect_explicit_sorry_positions, snapshot_sorry_goals, snapshot_sorry_guidance,
};
use super::parse_lean::{is_explicit_hole_tactic, parse_lean_file};
use super::types::*;
use crate::handlers::helpers::{format_expr, generate_tactic_suggestions, parse_tactic_script};
use crate::handlers::state::ServerState;
use crate::handlers::tactic::execute_simple_tactic;
use crate::proof_state::convert_goals;
use crate::rpc::{RequestId, Response, RpcError};
use clean_elab::elaborate;
use clean_elab::tactic::ProofState as InternalProofState;
use clean_parser::parse_expr_with_tactics_exact;
use std::time::{Duration, Instant};
use tracing::instrument;

const DEFAULT_FILL_SORRIES_TACTICS: &[&str] = &[
    "omega", "linarith", "simp", "ring", "norm_num", "ay_smt", "aesop",
];

fn normalized_tactic_sequence(sequence: &[String]) -> Vec<String> {
    let filtered: Vec<String> = sequence
        .iter()
        .map(|tactic| tactic.trim())
        .filter(|tactic| !tactic.is_empty())
        .map(str::to_string)
        .collect();
    if filtered.is_empty() {
        DEFAULT_FILL_SORRIES_TACTICS
            .iter()
            .map(|tactic| (*tactic).to_string())
            .collect()
    } else {
        filtered
    }
}

fn render_rewritten_proof(rewritten_prefix: &[String], remaining_suffix: &[String]) -> String {
    rewritten_prefix
        .iter()
        .chain(remaining_suffix.iter())
        .cloned()
        .collect::<Vec<_>>()
        .join("\n")
}

fn build_error_result(
    theorem: Option<ExtractedTheorem>,
    filled_proof: Option<String>,
    original_sorries: Vec<SorryLocation>,
    remaining_sorries: Vec<SorryLocation>,
    solved_sorries: usize,
    timing: TimingBreakdown,
    error: VerifyProofError,
    trust_summary: Option<TrustSummary>,
    sorry_goals: Vec<SorryGoalInfo>,
) -> FillSorriesResult {
    FillSorriesResult {
        verified: false,
        theorem,
        filled_proof,
        original_sorries,
        remaining_sorries,
        solved_sorries,
        time_ns: timing.total_ns,
        timing: Some(timing),
        error: Some(error),
        trust_summary,
        proof_term: None,
        sorry_goals,
    }
}

/// Replay a theorem proof and replace each `sorry` with the first tactic that
/// strictly reduces the active goal count.
#[instrument(skip(state))]
pub async fn handle_fill_sorries(
    state: &ServerState,
    id: RequestId,
    params: FillSorriesParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));

    let parse_start = Instant::now();
    let theorem = match parse_lean_file(&params.content) {
        Ok((theorem, _)) => theorem,
        Err(error) => {
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let result = FillSorriesResult {
                verified: false,
                theorem: None,
                filled_proof: None,
                original_sorries: vec![],
                remaining_sorries: vec![],
                solved_sorries: 0,
                time_ns: elapsed_ns,
                timing: Some(TimingBreakdown {
                    parse_ns: elapsed_ns,
                    elaborate_ns: 0,
                    verify_ns: 0,
                    total_ns: elapsed_ns,
                }),
                error: Some(VerifyProofError {
                    message: format!("failed to parse file: {error}"),
                    position: None,
                    expected_type: None,
                    actual_goals: vec![],
                    suggestions: vec!["check Lean syntax".to_string()],
                }),
                trust_summary: None,
                proof_term: None,
                sorry_goals: vec![],
            };
            return Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
        }
    };
    let parse_ns = parse_start.elapsed().as_nanos() as u64;

    let Some(theorem) = theorem else {
        let elapsed_ns = start.elapsed().as_nanos() as u64;
        let result = FillSorriesResult {
            verified: false,
            theorem: None,
            filled_proof: None,
            original_sorries: vec![],
            remaining_sorries: vec![],
            solved_sorries: 0,
            time_ns: elapsed_ns,
            timing: Some(TimingBreakdown {
                parse_ns,
                elaborate_ns: 0,
                verify_ns: 0,
                total_ns: elapsed_ns,
            }),
            error: Some(VerifyProofError {
                message: "no theorem found in file".to_string(),
                position: None,
                expected_type: None,
                actual_goals: vec![],
                suggestions: vec!["file must contain theorem or lemma declaration".to_string()],
            }),
            trust_summary: None,
            proof_term: None,
            sorry_goals: vec![],
        };
        return Response::success_typed(id.clone(), &result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
    };

    let original_tactics = parse_tactic_script(&theorem.original_proof);
    let normalized_original_proof = original_tactics.join("\n");
    let original_sorries = collect_explicit_sorry_positions(&theorem, &normalized_original_proof);

    super::initialize_verify_file_env(state).await;

    let elaborate_start = Instant::now();
    let surface_expr = match parse_expr_with_tactics_exact(&theorem.goal, &state.tactic_patterns) {
        Ok(expr) => expr,
        Err(error) => {
            let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let timing = TimingBreakdown {
                parse_ns,
                elaborate_ns,
                verify_ns: 0,
                total_ns: elapsed_ns,
            };
            let result = build_error_result(
                Some(theorem),
                Some(normalized_original_proof),
                original_sorries,
                vec![],
                0,
                timing,
                VerifyProofError {
                    message: format!("failed to parse goal: {error}"),
                    position: None,
                    expected_type: None,
                    actual_goals: vec![],
                    suggestions: vec!["goal type may use unknown Mathlib types".to_string()],
                },
                None,
                vec![],
            );
            return Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
        }
    };

    let env = state.env.read().await;
    let target = match elaborate(&env, &surface_expr) {
        Ok(expr) => expr,
        Err(error) => {
            let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let timing = TimingBreakdown {
                parse_ns,
                elaborate_ns,
                verify_ns: 0,
                total_ns: elapsed_ns,
            };
            let result = build_error_result(
                Some(theorem),
                Some(normalized_original_proof),
                original_sorries,
                vec![],
                0,
                timing,
                VerifyProofError {
                    message: format!("failed to elaborate goal: {error}"),
                    position: None,
                    expected_type: None,
                    actual_goals: vec![],
                    suggestions: vec!["goal type may require Mathlib context".to_string()],
                },
                None,
                vec![],
            );
            return Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
        }
    };
    let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;

    let verify_start = Instant::now();
    let tactic_sequence = normalized_tactic_sequence(&params.tactic_sequence);
    let mut proof_state = InternalProofState::new(env.clone(), target.clone());
    let mut rewritten_tactics = Vec::with_capacity(original_tactics.len());
    let mut solved_sorries = 0usize;
    let mut sorry_goals: Vec<SorryGoalInfo> = Vec::new();
    let mut sorry_index = 0usize;

    for (index, tactic) in original_tactics.iter().enumerate() {
        if start.elapsed() > timeout {
            let filled_proof =
                render_rewritten_proof(&rewritten_tactics, &original_tactics[index..]);
            let remaining_sorries = collect_explicit_sorry_positions(&theorem, &filled_proof);
            let verify_ns = verify_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let result = build_error_result(
                Some(theorem),
                Some(filled_proof),
                original_sorries,
                remaining_sorries,
                solved_sorries,
                TimingBreakdown {
                    parse_ns,
                    elaborate_ns,
                    verify_ns,
                    total_ns: elapsed_ns,
                },
                VerifyProofError {
                    message: "timeout exceeded".to_string(),
                    position: Some(VerifyProofPosition {
                        line: index + 1,
                        col: 1,
                    }),
                    expected_type: None,
                    actual_goals: convert_goals(&proof_state, &env)
                        .into_iter()
                        .map(|goal| goal.target_pp)
                        .collect(),
                    suggestions: vec!["simplify proof or use a shorter tactic sequence".to_string()],
                },
                Some(super::trust_summary_from_ledger(
                    proof_state.trust_ledger(),
                    false,
                    0,
                )),
                sorry_goals,
            );
            return Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
        }

        if is_explicit_hole_tactic(tactic) {
            let goals_at_sorry = snapshot_sorry_goals(&proof_state, &env);
            let llm_guidance = snapshot_sorry_guidance(&proof_state, &env);
            let before_goal_count = proof_state.goals().len();
            let before_sorry_count = proof_state.trust_ledger().sorry_count;
            let mut chosen_state = None;
            let mut chosen_tactic = None;

            for candidate in &tactic_sequence {
                if start.elapsed() > timeout {
                    break;
                }

                let mut candidate_state = proof_state.clone();
                if execute_simple_tactic(&mut candidate_state, candidate, &env).is_ok()
                    && candidate_state.goals().len() < before_goal_count
                    && candidate_state.trust_ledger().sorry_count == before_sorry_count
                {
                    chosen_state = Some(candidate_state);
                    chosen_tactic = Some(candidate.clone());
                    break;
                }
            }

            if let (Some(candidate_state), Some(replacement)) = (chosen_state, chosen_tactic) {
                sorry_goals.push(SorryGoalInfo {
                    sorry_index,
                    solved: true,
                    replacement_tactic: Some(replacement.clone()),
                    state_id: None,
                    search_hints: llm_guidance.search_hints.clone(),
                    suggested_tactics: llm_guidance.suggested_tactics.clone(),
                    relevant_lemmas: llm_guidance.relevant_lemmas.clone(),
                    mathverse_candidates: llm_guidance.mathverse_candidates.clone(),
                    goals: goals_at_sorry,
                });
                proof_state = candidate_state;
                rewritten_tactics.push(replacement);
                solved_sorries += 1;
            } else {
                // Cache the proof state at this unsolved sorry so callers can
                // resume interactive tactic application via `applyTactic`.
                let cached_id =
                    state
                        .proof_cache
                        .insert(proof_state.clone(), None, None, sorry_index as u32);
                sorry_goals.push(SorryGoalInfo {
                    sorry_index,
                    solved: false,
                    replacement_tactic: None,
                    state_id: Some(cached_id),
                    search_hints: llm_guidance.search_hints,
                    suggested_tactics: llm_guidance.suggested_tactics,
                    relevant_lemmas: llm_guidance.relevant_lemmas,
                    mathverse_candidates: llm_guidance.mathverse_candidates,
                    goals: goals_at_sorry,
                });
                if let Err(error) = execute_simple_tactic(&mut proof_state, tactic, &env) {
                    let filled_proof =
                        render_rewritten_proof(&rewritten_tactics, &original_tactics[index..]);
                    let remaining_sorries =
                        collect_explicit_sorry_positions(&theorem, &filled_proof);
                    let verify_ns = verify_start.elapsed().as_nanos() as u64;
                    let elapsed_ns = start.elapsed().as_nanos() as u64;
                    let result = build_error_result(
                        Some(theorem),
                        Some(filled_proof),
                        original_sorries,
                        remaining_sorries,
                        solved_sorries,
                        TimingBreakdown {
                            parse_ns,
                            elaborate_ns,
                            verify_ns,
                            total_ns: elapsed_ns,
                        },
                        VerifyProofError {
                            message: format!("original sorry failed to replay: {error}"),
                            position: Some(VerifyProofPosition {
                                line: index + 1,
                                col: 1,
                            }),
                            expected_type: None,
                            actual_goals: convert_goals(&proof_state, &env)
                                .into_iter()
                                .map(|goal| goal.target_pp)
                                .collect(),
                            suggestions: vec!["check theorem prelude and sorry support".to_string()],
                        },
                        Some(super::trust_summary_from_ledger(
                            proof_state.trust_ledger(),
                            false,
                            0,
                        )),
                        sorry_goals,
                    );
                    return Response::success_typed(id.clone(), &result).unwrap_or_else(|e| {
                        Response::error(id, RpcError::internal_error(e.to_string()))
                    });
                }
                rewritten_tactics.push(tactic.clone());
            }

            sorry_index += 1;
            continue;
        }

        if let Err(error) = execute_simple_tactic(&mut proof_state, tactic, &env) {
            let filled_proof =
                render_rewritten_proof(&rewritten_tactics, &original_tactics[index..]);
            let remaining_sorries = collect_explicit_sorry_positions(&theorem, &filled_proof);
            let verify_ns = verify_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let goals = convert_goals(&proof_state, &env);
            let result = build_error_result(
                Some(theorem),
                Some(filled_proof),
                original_sorries,
                remaining_sorries,
                solved_sorries,
                TimingBreakdown {
                    parse_ns,
                    elaborate_ns,
                    verify_ns,
                    total_ns: elapsed_ns,
                },
                VerifyProofError {
                    message: format!("tactic '{tactic}' failed: {error}"),
                    position: Some(VerifyProofPosition {
                        line: index + 1,
                        col: 1,
                    }),
                    expected_type: goals.first().map(|goal| goal.target_pp.clone()),
                    actual_goals: goals.into_iter().map(|goal| goal.target_pp).collect(),
                    suggestions: generate_tactic_suggestions(tactic),
                },
                Some(super::trust_summary_from_ledger(
                    proof_state.trust_ledger(),
                    false,
                    0,
                )),
                sorry_goals,
            );
            return Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
        }

        rewritten_tactics.push(tactic.clone());
    }

    let filled_proof = rewritten_tactics.join("\n");
    let remaining_sorries = collect_explicit_sorry_positions(&theorem, &filled_proof);
    let verify_ns = verify_start.elapsed().as_nanos() as u64;
    let elapsed_ns = start.elapsed().as_nanos() as u64;
    let timing = Some(TimingBreakdown {
        parse_ns,
        elaborate_ns,
        verify_ns,
        total_ns: elapsed_ns,
    });

    if proof_state.is_complete() {
        let closed_proof = proof_state.closed_proof();
        let verified = if remaining_sorries.is_empty() {
            super::verify_closed_proof(&env, &target, closed_proof.as_ref())
        } else {
            false
        };
        let trust_summary = super::trust_summary_from_ledger_with_closed_proof(
            proof_state.trust_ledger(),
            closed_proof.as_ref(),
            verified,
            0,
        );
        let result = FillSorriesResult {
            verified,
            theorem: Some(theorem),
            filled_proof: Some(filled_proof),
            original_sorries,
            remaining_sorries,
            solved_sorries,
            time_ns: elapsed_ns,
            timing,
            error: None,
            trust_summary: Some(trust_summary),
            // Part of #3221: extract kernel proof term for promotion pipeline.
            proof_term: if verified {
                closed_proof.as_ref().map(format_expr)
            } else {
                None
            },
            sorry_goals,
        };
        return Response::success_typed(id.clone(), &result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
    }

    let goals = convert_goals(&proof_state, &env);
    let result = FillSorriesResult {
        verified: false,
        theorem: Some(theorem),
        filled_proof: Some(filled_proof),
        original_sorries,
        remaining_sorries,
        solved_sorries,
        time_ns: elapsed_ns,
        timing,
        error: Some(VerifyProofError {
            message: "proof incomplete".to_string(),
            position: None,
            expected_type: goals.first().map(|goal| goal.target_pp.clone()),
            actual_goals: goals.into_iter().map(|goal| goal.target_pp).collect(),
            suggestions: vec!["proof does not close all goals".to_string()],
        }),
        trust_summary: Some(super::trust_summary_from_ledger(
            proof_state.trust_ledger(),
            false,
            0,
        )),
        proof_term: None,
        sorry_goals,
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}
