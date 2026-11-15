// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Handler for fillSorries: SorryHammer-style automatic hole filling.

use super::fill_sorries_support::{
    collect_explicit_sorry_positions, snapshot_sorry_goals, snapshot_sorry_guidance,
};
use super::parse_lean::{is_explicit_hole_tactic, parse_lean_file};
use super::types::*;
use crate::handlers::core::{run_with_env, WorkEnv};
use crate::handlers::helpers::{format_expr, generate_tactic_suggestions, parse_tactic_script};
use crate::handlers::state::ServerState;
use crate::handlers::tactic::execute_simple_tactic;
use crate::handlers::work::WorkError;
use crate::proof_state::convert_goals;
use crate::rpc::{RequestId, Response, RpcError};
use clean_elab::elaborate;
use clean_elab::tactic::ProofState as InternalProofState;
use clean_kernel::Environment;
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
#[instrument(skip(state, params), fields(content_bytes = params.content.len()))]
pub async fn handle_fill_sorries(
    state: &ServerState,
    id: RequestId,
    params: FillSorriesParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));

    // Parsing the file and its proof's script is request work: on the pool,
    // under the request's deadline (`super::parse_on_pool`).
    let content = params.content;
    let parsed = super::parse_on_pool(state, start, timeout, move || {
        let parse_start = Instant::now();
        let parsed = parse_lean_file(&content).map(|(theorem, _)| theorem);
        let parse_ns = parse_start.elapsed().as_nanos() as u64;
        let script = parsed
            .as_ref()
            .ok()
            .and_then(Option::as_ref)
            .map(|theorem| {
                let original_tactics = parse_tactic_script(&theorem.original_proof);
                let normalized_original_proof = original_tactics.join("\n");
                let original_sorries =
                    collect_explicit_sorry_positions(theorem, &normalized_original_proof);
                (
                    original_tactics,
                    normalized_original_proof,
                    original_sorries,
                )
            });
        (parsed, parse_ns, script)
    })
    .await;
    let (parsed, parse_ns, script) = match parsed {
        Ok(parsed) => parsed,
        Err(error) => return super::replay_response::<()>(id, timeout, Err(error)),
    };
    let theorem = match parsed {
        Ok(theorem) => theorem,
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

    let (Some(theorem), Some((original_tactics, normalized_original_proof, original_sorries))) =
        (theorem, script)
    else {
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

    let initialize_start = Instant::now();
    if let Err(error) = super::initialize_verify_file_env(state).await {
        let elapsed_ns = start.elapsed().as_nanos() as u64;
        let result = build_error_result(
            Some(theorem),
            Some(normalized_original_proof),
            original_sorries,
            vec![],
            0,
            TimingBreakdown {
                parse_ns,
                elaborate_ns: 0,
                verify_ns: 0,
                total_ns: elapsed_ns,
            },
            VerifyProofError {
                message: format!("failed to initialize verification environment: {error}"),
                position: None,
                expected_type: None,
                actual_goals: vec![],
                suggestions: vec!["check the server's kernel environment".to_string()],
            },
            None,
            vec![],
        );
        return Response::success_typed(id.clone(), &result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
    }
    // Environment construction is prerequisite setup, not proof execution.
    // Keep it in reported wall-clock latency without consuming the caller's
    // parsing/elaboration/replay budget.
    let effective_timeout = timeout.saturating_add(initialize_start.elapsed());

    // The replay runs on the work pool, under the deadline the timeout sets
    // (environment setup above excluded, as before). It caches no proof
    // state itself: the unsolved sorries' states come back with the result and
    // are cached here, so a replay the deadline interrupted caches nothing.
    let deadline = start.checked_add(effective_timeout);
    let remaining = effective_timeout.saturating_sub(start.elapsed());
    let tactic_sequence = params.tactic_sequence;
    let outcome = tokio::time::timeout(
        remaining,
        run_with_env(state, deadline, move |held| {
            let mut unsolved = Vec::new();
            let result = fill_sorries_on_pool(
                held,
                FillSorriesReplay {
                    theorem,
                    normalized_original_proof,
                    original_sorries,
                    original_tactics,
                    tactic_sequence,
                    parse_ns,
                    start,
                    effective_timeout,
                },
                &mut unsolved,
            );
            (result, unsolved)
        }),
    )
    .await
    .unwrap_or(Err(WorkError::Interrupted))
    .map(|(mut result, unsolved)| {
        for UnsolvedSorry {
            goal_position,
            state: proof_state,
            sorry_index,
        } in unsolved
        {
            let cached_id = state
                .proof_cache
                .insert(proof_state, None, None, sorry_index);
            if let Some(goal) = result.sorry_goals.get_mut(goal_position) {
                goal.state_id = Some(cached_id);
            }
        }
        result
    });
    super::replay_response(id, timeout, outcome)
}

/// What the replay of a `fillSorries` request needs from the request.
struct FillSorriesReplay {
    theorem: ExtractedTheorem,
    normalized_original_proof: String,
    original_sorries: Vec<SorryLocation>,
    original_tactics: Vec<String>,
    tactic_sequence: Vec<String>,
    parse_ns: u64,
    start: Instant,
    effective_timeout: Duration,
}

/// The proof state at an unsolved sorry, cached for `applyTactic` once the
/// replay has answered: it fills `sorry_goals[goal_position].state_id`.
struct UnsolvedSorry {
    goal_position: usize,
    state: InternalProofState,
    sorry_index: u32,
}

/// Elaborate the goal and replay the proof, filling sorries, against the held
/// environment. Runs on the work pool.
fn fill_sorries_on_pool(
    held: &WorkEnv,
    replay: FillSorriesReplay,
    unsolved: &mut Vec<UnsolvedSorry>,
) -> FillSorriesResult {
    let FillSorriesReplay {
        theorem,
        normalized_original_proof,
        original_sorries,
        original_tactics,
        tactic_sequence,
        parse_ns,
        start,
        effective_timeout,
    } = replay;

    let elaborate_start = Instant::now();
    let surface_expr = match parse_expr_with_tactics_exact(&theorem.goal, &held.patterns) {
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
            return result;
        }
    };

    let env: &Environment = &held.env;
    let target = match elaborate(env, &surface_expr) {
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
            return result;
        }
    };
    let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;

    let verify_start = Instant::now();
    let tactic_sequence = normalized_tactic_sequence(&tactic_sequence);
    let mut proof_state = InternalProofState::new(env.clone(), target.clone());
    let mut rewritten_tactics = Vec::with_capacity(original_tactics.len());
    let mut solved_sorries = 0usize;
    let mut sorry_goals: Vec<SorryGoalInfo> = Vec::new();
    let mut sorry_index = 0usize;

    for (index, tactic) in original_tactics.iter().enumerate() {
        if start.elapsed() > effective_timeout {
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
                    actual_goals: convert_goals(&proof_state, env)
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
            return result;
        }

        if is_explicit_hole_tactic(tactic) {
            let goals_at_sorry = snapshot_sorry_goals(&proof_state, env);
            let llm_guidance = snapshot_sorry_guidance(&proof_state, env);
            let before_goal_count = proof_state.goals().len();
            let before_sorry_count = proof_state.trust_ledger().sorry_count;
            let mut chosen_state = None;
            let mut chosen_tactic = None;

            for candidate in &tactic_sequence {
                if start.elapsed() > effective_timeout {
                    break;
                }

                let mut candidate_state = proof_state.clone();
                if execute_simple_tactic(&mut candidate_state, candidate, env).is_ok()
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
                // The proof state at this unsolved sorry is cached, once the
                // replay has answered, so callers can resume interactive
                // tactic application via `applyTactic`.
                unsolved.push(UnsolvedSorry {
                    goal_position: sorry_goals.len(),
                    state: proof_state.clone(),
                    sorry_index: sorry_index as u32,
                });
                sorry_goals.push(SorryGoalInfo {
                    sorry_index,
                    solved: false,
                    replacement_tactic: None,
                    state_id: None,
                    search_hints: llm_guidance.search_hints,
                    suggested_tactics: llm_guidance.suggested_tactics,
                    relevant_lemmas: llm_guidance.relevant_lemmas,
                    mathverse_candidates: llm_guidance.mathverse_candidates,
                    goals: goals_at_sorry,
                });
                if let Err(error) = execute_simple_tactic(&mut proof_state, tactic, env) {
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
                            actual_goals: convert_goals(&proof_state, env)
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
                    return result;
                }
                rewritten_tactics.push(tactic.clone());
            }

            sorry_index += 1;
            continue;
        }

        if let Err(error) = execute_simple_tactic(&mut proof_state, tactic, env) {
            let filled_proof =
                render_rewritten_proof(&rewritten_tactics, &original_tactics[index..]);
            let remaining_sorries = collect_explicit_sorry_positions(&theorem, &filled_proof);
            let verify_ns = verify_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let goals = convert_goals(&proof_state, env);
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
            return result;
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
            super::verify_closed_proof(env, &target, closed_proof.as_ref())
        } else {
            false
        };
        let trust_summary = super::trust_summary_from_ledger_with_closed_proof(
            env,
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
        return result;
    }

    let goals = convert_goals(&proof_state, env);
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

    result
}
