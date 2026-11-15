// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Handler for verifyFile: full Lean file verification (FATE benchmark format).

use super::parse_lean::parse_lean_file;
use super::types::*;
use crate::handlers::core::{run_with_env, WorkEnv};
use crate::handlers::helpers::{generate_tactic_suggestions, parse_tactic_script};
use crate::handlers::state::ServerState;
use crate::handlers::tactic;
use crate::handlers::work::WorkError;
use crate::rpc::{RequestId, Response, RpcError};
use clean_elab::elaborate;
use clean_kernel::Environment;
use clean_parser::parse_expr_with_tactics_exact;
use std::time::{Duration, Instant};
use tactic::execute_simple_tactic;
use tracing::instrument;

/// Handle verifyFile request
///
/// Parses a complete Lean file (FATE format) and:
/// 1. Extracts theorem/lemma declarations
/// 2. Identifies sorry locations
/// 3. If proof provided, verifies it against the theorem goal
///
/// This is Phase 1 of FATE support - syntax parsing without full Mathlib.
#[instrument(skip(state, params), fields(content_bytes = params.content.len()))]
pub async fn handle_verify_file(
    state: &ServerState,
    id: RequestId,
    params: VerifyFileParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));

    // Parse the file to extract theorem and sorries: request work, on the pool
    // under the request's deadline (`super::parse_on_pool`).
    let content = params.content;
    let parsed = super::parse_on_pool(state, start, timeout, move || {
        let parse_start = Instant::now();
        let parsed = parse_lean_file(&content);
        (parsed, parse_start.elapsed().as_nanos() as u64)
    })
    .await;
    let (parsed, parse_ns) = match parsed {
        Ok(parsed) => parsed,
        Err(error) => return super::replay_response::<()>(id, timeout, Err(error)),
    };
    let (theorem, sorries) = match parsed {
        Ok((t, s)) => (t, s),
        Err(e) => {
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let result = VerifyFileResult {
                verified: false,
                theorem: None,
                sorries: vec![],
                time_ns: elapsed_ns,
                timing: Some(TimingBreakdown {
                    parse_ns,
                    elaborate_ns: 0,
                    verify_ns: 0,
                    total_ns: elapsed_ns,
                }),
                error: Some(VerifyProofError {
                    message: format!("failed to parse file: {}", e),
                    position: None,
                    expected_type: None,
                    actual_goals: vec![],
                    suggestions: vec!["check Lean syntax".to_string()],
                }),
                trust_summary: None,
            };
            return Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
        }
    };

    // Initialize FATE Mathlib stubs if needed (lazy initialization)
    // This ensures types like Prime, IsPrincipalIdealRing, Polynomial are available
    // for elaboration even when no proof is provided.
    let initialize_start = Instant::now();
    if let Err(error) = super::initialize_verify_file_env(state).await {
        let elapsed_ns = start.elapsed().as_nanos() as u64;
        let result = VerifyFileResult {
            verified: false,
            theorem,
            sorries,
            time_ns: elapsed_ns,
            timing: Some(TimingBreakdown {
                parse_ns,
                elaborate_ns: 0,
                verify_ns: 0,
                total_ns: elapsed_ns,
            }),
            error: Some(VerifyProofError {
                message: format!("failed to initialize verification environment: {error}"),
                position: None,
                expected_type: None,
                actual_goals: vec![],
                suggestions: vec!["check the server's kernel environment".to_string()],
            }),
            trust_summary: None,
        };
        // The set-up is not charged to the timeout, as below.
        let effective_timeout = timeout.saturating_add(initialize_start.elapsed());
        return holes_answer(state, id, start, effective_timeout, result).await;
    }
    // Environment construction is prerequisite setup, not proof execution.
    // Keep it in reported wall-clock latency without consuming the caller's
    // parsing/elaboration/replay budget.
    let effective_timeout = timeout.saturating_add(initialize_start.elapsed());

    // If no proof provided, just return extracted info
    let proof = match &params.proof {
        Some(p) => p.clone(),
        None => {
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let expected_type = theorem.as_ref().map(|t| t.goal.clone());
            let result = VerifyFileResult {
                verified: false,
                theorem,
                sorries,
                time_ns: elapsed_ns,
                timing: Some(TimingBreakdown {
                    parse_ns,
                    elaborate_ns: 0,
                    verify_ns: 0,
                    total_ns: elapsed_ns,
                }),
                error: Some(VerifyProofError {
                    message: "no proof provided".to_string(),
                    position: None,
                    expected_type,
                    actual_goals: vec![],
                    suggestions: vec!["provide a proof parameter".to_string()],
                }),
                trust_summary: None,
            };
            return holes_answer(state, id, start, effective_timeout, result).await;
        }
    };

    // Extract goal from theorem
    let goal = match &theorem {
        Some(t) => t.goal.clone(),
        None => {
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let result = VerifyFileResult {
                verified: false,
                theorem: None,
                sorries,
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
            };
            return holes_answer(state, id, start, effective_timeout, result).await;
        }
    };

    // The replay runs on the work pool, under the deadline the timeout sets
    // (environment setup above excluded, as before).
    let deadline = start.checked_add(effective_timeout);
    let remaining = effective_timeout.saturating_sub(start.elapsed());
    let job_id = id.clone();
    let outcome = tokio::time::timeout(
        remaining,
        run_with_env(state, deadline, move |held| {
            verify_file_on_pool(
                held,
                job_id,
                VerifyFileReplay {
                    theorem,
                    sorries,
                    proof,
                    goal,
                    parse_ns,
                    start,
                    effective_timeout,
                },
            )
        }),
    )
    .await
    .unwrap_or(Err(WorkError::Interrupted));
    match outcome {
        Ok(response) => response,
        Err(error) => super::replay_response::<()>(id, timeout, Err(error)),
    }
}

/// Answer `result`, which lists the file's holes, building the answer on the
/// work pool inside the request's timeout (`start` + `timeout`). The answer
/// grows with the file: a file of 10 MiB of `sorry` lines has 1,747,619 holes,
/// 91.5 MB of JSON (review of 2026-10-19), and building it on a runtime
/// worker held that worker for as long. (The transport writes it there.)
async fn holes_answer(
    state: &ServerState,
    id: RequestId,
    start: Instant,
    timeout: Duration,
    result: VerifyFileResult,
) -> Response {
    let job_id = id.clone();
    let answered = super::parse_on_pool(state, start, timeout, move || {
        holes_response(job_id, &result)
    })
    .await;
    match answered {
        Ok(response) => response,
        Err(error) => super::replay_response::<()>(id, timeout, Err(error)),
    }
}

/// The response to `result` (`holes_answer`), built on a pool thread.
fn holes_response(id: RequestId, result: &VerifyFileResult) -> Response {
    // Tests build with debug assertions, so a request path that builds it on
    // the runtime again fails every test that takes it.
    debug_assert!(
        tokio::runtime::Handle::try_current().is_err(),
        "an answer listing a file's holes was built on an async runtime's thread"
    );
    Response::success_typed(id.clone(), result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// What the replay of a `verifyFile` request needs from the request.
struct VerifyFileReplay {
    theorem: Option<ExtractedTheorem>,
    sorries: Vec<SorryLocation>,
    proof: String,
    goal: String,
    parse_ns: u64,
    start: Instant,
    effective_timeout: Duration,
}

/// Elaborate the goal and replay the proof against the held environment. Runs
/// on the work pool.
fn verify_file_on_pool(held: &WorkEnv, id: RequestId, replay: VerifyFileReplay) -> Response {
    use crate::proof_state::convert_goals;
    use clean_elab::tactic::ProofState as InternalProofState;

    let VerifyFileReplay {
        theorem,
        sorries,
        proof,
        goal,
        parse_ns,
        start,
        effective_timeout,
    } = replay;
    let elaborate_start = Instant::now();

    // Parse and elaborate the goal (with tactic patterns for Named dispatch)
    let surface_expr = match parse_expr_with_tactics_exact(&goal, &held.patterns) {
        Ok(expr) => expr,
        Err(e) => {
            let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let result = VerifyFileResult {
                verified: false,
                theorem,
                sorries,
                time_ns: elapsed_ns,
                timing: Some(TimingBreakdown {
                    parse_ns,
                    elaborate_ns,
                    verify_ns: 0,
                    total_ns: elapsed_ns,
                }),
                error: Some(VerifyProofError {
                    message: format!("failed to parse goal: {}", e),
                    position: None,
                    expected_type: None,
                    actual_goals: vec![],
                    suggestions: vec!["goal type may use unknown Mathlib types".to_string()],
                }),
                trust_summary: None,
            };
            return Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
        }
    };

    let env: &Environment = &held.env;
    let target = match elaborate(env, &surface_expr) {
        Ok(expr) => expr,
        Err(e) => {
            let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let result = VerifyFileResult {
                verified: false,
                theorem,
                sorries,
                time_ns: elapsed_ns,
                timing: Some(TimingBreakdown {
                    parse_ns,
                    elaborate_ns,
                    verify_ns: 0,
                    total_ns: elapsed_ns,
                }),
                error: Some(VerifyProofError {
                    message: format!("failed to elaborate goal: {}", e),
                    position: None,
                    expected_type: None,
                    actual_goals: vec![],
                    suggestions: vec!["goal type may require Mathlib context".to_string()],
                }),
                trust_summary: None,
            };
            return Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
        }
    };

    let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;
    let verify_start = Instant::now();

    // Create proof state and execute tactics (clone target for verification)
    let mut proof_state = InternalProofState::new(env.clone(), target.clone());

    if proof_state.is_complete() {
        let closed_proof = proof_state.closed_proof();
        let verified = if !sorries.is_empty() {
            false
        } else {
            super::verify_closed_proof(env, &target, closed_proof.as_ref())
        };
        let trust_summary = super::trust_summary_from_ledger_with_closed_proof(
            env,
            proof_state.trust_ledger(),
            closed_proof.as_ref(),
            verified,
            0,
        );
        let verify_ns = verify_start.elapsed().as_nanos() as u64;
        let elapsed_ns = start.elapsed().as_nanos() as u64;
        let result = VerifyFileResult {
            verified,
            theorem,
            sorries,
            time_ns: elapsed_ns,
            timing: Some(TimingBreakdown {
                parse_ns,
                elaborate_ns,
                verify_ns,
                total_ns: elapsed_ns,
            }),
            error: None,
            trust_summary: Some(trust_summary),
        };
        return Response::success_typed(id.clone(), &result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
    }

    // Parse and execute tactics
    let tactics = parse_tactic_script(&proof);
    let mut last_error: Option<VerifyProofError> = None;

    for (idx, tactic_str) in tactics.iter().enumerate() {
        let tactic_line = idx + 1;
        let tactic = tactic_str.trim();
        if tactic.is_empty() {
            continue;
        }

        if start.elapsed() > effective_timeout {
            let verify_ns = verify_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let result = VerifyFileResult {
                verified: false,
                theorem,
                sorries,
                time_ns: elapsed_ns,
                timing: Some(TimingBreakdown {
                    parse_ns,
                    elaborate_ns,
                    verify_ns,
                    total_ns: elapsed_ns,
                }),
                error: Some(VerifyProofError {
                    message: "timeout exceeded".to_string(),
                    position: Some(VerifyProofPosition {
                        line: tactic_line,
                        col: 1,
                    }),
                    expected_type: None,
                    actual_goals: convert_goals(&proof_state, env)
                        .into_iter()
                        .map(|g| g.target_pp)
                        .collect(),
                    suggestions: vec!["simplify proof".to_string()],
                }),
                trust_summary: None,
            };
            return Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
        }

        match execute_simple_tactic(&mut proof_state, tactic, env) {
            Ok(()) => {
                if proof_state.is_complete() {
                    break;
                }
            }
            Err(e) => {
                let goals = convert_goals(&proof_state, env);
                last_error = Some(VerifyProofError {
                    message: format!("tactic '{}' failed: {}", tactic, e),
                    position: Some(VerifyProofPosition {
                        line: tactic_line,
                        col: 1,
                    }),
                    expected_type: goals.first().map(|g| g.target_pp.clone()),
                    actual_goals: goals.into_iter().map(|g| g.target_pp).collect(),
                    suggestions: generate_tactic_suggestions(tactic),
                });
                break;
            }
        }
    }

    let verify_ns = verify_start.elapsed().as_nanos() as u64;
    let elapsed_ns = start.elapsed().as_nanos() as u64;

    let timing = Some(TimingBreakdown {
        parse_ns,
        elaborate_ns,
        verify_ns,
        total_ns: elapsed_ns,
    });

    let is_complete = proof_state.is_complete();

    if is_complete {
        let closed_proof = proof_state.closed_proof();
        let verified = if !sorries.is_empty() {
            false
        } else {
            super::verify_closed_proof(env, &target, closed_proof.as_ref())
        };
        let trust_summary = super::trust_summary_from_ledger_with_closed_proof(
            env,
            proof_state.trust_ledger(),
            closed_proof.as_ref(),
            verified,
            0,
        );
        let result = VerifyFileResult {
            verified,
            theorem,
            sorries,
            time_ns: elapsed_ns,
            timing,
            error: None,
            trust_summary: Some(trust_summary),
        };
        return Response::success_typed(id.clone(), &result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
    }

    let goals = convert_goals(&proof_state, env);
    let result = VerifyFileResult {
        verified: false,
        theorem,
        sorries,
        time_ns: elapsed_ns,
        timing,
        error: last_error.or_else(|| {
            Some(VerifyProofError {
                message: "proof incomplete".to_string(),
                position: None,
                expected_type: goals.first().map(|g| g.target_pp.clone()),
                actual_goals: goals.into_iter().map(|g| g.target_pp).collect(),
                suggestions: vec!["proof does not close all goals".to_string()],
            })
        }),
        trust_summary: Some(super::trust_summary_from_ledger(
            proof_state.trust_ledger(),
            false,
            0,
        )),
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}
