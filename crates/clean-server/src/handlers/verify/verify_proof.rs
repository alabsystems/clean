// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Handler for verifyProof: single proof verification for LLM integration.

use super::types::*;
use crate::handlers::core::{run_with_env, WorkEnv};
use crate::handlers::helpers::{
    generate_tactic_suggestions, parse_error_col, parse_error_line, parse_tactic_script,
};
use crate::handlers::state::ServerState;
use crate::handlers::tactic;
use crate::handlers::work::WorkError;
use crate::rpc::{RequestId, Response};
use clean_elab::elaborate;
use clean_kernel::Environment;
use clean_parser::parse_expr_with_tactics_exact;
use std::time::{Duration, Instant};
use tactic::execute_simple_tactic;
use tracing::instrument;

/// Handle verifyProof request
///
/// Verifies a complete proof against a goal in one call. The proof can be
/// a tactic script (separated by `;` or newlines) or a term proof.
///
/// This is the main endpoint for verification-guided LLM proof search.
/// Includes TimingBreakdown for delta measurement per 4/delta bound theorem.
#[instrument(skip(state, params))]
pub async fn handle_verify_proof(
    state: &ServerState,
    id: RequestId,
    params: VerifyProofParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));
    let deadline = start.checked_add(timeout);

    let outcome = tokio::time::timeout(
        timeout,
        run_with_env(state, deadline, move |held| {
            verify_proof_on_pool(held, &params, start, timeout)
        }),
    )
    .await
    .unwrap_or(Err(WorkError::Interrupted));
    super::replay_response(id, timeout, outcome)
}

/// Parse, elaborate and replay the proof against the held environment. Runs on
/// the work pool.
fn verify_proof_on_pool(
    held: &WorkEnv,
    params: &VerifyProofParams,
    start: Instant,
    timeout: Duration,
) -> VerifyProofResult {
    use crate::proof_state::convert_goals;
    use clean_elab::tactic::ProofState as InternalProofState;

    // Track timing breakdown
    let parse_start = Instant::now();

    // Parse the goal (with tactic patterns for Named dispatch)
    let surface_expr = match parse_expr_with_tactics_exact(&params.goal, &held.patterns) {
        Ok(expr) => expr,
        Err(e) => {
            let parse_ns = parse_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let result = VerifyProofResult {
                verified: false,
                certificate: None,
                time_ns: elapsed_ns,
                timing: Some(TimingBreakdown {
                    parse_ns,
                    elaborate_ns: 0,
                    verify_ns: 0,
                    total_ns: elapsed_ns,
                }),
                error: Some(VerifyProofError {
                    message: format!("failed to parse goal: {}", e),
                    position: parse_error_line(&e).map(|line| VerifyProofPosition {
                        line,
                        col: parse_error_col(&e).unwrap_or(1),
                    }),
                    expected_type: None,
                    actual_goals: vec![],
                    suggestions: vec!["check goal syntax".to_string()],
                }),
                trust_summary: None,
            };
            return result;
        }
    };

    let parse_ns = parse_start.elapsed().as_nanos() as u64;
    let elaborate_start = Instant::now();

    // Elaborate the goal expression
    let env: &Environment = &held.env;
    let target = match elaborate(env, &surface_expr) {
        Ok(expr) => expr,
        Err(e) => {
            let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let result = VerifyProofResult {
                verified: false,
                certificate: None,
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
                    suggestions: vec!["check type syntax".to_string()],
                }),
                trust_summary: None,
            };
            return result;
        }
    };

    let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;
    let verify_start = Instant::now();

    // Create proof state (clone target so it remains available for verification)
    let mut proof_state = InternalProofState::new(env.clone(), target.clone());

    // Check for trivial proof (goal is already solved)
    if proof_state.is_complete() {
        let closed_proof = proof_state.closed_proof();
        let (verified, trust_summary) = super::verify_closed_proof_with_trust_summary(
            env,
            &target,
            closed_proof.as_ref(),
            proof_state.trust_ledger(),
            0,
        );
        let verify_ns = verify_start.elapsed().as_nanos() as u64;
        let elapsed_ns = start.elapsed().as_nanos() as u64;
        let result = VerifyProofResult {
            verified,
            certificate: None,
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
        return result;
    }

    // Parse and execute tactics
    let tactics = parse_tactic_script(&params.proof);
    let mut last_error: Option<VerifyProofError> = None;

    for (idx, tactic_str) in tactics.iter().enumerate() {
        let tactic_line = idx + 1; // 1-indexed line number
        let tactic = tactic_str.trim();
        if tactic.is_empty() {
            continue;
        }

        // Check timeout
        if start.elapsed() > timeout {
            let verify_ns = verify_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            let result = VerifyProofResult {
                verified: false,
                certificate: None,
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
            return result;
        }

        // Execute tactic
        match execute_simple_tactic(&mut proof_state, tactic, env) {
            Ok(()) => {
                // Tactic succeeded
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

    // Check if proof is complete — kernel type-check before claiming verified (#2179)
    let is_complete = proof_state.is_complete();

    if is_complete {
        let closed_proof = proof_state.closed_proof();
        let (verified, trust_summary) = super::verify_closed_proof_with_trust_summary(
            env,
            &target,
            closed_proof.as_ref(),
            proof_state.trust_ledger(),
            0,
        );
        let result = VerifyProofResult {
            verified,
            certificate: None,
            time_ns: elapsed_ns,
            timing,
            error: None,
            trust_summary: Some(trust_summary),
        };
        return result;
    }

    // Proof incomplete
    let goals = convert_goals(&proof_state, env);
    let result = VerifyProofResult {
        verified: false,
        certificate: None,
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

    result
}
