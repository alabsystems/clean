// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Handler for composeProof: splice per-sorry replacement tactics and verify.
//!
//! Closes the Pantograph feedback loop: after `fillSorries` returns unsolved
//! sorry goals and the caller discovers working tactics via `applyTactic`,
//! `composeProof` splices those tactics back into the proof and verifies the
//! complete result in a single call.

use super::fill_sorries_support::collect_explicit_sorry_positions;
use super::parse_lean::{is_explicit_hole_tactic, parse_lean_file};
use super::types::*;
use crate::handlers::helpers::{generate_tactic_suggestions, parse_tactic_script};
use crate::handlers::state::ServerState;
use crate::handlers::tactic::execute_simple_tactic;
use crate::proof_state::convert_goals;
use crate::rpc::{RequestId, Response, RpcError};
use clean_elab::elaborate;
use clean_elab::tactic::ProofState as InternalProofState;
use clean_parser::parse_expr_with_tactics_exact;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, Instant};
use tracing::instrument;

/// A per-sorry replacement tactic discovered via the interactive
/// `applyTactic` feedback loop.
#[derive(Debug, Clone, Deserialize)]
pub struct SorryReplacement {
    /// 0-indexed sorry number matching `SorryGoalInfo.sorry_index`.
    pub sorry_index: usize,
    /// Tactic (or semicolon-separated tactic sequence) to replace this sorry.
    pub tactic: String,
}

/// Request parameters for `composeProof`.
#[derive(Debug, Clone, Deserialize)]
pub struct ComposeProofParams {
    /// Complete Lean file content (same content passed to `fillSorries`).
    pub content: String,
    /// Per-sorry replacement tactics. Sorry indices not listed here remain as
    /// `sorry` in the output (and count toward `remaining_sorries`).
    pub replacements: Vec<SorryReplacement>,
    /// Optional timeout in milliseconds.
    pub timeout_ms: Option<u64>,
}

/// Result of proof composition and verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComposeProofResult {
    /// Whether the composed proof closes all goals and kernel-checks.
    pub verified: bool,
    /// Rewritten tactic script with replacements applied.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub composed_proof: Option<String>,
    /// Extracted theorem information.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub theorem: Option<ExtractedTheorem>,
    /// Remaining `sorry` positions in the composed proof.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub remaining_sorries: Vec<SorryLocation>,
    /// Number of sorry holes that were replaced by caller-provided tactics.
    pub replaced_count: usize,
    /// Total time in nanoseconds.
    pub time_ns: u64,
    /// Timing breakdown.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timing: Option<TimingBreakdown>,
    /// Error if composition or verification failed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<VerifyProofError>,
    /// Axiom usage summary for the composed proof.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_summary: Option<TrustSummary>,
}

/// Splice caller-provided replacement tactics into a proof and verify.
///
/// This is the complement of `fillSorries`: where `fillSorries` auto-discovers
/// tactics for sorry holes, `composeProof` uses caller-provided tactics
/// (typically discovered via the `applyTactic` interactive loop).
#[instrument(skip(state))]
pub async fn handle_compose_proof(
    state: &ServerState,
    id: RequestId,
    params: ComposeProofParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));

    // Build replacement lookup: sorry_index → tactic
    let replacement_map: HashMap<usize, &str> = params
        .replacements
        .iter()
        .map(|r| (r.sorry_index, r.tactic.as_str()))
        .collect();

    // --- Parse ---
    let parse_start = Instant::now();
    let theorem = match parse_lean_file(&params.content) {
        Ok((theorem, _)) => theorem,
        Err(error) => {
            return error_response(
                id,
                start,
                &format!("failed to parse file: {error}"),
                vec!["check Lean syntax".into()],
            );
        }
    };
    let parse_ns = parse_start.elapsed().as_nanos() as u64;

    let Some(theorem) = theorem else {
        return error_response(
            id,
            start,
            "no theorem found in file",
            vec!["file must contain theorem or lemma declaration".into()],
        );
    };

    let original_tactics = parse_tactic_script(&theorem.original_proof);

    // --- Elaborate ---
    let initialize_start = Instant::now();
    if let Err(error) = super::initialize_verify_file_env(state).await {
        let elapsed_ns = start.elapsed().as_nanos() as u64;
        return compose_error_response(
            id,
            Some(theorem),
            Some(original_tactics.join("\n")),
            0,
            TimingBreakdown {
                parse_ns,
                elaborate_ns: 0,
                verify_ns: 0,
                total_ns: elapsed_ns,
            },
            &format!("failed to initialize verification environment: {error}"),
            vec!["check the server's kernel environment".into()],
        );
    }
    // Environment construction is prerequisite setup, not proof execution.
    // Keep it in reported wall-clock latency without consuming the caller's
    // parsing/elaboration/replay budget.
    let effective_timeout = timeout.saturating_add(initialize_start.elapsed());

    let elaborate_start = Instant::now();
    let surface_expr = match parse_expr_with_tactics_exact(&theorem.goal, &state.tactic_patterns) {
        Ok(expr) => expr,
        Err(error) => {
            let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            return compose_error_response(
                id,
                Some(theorem),
                None,
                0,
                TimingBreakdown {
                    parse_ns,
                    elaborate_ns,
                    verify_ns: 0,
                    total_ns: elapsed_ns,
                },
                &format!("failed to parse goal: {error}"),
                vec!["goal type may use unknown Mathlib types".into()],
            );
        }
    };

    let env = state.env.read().await;
    let target = match elaborate(&env, &surface_expr) {
        Ok(expr) => expr,
        Err(error) => {
            let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            return compose_error_response(
                id,
                Some(theorem),
                None,
                0,
                TimingBreakdown {
                    parse_ns,
                    elaborate_ns,
                    verify_ns: 0,
                    total_ns: elapsed_ns,
                },
                &format!("failed to elaborate goal: {error}"),
                vec!["goal type may require Mathlib context".into()],
            );
        }
    };
    let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;

    // --- Replay with replacements ---
    let verify_start = Instant::now();
    let mut proof_state = InternalProofState::new(env.clone(), target.clone());
    let mut rewritten_tactics = Vec::with_capacity(original_tactics.len());
    let mut replaced_count = 0usize;
    let mut sorry_index = 0usize;

    for (index, tactic) in original_tactics.iter().enumerate() {
        if start.elapsed() > effective_timeout {
            let composed_proof = rewritten_tactics
                .iter()
                .cloned()
                .chain(original_tactics[index..].iter().cloned())
                .collect::<Vec<_>>()
                .join("\n");
            let verify_ns = verify_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            return compose_error_response(
                id,
                Some(theorem),
                Some(composed_proof),
                replaced_count,
                TimingBreakdown {
                    parse_ns,
                    elaborate_ns,
                    verify_ns,
                    total_ns: elapsed_ns,
                },
                "timeout exceeded",
                vec!["simplify proof or increase timeout".into()],
            );
        }

        if is_explicit_hole_tactic(tactic) {
            if let Some(replacement) = replacement_map.get(&sorry_index) {
                // Apply the caller-provided replacement tactic
                let replacement = replacement.trim().to_string();
                match execute_simple_tactic(&mut proof_state, &replacement, &env) {
                    Ok(()) => {
                        rewritten_tactics.push(replacement);
                        replaced_count += 1;
                    }
                    Err(error) => {
                        let composed_proof = rewritten_tactics
                            .iter()
                            .cloned()
                            .chain(original_tactics[index..].iter().cloned())
                            .collect::<Vec<_>>()
                            .join("\n");
                        let remaining_sorries =
                            collect_explicit_sorry_positions(&theorem, &composed_proof);
                        let verify_ns = verify_start.elapsed().as_nanos() as u64;
                        let elapsed_ns = start.elapsed().as_nanos() as u64;
                        let goals = convert_goals(&proof_state, &env);
                        let result = ComposeProofResult {
                            verified: false,
                            composed_proof: Some(composed_proof),
                            theorem: Some(theorem),
                            remaining_sorries,
                            replaced_count,
                            time_ns: elapsed_ns,
                            timing: Some(TimingBreakdown {
                                parse_ns,
                                elaborate_ns,
                                verify_ns,
                                total_ns: elapsed_ns,
                            }),
                            error: Some(VerifyProofError {
                                message: format!(
                                    "replacement tactic for sorry #{sorry_index} failed: {error}"
                                ),
                                position: Some(VerifyProofPosition {
                                    line: index + 1,
                                    col: 1,
                                }),
                                expected_type: goals.first().map(|g| g.target_pp.clone()),
                                actual_goals: goals.into_iter().map(|g| g.target_pp).collect(),
                                suggestions: vec![
                                    "verify the replacement tactic works via applyTactic first"
                                        .into(),
                                ],
                            }),
                            trust_summary: Some(super::trust_summary_from_ledger(
                                proof_state.trust_ledger(),
                                false,
                                0,
                            )),
                        };
                        return Response::success_typed(id.clone(), &result).unwrap_or_else(|e| {
                            Response::error(id, RpcError::internal_error(e.to_string()))
                        });
                    }
                }
            } else {
                // No replacement provided — keep the original sorry
                if let Err(error) = execute_simple_tactic(&mut proof_state, tactic, &env) {
                    let composed_proof = rewritten_tactics
                        .iter()
                        .cloned()
                        .chain(original_tactics[index..].iter().cloned())
                        .collect::<Vec<_>>()
                        .join("\n");
                    let verify_ns = verify_start.elapsed().as_nanos() as u64;
                    let elapsed_ns = start.elapsed().as_nanos() as u64;
                    return compose_error_response(
                        id,
                        Some(theorem),
                        Some(composed_proof),
                        replaced_count,
                        TimingBreakdown {
                            parse_ns,
                            elaborate_ns,
                            verify_ns,
                            total_ns: elapsed_ns,
                        },
                        &format!("original sorry failed to replay: {error}"),
                        vec!["check theorem prelude and sorry support".into()],
                    );
                }
                rewritten_tactics.push(tactic.clone());
            }
            sorry_index += 1;
            continue;
        }

        // Non-sorry tactic — replay verbatim
        if let Err(error) = execute_simple_tactic(&mut proof_state, tactic, &env) {
            let composed_proof = rewritten_tactics
                .iter()
                .cloned()
                .chain(original_tactics[index..].iter().cloned())
                .collect::<Vec<_>>()
                .join("\n");
            let verify_ns = verify_start.elapsed().as_nanos() as u64;
            let elapsed_ns = start.elapsed().as_nanos() as u64;
            return compose_error_response(
                id,
                Some(theorem),
                Some(composed_proof),
                replaced_count,
                TimingBreakdown {
                    parse_ns,
                    elaborate_ns,
                    verify_ns,
                    total_ns: elapsed_ns,
                },
                &format!("tactic '{tactic}' failed: {error}"),
                generate_tactic_suggestions(tactic),
            );
        }

        rewritten_tactics.push(tactic.clone());
    }

    // --- Verify the composed result ---
    let composed_proof = rewritten_tactics.join("\n");
    let remaining_sorries = collect_explicit_sorry_positions(&theorem, &composed_proof);
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
        let result = ComposeProofResult {
            verified,
            composed_proof: Some(composed_proof),
            theorem: Some(theorem),
            remaining_sorries,
            replaced_count,
            time_ns: elapsed_ns,
            timing,
            error: None,
            trust_summary: Some(trust_summary),
        };
        return Response::success_typed(id.clone(), &result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
    }

    // Proof incomplete — goals remain
    let goals = convert_goals(&proof_state, &env);
    let result = ComposeProofResult {
        verified: false,
        composed_proof: Some(composed_proof),
        theorem: Some(theorem),
        remaining_sorries,
        replaced_count,
        time_ns: elapsed_ns,
        timing,
        error: Some(VerifyProofError {
            message: "proof incomplete".into(),
            position: None,
            expected_type: goals.first().map(|g| g.target_pp.clone()),
            actual_goals: goals.into_iter().map(|g| g.target_pp).collect(),
            suggestions: vec!["proof does not close all goals".into()],
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

/// Minimal error response for early failures (parse, no theorem).
fn error_response(
    id: RequestId,
    start: Instant,
    message: &str,
    suggestions: Vec<String>,
) -> Response {
    let elapsed_ns = start.elapsed().as_nanos() as u64;
    let result = ComposeProofResult {
        verified: false,
        composed_proof: None,
        theorem: None,
        remaining_sorries: vec![],
        replaced_count: 0,
        time_ns: elapsed_ns,
        timing: Some(TimingBreakdown {
            parse_ns: elapsed_ns,
            elaborate_ns: 0,
            verify_ns: 0,
            total_ns: elapsed_ns,
        }),
        error: Some(VerifyProofError {
            message: message.into(),
            position: None,
            expected_type: None,
            actual_goals: vec![],
            suggestions,
        }),
        trust_summary: None,
    };
    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Error response with partial composition context.
fn compose_error_response(
    id: RequestId,
    theorem: Option<ExtractedTheorem>,
    composed_proof: Option<String>,
    replaced_count: usize,
    timing: TimingBreakdown,
    message: &str,
    suggestions: Vec<String>,
) -> Response {
    let remaining_sorries = match (&theorem, &composed_proof) {
        (Some(thm), Some(proof)) => collect_explicit_sorry_positions(thm, proof),
        _ => vec![],
    };
    let result = ComposeProofResult {
        verified: false,
        composed_proof,
        theorem,
        remaining_sorries,
        replaced_count,
        time_ns: timing.total_ns,
        timing: Some(timing),
        error: Some(VerifyProofError {
            message: message.into(),
            position: None,
            expected_type: None,
            actual_goals: vec![],
            suggestions,
        }),
        trust_summary: None,
    };
    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}
