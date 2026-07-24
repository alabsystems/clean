// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Handler for verifyProofBatch: parallel batch proof verification.

use super::types::*;
use crate::handlers::helpers::{
    generate_tactic_suggestions, parse_error_col, parse_error_line, parse_tactic_script,
};
use crate::handlers::state::ServerState;
use crate::handlers::tactic;
use crate::rpc::{RequestId, Response, RpcError};
use clean_elab::elaborate;
use clean_parser::parse_expr_with_tactics_exact;
use std::time::{Duration, Instant};
use tactic::execute_simple_tactic;
use tracing::instrument;

/// Handle verifyProofBatch request
///
/// Verifies multiple proofs in parallel using rayon. Critical for FATE-Eval
/// benchmark throughput (28s -> 28ms for 28K proofs).
///
/// Each proof is verified independently with timing breakdown for delta measurement.
#[instrument(skip(state))]
pub async fn handle_verify_proof_batch(
    state: &ServerState,
    id: RequestId,
    params: VerifyProofBatchParams,
) -> Response {
    use crate::proof_state::convert_goals;
    use clean_elab::tactic::ProofState as InternalProofState;
    use rayon::prelude::*;

    let start = Instant::now();

    // Handle empty batch
    if params.proofs.is_empty() {
        let result = VerifyProofBatchResult {
            results: vec![],
            total_time_ns: 0,
            throughput_ops_sec: 0.0,
            stats: VerifyProofBatchStats {
                verified_count: 0,
                failed_count: 0,
                avg_time_ns: 0,
                min_time_ns: 0,
                max_time_ns: 0,
            },
        };
        return Response::success_typed(id.clone(), &result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())));
    }

    // Configure thread pool if specified
    let pool = params.threads.map(|n| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(n.max(1))
            .build()
            .ok()
    });

    // Get environment snapshot (shared across all items)
    let env = state.env.read().await.clone();
    let default_timeout = state.default_timeout_ms;

    // Per-item timeout (divide global timeout among items)
    let item_timeout_ms = params
        .timeout_ms
        .unwrap_or(default_timeout * params.proofs.len() as u64)
        / (params.proofs.len() as u64).max(1);

    // Process a single proof item
    let process_item = |item: &VerifyProofBatchItem| -> VerifyProofBatchItemResult {
        let item_start = Instant::now();
        let timeout = Duration::from_millis(item_timeout_ms);

        // Track timing breakdown
        let parse_start = Instant::now();

        // Parse the goal (with tactic patterns for Named dispatch)
        let surface_expr = match parse_expr_with_tactics_exact(&item.goal, &state.tactic_patterns) {
            Ok(expr) => expr,
            Err(e) => {
                let parse_ns = parse_start.elapsed().as_nanos() as u64;
                let elapsed_ns = item_start.elapsed().as_nanos() as u64;
                return VerifyProofBatchItemResult {
                    id: item.id.clone(),
                    verified: false,
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
            }
        };

        let parse_ns = parse_start.elapsed().as_nanos() as u64;
        let elaborate_start = Instant::now();

        // Elaborate the goal expression
        let target = match elaborate(&env, &surface_expr) {
            Ok(expr) => expr,
            Err(e) => {
                let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;
                let elapsed_ns = item_start.elapsed().as_nanos() as u64;
                return VerifyProofBatchItemResult {
                    id: item.id.clone(),
                    verified: false,
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
            }
        };

        let elaborate_ns = elaborate_start.elapsed().as_nanos() as u64;
        let verify_start = Instant::now();

        // Create proof state (clone target so it remains available for verification)
        let mut proof_state = InternalProofState::new(env.clone(), target.clone());

        // Check for trivial proof — kernel type-check against goal type (#2179, #2200)
        if proof_state.is_complete() {
            let closed_proof = proof_state.closed_proof();
            let (verified, trust_summary) = super::verify_closed_proof_with_trust_summary(
                &env,
                &target,
                closed_proof.as_ref(),
                proof_state.trust_ledger(),
                0,
            );
            let verify_ns = verify_start.elapsed().as_nanos() as u64;
            let elapsed_ns = item_start.elapsed().as_nanos() as u64;
            return VerifyProofBatchItemResult {
                id: item.id.clone(),
                verified,
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
        }

        // Parse and execute tactics
        let tactics = parse_tactic_script(&item.proof);
        let mut last_error: Option<VerifyProofError> = None;

        for (idx, tactic_str) in tactics.iter().enumerate() {
            let tactic_line = idx + 1;
            let tactic = tactic_str.trim();
            if tactic.is_empty() {
                continue;
            }

            // Check timeout
            if item_start.elapsed() > timeout {
                let verify_ns = verify_start.elapsed().as_nanos() as u64;
                let elapsed_ns = item_start.elapsed().as_nanos() as u64;
                return VerifyProofBatchItemResult {
                    id: item.id.clone(),
                    verified: false,
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
                        actual_goals: convert_goals(&proof_state, &env)
                            .into_iter()
                            .map(|g| g.target_pp)
                            .collect(),
                        suggestions: vec!["simplify proof".to_string()],
                    }),
                    trust_summary: None,
                };
            }

            // Execute tactic
            match execute_simple_tactic(&mut proof_state, tactic, &env) {
                Ok(()) => {
                    if proof_state.is_complete() {
                        break;
                    }
                }
                Err(e) => {
                    let goals = convert_goals(&proof_state, &env);
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
        let elapsed_ns = item_start.elapsed().as_nanos() as u64;

        let timing = Some(TimingBreakdown {
            parse_ns,
            elaborate_ns,
            verify_ns,
            total_ns: elapsed_ns,
        });

        let is_complete = proof_state.is_complete();

        if is_complete {
            let closed_proof = proof_state.closed_proof();
            let (verified, trust_summary) = super::verify_closed_proof_with_trust_summary(
                &env,
                &target,
                closed_proof.as_ref(),
                proof_state.trust_ledger(),
                0,
            );
            VerifyProofBatchItemResult {
                id: item.id.clone(),
                verified,
                time_ns: elapsed_ns,
                timing,
                error: None,
                trust_summary: Some(trust_summary),
            }
        } else {
            let goals = convert_goals(&proof_state, &env);
            VerifyProofBatchItemResult {
                id: item.id.clone(),
                verified: false,
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
                trust_summary: Some(crate::handlers::trust_summary_from_ledger(
                    proof_state.trust_ledger(),
                    false,
                    0,
                )),
            }
        }
    };

    // Execute in parallel using rayon
    let results: Vec<VerifyProofBatchItemResult> = match pool {
        Some(Some(pool)) => pool.install(|| params.proofs.par_iter().map(process_item).collect()),
        _ => params.proofs.par_iter().map(process_item).collect(),
    };

    // Compute statistics
    let total_time_ns = start.elapsed().as_nanos() as u64;
    let verified_count = results.iter().filter(|r| r.verified).count();
    let failed_count = results.len() - verified_count;

    let times: Vec<u64> = results.iter().map(|r| r.time_ns).collect();
    let avg_time_ns = times.iter().sum::<u64>() / times.len().max(1) as u64;
    let min_time_ns = *times.iter().min().unwrap_or(&0);
    let max_time_ns = *times.iter().max().unwrap_or(&0);

    let throughput_ops_sec = if total_time_ns > 0 {
        (results.len() as f64) / (total_time_ns as f64 / 1e9)
    } else {
        0.0
    };

    let result = VerifyProofBatchResult {
        results,
        total_time_ns,
        throughput_ops_sec,
        stats: VerifyProofBatchStats {
            verified_count,
            failed_count,
            avg_time_ns,
            min_time_ns,
            max_time_ns,
        },
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}
