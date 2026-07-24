// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Handler for `searchProof`: full proof search combining the automation
//! cascade, fillSorries, and composeProof into a single endpoint.
//!
//! This is the top-level proof search entry point for the LLM-driven research
//! engine (#3177). Strategies:
//!
//! - `auto_only` — SMT bridge automation cascade (no LLM dependency)
//! - `decompose_then_search` — wrap goal as sorry sketch, run fillSorries +
//!   composeProof loop
//! - `auto_then_sorry` — try `auto_only` first, fall back to sorry filling

use super::prove_result_from_smt_verification;
use super::state::ServerState;
use super::types::ProveStatus;
use super::verify::TrustSummary;
use crate::proof_state::MathverseCandidate;
use crate::rpc::{RequestId, Response, RpcError};
use clean_auto::bridge::SmtBridge;
use clean_elab::elaborate;
use clean_parser::parse_expr_with_tactics_exact;
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};
use tracing::instrument;

/// Proof search strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Deserialize, Serialize)]
#[non_exhaustive]
#[serde(rename_all = "snake_case")]
pub enum SearchStrategy {
    /// Pure automation cascade via SMT bridge — no LLM dependency.
    #[default]
    AutoOnly,
    /// Wrap the goal as a sorry sketch, run fillSorries to discover tactics,
    /// then compose the result.
    DecomposeThenSearch,
    /// Try `auto_only` first; if it fails, fall back to `decompose_then_search`.
    AutoThenSorry,
}

/// Request parameters for `searchProof`.
#[derive(Debug, Clone, Deserialize)]
pub struct SearchProofParams {
    /// The theorem statement to prove (Lean expression syntax).
    pub theorem: String,
    /// Proof search strategy.
    #[serde(default)]
    pub strategy: SearchStrategy,
    /// Hypotheses available in scope (Lean expression syntax).
    #[serde(default)]
    pub hypotheses: Vec<String>,
    /// Maximum search depth (used by decompose strategies, default 20).
    #[serde(default)]
    pub max_depth: Option<u32>,
    /// Beam width for tree search (reserved for future LLM strategies).
    #[serde(default)]
    pub beam_width: Option<u32>,
    /// Optional timeout in milliseconds.
    pub timeout_ms: Option<u64>,
}

/// Statistics from a proof search run.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SearchStats {
    /// Number of nodes explored during search.
    pub nodes_explored: u64,
    /// Which strategy ultimately produced the result.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub strategy_used: Option<String>,
    /// Per-strategy timing in nanoseconds.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub strategy_timings: Vec<StrategyTiming>,
}

/// Timing for a single strategy attempt.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StrategyTiming {
    /// Strategy name.
    pub strategy: String,
    /// Wall-clock nanoseconds spent in this strategy.
    pub time_ns: u64,
    /// Whether this strategy succeeded.
    pub succeeded: bool,
}

/// Result of `searchProof`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchProofResult {
    /// Whether a proof was found.
    pub found: bool,
    /// Machine-readable status (verified / unverified / refuted / unknown).
    #[serde(default)]
    pub status: ProveStatus,
    /// Proof term (Lean syntax), present when status = verified.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_term: Option<String>,
    /// Tactic script that closes the goal (when found via sorry filling).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tactic_script: Option<String>,
    /// Human-readable proof sketch.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_sketch: Option<String>,
    /// The method/strategy that produced the proof.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub method: Option<String>,
    /// Reason for failure (when not found).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    /// Trust summary for the proof (axiom usage, sorry count).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_summary: Option<TrustSummary>,
    /// Search statistics.
    pub stats: SearchStats,
    /// Trust-filtered Mathverse Library candidates surfaced during proof search.
    #[serde(default)]
    pub mathverse_candidates: Vec<MathverseCandidate>,
    /// Total wall-clock time in nanoseconds.
    pub time_ns: u64,
}

/// Handle the `searchProof` JSON-RPC method.
#[instrument(skip(state))]
pub async fn handle_search_proof(
    state: &ServerState,
    id: RequestId,
    params: SearchProofParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));

    let result = tokio::time::timeout(timeout, async {
        search_proof_impl(state, &params, start, timeout).await
    })
    .await;

    let elapsed_ns = start.elapsed().as_nanos() as u64;

    match result {
        Ok(Ok(mut r)) => {
            r.time_ns = elapsed_ns;
            let success = r.found;
            state
                .metrics
                .record_request("searchProof", success, elapsed_ns / 1000);
            Response::success_typed(id.clone(), &r)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Err(e)) => {
            state
                .metrics
                .record_request("searchProof", false, elapsed_ns / 1000);
            Response::error(id, e)
        }
        Err(_) => {
            state
                .metrics
                .record_request("searchProof", false, elapsed_ns / 1000);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

async fn search_proof_impl(
    state: &ServerState,
    params: &SearchProofParams,
    start: Instant,
    timeout: Duration,
) -> Result<SearchProofResult, RpcError> {
    match params.strategy {
        SearchStrategy::AutoOnly => search_auto_only(state, params, start).await,
        SearchStrategy::DecomposeThenSearch => {
            search_decompose(state, params, start, timeout).await
        }
        SearchStrategy::AutoThenSorry => {
            search_auto_then_sorry(state, params, start, timeout).await
        }
    }
}

/// `auto_only` strategy: run SMT bridge automation cascade.
async fn search_auto_only(
    state: &ServerState,
    params: &SearchProofParams,
    _start: Instant,
) -> Result<SearchProofResult, RpcError> {
    let strategy_start = Instant::now();

    // Parse the goal
    let goal_surface = parse_expr_with_tactics_exact(&params.theorem, &state.tactic_patterns)
        .map_err(|e| RpcError::lean_parse_error(format!("Failed to parse theorem: {e}")))?;

    let env = state.env.read().await;

    // Elaborate
    let goal_expr = elaborate(&env, &goal_surface)
        .map_err(|e| RpcError::elaboration_error(format!("Failed to elaborate theorem: {e}")))?;

    // Create SMT bridge
    let mut bridge = SmtBridge::new(&env);
    let mut dropped_hypotheses = 0u32;

    for (i, hyp_str) in params.hypotheses.iter().enumerate() {
        let hyp_surface =
            parse_expr_with_tactics_exact(hyp_str, &state.tactic_patterns).map_err(|e| {
                RpcError::lean_parse_error(format!("Failed to parse hypothesis {i}: {e}"))
            })?;

        let hyp_expr = elaborate(&env, &hyp_surface).map_err(|e| {
            RpcError::elaboration_error(format!("Failed to elaborate hypothesis {i}: {e}"))
        })?;

        if bridge.add_hypothesis(&hyp_expr).is_err() {
            dropped_hypotheses += 1;
        }
    }
    if dropped_hypotheses > 0 {
        tracing::warn!(
            dropped = dropped_hypotheses,
            total = params.hypotheses.len(),
            "hypothesis(es) dropped in searchProof auto_only"
        );
    }

    let strategy_ns = strategy_start.elapsed().as_nanos() as u64;

    match bridge.prove(&goal_expr) {
        Ok(result) => {
            let prove_result = prove_result_from_smt_verification(&env, &goal_expr, result);
            Ok(SearchProofResult {
                found: prove_result.found,
                status: prove_result.status,
                proof_term: prove_result.proof_term,
                tactic_script: None,
                proof_sketch: prove_result.proof_sketch,
                method: prove_result.method.or(Some("auto_only".into())),
                reason: prove_result.reason,
                trust_summary: prove_result.trust_summary,
                stats: SearchStats {
                    nodes_explored: 1,
                    strategy_used: Some("auto_only".into()),
                    strategy_timings: vec![StrategyTiming {
                        strategy: "auto_only".into(),
                        time_ns: strategy_ns,
                        succeeded: prove_result.found,
                    }],
                },
                mathverse_candidates: Vec::new(),
                time_ns: 0, // filled in by caller
            })
        }
        Err(e) => Err(RpcError::internal_error(format!("SMT bridge error: {e}"))),
    }
}

/// `decompose_then_search` strategy: wrap goal as a sorry sketch, run
/// fillSorries to discover tactics.
async fn search_decompose(
    state: &ServerState,
    params: &SearchProofParams,
    start: Instant,
    timeout: Duration,
) -> Result<SearchProofResult, RpcError> {
    let strategy_start = Instant::now();

    // Build a synthetic Lean file with a sorry proof
    let sketch = format!(
        "theorem searchProof_goal : {} := by\n  sorry",
        params.theorem
    );

    // Use fillSorries internally
    let fill_params = super::verify::FillSorriesParams {
        content: sketch,
        tactic_sequence: vec![],
        timeout_ms: Some(remaining_ms(start, timeout)),
    };

    let fill_id = RequestId::Null;
    let fill_response = super::verify::handle_fill_sorries(state, fill_id, fill_params).await;

    let strategy_ns = strategy_start.elapsed().as_nanos() as u64;

    // Extract the result from the response
    let fill_result: Option<super::verify::FillSorriesResult> = fill_response
        .result
        .as_ref()
        .and_then(|v| serde_json::from_value(v.clone()).ok());

    match fill_result {
        Some(fr) if fr.verified => {
            let mathverse_candidates = mathverse_candidates_from_sorry_goals(&fr);
            Ok(SearchProofResult {
                found: true,
                status: ProveStatus::Verified,
                proof_term: fr.proof_term,
                tactic_script: fr.filled_proof,
                proof_sketch: Some("solved via decompose_then_search sorry filling".into()),
                method: Some("decompose_then_search".into()),
                reason: None,
                trust_summary: fr.trust_summary,
                stats: SearchStats {
                    nodes_explored: fr.solved_sorries as u64 + 1,
                    strategy_used: Some("decompose_then_search".into()),
                    strategy_timings: vec![StrategyTiming {
                        strategy: "decompose_then_search".into(),
                        time_ns: strategy_ns,
                        succeeded: true,
                    }],
                },
                mathverse_candidates,
                time_ns: 0,
            })
        }
        Some(fr) => {
            let remaining = fr.remaining_sorries.len();
            let mathverse_candidates = mathverse_candidates_from_sorry_goals(&fr);
            Ok(SearchProofResult {
                found: false,
                status: ProveStatus::Unknown,
                proof_term: None,
                tactic_script: fr.filled_proof,
                proof_sketch: None,
                method: Some("decompose_then_search".into()),
                reason: Some(format!(
                    "solved {}/{} sorry holes; {} remaining",
                    fr.solved_sorries,
                    fr.solved_sorries + remaining,
                    remaining
                )),
                trust_summary: fr.trust_summary,
                stats: SearchStats {
                    nodes_explored: fr.solved_sorries as u64 + 1,
                    strategy_used: Some("decompose_then_search".into()),
                    strategy_timings: vec![StrategyTiming {
                        strategy: "decompose_then_search".into(),
                        time_ns: strategy_ns,
                        succeeded: false,
                    }],
                },
                mathverse_candidates,
                time_ns: 0,
            })
        }
        None => {
            // fillSorries returned an error at the RPC level
            let error_msg = fill_response
                .error
                .as_ref()
                .map(|e| e.message.clone())
                .unwrap_or_else(|| "fillSorries returned no result".into());
            Ok(SearchProofResult {
                found: false,
                status: ProveStatus::Unknown,
                proof_term: None,
                tactic_script: None,
                proof_sketch: None,
                method: Some("decompose_then_search".into()),
                reason: Some(error_msg),
                trust_summary: None,
                stats: SearchStats {
                    nodes_explored: 0,
                    strategy_used: Some("decompose_then_search".into()),
                    strategy_timings: vec![StrategyTiming {
                        strategy: "decompose_then_search".into(),
                        time_ns: strategy_ns,
                        succeeded: false,
                    }],
                },
                mathverse_candidates: Vec::new(),
                time_ns: 0,
            })
        }
    }
}

/// `auto_then_sorry` strategy: try auto_only first, fall back to decompose.
async fn search_auto_then_sorry(
    state: &ServerState,
    params: &SearchProofParams,
    start: Instant,
    timeout: Duration,
) -> Result<SearchProofResult, RpcError> {
    // Phase 1: auto_only
    let auto_start = Instant::now();
    let auto_result = search_auto_only(state, params, start).await;
    let auto_ns = auto_start.elapsed().as_nanos() as u64;

    match &auto_result {
        Ok(r) if r.found => {
            // auto_only succeeded — return with combined stats
            return auto_result;
        }
        _ => {}
    }

    // Phase 2: decompose_then_search fallback
    let decompose_result = search_decompose(state, params, start, timeout).await;

    match decompose_result {
        Ok(mut r) => {
            // Merge strategy timings from both phases
            let auto_timing = StrategyTiming {
                strategy: "auto_only".into(),
                time_ns: auto_ns,
                succeeded: false,
            };
            r.stats.strategy_timings.insert(0, auto_timing);
            r.stats.strategy_used = if r.found {
                Some("auto_then_sorry(decompose)".into())
            } else {
                Some("auto_then_sorry".into())
            };
            r.method = Some("auto_then_sorry".into());
            Ok(r)
        }
        Err(e) => Err(e),
    }
}

/// Calculate remaining milliseconds before timeout.
fn remaining_ms(start: Instant, timeout: Duration) -> u64 {
    let elapsed = start.elapsed();
    if elapsed >= timeout {
        1 // minimum 1ms to avoid 0-timeout edge cases
    } else {
        (timeout - elapsed).as_millis() as u64
    }
}

fn mathverse_candidates_from_sorry_goals(
    fill_result: &super::verify::FillSorriesResult,
) -> Vec<MathverseCandidate> {
    let mut candidates = Vec::new();
    for sorry_goal in &fill_result.sorry_goals {
        for candidate in &sorry_goal.mathverse_candidates {
            if !candidates.contains(candidate) {
                candidates.push(candidate.clone());
            }
        }
    }
    candidates
}
