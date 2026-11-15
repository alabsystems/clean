// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Premise selection handlers.
//!
//! This module contains handlers for selecting relevant premises for goals:
//! - Single goal premise selection (getPremises)
//! - Batch premise selection (batchGetPremises)
//!
//! Both run on the server's work pool under the request's deadline
//! (`work.rs`). Selection makes few kernel calls, so the batch also reads the
//! clock between goals and stops once the deadline has passed; a single goal's
//! selection runs to its end (it is a scan of the environment) in its pool slot.

use super::core::{run_with_env, WorkEnv};
use super::state::ServerState;
use super::types::ns_from_us;
use super::work::{past, WorkError};
use crate::progress::ProgressSender;
use crate::rpc::{RequestId, Response, RpcError};
use clean_elab::elaborate;
use clean_parser::parse_expr_with_tactics_exact;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::time::{Duration, Instant};
use tracing::instrument;

// ============================================================================
// Premise Selection Types
// ============================================================================

/// Get premises request parameters
///
/// Requests relevant premises for a goal using premise selection algorithms
/// (MePo, MaSh, or hybrid). Designed for LLM theorem proving integration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GetPremisesParams {
    /// Goal to find premises for (Lean expression syntax)
    pub goal: String,
    /// Selection method: "mepo", "mash", "hybrid", or "all" (default: "hybrid")
    #[serde(default = "default_premise_method")]
    pub method: String,
    /// Maximum number of premises to return (default: 64)
    #[serde(default = "default_max_premises")]
    pub max_premises: usize,
    /// Relevance threshold (0.0 to 1.0, default: 0.1)
    #[serde(default = "default_premise_threshold")]
    pub threshold: f64,
    /// Optional timeout in milliseconds
    pub timeout_ms: Option<u64>,
}

fn default_premise_method() -> String {
    "hybrid".to_string()
}

fn default_max_premises() -> usize {
    64
}

fn default_premise_threshold() -> f64 {
    0.1
}

/// Get premises response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GetPremisesResult {
    /// Selected premises ranked by relevance
    pub premises: Vec<PremiseInfo>,
    /// Statistics about the selection
    pub stats: PremiseSelectionStats,
    /// Time taken in milliseconds
    pub time_ms: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Information about a selected premise
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PremiseInfo {
    /// Name of the theorem/lemma
    pub name: String,
    /// Relevance score (0.0 to 1.0)
    pub score: f64,
    /// Selection method that found this premise
    pub method: String,
}

/// Statistics about premise selection
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PremiseSelectionStats {
    /// Total candidates scanned in database
    pub candidates_scanned: usize,
    /// Threshold applied for filtering
    pub threshold_applied: f64,
    /// Method used for selection
    pub method_used: String,
    /// Elapsed time in milliseconds
    pub elapsed_ms: u64,
    /// Elapsed time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub elapsed_ns: Option<u64>,
}

/// Batch get premises request parameters
///
/// Accepts multiple goals for parallel premise selection, enabling efficient
/// premise recommendation for AI proof search across many subgoals.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchGetPremisesParams {
    /// List of goals to get premises for
    pub items: Vec<BatchGetPremisesItem>,
    /// Selection method: "mepo", "mash", or "hybrid" (default: "hybrid")
    #[serde(default = "default_premise_method")]
    pub method: String,
    /// Maximum premises per goal (default: 64)
    #[serde(default = "default_max_premises")]
    pub max_premises: usize,
    /// Relevance threshold (0.0 to 1.0, default: 0.1)
    #[serde(default = "default_premise_threshold")]
    pub threshold: f64,
    /// Optional timeout for entire batch in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Single item in batch get premises
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchGetPremisesItem {
    /// Unique identifier for this item
    pub id: String,
    /// Goal expression (Lean syntax)
    pub goal: String,
}

/// Batch get premises response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchGetPremisesResult {
    /// Results for each item (in same order)
    pub results: Vec<BatchGetPremisesItemResult>,
    /// Aggregate statistics
    pub stats: BatchGetPremisesStats,
    /// Total time in milliseconds
    pub time_ms: u64,
    /// Total time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Result for single batch get premises item
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchGetPremisesItemResult {
    /// Item ID (same as request)
    pub id: String,
    /// Whether premise selection succeeded
    pub success: bool,
    /// Selected premises (if successful)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub premises: Option<Vec<PremiseInfo>>,
    /// Error message (if failed)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Aggregate statistics for batch get premises
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchGetPremisesStats {
    /// Total number of goals
    pub total: usize,
    /// Number of successful selections
    pub succeeded: usize,
    /// Number of failed selections
    pub failed: usize,
    /// Method used for selection
    pub method_used: String,
    /// Total candidates scanned across all goals
    pub total_candidates_scanned: usize,
}

// ============================================================================
// Handler Implementations
// ============================================================================

/// Handle the "getPremises" method
///
/// Selects relevant premises for a goal using MePo/MaSh/Hybrid algorithms.
/// Designed for integration with LLM theorem provers (verification-guided search).
#[instrument(skip(state, params))]
pub async fn handle_get_premises(
    state: &ServerState,
    id: RequestId,
    params: GetPremisesParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));
    let deadline = start.checked_add(timeout);

    let result = tokio::time::timeout(
        timeout,
        run_with_env(state, deadline, move |held| {
            get_premises_impl(held, &params)
        }),
    )
    .await
    .unwrap_or(Err(WorkError::Interrupted));

    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(Ok(mut premises_result)) => {
            premises_result.time_ms = elapsed_ms;
            premises_result.stats.elapsed_ms = elapsed_ms;
            premises_result.time_ns = Some(ns_from_us(elapsed_us));
            premises_result.stats.elapsed_ns = Some(ns_from_us(elapsed_us));
            state
                .metrics
                .record_request("getPremises", true, elapsed_us);
            Response::success_typed(id.clone(), &premises_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Err(e)) => {
            state
                .metrics
                .record_request("getPremises", false, elapsed_us);
            Response::error(id, e)
        }
        Err(WorkError::Unavailable(detail)) => {
            state
                .metrics
                .record_request("getPremises", false, elapsed_us);
            Response::error(id, RpcError::internal_error(detail))
        }
        Err(WorkError::Interrupted) => {
            state
                .metrics
                .record_request("getPremises", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

fn get_premises_impl(
    held: &WorkEnv,
    params: &GetPremisesParams,
) -> Result<GetPremisesResult, RpcError> {
    use clean_auto::premise::{HybridSelector, MaShSelector, MePoSelector, PremiseDatabase};

    // Parse the goal expression
    let goal_surface = parse_expr_with_tactics_exact(&params.goal, &held.patterns)
        .map_err(|e| RpcError::lean_parse_error(format!("Failed to parse goal: {e}")))?;

    let env: &clean_kernel::Environment = &held.env;

    // Elaborate the goal
    let goal_expr = elaborate(env, &goal_surface)
        .map_err(|e| RpcError::elaboration_error(format!("Failed to elaborate goal: {e}")))?;

    // Build premise database from environment
    let mut premise_db = PremiseDatabase::new();
    for info in env.constants() {
        premise_db.add(info.name.clone(), info.type_.clone());
    }

    let candidates_scanned = premise_db.len();

    // Select premises based on method
    let (premises, method_used) = match params.method.as_str() {
        "mepo" => {
            let selector = MePoSelector::new(&premise_db)
                .with_threshold(params.threshold)
                .with_max_premises(params.max_premises);
            let selected = selector.select_with_scores(&goal_expr);
            let premises: Vec<PremiseInfo> = selected
                .into_iter()
                .map(|(p, score)| PremiseInfo {
                    name: p.name.to_string(),
                    score,
                    method: "mepo".to_string(),
                })
                .collect();
            (premises, "mepo".to_string())
        }
        "mash" => {
            let selector = MaShSelector::new(&premise_db).with_max_premises(params.max_premises);
            let selected = selector.select(&goal_expr);
            let premises: Vec<PremiseInfo> = selected
                .into_iter()
                .enumerate()
                .map(|(i, p)| PremiseInfo {
                    name: p.name.to_string(),
                    // MaSh doesn't expose scores directly, use rank-based score
                    score: 1.0 - (i as f64 / params.max_premises as f64),
                    method: "mash".to_string(),
                })
                .collect();
            (premises, "mash".to_string())
        }
        _ => {
            // "hybrid" is the default strategy
            let selector = HybridSelector::new(&premise_db).with_max_premises(params.max_premises);
            let selected = selector.select(&goal_expr);
            let premises: Vec<PremiseInfo> = selected
                .into_iter()
                .enumerate()
                .map(|(i, p)| PremiseInfo {
                    name: p.name.to_string(),
                    // Hybrid doesn't expose scores directly, use rank-based score
                    score: 1.0 - (i as f64 / params.max_premises as f64),
                    method: "hybrid".to_string(),
                })
                .collect();
            (premises, "hybrid".to_string())
        }
    };

    Ok(GetPremisesResult {
        premises,
        stats: PremiseSelectionStats {
            candidates_scanned,
            threshold_applied: params.threshold,
            method_used,
            elapsed_ms: 0, // Will be set by caller
            elapsed_ns: None,
        },
        time_ms: 0, // Will be set by caller
        time_ns: None,
    })
}

/// Handle the "batchGetPremises" method
///
/// Retrieves premise recommendations for multiple goals in a single request.
/// Uses shared premise database to avoid redundant construction.
#[instrument(skip(state, params))]
pub async fn handle_batch_get_premises(
    state: &ServerState,
    id: RequestId,
    params: BatchGetPremisesParams,
    progress: Option<ProgressSender>,
) -> Response {
    let start = Instant::now();
    let item_count = params.items.len() as u64;
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms * 10));

    let deadline = start.checked_add(timeout);

    let result = tokio::time::timeout(timeout, async {
        batch_get_premises(state, params, progress.clone(), deadline).await
    })
    .await
    .unwrap_or(Err(WorkError::Interrupted));

    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(mut batch_result) => {
            batch_result.time_ms = elapsed_ms;
            batch_result.time_ns = Some(ns_from_us(elapsed_us));
            let all_succeeded = batch_result.results.iter().all(|r| r.success);
            state
                .metrics
                .record_request("batchGetPremises", all_succeeded, elapsed_us);
            state.metrics.record_batch_items(item_count);
            Response::success_typed(id.clone(), &batch_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(WorkError::Unavailable(detail)) => {
            state
                .metrics
                .record_request("batchGetPremises", false, elapsed_us);
            Response::error(id, RpcError::internal_error(detail))
        }
        Err(WorkError::Interrupted) => {
            state
                .metrics
                .record_request("batchGetPremises", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

/// Run the batch on the work pool, streaming each goal's result to
/// `progress` as it is found.
async fn batch_get_premises(
    state: &ServerState,
    params: BatchGetPremisesParams,
    progress: Option<ProgressSender>,
    deadline: Option<Instant>,
) -> Result<BatchGetPremisesResult, WorkError> {
    let total = params.items.len();
    if let Some(progress) = progress.as_ref() {
        progress
            .notify(
                format!("Batch premise selection started ({total} goals)"),
                Some(0),
                None,
            )
            .await;
    }

    // Adaptive progress frequency
    let progress_interval = if total <= 100 {
        1
    } else if total <= 500 {
        total / 50
    } else if total <= 2000 {
        total / 100
    } else {
        total / 200
    };

    let (selected, mut each_selected) = tokio::sync::mpsc::unbounded_channel();
    let work = run_with_env(state, deadline, move |held| {
        batch_get_premises_impl(held, &params, deadline, |result| {
            // The request may have stopped listening; the batch goes on.
            let _ = selected.send(result.clone());
        })
    });
    let report = async {
        let mut completed = 0usize;
        while let Some(result) = each_selected.recv().await {
            completed += 1;
            let Some(progress) = progress.as_ref() else {
                continue;
            };
            let should_report =
                completed % progress_interval == 0 || completed == total || completed == 1;
            if should_report {
                let percentage = (completed * 100)
                    .checked_div(total)
                    .map_or(100, |p| p.min(100) as u8);

                progress
                    .notify(
                        format!("Selected {}/{} ({})", completed, total, result.id),
                        Some(percentage),
                        Some(json!({
                            "id": result.id,
                            "success": result.success,
                            "error": result.error,
                        })),
                    )
                    .await;
            }
        }
    };
    let (finished, ()) = tokio::join!(work, report);
    finished?.ok_or(WorkError::Interrupted)
}

/// Select premises for each goal against the held environment. Runs on the
/// work pool. Selection makes few kernel calls, so the clock is read before and
/// after each goal: `None` once the request's deadline has passed, and a goal
/// it passed during is not reported.
fn batch_get_premises_impl(
    held: &WorkEnv,
    params: &BatchGetPremisesParams,
    deadline: Option<Instant>,
    on_result: impl Fn(&BatchGetPremisesItemResult),
) -> Option<BatchGetPremisesResult> {
    use clean_auto::premise::{HybridSelector, MaShSelector, MePoSelector, PremiseDatabase};

    let env: &clean_kernel::Environment = &held.env;

    // Build premise database once for all items
    let mut premise_db = PremiseDatabase::new();
    for info in env.constants() {
        premise_db.add(info.name.clone(), info.type_.clone());
    }

    let candidates_scanned = premise_db.len();

    let total = params.items.len();
    let mut results = Vec::with_capacity(total);
    let mut succeeded = 0;
    let mut failed = 0;

    for item in &params.items {
        if past(deadline) {
            return None;
        }
        let item_start = Instant::now();

        // Parse the goal
        let goal_result = parse_expr_with_tactics_exact(&item.goal, &held.patterns);

        let (success, premises, error) = match goal_result {
            Ok(goal_surface) => {
                // Elaborate the goal
                match elaborate(env, &goal_surface) {
                    Ok(goal_expr) => {
                        // Select premises based on method
                        let selected = match params.method.as_str() {
                            "mepo" => {
                                let selector = MePoSelector::new(&premise_db)
                                    .with_threshold(params.threshold)
                                    .with_max_premises(params.max_premises);
                                let selected = selector.select_with_scores(&goal_expr);
                                selected
                                    .into_iter()
                                    .map(|(p, score)| PremiseInfo {
                                        name: p.name.to_string(),
                                        score,
                                        method: "mepo".to_string(),
                                    })
                                    .collect::<Vec<_>>()
                            }
                            "mash" => {
                                let selector = MaShSelector::new(&premise_db)
                                    .with_max_premises(params.max_premises);
                                let selected = selector.select(&goal_expr);
                                selected
                                    .into_iter()
                                    .enumerate()
                                    .map(|(i, p)| PremiseInfo {
                                        name: p.name.to_string(),
                                        score: 1.0 - (i as f64 / params.max_premises as f64),
                                        method: "mash".to_string(),
                                    })
                                    .collect::<Vec<_>>()
                            }
                            _ => {
                                // "hybrid" is the default strategy
                                let selector = HybridSelector::new(&premise_db)
                                    .with_max_premises(params.max_premises);
                                let selected = selector.select(&goal_expr);
                                selected
                                    .into_iter()
                                    .enumerate()
                                    .map(|(i, p)| PremiseInfo {
                                        name: p.name.to_string(),
                                        score: 1.0 - (i as f64 / params.max_premises as f64),
                                        method: "hybrid".to_string(),
                                    })
                                    .collect::<Vec<_>>()
                            }
                        };
                        (true, Some(selected), None)
                    }
                    Err(e) => (false, None, Some(format!("Failed to elaborate goal: {e}"))),
                }
            }
            Err(e) => (false, None, Some(format!("Failed to parse goal: {e}"))),
        };

        // A goal the deadline may have cut short is no answer: not reported,
        // and the batch answers the timeout error.
        if past(deadline) {
            return None;
        }
        let time_us = item_start.elapsed().as_micros() as u64;

        if success {
            succeeded += 1;
        } else {
            failed += 1;
        }

        let result = BatchGetPremisesItemResult {
            id: item.id.clone(),
            success,
            premises,
            error,
            time_us,
            time_ns: Some(ns_from_us(time_us)),
        };
        on_result(&result);
        results.push(result);
    }

    Some(BatchGetPremisesResult {
        results,
        stats: BatchGetPremisesStats {
            total,
            succeeded,
            failed,
            method_used: params.method.clone(),
            total_candidates_scanned: candidates_scanned * total,
        },
        time_ms: 0, // Will be set by caller
        time_ns: None,
    })
}
