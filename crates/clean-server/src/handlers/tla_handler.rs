// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TLA+ proof obligation handlers.
//!
//! This module contains handlers for proving TLA+ obligations:
//! - Single obligation proving (proveTLA)
//! - Batch obligation proving (batchProveTLA)

use super::state::ServerState;
use super::types::{ns_from_ms, ns_from_us};
use super::work::{batch_pool, run_item_until, WorkError};
use crate::progress::ProgressSender;
use crate::rpc::{RequestId, Response, RpcError};
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};
use tracing::instrument;

// ============================================================================
// TLA+ Types
// ============================================================================

/// Prove TLA+ obligation request parameters
///
/// Accepts a TLAPS-style obligation (sequent) and attempts to prove it.
/// This method is designed for integration with TLA+ proof systems (TLAPS/TLAPM).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProveTlaParams {
    /// The TLA+ obligation to prove (JSON-encoded TlaObligation)
    pub obligation: clean_tla::TlaObligation,
    /// Optional timeout in milliseconds (default: 10000)
    pub timeout_ms: Option<u64>,
}

/// Prove TLA+ obligation response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProveTlaResult {
    /// Whether the obligation was proved
    pub proved: bool,
    /// Proof certificate (JSON string) if proved
    #[serde(skip_serializing_if = "Option::is_none")]
    pub certificate: Option<String>,
    /// Time taken in milliseconds
    pub time_ms: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
    /// Tactics attempted during proof search
    pub tactics_tried: Vec<String>,
    /// Error message if proof failed
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Batch prove TLA+ obligations request parameters
///
/// Accepts multiple TLAPS-style obligations for batch processing with optional parallelism.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchProveTlaParams {
    /// List of obligations to prove
    pub items: Vec<BatchProveTlaItem>,
    /// Number of threads to use (0 = auto, default)
    #[serde(default)]
    pub threads: usize,
    /// Optional timeout for entire batch in milliseconds
    pub timeout_ms: Option<u64>,
}

/// Single item in batch TLA+ proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchProveTlaItem {
    /// Unique identifier for this item
    pub id: String,
    /// The TLA+ obligation to prove
    pub obligation: clean_tla::TlaObligation,
}

/// Batch prove TLA+ obligations response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchProveTlaResult {
    /// Results for each item (in same order)
    pub results: Vec<BatchProveTlaItemResult>,
    /// Aggregate statistics
    pub stats: BatchProveTlaStats,
    /// Total time in milliseconds
    pub time_ms: u64,
    /// Total time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Result for single batch TLA+ item
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchProveTlaItemResult {
    /// Item ID (same as request)
    pub id: String,
    /// Whether the obligation was proved
    pub proved: bool,
    /// Proof certificate (JSON string) if proved
    #[serde(skip_serializing_if = "Option::is_none")]
    pub certificate: Option<String>,
    /// Tactics attempted during proof search
    pub tactics_tried: Vec<String>,
    /// Error message if proof failed
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
}

/// Aggregate statistics for batch TLA+ proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchProveTlaStats {
    /// Total number of obligations
    pub total: usize,
    /// Number of proved obligations
    pub proved: usize,
    /// Number of failed obligations
    pub failed: usize,
    /// All obligations proved
    pub all_proved: bool,
    /// Total wall-clock time in microseconds
    pub wall_time_us: u64,
    /// Total wall-clock time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub wall_time_ns: Option<u64>,
    /// Sum of individual proof times (useful for parallelism analysis)
    pub sum_prove_time_us: u64,
    /// Sum of individual proof times in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sum_prove_time_ns: Option<u64>,
    /// Minimum proof time
    pub min_time_us: u64,
    /// Minimum proof time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub min_time_ns: Option<u64>,
    /// Maximum proof time
    pub max_time_us: u64,
    /// Maximum proof time in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_time_ns: Option<u64>,
    /// Effective speedup (sum_prove_time / wall_time)
    pub speedup: f64,
}

// ============================================================================
// Handler Implementations
// ============================================================================

/// Handle the "proveTLA" method
///
/// Accepts a TLAPS-style obligation and attempts to prove it using clean-tla tactics.
/// This is the main entry point for TY integration. The proof search runs on the
/// work pool under the request's deadline (`work.rs`).
#[instrument(skip(state, params))]
pub async fn handle_prove_tla(
    state: &ServerState,
    id: RequestId,
    params: ProveTlaParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(10_000));
    let deadline = start.checked_add(timeout);
    let obligation = params.obligation;

    let result = tokio::time::timeout(
        timeout,
        state
            .work
            .run(deadline, move || prove_tla_impl(&obligation)),
    )
    .await
    .unwrap_or(Err(WorkError::Interrupted));

    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(mut prove_result) => {
            prove_result.time_ms = elapsed_ms;
            prove_result.time_ns = Some(ns_from_us(elapsed_us));
            let success = prove_result.proved;
            state
                .metrics
                .record_request("proveTLA", success, elapsed_us);
            Response::success_typed(id.clone(), &prove_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(WorkError::Unavailable(detail)) => {
            state.metrics.record_request("proveTLA", false, elapsed_us);
            Response::error(id, RpcError::internal_error(detail))
        }
        Err(WorkError::Interrupted) => {
            state.metrics.record_request("proveTLA", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

fn prove_tla_impl(obligation: &clean_tla::TlaObligation) -> ProveTlaResult {
    // Use clean-tla's prove_tla_obligation function
    let result = clean_tla::tactic::prove_tla_obligation(obligation);

    ProveTlaResult {
        proved: result.proved,
        certificate: result.certificate,
        time_ms: result.time_ms,
        time_ns: Some(ns_from_ms(result.time_ms)),
        tactics_tried: result.tactics_tried,
        error: result.error,
    }
}

/// Handle the "batchProveTLA" method
///
/// Batch proving of TLA+ obligations with optional parallelism.
/// Designed for high-throughput TLAPS integration. The batch runs on the work
/// pool; every obligation runs under the request's deadline on the thread that
/// proves it, and none starts after it.
#[instrument(skip(state, params))]
pub async fn handle_batch_prove_tla(
    state: &ServerState,
    id: RequestId,
    params: BatchProveTlaParams,
    progress: Option<ProgressSender>,
) -> Response {
    let start = Instant::now();
    let item_count = params.items.len() as u64;
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms * 10));
    let deadline = start.checked_add(timeout);

    let result = tokio::time::timeout(timeout, async {
        batch_prove_tla_impl(state, params, progress.clone(), deadline).await
    })
    .await
    .unwrap_or(Err(WorkError::Interrupted));

    let elapsed_us = start.elapsed().as_micros() as u64;
    let elapsed_ms = elapsed_us / 1000;

    match result {
        Ok(mut batch_result) => {
            batch_result.time_ms = elapsed_ms;
            batch_result.time_ns = Some(ns_from_us(elapsed_us));
            let all_proved = batch_result.stats.all_proved;
            state
                .metrics
                .record_request("batchProveTLA", all_proved, elapsed_us);
            state.metrics.record_batch_items(item_count);
            Response::success_typed(id.clone(), &batch_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(WorkError::Unavailable(detail)) => {
            state
                .metrics
                .record_request("batchProveTLA", false, elapsed_us);
            Response::error(id, RpcError::internal_error(detail))
        }
        Err(WorkError::Interrupted) => {
            state
                .metrics
                .record_request("batchProveTLA", false, elapsed_us);
            Response::error(id, RpcError::timeout(timeout.as_millis() as u64))
        }
    }
}

/// One progress line of a batch, sent from the work to the request.
struct BatchProgress {
    message: String,
    percentage: u8,
    details: serde_json::Value,
}

async fn batch_prove_tla_impl(
    state: &ServerState,
    params: BatchProveTlaParams,
    progress: Option<ProgressSender>,
    deadline: Option<Instant>,
) -> Result<BatchProveTlaResult, WorkError> {
    let total = params.items.len();

    if let Some(ref progress) = progress {
        progress
            .notify(
                format!("Batch proveTLA started ({total} obligations)"),
                Some(0),
                None,
            )
            .await;
    }

    // Determine thread count: request param > server config > auto (0), capped
    // at the cores: a pool of the client's asking costs a thread each.
    let cores = std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get);
    let num_threads = if params.threads > 0 {
        params.threads
    } else {
        state.worker_threads
    }
    .min(cores);

    // For parallel processing, use Rayon
    let items = params.items;

    // Progress lines come back over this channel while the batch runs, and the
    // request forwards them: the work never holds the request's progress sender.
    let (lines, mut each_line) = tokio::sync::mpsc::unbounded_channel::<BatchProgress>();
    let reporting = progress.is_some();

    let work = state.work.run(deadline, move || {
        use rayon::prelude::*;
        use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

        let start = Instant::now();
        let completed = AtomicUsize::new(0);
        let interrupted = AtomicBool::new(false);
        let total_items = items.len();

        // A pool of this batch's own (the requested size, the cores otherwise,
        // no more threads than obligations), never rayon's global one
        // (`work::batch_pool`).
        let pool = batch_pool(
            if num_threads > 0 { num_threads } else { cores },
            total_items,
        )?;

        // Adaptive progress frequency: for large batches, only send progress
        // every N items to reduce overhead. Small batches get per-item progress.
        let progress_interval = if total_items <= 100 {
            1 // Every item
        } else if total_items <= 500 {
            total_items / 50 // ~50 updates
        } else if total_items <= 2000 {
            total_items / 100 // ~100 updates
        } else {
            total_items / 200 // ~200 updates max
        };

        let prove_item = |engine: &mut Option<clean_tla::tactic::TlaTacticEngine>,
                          item: &BatchProveTlaItem| {
            let item_start = Instant::now();
            // The deadline is thread-local: install it on the thread proving
            // this obligation, and start none after it.
            let started = !interrupted.load(Ordering::Relaxed)
                && !deadline.is_some_and(|deadline| item_start >= deadline);
            let proved = if started {
                // An engine is built (its environment kernel-checked) only for
                // an obligation that runs, and outside the deadline.
                let engine = engine.get_or_insert_with(clean_tla::tactic::TlaTacticEngine::new);
                run_item_until(deadline, || engine.prove(&item.obligation))
            } else {
                None
            };
            let Some(result) = proved else {
                interrupted.store(true, Ordering::Relaxed);
                return None;
            };
            let time_us = item_start.elapsed().as_micros() as u64;

            // Update progress with adaptive frequency (best effort, non-blocking)
            let done = completed.fetch_add(1, Ordering::Relaxed) + 1;
            if reporting {
                // Only send progress on interval boundaries or last item
                let should_report =
                    done % progress_interval == 0 || done == total_items || done == 1;
                if should_report {
                    let percentage = ((done * 100) / total_items) as u8;
                    let status = if result.proved { "proved" } else { "failed" };
                    let details = serde_json::json!({
                        "item_id": item.id,
                        "proved": result.proved,
                        "completed": done,
                        "total": total_items,
                        "time_us": time_us,
                    });
                    let _ = lines.send(BatchProgress {
                        message: format!("[{done}/{total_items}] {} - {status}", item.id),
                        percentage: percentage.min(99), // Reserve 100 for final
                        details,
                    });
                }
            }

            Some(BatchProveTlaItemResult {
                id: item.id.clone(),
                proved: result.proved,
                certificate: result.certificate,
                tactics_tried: result.tactics_tried,
                error: result.error,
                time_us,
                time_ns: Some(ns_from_us(time_us)),
            })
        };

        let results: Vec<Option<BatchProveTlaItemResult>> =
            pool.install(|| items.par_iter().map_init(|| None, prove_item).collect());

        let wall_time_us = start.elapsed().as_micros() as u64;
        // An obligation the deadline interrupted or never started leaves the
        // batch unfinished: no partial result is reported.
        Ok(results
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .map(|results| (results, wall_time_us)))
    });
    let report = async {
        while let Some(line) = each_line.recv().await {
            if let Some(ref progress) = progress {
                progress
                    .notify(line.message, Some(line.percentage), Some(line.details))
                    .await;
            }
        }
    };
    let (finished, ()) = tokio::join!(work, report);
    let (results, wall_time_us) = finished??.ok_or(WorkError::Interrupted)?;

    // Send final progress notification
    if let Some(ref progress) = progress {
        progress
            .notify(
                format!("Batch proveTLA complete ({total} obligations)"),
                Some(100),
                None,
            )
            .await;
    }

    // Compute statistics
    let proved_count = results.iter().filter(|r| r.proved).count();
    let failed_count = total - proved_count;
    let sum_prove_time_us: u64 = results.iter().map(|r| r.time_us).sum();
    let min_time_us = results.iter().map(|r| r.time_us).min().unwrap_or(0);
    let max_time_us = results.iter().map(|r| r.time_us).max().unwrap_or(0);
    let speedup = if wall_time_us > 0 {
        sum_prove_time_us as f64 / wall_time_us as f64
    } else {
        1.0
    };

    let stats = BatchProveTlaStats {
        total,
        proved: proved_count,
        failed: failed_count,
        all_proved: failed_count == 0,
        wall_time_us,
        wall_time_ns: Some(ns_from_us(wall_time_us)),
        sum_prove_time_us,
        sum_prove_time_ns: Some(ns_from_us(sum_prove_time_us)),
        min_time_us,
        min_time_ns: Some(ns_from_us(min_time_us)),
        max_time_us,
        max_time_ns: Some(ns_from_us(max_time_us)),
        speedup,
    };

    Ok(BatchProveTlaResult {
        results,
        stats,
        time_ms: 0, // Will be set by caller
        time_ns: None,
    })
}
