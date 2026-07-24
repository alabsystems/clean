// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parallel batch dispatcher for SMT-backed proof search.
//!
//! Uses rayon to process multiple proof queries in parallel. Each query
//! gets its own `AutomationEngine` + `SmtBridge` instance because
//! the bridge is single-shot (#2836) and not thread-safe.
//!
//! The dispatcher amortizes environment setup: the shared
//! [`Environment`] and any shared axioms from [`BatchConfig`] are
//! loaded once and referenced (read-only) by all parallel workers.

use super::types::{BatchConfig, BatchQuery, BatchQueryStatus, BatchResult, BatchStats};
use crate::engine::AutomationEngine;
use crate::engine_api::{AutomationOutcome, AutomationQuery};
use clean_kernel::Environment;
use rayon::prelude::*;
use std::time::Instant;

/// Parallel batch dispatcher for proof queries.
///
/// Holds the batch configuration and provides the [`dispatch`](Self::dispatch)
/// entry point. Each call to `dispatch` processes all queries, returning
/// results in the same order as the input.
///
/// # Thread Safety
///
/// The dispatcher itself is `Send + Sync`. Parallelism comes from rayon:
/// each query is processed on a rayon worker thread with its own
/// `AutomationEngine` instance (which is cheap to construct — it only
/// holds a `u32` config value).
pub struct BatchDispatcher {
    config: BatchConfig,
}

impl BatchDispatcher {
    /// Create a dispatcher with the given configuration.
    pub fn new(config: BatchConfig) -> Self {
        Self { config }
    }

    /// Process all queries in parallel, returning one result per query.
    ///
    /// Results are returned in the same order as the input `queries` slice.
    /// The `env` is shared read-only across all parallel workers.
    ///
    /// # Parallelism
    ///
    /// Uses rayon's parallel iterator. If `config.max_parallel` is set,
    /// a scoped thread pool with that many threads is used. Otherwise
    /// the global rayon pool (typically num_cpus threads) is used.
    pub fn dispatch(&self, env: &Environment, queries: &[BatchQuery]) -> DispatchResult {
        if queries.is_empty() {
            return DispatchResult::empty();
        }

        let batch_start = Instant::now();

        // Sort by priority descending for dispatch ordering.
        let mut indexed: Vec<(usize, &BatchQuery)> = queries.iter().enumerate().collect();
        indexed.sort_by_key(|b| std::cmp::Reverse(b.1.priority));

        let shared_axioms = &self.config.shared_axioms;
        let indexed_results =
            dispatch_parallel(&indexed, env, shared_axioms, self.config.max_parallel);
        let results = reorder_results(indexed_results, queries);

        let total_time_ns = batch_start.elapsed().as_nanos() as u64;
        let stats = compute_stats(&results, total_time_ns);

        DispatchResult { results, stats }
    }
}

/// Combined dispatch output: per-query results and aggregate stats.
#[derive(Debug)]
pub struct DispatchResult {
    /// Per-query results in the same order as the input queries.
    pub results: Vec<BatchResult>,
    /// Aggregate statistics for the batch.
    pub stats: BatchStats,
}

impl DispatchResult {
    fn empty() -> Self {
        Self {
            results: Vec::new(),
            stats: BatchStats {
                total: 0,
                proved: 0,
                disproved: 0,
                timeout: 0,
                unknown: 0,
                error: 0,
                total_time_ns: 0,
            },
        }
    }
}

/// Run indexed queries in parallel via rayon, returning (index, result) pairs.
fn dispatch_parallel(
    indexed: &[(usize, &BatchQuery)],
    env: &Environment,
    shared_axioms: &[clean_kernel::Expr],
    max_parallel: Option<usize>,
) -> Vec<(usize, BatchResult)> {
    let map_fn =
        |&(idx, query): &(usize, &BatchQuery)| (idx, dispatch_single(env, query, shared_axioms));

    if let Some(n) = max_parallel {
        let pool = rayon::ThreadPoolBuilder::new().num_threads(n).build();
        match pool {
            Ok(pool) => pool.install(|| indexed.par_iter().map(map_fn).collect()),
            Err(e) => {
                tracing::warn!(
                    error = %e,
                    "rayon pool creation failed, falling back to sequential dispatch"
                );
                indexed.iter().map(map_fn).collect()
            }
        }
    } else {
        indexed.par_iter().map(map_fn).collect()
    }
}

/// Re-order (index, result) pairs back to the original query order.
fn reorder_results(
    indexed_results: Vec<(usize, BatchResult)>,
    queries: &[BatchQuery],
) -> Vec<BatchResult> {
    let mut ordered: Vec<Option<BatchResult>> = (0..queries.len()).map(|_| None).collect();
    for (idx, result) in indexed_results {
        ordered[idx] = Some(result);
    }
    ordered
        .into_iter()
        .enumerate()
        .map(|(i, opt)| {
            opt.unwrap_or_else(|| {
                BatchResult::error(
                    queries[i].query_id,
                    0,
                    "query was not dispatched".to_string(),
                )
            })
        })
        .collect()
}

/// Process a single query on the current thread.
///
/// Creates a fresh `AutomationEngine` and `AutomationQuery` per call.
/// Shared axioms are injected as hypotheses.
fn dispatch_single(
    env: &Environment,
    query: &BatchQuery,
    shared_axioms: &[clean_kernel::Expr],
) -> BatchResult {
    let start = Instant::now();
    let query_id = query.query_id;

    let timeout = std::time::Duration::from_millis(query.timeout_ms);

    if timeout.is_zero() {
        return BatchResult::timeout(query_id, 0, "query timeout is zero".to_string());
    }

    // Build combined hypotheses: shared axioms + per-query hypotheses.
    let mut hypotheses: Vec<(clean_kernel::Expr, Option<crate::bridge::QuantifierOrigin>)> =
        Vec::with_capacity(shared_axioms.len() + query.hypotheses.len());
    for axiom in shared_axioms {
        hypotheses.push((axiom.clone(), None));
    }
    for hyp in &query.hypotheses {
        hypotheses.push((hyp.clone(), None));
    }

    let automation_query =
        AutomationQuery::new(&query.goal_expr, timeout).with_hypotheses(&hypotheses);

    let engine = AutomationEngine::new();
    let outcome = engine.auto_prove_with_query(env, automation_query);

    let elapsed_ns = start.elapsed().as_nanos() as u64;

    match outcome {
        AutomationOutcome::Verified(proof) => BatchResult::proved(query_id, *proof, elapsed_ns),
        AutomationOutcome::Refuted { .. } => BatchResult::disproved(query_id, elapsed_ns),
        AutomationOutcome::Unverified { reason, .. } => {
            BatchResult::unknown(query_id, elapsed_ns, reason)
        }
        AutomationOutcome::Unknown { reason, .. } => {
            if reason.to_ascii_lowercase().contains("timeout") {
                BatchResult::timeout(query_id, elapsed_ns, reason)
            } else {
                BatchResult::unknown(query_id, elapsed_ns, reason)
            }
        }
    }
}

/// Compute aggregate statistics from a batch of results.
fn compute_stats(results: &[BatchResult], total_time_ns: u64) -> BatchStats {
    let mut proved = 0;
    let mut disproved = 0;
    let mut timeout = 0;
    let mut unknown = 0;
    let mut error = 0;

    for result in results {
        match result.status {
            BatchQueryStatus::Proved => proved += 1,
            BatchQueryStatus::Disproved => disproved += 1,
            BatchQueryStatus::Timeout => timeout += 1,
            BatchQueryStatus::Unknown => unknown += 1,
            BatchQueryStatus::Error => error += 1,
        }
    }

    BatchStats {
        total: results.len(),
        proved,
        disproved,
        timeout,
        unknown,
        error,
        total_time_ns,
    }
}
