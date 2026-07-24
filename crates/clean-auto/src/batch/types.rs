// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch query types for parallel SMT-backed proof search.
//!
//! These types define the batch dispatch contract: callers submit
//! [`BatchQuery`] entries, the dispatcher processes them in parallel,
//! and results are collected into [`BatchResult`] with per-query
//! [`BatchQueryStatus`] outcomes.

use crate::ProofResult;
use clean_kernel::Expr;
use std::time::Duration;

/// Unique identifier for a query within a batch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct QueryId(pub u64);

/// A single query to submit to the batch dispatcher.
///
/// Each query is independent: it gets its own solver instance and
/// timeout budget. The `priority` field controls dispatch ordering
/// when the dispatcher has limited parallelism.
#[derive(Debug, Clone)]
pub struct BatchQuery {
    /// Unique identifier for correlating results.
    pub query_id: QueryId,
    /// The goal expression to prove.
    pub goal_expr: Expr,
    /// Per-query timeout in milliseconds.
    pub timeout_ms: u64,
    /// Higher values are dispatched first when parallelism is limited.
    pub priority: u32,
    /// Optional hypotheses to provide as context.
    pub hypotheses: Vec<Expr>,
}

impl BatchQuery {
    /// Create a batch query with default priority and no hypotheses.
    pub fn new(query_id: QueryId, goal_expr: Expr, timeout_ms: u64) -> Self {
        Self {
            query_id,
            goal_expr,
            timeout_ms,
            priority: 0,
            hypotheses: Vec::new(),
        }
    }

    /// Set the priority (higher = dispatched first).
    #[must_use]
    pub fn with_priority(mut self, priority: u32) -> Self {
        self.priority = priority;
        self
    }

    /// Attach hypotheses that will be loaded into each solver instance.
    #[must_use]
    pub fn with_hypotheses(mut self, hypotheses: Vec<Expr>) -> Self {
        self.hypotheses = hypotheses;
        self
    }

    /// Convert the timeout to a [`Duration`].
    pub(crate) fn timeout_duration(&self) -> Duration {
        Duration::from_millis(self.timeout_ms)
    }
}

/// Outcome status for a single batch query.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum BatchQueryStatus {
    /// A kernel-verifiable proof was found.
    Proved,
    /// The solver found a counterexample / refutation.
    Disproved,
    /// The query exceeded its timeout budget.
    Timeout,
    /// The solver returned an inconclusive result.
    Unknown,
    /// An error occurred during proof search.
    Error,
}

/// Result for a single query in the batch.
#[derive(Debug)]
pub struct BatchResult {
    /// The query this result corresponds to.
    pub query_id: QueryId,
    /// Outcome status.
    pub status: BatchQueryStatus,
    /// The proof term, if the query was proved.
    pub proof_term: Option<ProofResult>,
    /// Wall-clock time spent on this query in nanoseconds.
    pub time_ns: u64,
    /// Human-readable reason for non-proof outcomes.
    pub reason: Option<String>,
}

impl BatchResult {
    /// Create a proved result.
    pub(crate) fn proved(query_id: QueryId, proof: ProofResult, time_ns: u64) -> Self {
        Self {
            query_id,
            status: BatchQueryStatus::Proved,
            proof_term: Some(proof),
            time_ns,
            reason: None,
        }
    }

    /// Create a disproved result.
    pub(crate) fn disproved(query_id: QueryId, time_ns: u64) -> Self {
        Self {
            query_id,
            status: BatchQueryStatus::Disproved,
            proof_term: None,
            time_ns,
            reason: None,
        }
    }

    /// Create a timeout result.
    pub(crate) fn timeout(query_id: QueryId, time_ns: u64, reason: String) -> Self {
        Self {
            query_id,
            status: BatchQueryStatus::Timeout,
            proof_term: None,
            time_ns,
            reason: Some(reason),
        }
    }

    /// Create an unknown result.
    pub(crate) fn unknown(query_id: QueryId, time_ns: u64, reason: String) -> Self {
        Self {
            query_id,
            status: BatchQueryStatus::Unknown,
            proof_term: None,
            time_ns,
            reason: Some(reason),
        }
    }

    /// Create an error result.
    pub(crate) fn error(query_id: QueryId, time_ns: u64, reason: String) -> Self {
        Self {
            query_id,
            status: BatchQueryStatus::Error,
            proof_term: None,
            time_ns,
            reason: Some(reason),
        }
    }
}

/// Configuration for the batch dispatcher.
#[derive(Debug, Clone)]
pub struct BatchConfig {
    /// Maximum number of queries to process in parallel via rayon.
    /// Defaults to the rayon thread pool size (typically num_cpus).
    pub max_parallel: Option<usize>,
    /// Default per-query timeout in milliseconds, used when a query
    /// does not specify its own timeout.
    pub default_timeout_ms: u64,
    /// Shared axiom expressions loaded into every solver instance.
    /// Amortizes axiom setup cost across the batch.
    pub shared_axioms: Vec<Expr>,
}

impl BatchConfig {
    /// Create a batch config with sensible defaults.
    pub fn new() -> Self {
        Self {
            max_parallel: None,
            default_timeout_ms: 5_000,
            shared_axioms: Vec::new(),
        }
    }

    /// Set the maximum parallelism.
    #[must_use]
    pub fn with_max_parallel(mut self, max_parallel: usize) -> Self {
        self.max_parallel = Some(max_parallel.max(1));
        self
    }

    /// Set the default per-query timeout.
    #[must_use]
    pub fn with_default_timeout_ms(mut self, timeout_ms: u64) -> Self {
        self.default_timeout_ms = timeout_ms;
        self
    }

    /// Set shared axioms loaded into every solver instance.
    #[must_use]
    pub fn with_shared_axioms(mut self, axioms: Vec<Expr>) -> Self {
        self.shared_axioms = axioms;
        self
    }
}

impl Default for BatchConfig {
    fn default() -> Self {
        Self::new()
    }
}

/// Aggregate statistics from a batch run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchStats {
    /// Total queries submitted.
    pub total: usize,
    /// Number of proved queries.
    pub proved: usize,
    /// Number of disproved queries.
    pub disproved: usize,
    /// Number of timed-out queries.
    pub timeout: usize,
    /// Number of unknown-outcome queries.
    pub unknown: usize,
    /// Number of errored queries.
    pub error: usize,
    /// Total wall-clock time for the entire batch in nanoseconds.
    pub total_time_ns: u64,
}

impl BatchStats {
    /// Throughput in queries per second, or 0 if no time elapsed.
    pub fn queries_per_second(&self) -> f64 {
        if self.total_time_ns == 0 {
            return 0.0;
        }
        (self.total as f64) / (self.total_time_ns as f64 / 1_000_000_000.0)
    }

    /// Fraction of queries that were proved (0.0 to 1.0).
    pub fn prove_rate(&self) -> f64 {
        if self.total == 0 {
            return 0.0;
        }
        self.proved as f64 / self.total as f64
    }
}
