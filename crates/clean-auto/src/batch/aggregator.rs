// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Result aggregation and analysis for batch proof search.
//!
//! [`BatchAggregator`] consumes a set of [`BatchResult`] entries and
//! provides aggregate statistics, grouping by status, throughput
//! calculation, and identification of failed queries for retry or
//! escalation.

use super::types::{BatchQueryStatus, BatchResult, BatchStats, QueryId};

/// Aggregates and analyzes batch proof search results.
///
/// Designed to be used after `BatchDispatcher::dispatch` returns.
/// The aggregator takes ownership of results and provides various
/// analysis views.
pub struct BatchAggregator {
    results: Vec<BatchResult>,
    total_time_ns: u64,
}

impl BatchAggregator {
    /// Create an aggregator from dispatch results.
    pub fn new(results: Vec<BatchResult>, total_time_ns: u64) -> Self {
        Self {
            results,
            total_time_ns,
        }
    }

    /// Compute aggregate statistics.
    pub fn summarize(&self) -> BatchStats {
        let mut proved = 0;
        let mut disproved = 0;
        let mut timeout = 0;
        let mut unknown = 0;
        let mut error = 0;

        for result in &self.results {
            match result.status {
                BatchQueryStatus::Proved => proved += 1,
                BatchQueryStatus::Disproved => disproved += 1,
                BatchQueryStatus::Timeout => timeout += 1,
                BatchQueryStatus::Unknown => unknown += 1,
                BatchQueryStatus::Error => error += 1,
            }
        }

        BatchStats {
            total: self.results.len(),
            proved,
            disproved,
            timeout,
            unknown,
            error,
            total_time_ns: self.total_time_ns,
        }
    }

    /// Return query IDs that were successfully proved.
    pub fn proved_ids(&self) -> Vec<QueryId> {
        self.results
            .iter()
            .filter(|r| r.status == BatchQueryStatus::Proved)
            .map(|r| r.query_id)
            .collect()
    }

    /// Return query IDs grouped by status.
    pub fn group_by_status(&self) -> StatusGroups {
        let mut groups = StatusGroups::default();
        for result in &self.results {
            match result.status {
                BatchQueryStatus::Proved => groups.proved.push(result.query_id),
                BatchQueryStatus::Disproved => groups.disproved.push(result.query_id),
                BatchQueryStatus::Timeout => groups.timeout.push(result.query_id),
                BatchQueryStatus::Unknown => groups.unknown.push(result.query_id),
                BatchQueryStatus::Error => groups.error.push(result.query_id),
            }
        }
        groups
    }

    /// Return query IDs that failed (timeout, unknown, or error) and
    /// may benefit from retry with increased resources.
    pub fn retryable_ids(&self) -> Vec<QueryId> {
        self.results
            .iter()
            .filter(|r| {
                matches!(
                    r.status,
                    BatchQueryStatus::Timeout | BatchQueryStatus::Unknown
                )
            })
            .map(|r| r.query_id)
            .collect()
    }

    /// Return query IDs that encountered errors (not just timeouts).
    pub fn error_ids(&self) -> Vec<QueryId> {
        self.results
            .iter()
            .filter(|r| r.status == BatchQueryStatus::Error)
            .map(|r| r.query_id)
            .collect()
    }

    /// Access the underlying results.
    pub fn results(&self) -> &[BatchResult] {
        &self.results
    }

    /// Consume the aggregator and return the results.
    pub fn into_results(self) -> Vec<BatchResult> {
        self.results
    }

    /// Average time per query in nanoseconds, or 0 if batch is empty.
    pub fn avg_time_ns(&self) -> u64 {
        if self.results.is_empty() {
            return 0;
        }
        let total: u64 = self.results.iter().map(|r| r.time_ns).sum();
        total / self.results.len() as u64
    }
}

/// Query IDs grouped by outcome status.
#[derive(Debug, Default)]
pub struct StatusGroups {
    pub proved: Vec<QueryId>,
    pub disproved: Vec<QueryId>,
    pub timeout: Vec<QueryId>,
    pub unknown: Vec<QueryId>,
    pub error: Vec<QueryId>,
}
