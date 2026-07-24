// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rolling window throughput and acceptance statistics for the discovery loop.
//!
//! Tracks per-iteration metrics and provides both cumulative and rolling
//! window statistics. The rolling window detects convergence or divergence
//! in the discovery loop's acceptance rate over recent iterations.
//!
//! Part of #3258.

use std::collections::VecDeque;
use std::fmt;

/// Default number of recent iterations to keep in the rolling window.
const DEFAULT_WINDOW_SIZE: usize = 100;

/// Nanoseconds per second, used for throughput calculation.
const NS_PER_SEC: f64 = 1_000_000_000.0;

/// A snapshot of one discovery iteration's metrics.
#[derive(Debug, Clone, Copy)]
pub(crate) struct IterationSnapshot {
    pub(crate) candidates: u64,
    pub(crate) accepted: u64,
    pub(crate) time_ns: u64,
}

/// Running statistics for the discovery loop.
///
/// Maintains both cumulative totals and a rolling window of recent
/// iterations for detecting trends in throughput and acceptance rate.
pub struct DiscoveryStats {
    total_iterations: u64,
    total_candidates: u64,
    total_accepted: u64,
    total_rejected: u64,
    total_time_ns: u64,
    rolling_window: VecDeque<IterationSnapshot>,
    window_size: usize,
}

impl fmt::Debug for DiscoveryStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DiscoveryStats")
            .field("total_iterations", &self.total_iterations)
            .field("total_candidates", &self.total_candidates)
            .field("total_accepted", &self.total_accepted)
            .field("total_rejected", &self.total_rejected)
            .field("window_len", &self.rolling_window.len())
            .finish()
    }
}

/// Formatted summary of discovery statistics.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct StatsReport {
    /// Cumulative acceptance rate (0.0 to 1.0).
    pub acceptance_rate: f64,
    /// Cumulative throughput (candidates/sec).
    pub throughput_per_sec: f64,
    /// Rolling window acceptance rate.
    pub rolling_acceptance_rate: f64,
    /// Rolling window throughput.
    pub rolling_throughput_per_sec: f64,
    /// Total iterations completed.
    pub total_iterations: u64,
    /// Total candidates evaluated.
    pub total_candidates: u64,
    /// Total accepted candidates.
    pub total_accepted: u64,
}

impl fmt::Display for StatsReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "acceptance {:.1}% ({}/{}), throughput {:.0} cand/s, \
             rolling {:.1}% at {:.0} cand/s over {} iterations",
            self.acceptance_rate * 100.0,
            self.total_accepted,
            self.total_candidates,
            self.throughput_per_sec,
            self.rolling_acceptance_rate * 100.0,
            self.rolling_throughput_per_sec,
            self.total_iterations,
        )
    }
}

impl DiscoveryStats {
    /// Create new statistics tracker with the given rolling window size.
    #[must_use]
    pub fn new(window_size: usize) -> Self {
        let ws = if window_size == 0 {
            DEFAULT_WINDOW_SIZE
        } else {
            window_size
        };
        Self {
            total_iterations: 0,
            total_candidates: 0,
            total_accepted: 0,
            total_rejected: 0,
            total_time_ns: 0,
            rolling_window: VecDeque::with_capacity(ws),
            window_size: ws,
        }
    }

    /// Record a completed iteration's metrics.
    pub fn record_iteration(&mut self, candidates: u64, accepted: u64, time_ns: u64) {
        let accepted = accepted.min(candidates);
        self.total_iterations = self.total_iterations.saturating_add(1);
        self.total_candidates = self.total_candidates.saturating_add(candidates);
        self.total_accepted = self.total_accepted.saturating_add(accepted);
        self.total_rejected = self
            .total_rejected
            .saturating_add(candidates.saturating_sub(accepted));
        self.total_time_ns = self.total_time_ns.saturating_add(time_ns);

        if self.rolling_window.len() >= self.window_size {
            self.rolling_window.pop_front();
        }
        self.rolling_window.push_back(IterationSnapshot {
            candidates,
            accepted,
            time_ns,
        });
    }

    /// Cumulative acceptance rate (0.0 to 1.0).
    #[must_use]
    pub fn acceptance_rate(&self) -> f64 {
        safe_rate(self.total_accepted, self.total_candidates)
    }

    /// Cumulative throughput in candidates per second.
    #[must_use]
    pub fn throughput_per_sec(&self) -> f64 {
        safe_throughput(self.total_candidates, self.total_time_ns)
    }

    /// Rolling window acceptance rate.
    #[must_use]
    pub fn rolling_acceptance_rate(&self) -> f64 {
        let (cand, acc, _) = self.rolling_totals();
        safe_rate(acc, cand)
    }

    /// Rolling window throughput in candidates per second.
    #[must_use]
    pub fn rolling_throughput_per_sec(&self) -> f64 {
        let (cand, _, time) = self.rolling_totals();
        safe_throughput(cand, time)
    }

    /// Total iterations completed.
    #[must_use]
    pub fn total_iterations(&self) -> u64 {
        self.total_iterations
    }

    /// Total candidates evaluated.
    #[must_use]
    pub fn total_candidates(&self) -> u64 {
        self.total_candidates
    }

    /// Total accepted candidates.
    #[must_use]
    pub fn total_accepted(&self) -> u64 {
        self.total_accepted
    }

    /// Generate a formatted statistics report.
    #[must_use]
    pub fn report(&self) -> StatsReport {
        StatsReport {
            acceptance_rate: self.acceptance_rate(),
            throughput_per_sec: self.throughput_per_sec(),
            rolling_acceptance_rate: self.rolling_acceptance_rate(),
            rolling_throughput_per_sec: self.rolling_throughput_per_sec(),
            total_iterations: self.total_iterations,
            total_candidates: self.total_candidates,
            total_accepted: self.total_accepted,
        }
    }

    /// Sum candidates, accepted, and time across the rolling window.
    fn rolling_totals(&self) -> (u64, u64, u64) {
        self.rolling_window
            .iter()
            .fold((0u64, 0u64, 0u64), |(c, a, t), s| {
                (
                    c.saturating_add(s.candidates),
                    a.saturating_add(s.accepted),
                    t.saturating_add(s.time_ns),
                )
            })
    }
}

impl Default for DiscoveryStats {
    fn default() -> Self {
        Self::new(DEFAULT_WINDOW_SIZE)
    }
}

/// Safe division for rate calculations.
fn safe_rate(numerator: u64, denominator: u64) -> f64 {
    if denominator == 0 {
        0.0
    } else {
        numerator as f64 / denominator as f64
    }
}

/// Safe throughput calculation (candidates per second from nanoseconds).
fn safe_throughput(candidates: u64, time_ns: u64) -> f64 {
    if time_ns == 0 {
        0.0
    } else {
        candidates as f64 * NS_PER_SEC / time_ns as f64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stats_new_empty() {
        let stats = DiscoveryStats::new(10);
        assert_eq!(stats.total_iterations(), 0);
        assert_eq!(stats.total_candidates(), 0);
        assert_eq!(stats.total_accepted(), 0);
        assert_eq!(stats.acceptance_rate(), 0.0);
        assert_eq!(stats.throughput_per_sec(), 0.0);
    }

    #[test]
    fn test_stats_record_single_iteration() {
        let mut stats = DiscoveryStats::new(10);
        stats.record_iteration(100, 25, 1_000_000_000);

        assert_eq!(stats.total_iterations(), 1);
        assert_eq!(stats.total_candidates(), 100);
        assert_eq!(stats.total_accepted(), 25);
        assert_eq!(stats.total_rejected, 75);
    }

    #[test]
    fn test_stats_acceptance_rate_calculation() {
        let mut stats = DiscoveryStats::new(10);
        stats.record_iteration(200, 50, 500_000_000);
        stats.record_iteration(100, 10, 500_000_000);

        // 60/300 = 0.2
        let rate = stats.acceptance_rate();
        assert!((rate - 0.2).abs() < 1e-9, "expected 0.2, got {rate}");

        // 300 candidates / 1.0 sec = 300/s
        let tps = stats.throughput_per_sec();
        assert!((tps - 300.0).abs() < 1e-6, "expected 300.0, got {tps}");
    }

    #[test]
    fn test_stats_rolling_window_eviction() {
        let mut stats = DiscoveryStats::new(3);

        // Fill window with 3 iterations of 100% acceptance.
        for _ in 0..3 {
            stats.record_iteration(10, 10, 100_000_000);
        }
        assert!(
            (stats.rolling_acceptance_rate() - 1.0).abs() < 1e-9,
            "full window should be 100%"
        );

        // Add an iteration with 0% acceptance -- oldest is evicted.
        stats.record_iteration(10, 0, 100_000_000);

        // Window now holds [10/10, 10/10, 10/0] => 20/30 ~= 0.667
        let rolling = stats.rolling_acceptance_rate();
        assert!(
            (rolling - 2.0 / 3.0).abs() < 1e-6,
            "expected ~0.667, got {rolling}"
        );

        // Cumulative is 30/40 = 0.75
        let cumulative = stats.acceptance_rate();
        assert!(
            (cumulative - 0.75).abs() < 1e-9,
            "expected 0.75, got {cumulative}"
        );
    }

    #[test]
    fn test_stats_report_display() {
        let mut stats = DiscoveryStats::new(10);
        stats.record_iteration(1000, 100, 1_000_000_000);

        let report = stats.report();
        let display = format!("{report}");

        assert!(display.contains("1000"), "should contain total candidates");
        assert!(display.contains("100"), "should contain total accepted");
        assert!(display.contains("10.0%"), "should contain acceptance rate");
    }

    #[test]
    fn test_stats_rolling_throughput() {
        let mut stats = DiscoveryStats::new(5);
        // 50 candidates in 0.5 seconds => 100/s
        stats.record_iteration(50, 10, 500_000_000);

        let rolling_tps = stats.rolling_throughput_per_sec();
        assert!(
            (rolling_tps - 100.0).abs() < 1e-6,
            "expected 100.0, got {rolling_tps}"
        );
    }

    #[test]
    fn test_stats_default() {
        let stats = DiscoveryStats::default();
        assert_eq!(stats.window_size, DEFAULT_WINDOW_SIZE);
        assert_eq!(stats.total_iterations(), 0);
    }

    #[test]
    fn test_stats_zero_window_uses_default() {
        let stats = DiscoveryStats::new(0);
        assert_eq!(stats.window_size, DEFAULT_WINDOW_SIZE);
    }
}
