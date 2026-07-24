// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic execution tracing and debug infrastructure.
//!
//! Provides structured recording of tactic execution for profiling and
//! debugging proof automation. Each tactic invocation is captured as a
//! [`TraceEntry`] recording name, depth, goal counts, timing, and outcome.
//!
//! # Usage
//!
//! ```text
//! let mut trace = TacticTrace::new();
//! trace.enable();
//! trace.enter("simp", 3);
//! // ... run tactic ...
//! trace.exit(2, TraceResult::Success);
//! let output = trace.format_trace();
//! ```

use std::time::Instant;

/// Result of a single tactic execution step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TraceResult {
    /// Tactic succeeded.
    Success,
    /// Tactic failed with a reason.
    Failure(String),
    /// Tactic was skipped (e.g., not applicable).
    Skipped,
}

/// A single entry in the tactic execution trace.
#[derive(Debug, Clone)]
pub(crate) struct TraceEntry {
    /// Name of the tactic that was executed.
    pub(crate) tactic_name: String,
    /// Nesting depth at time of execution (0 = top-level).
    pub(crate) depth: usize,
    /// Number of open goals before the tactic ran.
    pub(crate) before_goals: usize,
    /// Number of open goals after the tactic ran.
    pub(crate) after_goals: usize,
    /// Wall-clock duration in nanoseconds.
    pub(crate) duration_ns: u64,
    /// Outcome of the tactic.
    pub(crate) result: TraceResult,
}

/// Tracks an in-progress tactic invocation before `exit` is called.
#[derive(Debug)]
struct PendingEntry {
    tactic_name: String,
    depth: usize,
    before_goals: usize,
    start: Instant,
}

/// Structured recorder for tactic execution sequences.
///
/// When enabled, records every `enter`/`exit` pair as a [`TraceEntry`].
/// When disabled, `enter`/`exit` calls are no-ops (zero allocation).
///
/// Depth tracking is automatic: each `enter` increments depth, each `exit`
/// decrements it. Unmatched calls are silently tolerated so tracing never
/// panics in production.
#[derive(Debug)]
pub(crate) struct TacticTrace {
    entries: Vec<TraceEntry>,
    pending: Vec<PendingEntry>,
    depth: usize,
    enabled: bool,
}

impl TacticTrace {
    /// Create a new trace in the disabled state.
    pub(crate) fn new() -> Self {
        Self {
            entries: Vec::new(),
            pending: Vec::new(),
            depth: 0,
            enabled: false,
        }
    }

    /// Enable trace recording. Future `enter`/`exit` calls will be captured.
    pub(crate) fn enable(&mut self) {
        self.enabled = true;
    }

    /// Disable trace recording. Future `enter`/`exit` calls are no-ops.
    pub(crate) fn disable(&mut self) {
        self.enabled = false;
    }

    /// Returns whether tracing is currently enabled.
    pub(crate) fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Record the start of a tactic invocation.
    ///
    /// Must be paired with a subsequent [`exit`](Self::exit) call.
    /// If tracing is disabled, this is a no-op.
    pub(crate) fn enter(&mut self, name: &str, goal_count: usize) {
        if !self.enabled {
            return;
        }
        self.pending.push(PendingEntry {
            tactic_name: name.to_string(),
            depth: self.depth,
            before_goals: goal_count,
            start: Instant::now(),
        });
        self.depth += 1;
    }

    /// Record the completion of the most recent tactic invocation.
    ///
    /// If tracing is disabled or there is no matching `enter`, this is a no-op.
    pub(crate) fn exit(&mut self, goal_count: usize, result: TraceResult) {
        if !self.enabled {
            return;
        }
        let Some(pending) = self.pending.pop() else {
            return;
        };
        self.depth = self.depth.saturating_sub(1);
        let duration_ns = pending.start.elapsed().as_nanos() as u64;
        self.entries.push(TraceEntry {
            tactic_name: pending.tactic_name,
            depth: pending.depth,
            before_goals: pending.before_goals,
            after_goals: goal_count,
            duration_ns,
            result,
        });
    }

    /// Format the trace as a human-readable indented string.
    ///
    /// Each entry is rendered as:
    /// ```text
    ///   simp: 3 -> 2 goals [Success] (1234ns)
    /// ```
    /// where leading spaces encode nesting depth (2 spaces per level).
    #[must_use]
    pub(crate) fn format_trace(&self) -> String {
        if self.entries.is_empty() {
            return String::from("(empty trace)");
        }
        let mut lines = Vec::with_capacity(self.entries.len());
        for entry in &self.entries {
            let indent = "  ".repeat(entry.depth);
            let result_str = match &entry.result {
                TraceResult::Success => "Success".to_string(),
                TraceResult::Failure(msg) => format!("Failure: {msg}"),
                TraceResult::Skipped => "Skipped".to_string(),
            };
            lines.push(format!(
                "{indent}{}: {} -> {} goals [{result_str}] ({}ns)",
                entry.tactic_name, entry.before_goals, entry.after_goals, entry.duration_ns,
            ));
        }
        lines.join("\n")
    }

    /// Return a slice of all recorded entries.
    #[must_use]
    pub(crate) fn entries(&self) -> &[TraceEntry] {
        &self.entries
    }

    /// Total wall-clock nanoseconds across all recorded entries.
    ///
    /// Note: nested entries may overlap, so this is a sum, not elapsed time.
    #[must_use]
    pub(crate) fn total_duration_ns(&self) -> u64 {
        self.entries.iter().map(|e| e.duration_ns).sum()
    }

    /// Number of entries with [`TraceResult::Success`].
    #[must_use]
    pub(crate) fn success_count(&self) -> usize {
        self.entries
            .iter()
            .filter(|e| e.result == TraceResult::Success)
            .count()
    }

    /// Number of entries with [`TraceResult::Failure`].
    #[must_use]
    pub(crate) fn failure_count(&self) -> usize {
        self.entries
            .iter()
            .filter(|e| matches!(e.result, TraceResult::Failure(_)))
            .count()
    }

    /// Number of entries with [`TraceResult::Skipped`].
    #[must_use]
    pub(crate) fn skipped_count(&self) -> usize {
        self.entries
            .iter()
            .filter(|e| e.result == TraceResult::Skipped)
            .count()
    }

    /// Clear all recorded entries and reset depth to zero.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.pending.clear();
        self.depth = 0;
    }

    /// Current nesting depth.
    #[must_use]
    pub(crate) fn current_depth(&self) -> usize {
        self.depth
    }
}

impl Default for TacticTrace {
    fn default() -> Self {
        Self::new()
    }
}
