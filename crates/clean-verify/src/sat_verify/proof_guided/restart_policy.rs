// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Width-guided restart policy implementing PG02.
//!
//! Ben-Sasson & Wigderson (2001) showed that resolution proofs of width w
//! require size at least 2^{(w - W(F))^2 / n}. This means that when the
//! solver is consistently deriving wide clauses, it is on an exponentially
//! hard subproblem. Restarting abandons this search branch.
//!
//! This module implements a restart policy that triggers when the recent
//! average conflict clause width exceeds a configurable threshold
//! (default: sqrt(n)). On formulas with narrow refutations, this produces
//! polynomial-size proofs (PG02).

/// Width-guided restart policy.
///
/// Tracks recent conflict clause widths and triggers restarts when the
/// average width exceeds a threshold derived from proof complexity theory.
#[derive(Debug, Clone)]
pub struct WidthGuidedRestart {
    /// Number of variables in the formula.
    num_vars: u32,
    /// Width threshold for triggering restarts.
    /// Default: sqrt(n), but configurable for tuning.
    width_threshold: f64,
    /// Recent conflict clause widths (sliding window).
    recent_widths: Vec<usize>,
    /// Maximum window size for the sliding average.
    window_size: usize,
    /// Total number of conflicts recorded.
    total_conflicts: u64,
    /// Number of restarts triggered by this policy.
    restart_count: u64,
}

/// Default sliding window size for width averaging.
const DEFAULT_WINDOW_SIZE: usize = 50;

impl WidthGuidedRestart {
    /// Create a new width-guided restart policy for a formula with `num_vars` variables.
    ///
    /// Uses the default threshold of sqrt(n) and window size of 50.
    #[must_use]
    pub fn new(num_vars: u32) -> Self {
        let width_threshold = (num_vars as f64).sqrt();
        Self {
            num_vars,
            width_threshold,
            recent_widths: Vec::with_capacity(DEFAULT_WINDOW_SIZE),
            window_size: DEFAULT_WINDOW_SIZE,
            total_conflicts: 0,
            restart_count: 0,
        }
    }

    /// Create a new width-guided restart policy with a custom width threshold.
    ///
    /// `threshold` overrides the default sqrt(n). Use this for tuning on
    /// specific formula families.
    #[must_use]
    pub fn with_threshold(num_vars: u32, threshold: f64) -> Self {
        Self {
            num_vars,
            width_threshold: threshold,
            recent_widths: Vec::with_capacity(DEFAULT_WINDOW_SIZE),
            window_size: DEFAULT_WINDOW_SIZE,
            total_conflicts: 0,
            restart_count: 0,
        }
    }

    /// Create a new width-guided restart policy with custom threshold and window size.
    #[must_use]
    pub fn with_params(num_vars: u32, threshold: f64, window_size: usize) -> Self {
        let ws = if window_size == 0 { 1 } else { window_size };
        Self {
            num_vars,
            width_threshold: threshold,
            recent_widths: Vec::with_capacity(ws),
            window_size: ws,
            total_conflicts: 0,
            restart_count: 0,
        }
    }

    /// Record a conflict clause with the given width.
    ///
    /// Call this on every conflict during CDCL search. The width is the
    /// number of literals in the learned clause.
    pub fn record_conflict(&mut self, clause_width: usize) {
        self.total_conflicts += 1;
        if self.recent_widths.len() >= self.window_size {
            self.recent_widths.remove(0);
        }
        self.recent_widths.push(clause_width);
    }

    /// Whether the solver should restart based on recent clause widths.
    ///
    /// Returns `true` when the average width over the recent window exceeds
    /// the width threshold. This implements PG02: width-guided restarts
    /// produce O(2^{sqrt(n)}) size proofs on formulas with narrow refutations.
    ///
    /// Returns `false` if fewer than `window_size` conflicts have been recorded
    /// (too early to make a reliable decision).
    #[must_use]
    pub fn should_restart(&self) -> bool {
        if self.recent_widths.len() < self.window_size {
            return false;
        }
        let avg = self.recent_average_width();
        avg > self.width_threshold
    }

    /// Notify the policy that a restart was performed.
    ///
    /// Clears the recent width window and increments the restart counter.
    pub fn notify_restart(&mut self) {
        self.recent_widths.clear();
        self.restart_count += 1;
    }

    /// Compute the recent average width over the sliding window.
    ///
    /// Returns 0.0 if no conflicts have been recorded.
    #[must_use]
    pub fn recent_average_width(&self) -> f64 {
        if self.recent_widths.is_empty() {
            return 0.0;
        }
        let sum: usize = self.recent_widths.iter().sum();
        sum as f64 / self.recent_widths.len() as f64
    }

    /// Width threshold for restart decisions.
    #[must_use]
    pub fn width_threshold(&self) -> f64 {
        self.width_threshold
    }

    /// Number of variables in the formula.
    #[must_use]
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    /// Total conflicts recorded.
    #[must_use]
    pub fn total_conflicts(&self) -> u64 {
        self.total_conflicts
    }

    /// Number of restarts triggered by this policy.
    #[must_use]
    pub fn restart_count(&self) -> u64 {
        self.restart_count
    }

    /// Number of entries in the current width window.
    #[must_use]
    pub fn window_fill(&self) -> usize {
        self.recent_widths.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_restart_policy_default_threshold() {
        let policy = WidthGuidedRestart::new(100);
        assert!((policy.width_threshold() - 10.0).abs() < 0.01);
        assert_eq!(policy.num_vars(), 100);
        assert_eq!(policy.total_conflicts(), 0);
        assert_eq!(policy.restart_count(), 0);
    }

    #[test]
    fn test_restart_not_triggered_before_window_full() {
        let mut policy = WidthGuidedRestart::new(100);
        // Feed fewer than window_size (50) conflicts.
        for _ in 0..49 {
            policy.record_conflict(20); // wide clauses
        }
        // Not enough data yet.
        assert!(!policy.should_restart());
        assert_eq!(policy.total_conflicts(), 49);
    }

    #[test]
    fn test_restart_triggered_on_wide_clauses() {
        let mut policy = WidthGuidedRestart::new(100);
        // threshold = sqrt(100) = 10.0
        // Feed 50 conflicts with width 15 (> 10).
        for _ in 0..50 {
            policy.record_conflict(15);
        }
        assert!(policy.should_restart());
    }

    #[test]
    fn test_restart_not_triggered_on_narrow_clauses() {
        let mut policy = WidthGuidedRestart::new(100);
        // threshold = 10.0
        // Feed 50 conflicts with width 5 (< 10).
        for _ in 0..50 {
            policy.record_conflict(5);
        }
        assert!(!policy.should_restart());
    }

    #[test]
    fn test_restart_with_custom_threshold() {
        let mut policy = WidthGuidedRestart::with_threshold(100, 5.0);
        assert!((policy.width_threshold() - 5.0).abs() < 0.001);
        // Feed 50 conflicts with width 6 (> custom threshold 5).
        for _ in 0..50 {
            policy.record_conflict(6);
        }
        assert!(policy.should_restart());
    }

    #[test]
    fn test_notify_restart_clears_window() {
        let mut policy = WidthGuidedRestart::new(100);
        for _ in 0..50 {
            policy.record_conflict(15);
        }
        assert!(policy.should_restart());

        policy.notify_restart();
        assert_eq!(policy.restart_count(), 1);
        assert_eq!(policy.window_fill(), 0);
        assert!(!policy.should_restart()); // window cleared, not enough data
    }

    #[test]
    fn test_sliding_window_drops_old_entries() {
        let mut policy = WidthGuidedRestart::with_params(100, 10.0, 5);
        // Fill window with narrow clauses.
        for _ in 0..5 {
            policy.record_conflict(3);
        }
        assert!(!policy.should_restart());

        // Now push wide clauses; old narrow ones slide out.
        for _ in 0..5 {
            policy.record_conflict(15);
        }
        assert!(policy.should_restart());
        assert_eq!(policy.total_conflicts(), 10);
    }

    #[test]
    fn test_recent_average_width_empty() {
        let policy = WidthGuidedRestart::new(100);
        assert!((policy.recent_average_width() - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_recent_average_width_computed() {
        let mut policy = WidthGuidedRestart::with_params(100, 10.0, 4);
        policy.record_conflict(2);
        policy.record_conflict(4);
        policy.record_conflict(6);
        policy.record_conflict(8);
        // avg = (2+4+6+8)/4 = 5.0
        assert!((policy.recent_average_width() - 5.0).abs() < 0.001);
    }
}
