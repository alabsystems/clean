// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Width-aware branching heuristic for proof-guided CDCL.
//!
//! Adjusts variable selection based on proof complexity metrics.
//! Variables appearing in narrow (low-width) clauses are preferred because
//! narrow refutations lead to small proofs (Ben-Sasson & Wigderson, 2001).
//!
//! This heuristic works alongside VSIDS: it does not replace the activity
//! scores but provides an additional signal that biases branching toward
//! variables that participate in narrow conflict clauses.

use super::complexity_tracker::ProofComplexity;

/// Width-guided branching heuristic.
///
/// Wraps a snapshot of proof complexity metrics and provides methods
/// for adjusting variable activity based on clause width observations.
#[derive(Debug, Clone)]
pub struct WidthGuidedBranching {
    /// Width threshold: sqrt(n). Clauses narrower than this are "good".
    width_threshold: f64,
    /// Recent average width from the complexity tracker.
    recent_avg_width: f64,
    /// Maximum width observed.
    max_width: usize,
    /// Number of variables in the formula.
    num_vars: u32,
}

impl WidthGuidedBranching {
    /// Create a new width-guided branching heuristic from complexity metrics.
    #[must_use]
    pub fn from_complexity(complexity: &ProofComplexity) -> Self {
        Self {
            width_threshold: complexity.width_threshold(),
            recent_avg_width: complexity.recent_average_width(),
            max_width: complexity.max_width(),
            num_vars: complexity.num_vars(),
        }
    }

    /// Create a new width-guided branching heuristic with explicit parameters.
    ///
    /// Useful for testing without a full `ProofComplexity` tracker.
    #[must_use]
    pub fn new(num_vars: u32, recent_avg_width: f64, max_width: usize) -> Self {
        let width_threshold = (num_vars as f64).sqrt();
        Self {
            width_threshold,
            recent_avg_width,
            max_width,
            num_vars,
        }
    }

    /// Compute an activity adjustment for a variable appearing in a clause
    /// of the given width.
    ///
    /// Variables in narrow clauses (width < sqrt(n)) get a positive bump.
    /// Variables in wide clauses (width > sqrt(n)) get no extra bump (0.0).
    ///
    /// The bump magnitude is proportional to how much narrower the clause is
    /// relative to the threshold: `(threshold - width) / threshold`.
    /// This ranges from ~1.0 for unit clauses to ~0.0 at the threshold.
    #[must_use]
    pub fn adjust_activity(&self, clause_width: usize) -> f64 {
        if self.width_threshold <= 0.0 || self.num_vars == 0 {
            return 0.0;
        }
        let width_f = clause_width as f64;
        if width_f >= self.width_threshold {
            // Wide clause: no extra activity bump.
            return 0.0;
        }
        // Narrow clause: bump proportional to how narrow it is.
        (self.width_threshold - width_f) / self.width_threshold
    }

    /// Whether the VSIDS decay factor should be increased (extra decay)
    /// because proof width is growing.
    ///
    /// When the recent average width exceeds the threshold, the solver is
    /// in an exponentially hard region. Extra decay causes the solver to
    /// forget old (wide) activity scores faster, making it more responsive
    /// to new narrow-clause signals after a restart.
    #[must_use]
    pub fn should_decay_extra(&self) -> bool {
        if self.width_threshold <= 0.0 {
            return false;
        }
        self.recent_avg_width > self.width_threshold
    }

    /// The width threshold (sqrt(n)).
    #[must_use]
    pub fn width_threshold(&self) -> f64 {
        self.width_threshold
    }

    /// Recent average width from the complexity tracker snapshot.
    #[must_use]
    pub fn recent_avg_width(&self) -> f64 {
        self.recent_avg_width
    }

    /// Maximum width observed.
    #[must_use]
    pub fn max_width(&self) -> usize {
        self.max_width
    }
}

#[cfg(test)]
mod tests {
    use super::super::complexity_tracker::ProofComplexity;
    use super::*;

    #[test]
    fn test_width_guided_from_complexity() {
        let mut pc = ProofComplexity::new(100);
        // Feed some narrow conflicts.
        for _ in 0..10 {
            pc.update_on_conflict(3, 2, 10);
        }
        let heuristic = WidthGuidedBranching::from_complexity(&pc);
        assert!((heuristic.width_threshold() - 10.0).abs() < 0.01);
        assert!(heuristic.recent_avg_width() > 0.0);
    }

    #[test]
    fn test_adjust_activity_narrow_clause_gets_bump() {
        let h = WidthGuidedBranching::new(100, 5.0, 8);
        // threshold = sqrt(100) = 10.0
        // clause of width 3: bump = (10 - 3) / 10 = 0.7
        let bump = h.adjust_activity(3);
        assert!((bump - 0.7).abs() < 0.001);
    }

    #[test]
    fn test_adjust_activity_wide_clause_no_bump() {
        let h = WidthGuidedBranching::new(100, 5.0, 15);
        // threshold = 10.0, clause width 12 > threshold
        let bump = h.adjust_activity(12);
        assert!((bump - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_adjust_activity_at_threshold_no_bump() {
        let h = WidthGuidedBranching::new(100, 5.0, 10);
        // threshold = 10.0, clause width exactly 10
        let bump = h.adjust_activity(10);
        assert!((bump - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_adjust_activity_unit_clause_max_bump() {
        let h = WidthGuidedBranching::new(100, 5.0, 5);
        // threshold = 10.0, clause width 1: bump = (10-1)/10 = 0.9
        let bump = h.adjust_activity(1);
        assert!((bump - 0.9).abs() < 0.001);
    }

    #[test]
    fn test_adjust_activity_zero_vars() {
        let h = WidthGuidedBranching::new(0, 0.0, 0);
        assert!((h.adjust_activity(3) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_should_decay_extra_when_width_growing() {
        // recent_avg_width = 15.0 > threshold = 10.0
        let h = WidthGuidedBranching::new(100, 15.0, 20);
        assert!(h.should_decay_extra());
    }

    #[test]
    fn test_should_not_decay_extra_when_width_narrow() {
        // recent_avg_width = 5.0 < threshold = 10.0
        let h = WidthGuidedBranching::new(100, 5.0, 8);
        assert!(!h.should_decay_extra());
    }

    #[test]
    fn test_should_not_decay_extra_zero_vars() {
        let h = WidthGuidedBranching::new(0, 0.0, 0);
        assert!(!h.should_decay_extra());
    }
}
