// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof complexity tracking during CDCL search.
//!
//! Tracks three proof complexity metrics incrementally as conflict clauses
//! are derived:
//!
//! - **Width**: maximum clause width (number of literals) across all
//!   derived clauses. Ben-Sasson & Wigderson (2001) showed that resolution
//!   proofs of width w require size >= 2^{(w - W(F))^2 / n}.
//!
//! - **Space**: maximum number of clauses simultaneously "active" (needed
//!   for future derivations). Approximated by the size of the current
//!   learned clause database after deletion. Atserias & Dalmau (2008)
//!   showed space >= width - O(log n).
//!
//! - **Depth**: maximum depth in the resolution proof DAG. Deep proofs
//!   indicate the solver is exploring long resolution chains, which
//!   correlates with poor search performance.

/// Proof complexity metrics tracked during CDCL search.
///
/// Updated incrementally on each conflict. These metrics enable
/// proof-complexity-aware restart and branching decisions.
#[derive(Debug, Clone, PartialEq)]
pub struct ProofComplexity {
    /// Maximum clause width seen among all derived conflict clauses.
    /// Width of a clause = number of literals in it.
    width: usize,
    /// Maximum number of simultaneously active clauses (space complexity).
    /// Approximated by the peak learned clause count before deletion.
    space: usize,
    /// Maximum resolution proof depth for any conflict clause.
    /// Depth is the length of the longest resolution chain leading to
    /// the conflict clause.
    depth: usize,
    /// Number of variables in the formula (n). Used for the sqrt(n)
    /// threshold in width-based restart decisions.
    num_vars: u32,
    /// Total number of conflict clauses derived so far.
    num_conflicts: u64,
    /// Running sum of conflict clause widths (for computing average width).
    total_width: u64,
    /// Recent conflict clause widths (sliding window for local average).
    /// Bounded to `RECENT_WINDOW_SIZE` entries.
    recent_widths: Vec<usize>,
    /// Current count of active (non-deleted) learned clauses.
    active_clause_count: usize,
}

/// Size of the sliding window for recent conflict clause widths.
const RECENT_WINDOW_SIZE: usize = 64;

impl ProofComplexity {
    /// Create a new complexity tracker for a formula with `num_vars` variables.
    #[must_use]
    pub fn new(num_vars: u32) -> Self {
        Self {
            width: 0,
            space: 0,
            depth: 0,
            num_vars,
            num_conflicts: 0,
            total_width: 0,
            recent_widths: Vec::with_capacity(RECENT_WINDOW_SIZE),
            active_clause_count: 0,
        }
    }

    /// Update metrics when a new conflict clause is derived.
    ///
    /// `clause_width` is the number of literals in the conflict clause.
    /// `proof_depth` is the depth of the resolution chain that produced it.
    /// `current_learned_count` is the current size of the learned clause DB.
    pub fn update_on_conflict(
        &mut self,
        clause_width: usize,
        proof_depth: usize,
        current_learned_count: usize,
    ) {
        self.num_conflicts += 1;
        self.total_width += clause_width as u64;

        if clause_width > self.width {
            self.width = clause_width;
        }
        if proof_depth > self.depth {
            self.depth = proof_depth;
        }

        self.active_clause_count = current_learned_count;
        if current_learned_count > self.space {
            self.space = current_learned_count;
        }

        // Maintain sliding window of recent widths.
        if self.recent_widths.len() >= RECENT_WINDOW_SIZE {
            self.recent_widths.remove(0);
        }
        self.recent_widths.push(clause_width);
    }

    /// Whether the solver should restart based on proof complexity metrics.
    ///
    /// The key insight from Ben-Sasson & Wigderson (2001): if the solver
    /// is consistently deriving clauses of width > sqrt(n), it is on an
    /// exponentially hard subproblem (the proof size grows as
    /// 2^{width^2/n}). Restarting abandons this search branch.
    ///
    /// Returns `true` when the recent average width exceeds sqrt(n).
    #[must_use]
    pub fn should_restart(&self) -> bool {
        if self.recent_widths.is_empty() || self.num_vars == 0 {
            return false;
        }
        let sqrt_n = (self.num_vars as f64).sqrt();
        let recent_avg = self.recent_average_width();
        recent_avg > sqrt_n
    }

    /// Compute the recent average conflict clause width.
    ///
    /// Uses the sliding window of the last `RECENT_WINDOW_SIZE` conflicts.
    /// Returns 0.0 if no conflicts have been recorded.
    #[must_use]
    pub fn recent_average_width(&self) -> f64 {
        if self.recent_widths.is_empty() {
            return 0.0;
        }
        let sum: usize = self.recent_widths.iter().sum();
        sum as f64 / self.recent_widths.len() as f64
    }

    /// Compute the global average conflict clause width.
    ///
    /// Returns 0.0 if no conflicts have been recorded.
    #[must_use]
    pub fn global_average_width(&self) -> f64 {
        if self.num_conflicts == 0 {
            return 0.0;
        }
        self.total_width as f64 / self.num_conflicts as f64
    }

    /// The width complexity threshold: sqrt(n).
    ///
    /// Clauses wider than this threshold indicate the solver is in an
    /// exponentially hard region of the proof search space.
    #[must_use]
    pub fn width_threshold(&self) -> f64 {
        (self.num_vars as f64).sqrt()
    }

    /// Check the space-width inequality (Atserias & Dalmau 2008).
    ///
    /// Returns `true` if the observed space >= width - c * log(n) for
    /// a constant c. This is a necessary condition for any valid
    /// resolution refutation. If violated, it indicates a bug in the
    /// complexity tracking (not in the solver).
    #[must_use]
    pub fn check_space_width_inequality(&self) -> bool {
        if self.num_vars == 0 || self.width == 0 {
            return true;
        }
        let log_n = (self.num_vars as f64).ln();
        // space >= width - c * log(n), with c = 1 (conservative constant).
        // Rearranged: space + log(n) >= width.
        (self.space as f64) + log_n >= self.width as f64
    }

    /// Maximum clause width observed.
    #[must_use]
    pub fn max_width(&self) -> usize {
        self.width
    }

    /// Maximum space (peak learned clause count) observed.
    #[must_use]
    pub fn max_space(&self) -> usize {
        self.space
    }

    /// Maximum proof depth observed.
    #[must_use]
    pub fn max_depth(&self) -> usize {
        self.depth
    }

    /// Number of variables in the formula.
    #[must_use]
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    /// Total number of conflicts recorded.
    #[must_use]
    pub fn num_conflicts(&self) -> u64 {
        self.num_conflicts
    }

    /// Current count of active learned clauses.
    #[must_use]
    pub fn active_clause_count(&self) -> usize {
        self.active_clause_count
    }

    /// Estimated proof size lower bound based on the width-size trade-off.
    ///
    /// Returns 2^{(w - W(F))^2 / n} where w is the observed maximum width
    /// and W(F) is the initial clause width (approximated by 3, the
    /// typical width of learned clauses in structured formulas).
    ///
    /// Returns `f64::INFINITY` if the estimate overflows.
    #[must_use]
    pub fn estimated_proof_size_lower_bound(&self) -> f64 {
        if self.num_vars == 0 || self.width == 0 {
            return 1.0;
        }
        // W(F) ~ initial clause width; approximate as 3 for 3-SAT.
        let initial_width = 3.0_f64;
        let excess = (self.width as f64 - initial_width).max(0.0);
        let exponent = excess * excess / self.num_vars as f64;
        2.0_f64.powf(exponent)
    }
}
