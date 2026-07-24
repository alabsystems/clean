// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VSIDS (Variable State Independent Decaying Sum) decision heuristic.
//!
//! VSIDS is the dominant decision heuristic in modern CDCL SAT solvers.
//! Each variable has an activity score that is bumped when the variable
//! participates in conflict analysis. Decay is implemented efficiently
//! by increasing the bump increment rather than scaling all scores down.
//!
//! Reference: Moskewicz et al., "Chaff: Engineering an Efficient SAT Solver",
//! DAC 2001. Extended in MiniSat (Een & Sorensson, 2003).

use super::AssignValue;
use crate::spec::ProofStatus;

/// Threshold for rescaling activity scores to prevent floating-point overflow.
const RESCALE_THRESHOLD: f64 = 1e100;

/// VSIDS activity scores.
///
/// Each variable has an activity score. When a variable participates in
/// conflict analysis, its score is bumped. Decay is implemented by
/// increasing the bump amount rather than dividing all scores — this is
/// the MiniSat optimization that avoids O(n) work per conflict.
#[derive(Debug, Clone)]
pub struct VsidsScores {
    /// Activity score for each variable (index 0 unused, 1..=num_vars valid).
    activity: Vec<f64>,
    /// Bump increment (grows over time to implement decay).
    bump_amount: f64,
    /// Decay factor (typically 0.95). After each conflict, bump_amount
    /// is divided by this, which is equivalent to multiplying all other
    /// scores by decay_factor.
    decay_factor: f64,
}

impl VsidsScores {
    /// Create a new VSIDS score table for `num_vars` variables.
    ///
    /// All variables start with equal activity (0.0).
    /// The decay factor controls how quickly old activity fades:
    /// - 0.95 is the MiniSat default (slow decay, long memory)
    /// - 0.80 is aggressive (fast decay, recent conflicts dominate)
    ///
    /// # Panics
    /// Panics if `decay_factor` is not in (0, 1).
    #[must_use]
    pub fn new(num_vars: u32, decay_factor: f64) -> Self {
        assert!(
            decay_factor > 0.0 && decay_factor < 1.0,
            "decay_factor must be in (0, 1), got {decay_factor}"
        );
        Self {
            activity: vec![0.0; (num_vars + 1) as usize],
            bump_amount: 1.0,
            decay_factor,
        }
    }

    /// Bump variable activity (called during conflict analysis).
    ///
    /// Adds the current `bump_amount` to the variable's score. Since
    /// `bump_amount` grows over time (via `decay`), recent bumps
    /// contribute more than old ones — implementing exponential decay
    /// without touching all scores.
    pub fn bump(&mut self, var: u32) {
        let idx = var as usize;
        if idx < self.activity.len() {
            self.activity[idx] += self.bump_amount;
            self.rescale_if_needed();
        }
    }

    /// Apply decay: equivalent to multiplying all scores by `decay_factor`,
    /// but implemented by dividing `bump_amount` by `decay_factor` instead.
    ///
    /// This is the key MiniSat optimization: O(1) instead of O(n) per conflict.
    pub fn decay(&mut self) {
        self.bump_amount /= self.decay_factor;
    }

    /// Pick the unassigned variable with highest activity.
    ///
    /// Returns `None` if all variables are assigned. Variable indices start
    /// at 1 (index 0 is unused).
    #[must_use]
    pub fn pick_decision(&self, assignment: &[Option<AssignValue>]) -> Option<u32> {
        let mut best_var: Option<u32> = None;
        let mut best_score: f64 = -1.0;

        // Skip index 0 (unused). Iterate 1..min(activity.len, assignment.len).
        let limit = self.activity.len().min(assignment.len());
        // Index `var` looks up two parallel arrays (`assignment` and
        // `self.activity`) and is also emitted in the result.
        #[allow(clippy::needless_range_loop)]
        for var in 1..limit {
            if assignment[var].is_none() && self.activity[var] > best_score {
                best_score = self.activity[var];
                best_var = Some(var as u32);
            }
        }
        best_var
    }

    /// Get the activity score for a variable.
    #[must_use]
    pub fn activity(&self, var: u32) -> f64 {
        let idx = var as usize;
        if idx < self.activity.len() {
            self.activity[idx]
        } else {
            0.0
        }
    }

    /// Get the number of variables tracked.
    #[must_use]
    pub fn num_vars(&self) -> u32 {
        // activity[0] is unused, so num_vars = len - 1
        (self.activity.len().saturating_sub(1)) as u32
    }

    /// Rescale all activities when any exceeds threshold (prevents overflow).
    ///
    /// Divides all scores and the bump_amount by `RESCALE_THRESHOLD`.
    /// This preserves relative ordering of all scores.
    fn rescale_if_needed(&mut self) {
        let needs_rescale = self.activity.iter().any(|&a| a > RESCALE_THRESHOLD);
        if needs_rescale {
            let scale = 1.0 / RESCALE_THRESHOLD;
            for score in &mut self.activity {
                *score *= scale;
            }
            self.bump_amount *= scale;
        }
    }
}

/// VSIDS is a heuristic, not a soundness-critical component.
/// But we verify that it maintains a consistent total ordering on unassigned vars:
/// `pick_decision` always returns the variable with the strictly highest activity
/// among all unassigned variables, or `None` when all are assigned.
pub const VSIDS_ORDERING_CONSISTENT: ProofStatus = ProofStatus::DerivedPending;

/// The decay mechanism preserves relative ordering: if `activity(x) > activity(y)`
/// before decay, then `activity(x) > activity(y)` after decay. This follows because
/// decay is equivalent to multiplying all scores by a positive constant.
pub const VSIDS_DECAY_PRESERVES_ORDER: ProofStatus = ProofStatus::DerivedPending;

/// Rescaling preserves relative ordering for the same reason as decay:
/// dividing all scores by the same positive constant preserves comparisons.
pub const VSIDS_RESCALE_PRESERVES_ORDER: ProofStatus = ProofStatus::DerivedPending;
