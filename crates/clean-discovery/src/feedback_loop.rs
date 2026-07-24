// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feedback integration for adaptive candidate generation.
//!
//! Analyzes kernel rejections to guide the next batch of candidates and
//! expands around accepted theorems by perturbing parameters. This closes
//! the AI -> elaboration -> kernel -> feedback cycle.
//!
//! Part of #3258.

use crate::candidate::{CandidateId, CandidateTheorem, ParamValue, VerificationOutcome};
use crate::family::TheoremFamily;
use crate::feedback::{FeedbackAnalyzer, FeedbackCategory, FeedbackEntry};

/// Direction to shift a numeric parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AdjustDirection {
    /// Increase the parameter value.
    Increase,
    /// Decrease the parameter value.
    Decrease,
}

/// Suggested adjustment after analyzing a kernel rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CandidateAdjustment {
    /// Hint about the expected type to guide proof term construction.
    TypeFixHint { expected_pattern: String },
    /// Shift a specific numeric parameter up or down.
    ParameterShift {
        param_index: usize,
        direction: AdjustDirection,
    },
    /// Suggest switching to a different theorem family.
    StrategySwitch { suggested_family: TheoremFamily },
    /// No actionable adjustment could be derived.
    NoAdjustment,
}

/// Aggregate counts of adjustment types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct AdjustmentSummary {
    /// Number of type fix hints issued.
    pub type_fix_hints: u64,
    /// Number of parameter shifts issued.
    pub parameter_shifts: u64,
    /// Number of strategy switches issued.
    pub strategy_switches: u64,
    /// Number of no-adjustment results.
    pub no_adjustments: u64,
    /// Total adjustments recorded.
    pub total: u64,
}

/// Manages the feedback cycle between kernel verification and candidate
/// generation.
///
/// Tracks rejection/acceptance counts and records adjustment history
/// for downstream analysis.
pub struct FeedbackLoop {
    analyzer: FeedbackAnalyzer,
    adjustment_history: Vec<CandidateAdjustment>,
    acceptance_count: u64,
    rejection_count: u64,
    /// Counter for generating unique candidate IDs in neighbor expansion.
    next_id: u64,
}

impl FeedbackLoop {
    /// Create a new feedback loop with fresh state.
    #[must_use]
    pub fn new() -> Self {
        Self {
            analyzer: FeedbackAnalyzer::new(),
            adjustment_history: Vec::new(),
            acceptance_count: 0,
            rejection_count: 0,
            next_id: 1_000_000,
        }
    }

    /// Analyze a rejected candidate and produce an adjustment hint.
    ///
    /// Records the adjustment in history for summary reporting.
    pub fn process_rejection(&mut self, outcome: &VerificationOutcome) -> CandidateAdjustment {
        self.rejection_count = self.rejection_count.saturating_add(1);

        let adjustment = self
            .analyzer
            .classify(outcome)
            .map_or(CandidateAdjustment::NoAdjustment, |entry| {
                feedback_to_adjustment(&entry, outcome)
            });

        self.adjustment_history.push(adjustment.clone());
        adjustment
    }

    /// Generate neighbor candidates by perturbing accepted theorem parameters.
    ///
    /// For each `Nat` parameter, generates candidates with value +1 and -1
    /// (if > 0). Returns fresh candidates with unique IDs.
    pub fn process_acceptance(&mut self, candidate: &CandidateTheorem) -> Vec<CandidateTheorem> {
        self.acceptance_count = self.acceptance_count.saturating_add(1);
        let mut neighbors = Vec::new();

        for (idx, value) in candidate.params.0.iter().enumerate() {
            let ParamValue::Nat(current) = value else {
                continue;
            };

            // Try +1
            if let Some(up) = current.checked_add(1) {
                neighbors.push(self.build_neighbor(candidate, idx, up));
            }

            // Try -1 (if > 0)
            if *current > 0 {
                neighbors.push(self.build_neighbor(candidate, idx, current - 1));
            }
        }

        neighbors
    }

    /// Number of accepted candidates processed.
    #[must_use]
    pub fn acceptance_count(&self) -> u64 {
        self.acceptance_count
    }

    /// Number of rejected candidates processed.
    #[must_use]
    pub fn rejection_count(&self) -> u64 {
        self.rejection_count
    }

    /// Summarize the types of adjustments issued so far.
    #[must_use]
    pub fn adjustment_summary(&self) -> AdjustmentSummary {
        let mut summary = AdjustmentSummary::default();
        for adj in &self.adjustment_history {
            match adj {
                CandidateAdjustment::TypeFixHint { .. } => summary.type_fix_hints += 1,
                CandidateAdjustment::ParameterShift { .. } => summary.parameter_shifts += 1,
                CandidateAdjustment::StrategySwitch { .. } => summary.strategy_switches += 1,
                CandidateAdjustment::NoAdjustment => summary.no_adjustments += 1,
            }
        }
        summary.total = self.adjustment_history.len() as u64;
        summary
    }

    /// Build a neighbor candidate by replacing one Nat parameter.
    fn build_neighbor(
        &mut self,
        base: &CandidateTheorem,
        param_index: usize,
        new_value: u64,
    ) -> CandidateTheorem {
        let mut params = base.params.clone();
        if let Some(slot) = params.0.get_mut(param_index) {
            *slot = ParamValue::Nat(new_value);
        }

        let id = CandidateId(self.next_id);
        self.next_id = self.next_id.saturating_add(1);

        CandidateTheorem {
            id,
            family: base.family,
            params,
            statement: base.statement.clone(),
            proof: base.proof.clone(),
        }
    }
}

impl Default for FeedbackLoop {
    fn default() -> Self {
        Self::new()
    }
}

/// Map a feedback classification to a candidate adjustment.
fn feedback_to_adjustment(
    entry: &FeedbackEntry,
    outcome: &VerificationOutcome,
) -> CandidateAdjustment {
    match &entry.category {
        FeedbackCategory::TypeMismatch | FeedbackCategory::DefEqFailure => {
            let hint = outcome
                .inferred_type
                .as_ref()
                .map(|expr| format!("{expr:?}"))
                .or_else(|| entry.param_hint.clone())
                .unwrap_or_else(|| "proof_term : statement".to_owned());
            CandidateAdjustment::TypeFixHint {
                expected_pattern: hint,
            }
        }
        FeedbackCategory::UniverseError => CandidateAdjustment::ParameterShift {
            param_index: 0,
            direction: AdjustDirection::Decrease,
        },
        FeedbackCategory::SortError => CandidateAdjustment::StrategySwitch {
            suggested_family: TheoremFamily::NewAbstractDomain,
        },
        FeedbackCategory::UnknownConst(_) | FeedbackCategory::Other(_) => {
            CandidateAdjustment::NoAdjustment
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::candidate::ParamVec;
    use clean_kernel::Expr;

    fn make_candidate(params: Vec<ParamValue>) -> CandidateTheorem {
        CandidateTheorem {
            id: CandidateId(42),
            family: TheoremFamily::CertSizeBound,
            params: ParamVec(params),
            statement: Expr::prop(),
            proof: None,
        }
    }

    fn make_rejected(error: &str) -> VerificationOutcome {
        VerificationOutcome {
            candidate_id: CandidateId(42),
            verified: false,
            inferred_type: None,
            error: Some(error.to_owned()),
            time_ns: 100,
        }
    }

    #[test]
    fn test_process_rejection_type_mismatch() {
        let mut fl = FeedbackLoop::new();
        let adj = fl.process_rejection(&make_rejected("Type mismatch: expected Nat, got Bool"));

        assert!(
            matches!(adj, CandidateAdjustment::TypeFixHint { .. }),
            "type mismatch should produce TypeFixHint"
        );
        assert_eq!(fl.rejection_count(), 1);
        assert_eq!(fl.adjustment_history.len(), 1);
    }

    #[test]
    fn test_process_rejection_universe_error() {
        let mut fl = FeedbackLoop::new();
        let adj = fl.process_rejection(&make_rejected("universe level constraint violated"));

        assert_eq!(
            adj,
            CandidateAdjustment::ParameterShift {
                param_index: 0,
                direction: AdjustDirection::Decrease,
            }
        );
    }

    #[test]
    fn test_process_rejection_sort_error_strategy_switch() {
        let mut fl = FeedbackLoop::new();
        let adj = fl.process_rejection(&make_rejected("Expected sort, got: App(...)"));

        assert!(
            matches!(adj, CandidateAdjustment::StrategySwitch { .. }),
            "sort error should suggest strategy switch"
        );
    }

    #[test]
    fn test_process_rejection_unknown_const_no_adjustment() {
        let mut fl = FeedbackLoop::new();
        let adj = fl.process_rejection(&make_rejected("Unknown constant: Foo.bar"));

        assert_eq!(adj, CandidateAdjustment::NoAdjustment);
    }

    #[test]
    fn test_process_acceptance_generates_neighbors() {
        let mut fl = FeedbackLoop::new();
        let candidate = make_candidate(vec![
            ParamValue::Nat(2),
            ParamValue::Choice(1),
            ParamValue::Nat(0),
        ]);
        let neighbors = fl.process_acceptance(&candidate);

        // Nat(2) generates +1=3 and -1=1; Choice(1) skipped;
        // Nat(0) generates +1=1 (no -1 since 0).
        assert_eq!(neighbors.len(), 3, "expected 3 neighbors");
        assert_eq!(fl.acceptance_count(), 1);

        // All IDs should be unique.
        let ids: std::collections::HashSet<_> = neighbors.iter().map(|c| c.id).collect();
        assert_eq!(ids.len(), 3, "all neighbor IDs should be unique");
    }

    #[test]
    fn test_process_acceptance_empty_params() {
        let mut fl = FeedbackLoop::new();
        let candidate = make_candidate(Vec::new());
        let neighbors = fl.process_acceptance(&candidate);

        assert!(neighbors.is_empty(), "no params means no neighbors");
        assert_eq!(fl.acceptance_count(), 1);
    }

    #[test]
    fn test_adjustment_summary() {
        let mut fl = FeedbackLoop::new();
        fl.adjustment_history = vec![
            CandidateAdjustment::TypeFixHint {
                expected_pattern: "Prop".to_owned(),
            },
            CandidateAdjustment::TypeFixHint {
                expected_pattern: "Eq".to_owned(),
            },
            CandidateAdjustment::ParameterShift {
                param_index: 1,
                direction: AdjustDirection::Decrease,
            },
            CandidateAdjustment::StrategySwitch {
                suggested_family: TheoremFamily::DomainTightness,
            },
            CandidateAdjustment::NoAdjustment,
        ];

        let summary = fl.adjustment_summary();
        assert_eq!(summary.type_fix_hints, 2);
        assert_eq!(summary.parameter_shifts, 1);
        assert_eq!(summary.strategy_switches, 1);
        assert_eq!(summary.no_adjustments, 1);
        assert_eq!(summary.total, 5);
    }
}
