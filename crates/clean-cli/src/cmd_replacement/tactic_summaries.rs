// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Count summaries and the strict solver fragment dashboard.

use super::*;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityCountSummary {
    pub(crate) tactic_row_count: usize,
    pub(crate) lean4_total: u32,
    pub(crate) clean_total: u32,
    pub(crate) matched_total: u32,
    pub(crate) clean_gap_total: u32,
    pub(crate) proof_carrying_rows: usize,
    pub(crate) partial_rows: usize,
    pub(crate) parity_gap_rows: usize,
}

impl TacticParityCountSummary {
    pub(crate) fn from_rows(rows: &[TacticParityCountRow]) -> Self {
        Self {
            tactic_row_count: rows.len(),
            lean4_total: rows.iter().map(|row| row.lean4_count).sum(),
            clean_total: rows.iter().map(|row| row.clean_count).sum(),
            matched_total: rows.iter().map(|row| row.matched_count).sum(),
            clean_gap_total: rows.iter().map(|row| row.clean_gap_count).sum(),
            proof_carrying_rows: rows
                .iter()
                .filter(|row| row.status == TacticParityStatus::ProofCarrying)
                .count(),
            partial_rows: rows
                .iter()
                .filter(|row| row.status == TacticParityStatus::EvidenceBackedPartial)
                .count(),
            parity_gap_rows: rows
                .iter()
                .filter(|row| row.status == TacticParityStatus::Lean4ParityGap)
                .count(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityCountRow {
    pub(crate) tactic: &'static str,
    pub(crate) status: TacticParityStatus,
    pub(crate) lean4_count: u32,
    pub(crate) clean_count: u32,
    pub(crate) matched_count: u32,
    pub(crate) clean_gap_count: u32,
    pub(crate) evidence: &'static str,
    pub(crate) blocker: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) generated_cases: Option<TacticParityGeneratedCaseEvidence>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) remaining_blocker: Option<TacticParityGapEvidence>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityGeneratedCaseEvidence {
    pub(crate) generated_by: &'static str,
    pub(crate) fail_closed: bool,
    pub(crate) case_count: u32,
    pub(crate) matched_case_count: u32,
    pub(crate) cases: Vec<TacticParityGeneratedCase>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityGeneratedCase {
    pub(crate) case_id: &'static str,
    pub(crate) lean4_fixture: &'static str,
    pub(crate) clean_fixture: &'static str,
    pub(crate) expected_behavior: &'static str,
    pub(crate) clean_behavior: &'static str,
    pub(crate) matched: bool,
    pub(crate) evidence: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityGapEvidence {
    pub(crate) fail_closed: bool,
    pub(crate) gap_count: u32,
    pub(crate) representative_gap_cases: Vec<&'static str>,
    pub(crate) gate_required_to_clear: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct StrictSolverFragmentCountSummary {
    pub(crate) source_artifact: &'static str,
    pub(crate) row_count: usize,
    pub(crate) supported_zero_trust_rows: usize,
    pub(crate) unsupported_reject_and_fallback_rows: usize,
    pub(crate) zero_trust_recovery_rows: usize,
}

impl StrictSolverFragmentCountSummary {
    pub(crate) fn from_dashboard(dashboard: &StrictSolverFragmentDashboard) -> Self {
        Self {
            source_artifact: dashboard.source_artifact,
            row_count: dashboard.row_count,
            supported_zero_trust_rows: dashboard.supported_zero_trust_rows,
            unsupported_reject_and_fallback_rows: dashboard.unsupported_reject_and_fallback_rows,
            zero_trust_recovery_rows: dashboard.zero_trust_recovery_rows,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct StrictReconstructionRow {
    pub(crate) fragment: &'static str,
    pub(crate) strict_mode: bool,
    pub(crate) direct_trust_rejected: bool,
    pub(crate) zero_trust_recovery: bool,
    pub(crate) residual_trust_allowed_outside_strict: bool,
    pub(crate) status: StrictReconstructionStatus,
    pub(crate) evidence: &'static str,
    pub(crate) blocker: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct StrictSolverFragmentDashboard {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) source_artifact: &'static str,
    pub(crate) status: &'static str,
    pub(crate) strict_reconstruction_gate: StrictSolverFragmentDashboardGate,
    pub(crate) row_count: usize,
    pub(crate) supported_zero_trust_rows: usize,
    pub(crate) unsupported_reject_and_fallback_rows: usize,
    pub(crate) direct_trust_rejected_rows: usize,
    pub(crate) zero_trust_recovery_rows: usize,
    pub(crate) residual_trust_acceptance_rows: usize,
    pub(crate) rows: Vec<StrictSolverFragmentDashboardRow>,
}

impl StrictSolverFragmentDashboard {
    pub(crate) fn current() -> Self {
        let rows = strict_solver_fragment_dashboard_rows();
        let row_count = rows.len();
        let supported_zero_trust_rows = rows
            .iter()
            .filter(|row| row.behavior == StrictSolverFragmentBehavior::SupportedZeroTrust)
            .count();
        let unsupported_reject_and_fallback_rows = rows
            .iter()
            .filter(|row| {
                row.behavior == StrictSolverFragmentBehavior::UnsupportedRejectAndFallback
            })
            .count();
        let direct_trust_rejected_rows =
            rows.iter().filter(|row| row.direct_trust_rejected).count();
        let zero_trust_recovery_rows = rows.iter().filter(|row| row.zero_trust_recovery).count();
        let residual_trust_acceptance_rows = rows
            .iter()
            .filter(|row| row.residual_trust_accepted_in_strict)
            .count();
        let strict_reconstruction_gate = StrictSolverFragmentDashboardGate::from_counts(
            row_count,
            supported_zero_trust_rows,
            zero_trust_recovery_rows,
            residual_trust_acceptance_rows,
        );

        Self {
            schema_version: STRICT_SOLVER_FRAGMENT_DASHBOARD_SCHEMA_VERSION,
            generated_by: "clean replacement tactic-parity --json",
            source_artifact: STRICT_SOLVER_FRAGMENT_DASHBOARD_PATH,
            status: if strict_reconstruction_gate.passed {
                "passed"
            } else {
                "blocked"
            },
            strict_reconstruction_gate,
            row_count,
            supported_zero_trust_rows,
            unsupported_reject_and_fallback_rows,
            direct_trust_rejected_rows,
            zero_trust_recovery_rows,
            residual_trust_acceptance_rows,
            rows,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct StrictSolverFragmentDashboardGate {
    pub(crate) gate: &'static str,
    pub(crate) passed: bool,
    pub(crate) row_count: StrictSolverFragmentCountGate,
    pub(crate) supported_zero_trust_rows: StrictSolverFragmentCountGate,
    pub(crate) zero_trust_recovery_rows: StrictSolverFragmentCountGate,
    pub(crate) residual_trust_acceptance_rows: StrictSolverFragmentCountGate,
    pub(crate) blocker: &'static str,
}

impl StrictSolverFragmentDashboardGate {
    pub(crate) fn from_counts(
        row_count: usize,
        supported_zero_trust_rows: usize,
        zero_trust_recovery_rows: usize,
        residual_trust_acceptance_rows: usize,
    ) -> Self {
        let row_count = StrictSolverFragmentCountGate::new(
            STRICT_SOLVER_FRAGMENT_EXPECTED_ROW_COUNT,
            row_count,
        );
        let supported_zero_trust_rows = StrictSolverFragmentCountGate::new(
            STRICT_SOLVER_FRAGMENT_EXPECTED_SUPPORTED_ZERO_TRUST_ROWS,
            supported_zero_trust_rows,
        );
        let zero_trust_recovery_rows = StrictSolverFragmentCountGate::new(
            STRICT_SOLVER_FRAGMENT_EXPECTED_ZERO_TRUST_RECOVERY_ROWS,
            zero_trust_recovery_rows,
        );
        let residual_trust_acceptance_rows = StrictSolverFragmentCountGate::new(
            STRICT_SOLVER_FRAGMENT_EXPECTED_RESIDUAL_TRUST_ACCEPTANCE_ROWS,
            residual_trust_acceptance_rows,
        );
        let passed = row_count.passed
            && supported_zero_trust_rows.passed
            && zero_trust_recovery_rows.passed
            && residual_trust_acceptance_rows.passed;

        Self {
            gate: "strict-reconstruction-generated-evidence",
            passed,
            row_count,
            supported_zero_trust_rows,
            zero_trust_recovery_rows,
            residual_trust_acceptance_rows,
            blocker: if passed {
                "generated strict solver-fragment counts match the strict reconstruction gate"
            } else {
                "generated strict solver-fragment counts do not match the strict reconstruction gate"
            },
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct StrictSolverFragmentCountGate {
    pub(crate) expected: usize,
    pub(crate) observed: usize,
    pub(crate) passed: bool,
}

impl StrictSolverFragmentCountGate {
    pub(crate) fn new(expected: usize, observed: usize) -> Self {
        Self {
            expected,
            observed,
            passed: expected == observed,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct StrictSolverFragmentDashboardRow {
    pub(crate) fragment: &'static str,
    pub(crate) behavior: StrictSolverFragmentBehavior,
    pub(crate) strict_mode: bool,
    pub(crate) direct_trust_rejected: bool,
    pub(crate) zero_trust_required: bool,
    pub(crate) zero_trust_recovery: bool,
    pub(crate) residual_trust_accepted_in_strict: bool,
    pub(crate) evidence: &'static str,
}
