// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::bridge::ay_backend::{
    AyProofBackend, AyProofResult, KernelReconstructionCandidate, ResidualTrustSummary,
    TrustBudget, VariableMapping,
};
use clean_kernel::Expr;
use std::fmt::Write;

#[derive(Debug)]
pub(super) enum ReconstructionGateStatus {
    NoCandidate,
    ZeroTrust,
    WithResidual {
        trust_count: usize,
        residual: ResidualTrustSummary,
    },
}

impl std::fmt::Display for ReconstructionGateStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoCandidate => write!(f, "NO_CANDIDATE"),
            Self::ZeroTrust => write!(f, "ZERO_TRUST"),
            Self::WithResidual {
                trust_count,
                residual,
            } => {
                write!(f, "RESIDUAL(trust={trust_count}")?;
                if residual.arithmetic_boundary_steps() > 0 {
                    write!(f, ", arith={}", residual.arithmetic_boundary_steps())?;
                }
                if residual.alethe_trust_steps() > 0 {
                    write!(f, ", alethe={}", residual.alethe_trust_steps())?;
                }
                if residual.local_gap_steps() > 0 {
                    write!(f, ", gap={}", residual.local_gap_steps())?;
                }
                write!(f, ")")
            }
        }
    }
}

pub(super) struct ReplacementGateRow {
    pub(super) case: &'static str,
    pub(super) proof_present: bool,
    pub(super) native_quality_complete: bool,
    pub(super) unlimited: ReconstructionGateStatus,
    pub(super) zero_trust: ReconstructionGateStatus,
}

impl ReplacementGateRow {
    pub(super) fn disposition(&self) -> &'static str {
        match (&self.unlimited, &self.zero_trust) {
            (ReconstructionGateStatus::NoCandidate, _) => "blocked on reconstruction absence",
            (_, ReconstructionGateStatus::ZeroTrust) => "replacement-ready",
            (ReconstructionGateStatus::ZeroTrust, ReconstructionGateStatus::NoCandidate) => {
                "replacement-ready"
            }
            (
                ReconstructionGateStatus::WithResidual { .. },
                ReconstructionGateStatus::NoCandidate,
            ) => "blocked on residual trust",
            (ReconstructionGateStatus::WithResidual { .. }, _) => "blocked on residual trust",
            (
                ReconstructionGateStatus::ZeroTrust,
                ReconstructionGateStatus::WithResidual { .. },
            ) => "replacement-ready",
        }
    }
}

pub(super) fn classify_candidate(
    candidate: &Option<KernelReconstructionCandidate>,
) -> ReconstructionGateStatus {
    match candidate {
        None => ReconstructionGateStatus::NoCandidate,
        Some(c) if c.quality().is_fully_verified() => ReconstructionGateStatus::ZeroTrust,
        Some(c) => ReconstructionGateStatus::WithResidual {
            trust_count: c.quality().trust_count(),
            residual: c.residual(),
        },
    }
}

pub(super) fn evaluate_gate_case(
    backend: &mut AyProofBackend,
    map: &VariableMapping,
    negated_goal: &Expr,
) -> (
    bool,
    bool,
    Option<KernelReconstructionCandidate>,
    Option<KernelReconstructionCandidate>,
) {
    let result = backend
        .check_sat()
        .expect("proof-enabled backend should solve retained fixture");
    assert!(
        matches!(&result, AyProofResult::Unsat { .. }),
        "expected UNSAT from retained fixture, got {result:?}",
    );

    let mut proof_present = false;
    let mut native_quality_complete = false;
    if let AyProofResult::Unsat { proof, quality, .. } = &result {
        (proof_present, native_quality_complete) = (
            proof.as_ref().is_some_and(|text| !text.trim().is_empty()),
            quality.as_ref().is_some_and(|q| q.is_complete()),
        );
    }

    let unlimited = backend.attempt_kernel_reconstruction_with_budget(
        map,
        negated_goal,
        TrustBudget::Unlimited,
    );
    let zero_trust = backend.attempt_kernel_reconstruction_with_budget(
        map,
        negated_goal,
        TrustBudget::ZeroTrust,
    );

    (
        proof_present,
        native_quality_complete,
        unlimited,
        zero_trust,
    )
}

pub(super) fn print_and_verify_gate_matrix(rows: &[ReplacementGateRow]) {
    let mut matrix = String::new();
    writeln!(
        &mut matrix,
        "\n=== #2386 Proof-Producing Replacement Gate ===\n"
    )
    .expect("write matrix header");
    writeln!(
        &mut matrix,
        "{:<10} {:<8} {:<10} {:<30} {:<30} DISPOSITION",
        "CASE", "PROOF", "NATIVE_OK", "UNLIMITED", "ZERO_TRUST"
    )
    .expect("write matrix columns");
    writeln!(&mut matrix, "{}", "-".repeat(110)).expect("write matrix divider");
    for row in rows {
        writeln!(
            &mut matrix,
            "{:<10} {:<8} {:<10} {:<30} {:<30} {}",
            row.case,
            if row.proof_present { "YES" } else { "NO" },
            if row.native_quality_complete {
                "COMPLETE"
            } else {
                "INCOMPLETE"
            },
            format!("{}", row.unlimited),
            format!("{}", row.zero_trust),
            row.disposition(),
        )
        .expect("write matrix row");
    }
    writeln!(&mut matrix).expect("write matrix trailer");
    tracing::info!("{matrix}");

    for row in rows {
        if matches!(row.zero_trust, ReconstructionGateStatus::ZeroTrust) {
            assert!(
                !matches!(row.unlimited, ReconstructionGateStatus::NoCandidate),
                "{}: zero-trust accepted but unlimited has no candidate — inconsistent",
                row.case,
            );
        }
    }
}
