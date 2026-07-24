// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Replacement rows, readiness accounting, and Python-wrapper proofs.

use super::*;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReplacementRow {
    pub(crate) id: &'static str,
    pub(crate) area: &'static str,
    pub(crate) owner_slot: &'static str,
    pub(crate) issue: IssueRef,
    /// The status hand-declared in `declared_replacement_rows()` — a *claim*.
    pub(crate) status: ReplacementStatus,
    /// Measured state of `evidence_artifact` on disk (M2). Derived, not declared.
    pub(crate) evidence_state: EvidenceState,
    /// `status` reconciled against `evidence_state` (M2): a declared `Green`
    /// with missing/stub evidence is reported as `PendingEvidence`. This is the
    /// status the launch gate consumes, so the scorecard cannot silently lie.
    pub(crate) effective_status: ReplacementStatus,
    pub(crate) required_for_launch: bool,
    pub(crate) gate_command: &'static str,
    pub(crate) evidence_artifact: &'static str,
    pub(crate) blocker: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReplacementReadinessAccounting {
    pub(crate) required_row_count: usize,
    pub(crate) green_required_row_count: usize,
    pub(crate) non_green_required_row_count: usize,
    pub(crate) blocked_required_row_count: usize,
    pub(crate) pending_evidence_required_row_count: usize,
    pub(crate) in_progress_required_row_count: usize,
    pub(crate) launch_blocking_row_ids: Vec<&'static str>,
    pub(crate) rust_first_launch_blocking_command_ids: Vec<&'static str>,
    pub(crate) python_wrapper_count: usize,
    pub(crate) remaining_python_wrapper_count: usize,
    pub(crate) launch_blocking_python_wrapper_count: usize,
    pub(crate) replacement_critical_python_wrapper_count: usize,
    pub(crate) rust_owned_python_wrapper_count: usize,
    pub(crate) demoted_python_reference_count: usize,
    pub(crate) certification_python_dependency_count: usize,
    pub(crate) certification_python_dependency_ids: Vec<&'static str>,
    pub(crate) non_launch_python_reference_ids: Vec<&'static str>,
    pub(crate) demoted_python_reference_proofs: Vec<DemotedPythonReferenceProof>,
    pub(crate) rust_owned_python_wrapper_proofs: Vec<RustOwnedPythonWrapperProof>,
    pub(crate) python_wrapper_fail_closed_policy: &'static str,
    pub(crate) python_wrappers: Vec<PythonWrapperReadiness>,
    pub(crate) benchmark_launch_gate: BenchmarkLaunchGateAccounting,
    pub(crate) product_surfaces: Vec<ProductSurfaceReadiness>,
    pub(crate) replacement_row_proof_surface_audit: ReplacementRowProofSurfaceAudit,
    pub(crate) reviewer_proof_command_deck: ReviewerProofCommandDeck,
    pub(crate) certification_wrapper_free_gate: CertificationWrapperFreeGate,
    pub(crate) blocker_evidence_requirements: Vec<ReplacementBlockerEvidenceRequirement>,
    pub(crate) full_replacement_certification_gate: FullReplacementCertificationGate,
}

impl ReplacementReadinessAccounting {
    pub(crate) fn from_current(
        rows: &[ReplacementRow],
        tooling: &RustFirstToolingStatus,
        zero_trust_gates_passed: bool,
        rows_ready: bool,
        launch_ready: bool,
    ) -> Self {
        // M2: readiness accounting reads the evidence-derived `effective_status`,
        // not the hand-declared `status`. A row whose evidence is missing/stub is
        // launch-blocking even if a human typed `Green` into the literal table.
        let required_rows: Vec<_> = rows.iter().filter(|row| row.required_for_launch).collect();
        let launch_blocking_row_ids = required_rows
            .iter()
            .filter(|row| row.effective_status != ReplacementStatus::Green)
            .map(|row| row.id)
            .collect();
        let rust_first_launch_blocking_command_ids = tooling
            .commands
            .iter()
            .filter(|row| {
                row.replacement_critical
                    && row.status != ToolMigrationStatus::RustOwned
                    && row.status != ToolMigrationStatus::Demoted
            })
            .map(|row| row.id)
            .collect();
        let product_surfaces = tooling
            .commands
            .iter()
            .filter(|row| {
                row.replacement_critical && row.planned_rust_surface.starts_with("clean ")
            })
            .map(ProductSurfaceReadiness::from_tooling_row)
            .collect();
        let python_wrappers: Vec<_> = tooling
            .commands
            .iter()
            .filter(|row| is_python_wrapper_command(row.command))
            .map(PythonWrapperReadiness::from_tooling_row)
            .collect();
        let certification_python_dependency_ids: Vec<&'static str> = python_wrappers
            .iter()
            .filter(|row| row.launch_blocking)
            .map(|row| row.id)
            .collect();
        let non_launch_python_reference_ids = python_wrappers
            .iter()
            .filter(|row| {
                !row.launch_blocking
                    && (!row.replacement_critical || row.status == ToolMigrationStatus::Demoted)
            })
            .map(|row| row.id)
            .collect();
        let demoted_python_reference_proofs = tooling
            .commands
            .iter()
            .filter(|row| {
                is_python_wrapper_command(row.command)
                    && row.status == ToolMigrationStatus::Demoted
                    && !row.replacement_critical
            })
            .map(DemotedPythonReferenceProof::from_tooling_row)
            .collect();
        let rust_owned_python_wrapper_proofs = tooling
            .commands
            .iter()
            .filter(|row| {
                is_python_wrapper_command(row.command)
                    && row.status == ToolMigrationStatus::RustOwned
                    && row.replacement_critical
            })
            .map(RustOwnedPythonWrapperProof::from_tooling_row)
            .collect();
        let benchmark_launch_gate = tooling
            .commands
            .iter()
            .find(|row| row.id == "benchmark-publication-launch")
            .map(BenchmarkLaunchGateAccounting::from_tooling_row)
            .unwrap_or_else(BenchmarkLaunchGateAccounting::missing);
        let replacement_row_proof_surface_audit = ReplacementRowProofSurfaceAudit::from_rows(rows);
        let reviewer_proof_command_deck = ReviewerProofCommandDeck::from_rows(rows);
        let certification_wrapper_free_gate = CertificationWrapperFreeGate::new(
            &certification_python_dependency_ids,
            &replacement_row_proof_surface_audit,
            &reviewer_proof_command_deck,
        );
        let blocker_evidence_requirements = required_rows
            .iter()
            .filter(|row| row.effective_status != ReplacementStatus::Green)
            .map(|row| ReplacementBlockerEvidenceRequirement::from_replacement_row(row))
            .collect();
        let full_replacement_certification_gate = FullReplacementCertificationGate::new(
            zero_trust_gates_passed,
            rows_ready,
            tooling.launch_ready,
            launch_ready,
        );

        Self {
            required_row_count: required_rows.len(),
            green_required_row_count: required_rows
                .iter()
                .filter(|row| row.effective_status == ReplacementStatus::Green)
                .count(),
            non_green_required_row_count: required_rows
                .iter()
                .filter(|row| row.effective_status != ReplacementStatus::Green)
                .count(),
            blocked_required_row_count: required_rows
                .iter()
                .filter(|row| row.effective_status == ReplacementStatus::Blocked)
                .count(),
            pending_evidence_required_row_count: required_rows
                .iter()
                .filter(|row| row.effective_status == ReplacementStatus::PendingEvidence)
                .count(),
            in_progress_required_row_count: required_rows
                .iter()
                .filter(|row| row.effective_status == ReplacementStatus::InProgress)
                .count(),
            launch_blocking_row_ids,
            rust_first_launch_blocking_command_ids,
            python_wrapper_count: python_wrappers.len(),
            remaining_python_wrapper_count: python_wrappers
                .iter()
                .filter(|row| row.status != ToolMigrationStatus::RustOwned)
                .count(),
            launch_blocking_python_wrapper_count: python_wrappers
                .iter()
                .filter(|row| row.launch_blocking)
                .count(),
            replacement_critical_python_wrapper_count: python_wrappers
                .iter()
                .filter(|row| row.replacement_critical)
                .count(),
            rust_owned_python_wrapper_count: python_wrappers
                .iter()
                .filter(|row| row.status == ToolMigrationStatus::RustOwned)
                .count(),
            demoted_python_reference_count: python_wrappers
                .iter()
                .filter(|row| row.status == ToolMigrationStatus::Demoted)
                .count(),
            certification_python_dependency_count: python_wrappers
                .iter()
                .filter(|row| row.launch_blocking)
                .count(),
            certification_python_dependency_ids,
            non_launch_python_reference_ids,
            demoted_python_reference_proofs,
            rust_owned_python_wrapper_proofs,
            python_wrapper_fail_closed_policy:
                "Any Python wrapper needed to generate or certify replacement evidence is launch-blocking unless it is Rust-owned or explicitly demoted as non-launch audit evidence.",
            python_wrappers,
            benchmark_launch_gate,
            product_surfaces,
            replacement_row_proof_surface_audit,
            reviewer_proof_command_deck,
            certification_wrapper_free_gate,
            blocker_evidence_requirements,
            full_replacement_certification_gate,
        }
    }
}

pub(crate) fn is_python_wrapper_command(command: &str) -> bool {
    command.contains("python3")
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct PythonWrapperReadiness {
    pub(crate) id: &'static str,
    pub(crate) command: &'static str,
    pub(crate) replacement_critical: bool,
    pub(crate) status: ToolMigrationStatus,
    pub(crate) target_rust_surface: &'static str,
    pub(crate) launch_blocking: bool,
    pub(crate) evidence_required_to_retire: &'static str,
}

impl PythonWrapperReadiness {
    pub(crate) fn from_tooling_row(row: &PythonToolMigrationRow) -> Self {
        Self {
            id: row.id,
            command: row.command,
            replacement_critical: row.replacement_critical,
            status: row.status,
            target_rust_surface: row.planned_rust_surface,
            launch_blocking: row.replacement_critical
                && row.status != ToolMigrationStatus::RustOwned
                && row.status != ToolMigrationStatus::Demoted,
            evidence_required_to_retire: row.removal_condition,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct DemotedPythonReferenceProof {
    pub(crate) id: &'static str,
    pub(crate) python_command: &'static str,
    pub(crate) status: ToolMigrationStatus,
    pub(crate) replacement_critical: bool,
    pub(crate) certifying: bool,
    pub(crate) rust_status_surface: &'static str,
    pub(crate) exclusion_reason: &'static str,
    pub(crate) evidence_required_to_reclassify: &'static str,
}

impl DemotedPythonReferenceProof {
    pub(crate) fn from_tooling_row(row: &PythonToolMigrationRow) -> Self {
        Self {
            id: row.id,
            python_command: row.command,
            status: row.status,
            replacement_critical: row.replacement_critical,
            certifying: false,
            rust_status_surface: row.planned_rust_surface,
            exclusion_reason: row.blocker,
            evidence_required_to_reclassify: row.removal_condition,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RustOwnedPythonWrapperProof {
    pub(crate) id: &'static str,
    pub(crate) legacy_python_command: &'static str,
    pub(crate) status: ToolMigrationStatus,
    pub(crate) replacement_critical: bool,
    pub(crate) python_path_certifying: bool,
    pub(crate) rust_certifying_surface: &'static str,
    pub(crate) legacy_python_path_status: &'static str,
    pub(crate) evidence_required_to_retire: &'static str,
}

impl RustOwnedPythonWrapperProof {
    pub(crate) fn from_tooling_row(row: &PythonToolMigrationRow) -> Self {
        Self {
            id: row.id,
            legacy_python_command: row.command,
            status: row.status,
            replacement_critical: row.replacement_critical,
            python_path_certifying: false,
            rust_certifying_surface: row.planned_rust_surface,
            legacy_python_path_status: row.blocker,
            evidence_required_to_retire: row.removal_condition,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReplacementRowProofSurfaceAudit {
    pub(crate) status: &'static str,
    pub(crate) checked_row_count: usize,
    pub(crate) wrapper_gate_row_count: usize,
    pub(crate) wrapper_gate_row_ids: Vec<&'static str>,
    pub(crate) wrapper_evidence_artifact_row_count: usize,
    pub(crate) wrapper_evidence_artifact_row_ids: Vec<&'static str>,
    pub(crate) reviewer_rule: &'static str,
}

impl ReplacementRowProofSurfaceAudit {
    pub(crate) fn from_rows(rows: &[ReplacementRow]) -> Self {
        let wrapper_gate_row_ids: Vec<_> = rows
            .iter()
            .filter(|row| is_wrapper_proof_surface(row.gate_command))
            .map(|row| row.id)
            .collect();
        let wrapper_evidence_artifact_row_ids: Vec<_> = rows
            .iter()
            .filter(|row| is_wrapper_proof_surface(row.evidence_artifact))
            .map(|row| row.id)
            .collect();
        let status =
            if wrapper_gate_row_ids.is_empty() && wrapper_evidence_artifact_row_ids.is_empty() {
                "passed"
            } else {
                "blocked"
            };

        Self {
            status,
            checked_row_count: rows.len(),
            wrapper_gate_row_count: wrapper_gate_row_ids.len(),
            wrapper_gate_row_ids,
            wrapper_evidence_artifact_row_count: wrapper_evidence_artifact_row_ids.len(),
            wrapper_evidence_artifact_row_ids,
            reviewer_rule:
                "Replacement row gate_command and evidence_artifact fields must not require python3, pytest, scripts/*.py, scripts/*.sh, or ./scripts/* wrappers for external certification.",
        }
    }
}

pub(crate) fn is_wrapper_proof_surface(value: &str) -> bool {
    value.contains("python3")
        || value.contains("pytest")
        || value.contains("scripts/") && (value.contains(".py") || value.contains(".sh"))
}
