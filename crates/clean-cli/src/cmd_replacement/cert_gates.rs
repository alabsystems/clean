// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certification, benchmark, and product-surface launch gates.

use super::*;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReplacementBlockerEvidenceRequirement {
    pub(crate) row_id: &'static str,
    pub(crate) owner_slot: &'static str,
    pub(crate) status: ReplacementStatus,
    pub(crate) gate_command: &'static str,
    pub(crate) evidence_artifact: &'static str,
    pub(crate) required_evidence: &'static str,
}

impl ReplacementBlockerEvidenceRequirement {
    pub(crate) fn from_replacement_row(row: &ReplacementRow) -> Self {
        Self {
            row_id: row.id,
            owner_slot: row.owner_slot,
            status: row.status,
            gate_command: row.gate_command,
            evidence_artifact: row.evidence_artifact,
            required_evidence: row.blocker,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct FullReplacementCertificationGate {
    pub(crate) target_claim: &'static str,
    pub(crate) launch_ready: bool,
    pub(crate) zero_trust_gates_passed: bool,
    pub(crate) replacement_rows_ready: bool,
    pub(crate) rust_first_tooling_ready: bool,
    pub(crate) required_conditions: Vec<&'static str>,
    pub(crate) fail_closed_reason: &'static str,
}

impl FullReplacementCertificationGate {
    pub(crate) fn new(
        zero_trust_gates_passed: bool,
        replacement_rows_ready: bool,
        rust_first_tooling_ready: bool,
        launch_ready: bool,
    ) -> Self {
        Self {
            target_claim: TARGET_CLAIM,
            launch_ready,
            zero_trust_gates_passed,
            replacement_rows_ready,
            rust_first_tooling_ready,
            required_conditions: vec![
                "all required replacement rows are green",
                "all required zero-trust gates pass from checked-in evidence",
                "replacement-critical Python wrappers are Rust-owned or explicitly demoted as non-launch evidence",
                "certification_python_dependency_count is zero; any nonzero value blocks external certification",
                "each non-green row has a concrete gate_command and evidence_artifact before public full-replacement claims",
            ],
            fail_closed_reason: if launch_ready {
                "all replacement certification conditions passed"
            } else {
                "clean full Lean4 replacement is not certified until every required row is green, zero-trust gates pass, and replacement-critical wrapper gates are accounted for"
            },
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct BenchmarkLaunchGateAccounting {
    pub(crate) id: &'static str,
    pub(crate) rust_surface: &'static str,
    pub(crate) python_gate_command: &'static str,
    pub(crate) status: ToolMigrationStatus,
    pub(crate) launch_blocking: bool,
    pub(crate) required_artifact: &'static str,
    pub(crate) required_parity_claim: &'static str,
}

impl BenchmarkLaunchGateAccounting {
    pub(crate) fn from_tooling_row(row: &PythonToolMigrationRow) -> Self {
        let required_parity_claim = if row.status == ToolMigrationStatus::Demoted
            && !row.replacement_critical
        {
            "benchmark publication evidence accepted for this replacement pass; Rust parity remains audit evidence, not launch-blocking replacement evidence"
        } else {
            "published-status, freshness, reachable source/publication commits, committed current-run evidence, canonical command/input/artifact coverage, dirty-evidence rejection, required-artifact rejection, and publication_commit artifact hash rejection"
        };

        Self {
            id: row.id,
            rust_surface: row.planned_rust_surface,
            python_gate_command: row.command,
            status: row.status,
            launch_blocking: row.replacement_critical
                && row.status != ToolMigrationStatus::RustOwned
                && row.status != ToolMigrationStatus::Demoted,
            required_artifact: "reports/benchmarks/publication/current.json",
            required_parity_claim,
        }
    }

    pub(crate) fn missing() -> Self {
        Self {
            id: "benchmark-publication-launch",
            rust_surface: "clean bench publication-check --launch --json",
            python_gate_command: "python3 scripts/check_benchmark_publication.py --check --launch",
            status: ToolMigrationStatus::MissingOwner,
            launch_blocking: true,
            required_artifact: "reports/benchmarks/publication/current.json",
            required_parity_claim:
                "missing benchmark launch migration row is itself a replacement blocker",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ProductSurfaceReadiness {
    pub(crate) id: &'static str,
    pub(crate) owner_slot: &'static str,
    pub(crate) surface: &'static str,
    pub(crate) source_artifact: &'static str,
    pub(crate) status: ToolMigrationStatus,
    pub(crate) replacement_critical: bool,
    pub(crate) launch_blocking: bool,
    pub(crate) blocker: &'static str,
}

impl ProductSurfaceReadiness {
    pub(crate) fn from_tooling_row(row: &PythonToolMigrationRow) -> Self {
        Self {
            id: row.id,
            owner_slot: row.owner_slot,
            surface: row.planned_rust_surface,
            source_artifact: row.source_artifact,
            status: row.status,
            replacement_critical: row.replacement_critical,
            launch_blocking: row.replacement_critical
                && row.status != ToolMigrationStatus::RustOwned
                && row.status != ToolMigrationStatus::Demoted,
            blocker: row.blocker,
        }
    }
}

impl ReplacementReportKind {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::NativeLibrary => "native-library",
            Self::MathverseReplay => "mathverse-replay",
            Self::LspInfoview => "lsp-infoview",
            Self::FrontendParity => "frontend-parity",
        }
    }

    pub(crate) fn expected_schema(self) -> &'static str {
        match self {
            Self::NativeLibrary => "clean-native-library-replacement-v1",
            Self::MathverseReplay => "clean-mathverse-replay-replacement-v1",
            Self::LspInfoview => "clean-lsp-infoview-parity-v1",
            Self::FrontendParity => "clean-frontend-parity-scorecard-v1",
        }
    }

    pub(crate) fn replacement_row_id(self) -> &'static str {
        match self {
            Self::NativeLibrary => "native-libraries",
            Self::MathverseReplay => "mathverse-replay",
            Self::LspInfoview => "lsp-infoview",
            Self::FrontendParity => "frontend-parity",
        }
    }

    pub(crate) fn issue(self) -> u64 {
        match self {
            Self::NativeLibrary => 3713,
            Self::MathverseReplay => 3714,
            Self::LspInfoview => 3709,
            Self::FrontendParity => 3700,
        }
    }

    pub(crate) fn status_field(self) -> &'static str {
        match self {
            Self::NativeLibrary | Self::MathverseReplay => "status",
            Self::LspInfoview | Self::FrontendParity => "overall_status",
        }
    }

    pub(crate) fn expected_status(self) -> &'static str {
        match self {
            Self::NativeLibrary | Self::MathverseReplay => "in_progress",
            Self::LspInfoview => "pending_evidence",
            Self::FrontendParity => "in_progress",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReplacementReportValidation {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) report_kind: ReplacementReportKind,
    pub(crate) report_path: String,
    pub(crate) report_schema_version: String,
    pub(crate) artifact_status: String,
    pub(crate) replacement_row: ReplacementReportRowValidation,
    pub(crate) validation_passed: bool,
    pub(crate) validation_status: &'static str,
    pub(crate) launch_ready_claimed: bool,
    pub(crate) row_count: usize,
    pub(crate) evidence_row_count: usize,
    pub(crate) blocker_count: usize,
    pub(crate) checks: Vec<ReplacementReportValidationCheck>,
    pub(crate) failures: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReplacementReportRowValidation {
    pub(crate) id: String,
    pub(crate) issue: u64,
    pub(crate) expected_by_scorecard: bool,
    pub(crate) recommended_scorecard_status: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReplacementReportValidationCheck {
    pub(crate) id: &'static str,
    pub(crate) status: ReplacementReportValidationCheckStatus,
    pub(crate) detail: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ReplacementReportValidationCheckStatus {
    Pass,
    Fail,
}
