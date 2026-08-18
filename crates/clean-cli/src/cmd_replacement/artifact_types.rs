// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Artifact structs, lane expectations, and status enums.

use super::*;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ZeroTrustGateRow {
    pub(crate) id: &'static str,
    pub(crate) issue: IssueRef,
    pub(crate) debt_class: ZeroTrustDebtClass,
    pub(crate) required_for_launch: bool,
    pub(crate) command: &'static str,
    pub(crate) source_artifacts: Vec<&'static str>,
    pub(crate) active_debt_count: u32,
    pub(crate) evidence_summary: String,
    pub(crate) status: ZeroTrustGateStatus,
    pub(crate) fail_closed_reason: String,
}

#[derive(Debug, Deserialize)]
pub(crate) struct Lean4BaselineArtifact {
    pub(crate) schema_version: u32,
    pub(crate) lean4_version: String,
    pub(crate) expressions_sha256: String,
    pub(crate) normalization_version: u32,
    pub(crate) cases: Vec<serde_json::Value>,
}

#[derive(Debug, Deserialize)]
pub(crate) struct UncheckedDeclRatchetArtifact {
    pub(crate) add_decl_structural_count: u32,
    pub(crate) add_decl_unchecked_count: u32,
    #[serde(default)]
    pub(crate) add_decl_structural_production_sites: Vec<UncheckedDeclProductionSite>,
    #[serde(default)]
    pub(crate) add_decl_unchecked_production_sites: Vec<UncheckedDeclProductionSite>,
    pub(crate) files: Vec<UncheckedDeclRatchetEntry>,
    pub(crate) last_updated: String,
}

#[derive(Debug, Deserialize)]
pub(crate) struct UncheckedDeclRatchetEntry {
    pub(crate) method: String,
    pub(crate) count: u32,
}

/// A live non-`#[cfg(test)]` call site of `add_decl_structural` /
/// `add_decl_unchecked`, individually accounted with its soundness
/// justification (G3 honesty correction, 2026-07-01). Each site contributes
/// `occurrences` (default 1) to the per-method ratchet count.
#[derive(Debug, Deserialize)]
pub(crate) struct UncheckedDeclProductionSite {
    pub(crate) file: String,
    pub(crate) method: String,
    pub(crate) trust: String,
    #[serde(default)]
    pub(crate) occurrences: Option<u32>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(crate) struct KernelSoundnessLaunchEvidenceArtifact {
    pub(crate) schema_version: String,
    pub(crate) generated_by: String,
    pub(crate) generated_at: String,
    pub(crate) gate_command: String,
    pub(crate) status: String,
    pub(crate) summary: KernelSoundnessLaunchEvidenceSummary,
    pub(crate) kernel_differential: KernelSoundnessLaunchDifferentialEvidence,
    pub(crate) source_sha256: BTreeMap<String, String>,
    pub(crate) lanes: Vec<KernelSoundnessLaunchLaneEvidence>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(crate) struct KernelSoundnessLaunchEvidenceSummary {
    pub(crate) expected_steps: u32,
    pub(crate) steps: u32,
    pub(crate) passed: u32,
    pub(crate) failed: u32,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(crate) struct KernelSoundnessLaunchDifferentialEvidence {
    pub(crate) baseline_path: String,
    pub(crate) expressions_path: String,
    pub(crate) baseline_schema_version: u32,
    pub(crate) normalization_version: u32,
    pub(crate) baseline_cases: usize,
    pub(crate) expression_count: usize,
    pub(crate) expressions_sha256: String,
    pub(crate) baseline_sha256: String,
    pub(crate) expressions_file_sha256: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(crate) struct KernelSoundnessLaunchLaneEvidence {
    pub(crate) id: String,
    pub(crate) expected_tests: Option<u32>,
    pub(crate) expected_output: Option<String>,
    pub(crate) matched_expected_count: bool,
    pub(crate) matched_expected_output: bool,
    pub(crate) status: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(crate) struct DenySorryLaunchEvidenceArtifact {
    pub(crate) schema_version: String,
    pub(crate) generated_by: String,
    pub(crate) generated_at: String,
    pub(crate) gate_command: String,
    pub(crate) status: String,
    pub(crate) summary: DenySorryLaunchEvidenceSummary,
    pub(crate) ratchet: DenySorryLaunchRatchetEvidence,
    pub(crate) source_sha256: BTreeMap<String, String>,
    pub(crate) lanes: Vec<DenySorryLaunchLaneEvidence>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(crate) struct DenySorryLaunchEvidenceSummary {
    pub(crate) expected_steps: u32,
    pub(crate) steps: u32,
    pub(crate) passed: u32,
    pub(crate) failed: u32,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(crate) struct DenySorryLaunchRatchetEvidence {
    pub(crate) path: String,
    pub(crate) add_decl_structural_count: u32,
    pub(crate) add_decl_unchecked_count: u32,
    pub(crate) sha256: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(crate) struct DenySorryLaunchLaneEvidence {
    pub(crate) id: String,
    pub(crate) expected_tests: Option<u32>,
    pub(crate) matched_expected_count: bool,
    pub(crate) status: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(crate) struct AxiomAuditLaunchEvidenceArtifact {
    pub(crate) schema_version: String,
    pub(crate) generated_by: String,
    pub(crate) generated_at: String,
    pub(crate) gate_command: String,
    pub(crate) status: String,
    pub(crate) summary: AxiomAuditLaunchEvidenceSummary,
    pub(crate) axiom_audit: AxiomAuditLaunchAuditEvidence,
    pub(crate) source_sha256: BTreeMap<String, String>,
    pub(crate) lanes: Vec<AxiomAuditLaunchLaneEvidence>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(crate) struct AxiomAuditLaunchEvidenceSummary {
    pub(crate) expected_steps: u32,
    pub(crate) steps: u32,
    pub(crate) passed: u32,
    pub(crate) failed: u32,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(crate) struct AxiomAuditLaunchAuditEvidence {
    pub(crate) path: String,
    pub(crate) total_domain_axioms: u32,
    pub(crate) total_all_axioms: u32,
    pub(crate) total_theorems: u32,
    pub(crate) constructive_theorems: u32,
    pub(crate) conjecture_rows: usize,
    pub(crate) nonzero_axiom_rows: usize,
    pub(crate) sha256: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub(crate) struct AxiomAuditLaunchLaneEvidence {
    pub(crate) id: String,
    #[serde(default)]
    pub(crate) description: String,
    pub(crate) status: String,
}

#[derive(Debug, Deserialize)]
pub(crate) struct AxiomAuditArtifact {
    pub(crate) total_domain_axioms: u32,
    pub(crate) total_all_axioms: u32,
    pub(crate) total_theorems: u32,
    pub(crate) constructive_theorems: u32,
    pub(crate) conjectures: BTreeMap<String, AxiomAuditConjecture>,
}

#[derive(Debug, Deserialize)]
pub(crate) struct AxiomAuditConjecture {
    #[serde(default)]
    pub(crate) axioms: u32,
    #[serde(default)]
    pub(crate) proof_mechanism: Option<String>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct KernelSoundnessLaneExpectation {
    pub(crate) id: &'static str,
    pub(crate) expected_tests: Option<u32>,
    pub(crate) expected_output: Option<&'static str>,
    /// Argv the generator executes to decide this lane's verdict.
    ///
    /// `None` marks a lane that is executed in-process (the differential
    /// preflight), so there is no subprocess to spawn. Every other lane MUST
    /// carry a command: a lane with no way to be executed can only ever be
    /// self-declared, which is precisely what this artifact must not do.
    pub(crate) command: Option<&'static [&'static str]>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct DenySorryLaneExpectation {
    pub(crate) id: &'static str,
    pub(crate) expected_tests: Option<u32>,
    /// Argv the generator executes to decide this lane's verdict.
    ///
    /// `None` marks a lane that is executed in-process (the sorry-bypass lint
    /// and the unchecked-decl ratchet closure), so there is no subprocess to
    /// spawn. Every other lane MUST carry a command: a lane with no way to be
    /// executed can only ever be self-declared, which is precisely what this
    /// artifact must not do.
    pub(crate) command: Option<&'static [&'static str]>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct AxiomAuditLaneExpectation {
    pub(crate) id: &'static str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub(crate) enum ReplacementStatus {
    Blocked,
    PendingEvidence,
    InProgress,
    Green,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ToolMigrationStatus {
    MissingOwner,
    Transitional,
    Demoted,
    RustOwned,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ZeroTrustGateStatus {
    Blocked,
    PendingEvidence,
    Passed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ZeroTrustDebtClass {
    KernelSoundness,
    SorryAndTrustedFallback,
    AxiomAudit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub(crate) enum TacticParityStatus {
    Lean4ParityGap,
    EvidenceBackedPartial,
    ProofCarrying,
}

impl TacticParityStatus {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Lean4ParityGap => "lean4_parity_gap",
            Self::EvidenceBackedPartial => "evidence_backed_partial",
            Self::ProofCarrying => "proof_carrying",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub(crate) enum StrictReconstructionStatus {
    #[allow(dead_code)]
    ParityGap,
    #[allow(dead_code)]
    EvidenceGap,
    SupportedZeroTrust,
}

impl StrictReconstructionStatus {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::ParityGap => "parity_gap",
            Self::EvidenceGap => "evidence_gap",
            Self::SupportedZeroTrust => "supported_zero_trust",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(crate) enum StrictSolverFragmentBehavior {
    SupportedZeroTrust,
    UnsupportedRejectAndFallback,
}

impl ReplacementStatus {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Blocked => "blocked",
            Self::PendingEvidence => "pending_evidence",
            Self::InProgress => "in_progress",
            Self::Green => "green",
        }
    }
}

impl ToolMigrationStatus {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::MissingOwner => "missing_owner",
            Self::Transitional => "transitional",
            Self::Demoted => "demoted",
            Self::RustOwned => "rust_owned",
        }
    }
}

impl ZeroTrustGateStatus {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Blocked => "blocked",
            Self::PendingEvidence => "pending_evidence",
            Self::Passed => "passed",
        }
    }
}

pub(crate) fn count_by_status(rows: &[ReplacementRow]) -> BTreeMap<ReplacementStatus, usize> {
    let mut counts = BTreeMap::new();
    for row in rows {
        *counts.entry(row.status).or_insert(0) += 1;
    }
    counts
}

/// Count rows by their evidence-derived `effective_status` (M2). This is what the
/// launch gate and honest dashboards should read; `count_by_status` counts the
/// hand-declared claims.
pub(crate) fn count_by_effective_status(
    rows: &[ReplacementRow],
) -> BTreeMap<ReplacementStatus, usize> {
    let mut counts = BTreeMap::new();
    for row in rows {
        *counts.entry(row.effective_status).or_insert(0) += 1;
    }
    counts
}

pub(crate) fn count_tool_migration_status(
    rows: &[PythonToolMigrationRow],
) -> BTreeMap<ToolMigrationStatus, usize> {
    let mut counts = BTreeMap::new();
    for row in rows {
        *counts.entry(row.status).or_insert(0) += 1;
    }
    counts
}

pub(crate) fn count_tactic_status(rows: &[TacticParityRow]) -> BTreeMap<TacticParityStatus, usize> {
    let mut counts = BTreeMap::new();
    for row in rows {
        *counts.entry(row.lean4_parity_status).or_insert(0) += 1;
    }
    counts
}

pub(crate) fn count_reconstruction_status(
    rows: &[StrictReconstructionRow],
) -> BTreeMap<StrictReconstructionStatus, usize> {
    let mut counts = BTreeMap::new();
    for row in rows {
        *counts.entry(row.status).or_insert(0) += 1;
    }
    counts
}

pub(crate) fn count_zero_trust_gate_status(
    rows: &[ZeroTrustGateRow],
) -> BTreeMap<ZeroTrustGateStatus, usize> {
    let mut counts = BTreeMap::new();
    for row in rows {
        *counts.entry(row.status).or_insert(0) += 1;
    }
    counts
}
