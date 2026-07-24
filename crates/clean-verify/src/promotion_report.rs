// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured promotion reports for theorem and artifact audit handoff.
//!
//! This module is intentionally independent from the existing
//! `proofs::promote` pipeline report. It records the audit-facing state needed
//! by promotion tooling: before/after status, axiom closure, trust markers,
//! Mathverse export eligibility, demasquerade results, and reason codes.

use crate::spec::ProofStatus;
use serde::{Deserialize, Serialize};

/// Stable schema tag for serialized promotion reports.
pub const PROMOTION_REPORT_SCHEMA_VERSION: &str = "clean.promotion_report.v1";

/// A structured report for a batch of promotion decisions.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PromotionReport {
    /// Stable schema version for downstream consumers.
    pub schema_version: String,
    /// Per-theorem promotion entries, sorted by theorem/artifact id by [`PromotionReport::new`].
    pub entries: Vec<PromotionEntry>,
}

impl PromotionReport {
    /// Build a normalized report with deterministic entry and list ordering.
    #[must_use]
    pub fn new(mut entries: Vec<PromotionEntry>) -> Self {
        for entry in &mut entries {
            entry.normalize();
        }
        entries.sort_by(|lhs, rhs| lhs.id.cmp(&rhs.id));

        Self {
            schema_version: PROMOTION_REPORT_SCHEMA_VERSION.to_owned(),
            entries,
        }
    }

    /// Serialize this report as compact JSON.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Serialize this report as pretty JSON.
    pub fn to_json_pretty(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Parse a report from JSON.
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }

    /// Render this report as a stable Markdown table plus validation findings.
    #[must_use]
    pub fn to_markdown(&self) -> String {
        let mut markdown = String::new();
        markdown.push_str("# Promotion Report\n\n");
        markdown.push_str(&format!("Schema: `{}`\n\n", self.schema_version));
        markdown.push_str("| Theorem | Artifact | Prior | New | Diff | Axioms | Trust | Mathverse | Demasquerade | Reasons |\n");
        markdown.push_str("|---|---|---|---|---|---:|---|---|---|---|\n");

        for entry in &self.entries {
            markdown.push_str(&entry.to_markdown_row());
            markdown.push('\n');
        }

        let findings = self.regression_findings();
        markdown.push_str("\n## Findings\n");
        if findings.is_empty() {
            markdown.push_str("None\n");
        } else {
            for finding in findings {
                markdown.push_str("- ");
                markdown.push_str(finding.severity.as_str());
                markdown.push_str(": `");
                markdown.push_str(&escape_markdown_cell(&finding.id.theorem_id));
                markdown.push_str("` ");
                markdown.push_str(finding.reason_code.as_str());
                markdown.push_str(" - ");
                markdown.push_str(&escape_markdown_cell(&finding.message));
                markdown.push('\n');
            }
        }

        markdown
    }

    /// Detect promotion report regressions that must not silently pass audit.
    #[must_use]
    pub fn regression_findings(&self) -> Vec<PromotionFinding> {
        let mut findings = Vec::new();

        for entry in &self.entries {
            if is_unaudited_axiom_to_kernel_promotion(entry) {
                findings.push(PromotionFinding {
                    id: entry.id.clone(),
                    severity: PromotionFindingSeverity::Error,
                    reason_code: PromotionReasonCode::AuditMetadataMissing,
                    message: "Axiomatized -> KernelProved promotion requires audit metadata"
                        .to_owned(),
                });
            }

            if entry.new_status == PromotionStatus::KernelProved
                && !entry.axiom_closure.transitive_axioms.is_empty()
            {
                findings.push(PromotionFinding {
                    id: entry.id.clone(),
                    severity: PromotionFindingSeverity::Error,
                    reason_code: PromotionReasonCode::AxiomClosureNonempty,
                    message: "KernelProved entry has a non-empty transitive axiom closure"
                        .to_owned(),
                });
            }
        }

        findings
    }
}

/// A single theorem or artifact promotion decision.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PromotionEntry {
    /// Stable theorem/artifact id pair.
    pub id: PromotionArtifactId,
    /// Status before the promotion attempt.
    pub prior_status: PromotionStatus,
    /// Status after the promotion attempt.
    pub new_status: PromotionStatus,
    /// Transitive axiom closure observed during audit.
    pub axiom_closure: AxiomClosure,
    /// Trust markers supporting the new status.
    pub trust_markers: TrustMarkers,
    /// Decision for exporting this theorem/artifact into Mathverse.
    pub mathverse_export: MathverseExportDecision,
    /// Demasquerade classifier result.
    pub demasquerade: DemasqueradeResult,
    /// Optional audit metadata. Required for Axiomatized -> KernelProved.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub audit: Option<PromotionAuditMetadata>,
    /// Stable reason codes for downstream filtering and dashboards.
    pub reason_codes: Vec<PromotionReasonCode>,
}

impl PromotionEntry {
    /// Return the computed status diff for this entry.
    #[must_use]
    pub fn status_diff(&self) -> StatusDiff {
        status_diff(self.prior_status, self.new_status)
    }

    /// True when this entry carries substantive audit metadata.
    #[must_use]
    pub fn has_audit_metadata(&self) -> bool {
        self.audit
            .as_ref()
            .is_some_and(PromotionAuditMetadata::is_substantive)
    }

    fn normalize(&mut self) {
        self.axiom_closure.normalize();
        self.trust_markers.normalize();
        self.mathverse_export.normalize();
        self.demasquerade.normalize();
        if let Some(audit) = &mut self.audit {
            audit.normalize();
        }
        sort_dedup(&mut self.reason_codes);
    }

    fn to_markdown_row(&self) -> String {
        format!(
            "| {} | {} | `{}` | `{}` | `{}` | {} | {} | `{}` | `{}` | {} |",
            markdown_code(&self.id.theorem_id),
            markdown_code(self.id.artifact_id.as_deref().unwrap_or("-")),
            self.prior_status.as_str(),
            self.new_status.as_str(),
            self.status_diff().as_str(),
            self.axiom_closure.transitive_axioms.len(),
            markdown_code(&join_as_str(&self.trust_markers.markers)),
            self.mathverse_export.decision.as_str(),
            self.demasquerade.classification.as_str(),
            markdown_code(&join_as_str(&self.reason_codes)),
        )
    }
}

/// Stable theorem id plus optional artifact id.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PromotionArtifactId {
    /// Stable theorem id, for example `S01` or `C030c`.
    pub theorem_id: String,
    /// Optional external artifact id, for example an Mathverse shard key.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifact_id: Option<String>,
}

impl PromotionArtifactId {
    /// Build an id with no external artifact id.
    #[must_use]
    pub fn new(theorem_id: impl Into<String>) -> Self {
        Self {
            theorem_id: theorem_id.into(),
            artifact_id: None,
        }
    }

    /// Attach an external artifact id.
    #[must_use]
    pub fn with_artifact_id(mut self, artifact_id: impl Into<String>) -> Self {
        self.artifact_id = Some(artifact_id.into());
        self
    }
}

/// Promotion status vocabulary used by audit reports.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PromotionStatus {
    /// Status could not be classified.
    Unknown,
    /// Statement is present but proof is axiomatized.
    Axiomatized,
    /// Proof exists but has tracked axiom dependencies.
    AxiomDependent,
    /// Source proof was checked, but not independently replayed by the clean kernel.
    SourceVerified,
    /// Proof was accepted by the clean kernel with no domain axiom closure.
    KernelProved,
    /// Entry was intentionally demoted during demasquerade.
    Demoted,
    /// Promotion was rejected.
    Rejected,
    /// Promotion was skipped.
    Skipped,
}

impl PromotionStatus {
    /// Stable string used in Markdown and reason text.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Unknown => "unknown",
            Self::Axiomatized => "axiomatized",
            Self::AxiomDependent => "axiom_dependent",
            Self::SourceVerified => "source_verified",
            Self::KernelProved => "kernel_proved",
            Self::Demoted => "demoted",
            Self::Rejected => "rejected",
            Self::Skipped => "skipped",
        }
    }

    fn trust_rank(self) -> Option<u8> {
        match self {
            Self::Axiomatized => Some(0),
            Self::AxiomDependent => Some(1),
            Self::SourceVerified => Some(2),
            Self::KernelProved => Some(3),
            Self::Unknown | Self::Demoted | Self::Rejected | Self::Skipped => None,
        }
    }
}

impl From<ProofStatus> for PromotionStatus {
    fn from(status: ProofStatus) -> Self {
        match status {
            ProofStatus::Axiom => Self::Axiomatized,
            ProofStatus::DerivedPending => Self::AxiomDependent,
            ProofStatus::DerivedProved => Self::KernelProved,
        }
    }
}

/// Computed before/after status relationship.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StatusDiff {
    /// Status did not change.
    Unchanged,
    /// Status moved to a higher-trust state.
    Promoted,
    /// Status was intentionally demoted.
    Demoted,
    /// Status moved to a lower-trust state.
    Regressed,
    /// Diff cannot be classified from status ranks.
    Unknown,
}

impl StatusDiff {
    /// Stable string used in Markdown and reason text.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Unchanged => "unchanged",
            Self::Promoted => "promoted",
            Self::Demoted => "demoted",
            Self::Regressed => "regressed",
            Self::Unknown => "unknown",
        }
    }
}

/// Compute the relationship between two promotion statuses.
#[must_use]
pub fn status_diff(prior_status: PromotionStatus, new_status: PromotionStatus) -> StatusDiff {
    if prior_status == new_status {
        return StatusDiff::Unchanged;
    }

    if new_status == PromotionStatus::Demoted {
        return StatusDiff::Demoted;
    }

    match (prior_status.trust_rank(), new_status.trust_rank()) {
        (Some(prior), Some(new)) if new > prior => StatusDiff::Promoted,
        (Some(prior), Some(new)) if new < prior => StatusDiff::Regressed,
        (Some(_), Some(_)) => StatusDiff::Unchanged,
        _ => StatusDiff::Unknown,
    }
}

/// Direct and transitive axiom closure for a promotion candidate.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AxiomClosure {
    /// Axioms directly referenced by the promoted artifact.
    pub direct_axioms: Vec<String>,
    /// Full transitive axiom closure.
    pub transitive_axioms: Vec<String>,
}

impl AxiomClosure {
    /// Build a normalized axiom closure.
    #[must_use]
    pub fn new(
        direct_axioms: impl IntoIterator<Item = impl Into<String>>,
        transitive_axioms: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        let mut closure = Self {
            direct_axioms: direct_axioms.into_iter().map(Into::into).collect(),
            transitive_axioms: transitive_axioms.into_iter().map(Into::into).collect(),
        };
        closure.normalize();
        closure
    }

    /// True when no direct or transitive axioms remain.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.direct_axioms.is_empty() && self.transitive_axioms.is_empty()
    }

    fn normalize(&mut self) {
        sort_dedup(&mut self.direct_axioms);
        sort_dedup(&mut self.transitive_axioms);
    }
}

/// Audit metadata attached to a promotion.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PromotionAuditMetadata {
    /// Issue, PR, or report id that authorized the status change.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub issue: Option<String>,
    /// Person or worker that performed the audit.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub auditor: Option<String>,
    /// Stable evidence references, such as proof hashes or report paths.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub evidence: Vec<String>,
    /// Review date or timestamp, if known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reviewed_at: Option<String>,
}

impl PromotionAuditMetadata {
    /// True when at least one audit field is populated.
    #[must_use]
    pub fn is_substantive(&self) -> bool {
        self.issue.is_some()
            || self.auditor.is_some()
            || !self.evidence.is_empty()
            || self.reviewed_at.is_some()
    }

    fn normalize(&mut self) {
        sort_dedup(&mut self.evidence);
    }
}

/// Trust markers recorded for a promotion candidate.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustMarkers {
    /// Stable trust marker set.
    pub markers: Vec<TrustMarker>,
}

impl TrustMarkers {
    /// Build normalized trust markers.
    #[must_use]
    pub fn new(markers: impl IntoIterator<Item = TrustMarker>) -> Self {
        let mut trust = Self {
            markers: markers.into_iter().collect(),
        };
        trust.normalize();
        trust
    }

    fn normalize(&mut self) {
        sort_dedup(&mut self.markers);
    }
}

/// Individual trust markers for promotion reports.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TrustMarker {
    /// A proof term is present.
    ProofTermPresent,
    /// Proof was checked by the clean kernel.
    KernelChecked,
    /// Transitive axiom closure is empty.
    AxiomFree,
    /// Demasquerade checks were run.
    DemasqueradeChecked,
    /// Audit metadata is present.
    AuditMetadataPresent,
    /// Artifact may pass into Mathverse export.
    MathverseExportEligible,
}

impl TrustMarker {
    /// Stable string used in Markdown and reason text.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ProofTermPresent => "proof_term_present",
            Self::KernelChecked => "kernel_checked",
            Self::AxiomFree => "axiom_free",
            Self::DemasqueradeChecked => "demasquerade_checked",
            Self::AuditMetadataPresent => "audit_metadata_present",
            Self::MathverseExportEligible => "mathverse_export_eligible",
        }
    }
}

/// Mathverse export decision for a promoted artifact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MathverseExportDecision {
    /// Export action selected for this artifact.
    pub decision: MathverseExportAction,
    /// Target export tier.
    pub tier: MathverseExportTier,
    /// Reason codes explaining the export decision.
    pub reason_codes: Vec<PromotionReasonCode>,
}

impl MathverseExportDecision {
    /// Build a normalized Mathverse export decision.
    #[must_use]
    pub fn new(
        decision: MathverseExportAction,
        tier: MathverseExportTier,
        reason_codes: impl IntoIterator<Item = PromotionReasonCode>,
    ) -> Self {
        let mut export = Self {
            decision,
            tier,
            reason_codes: reason_codes.into_iter().collect(),
        };
        export.normalize();
        export
    }

    fn normalize(&mut self) {
        sort_dedup(&mut self.reason_codes);
    }
}

/// Mathverse export action.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MathverseExportAction {
    /// Export the artifact at the requested tier.
    Export,
    /// Hold artifact outside export pending review.
    Quarantine,
    /// Reject the artifact from export.
    Reject,
    /// Defer the decision.
    Defer,
}

impl MathverseExportAction {
    /// Stable string used in Markdown and reason text.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Export => "export",
            Self::Quarantine => "quarantine",
            Self::Reject => "reject",
            Self::Defer => "defer",
        }
    }
}

/// Mathverse export tier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MathverseExportTier {
    /// Proof-training export: kernel proved and axiom free only.
    ProofTraining,
    /// Premise-selection export.
    PremiseSelection,
    /// Statement-only export.
    StatementOnly,
    /// No export tier.
    None,
}

/// Demasquerade classifier result for a promotion candidate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DemasqueradeResult {
    /// Overall demasquerade classification.
    pub classification: DemasqueradeClassification,
    /// Demasquerade rule hits, if any.
    pub rule_hits: Vec<DemasqueradeRule>,
    /// Stable evidence references.
    pub evidence: Vec<String>,
}

impl DemasqueradeResult {
    /// Build a normalized demasquerade result.
    #[must_use]
    pub fn new(
        classification: DemasqueradeClassification,
        rule_hits: impl IntoIterator<Item = DemasqueradeRule>,
        evidence: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        let mut result = Self {
            classification,
            rule_hits: rule_hits.into_iter().collect(),
            evidence: evidence.into_iter().map(Into::into).collect(),
        };
        result.normalize();
        result
    }

    fn normalize(&mut self) {
        sort_dedup(&mut self.rule_hits);
        sort_dedup(&mut self.evidence);
    }
}

/// Demasquerade audit classification.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DemasqueradeClassification {
    /// Checked and no masquerade pattern was found.
    Clean,
    /// A masquerade pattern was found.
    MasqueradeDetected,
    /// Intentional demotion removed the masquerade claim.
    Demoted,
    /// Audit did not run.
    NotChecked,
    /// Audit needs human review.
    NeedsReview,
}

impl DemasqueradeClassification {
    /// Stable string used in Markdown and reason text.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Clean => "clean",
            Self::MasqueradeDetected => "masquerade_detected",
            Self::Demoted => "demoted",
            Self::NotChecked => "not_checked",
            Self::NeedsReview => "needs_review",
        }
    }
}

/// Demasquerade rule identifiers from the audit methodology.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DemasqueradeRule {
    /// Rule M1: alias collapse.
    M1AliasCollapse,
    /// Rule M2: argument-discarding carrier.
    M2ArgumentDiscardingCarrier,
    /// Rule M3: induction hypothesis ignored.
    M3IgnoredInductionHypothesis,
    /// Rule M4: proof is reflexivity up to wrappers.
    M4ReflexivityOnlyProof,
    /// Secondary sorry-inhabited opaque pattern.
    SorryMasquerade,
}

/// Stable reason codes for report entries and validation findings.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PromotionReasonCode {
    /// Status did not change.
    StatusUnchanged,
    /// Status was promoted to a stronger proof state.
    StatusPromoted,
    /// Status was demoted.
    StatusDemoted,
    /// Kernel proof was accepted.
    KernelProofAccepted,
    /// Kernel proof was rejected.
    KernelProofRejected,
    /// Axiom closure is empty.
    AxiomClosureEmpty,
    /// Axiom closure is non-empty.
    AxiomClosureNonempty,
    /// Audit metadata is present.
    AuditMetadataPresent,
    /// Audit metadata is missing.
    AuditMetadataMissing,
    /// Demasquerade audit is clean.
    DemasqueradeClean,
    /// Demasquerade audit found a masquerade pattern.
    DemasqueradeFinding,
    /// Mathverse export was allowed.
    MathverseExportAllowed,
    /// Mathverse export was rejected.
    MathverseExportRejected,
    /// Mathverse export was deferred.
    MathverseExportDeferred,
}

impl PromotionReasonCode {
    /// Stable string used in Markdown and reason text.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::StatusUnchanged => "status_unchanged",
            Self::StatusPromoted => "status_promoted",
            Self::StatusDemoted => "status_demoted",
            Self::KernelProofAccepted => "kernel_proof_accepted",
            Self::KernelProofRejected => "kernel_proof_rejected",
            Self::AxiomClosureEmpty => "axiom_closure_empty",
            Self::AxiomClosureNonempty => "axiom_closure_nonempty",
            Self::AuditMetadataPresent => "audit_metadata_present",
            Self::AuditMetadataMissing => "audit_metadata_missing",
            Self::DemasqueradeClean => "demasquerade_clean",
            Self::DemasqueradeFinding => "demasquerade_finding",
            Self::MathverseExportAllowed => "mathverse_export_allowed",
            Self::MathverseExportRejected => "mathverse_export_rejected",
            Self::MathverseExportDeferred => "mathverse_export_deferred",
        }
    }
}

/// Report validation finding.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PromotionFinding {
    /// Entry id that triggered the finding.
    pub id: PromotionArtifactId,
    /// Finding severity.
    pub severity: PromotionFindingSeverity,
    /// Machine-readable reason code.
    pub reason_code: PromotionReasonCode,
    /// Human-readable finding message.
    pub message: String,
}

/// Finding severity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PromotionFindingSeverity {
    /// Fatal audit issue.
    Error,
    /// Non-fatal warning.
    Warning,
}

impl PromotionFindingSeverity {
    /// Stable string used in Markdown.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Error => "error",
            Self::Warning => "warning",
        }
    }
}

fn is_unaudited_axiom_to_kernel_promotion(entry: &PromotionEntry) -> bool {
    entry.prior_status == PromotionStatus::Axiomatized
        && entry.new_status == PromotionStatus::KernelProved
        && !entry.has_audit_metadata()
}

fn sort_dedup<T: Ord>(items: &mut Vec<T>) {
    items.sort();
    items.dedup();
}

trait MarkdownStr {
    fn as_str(&self) -> &'static str;
}

impl MarkdownStr for TrustMarker {
    fn as_str(&self) -> &'static str {
        (*self).as_str()
    }
}

impl MarkdownStr for PromotionReasonCode {
    fn as_str(&self) -> &'static str {
        (*self).as_str()
    }
}

fn join_as_str<T: MarkdownStr>(items: &[T]) -> String {
    if items.is_empty() {
        return "-".to_owned();
    }

    items
        .iter()
        .map(MarkdownStr::as_str)
        .collect::<Vec<_>>()
        .join(", ")
}

fn markdown_code(value: &str) -> String {
    if value == "-" {
        return "-".to_owned();
    }
    format!("`{}`", escape_markdown_cell(value))
}

fn escape_markdown_cell(value: &str) -> String {
    value
        .replace('\\', "\\\\")
        .replace('|', "\\|")
        .replace('\n', "<br>")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn audited_kernel_entry() -> PromotionEntry {
        PromotionEntry {
            id: PromotionArtifactId::new("S01").with_artifact_id("mathverse://clean-native/S01"),
            prior_status: PromotionStatus::Axiomatized,
            new_status: PromotionStatus::KernelProved,
            axiom_closure: AxiomClosure::new(Vec::<String>::new(), Vec::<String>::new()),
            trust_markers: TrustMarkers::new([
                TrustMarker::KernelChecked,
                TrustMarker::ProofTermPresent,
                TrustMarker::AxiomFree,
                TrustMarker::AuditMetadataPresent,
                TrustMarker::DemasqueradeChecked,
                TrustMarker::MathverseExportEligible,
            ]),
            mathverse_export: MathverseExportDecision::new(
                MathverseExportAction::Export,
                MathverseExportTier::ProofTraining,
                [PromotionReasonCode::MathverseExportAllowed],
            ),
            demasquerade: DemasqueradeResult::new(
                DemasqueradeClassification::Clean,
                Vec::<DemasqueradeRule>::new(),
                ["M1-M4 negative"],
            ),
            audit: Some(PromotionAuditMetadata {
                issue: Some("#3675".to_owned()),
                auditor: Some("worker-c".to_owned()),
                evidence: vec![
                    "demasquerade:M1-M4".to_owned(),
                    "proof_hash:abc123".to_owned(),
                ],
                reviewed_at: Some("2026-04-23".to_owned()),
            }),
            reason_codes: vec![
                PromotionReasonCode::KernelProofAccepted,
                PromotionReasonCode::AxiomClosureEmpty,
                PromotionReasonCode::AuditMetadataPresent,
                PromotionReasonCode::DemasqueradeClean,
                PromotionReasonCode::MathverseExportAllowed,
                PromotionReasonCode::StatusPromoted,
            ],
        }
    }

    #[test]
    fn stable_json_render() {
        let report = PromotionReport::new(vec![audited_kernel_entry()]);

        let json = report.to_json_pretty().expect("report should serialize");

        assert_eq!(
            json,
            r##"{
  "schema_version": "clean.promotion_report.v1",
  "entries": [
    {
      "id": {
        "theorem_id": "S01",
        "artifact_id": "mathverse://clean-native/S01"
      },
      "prior_status": "axiomatized",
      "new_status": "kernel_proved",
      "axiom_closure": {
        "direct_axioms": [],
        "transitive_axioms": []
      },
      "trust_markers": {
        "markers": [
          "proof_term_present",
          "kernel_checked",
          "axiom_free",
          "demasquerade_checked",
          "audit_metadata_present",
          "mathverse_export_eligible"
        ]
      },
      "mathverse_export": {
        "decision": "export",
        "tier": "proof_training",
        "reason_codes": [
          "mathverse_export_allowed"
        ]
      },
      "demasquerade": {
        "classification": "clean",
        "rule_hits": [],
        "evidence": [
          "M1-M4 negative"
        ]
      },
      "audit": {
        "issue": "#3675",
        "auditor": "worker-c",
        "evidence": [
          "demasquerade:M1-M4",
          "proof_hash:abc123"
        ],
        "reviewed_at": "2026-04-23"
      },
      "reason_codes": [
        "status_promoted",
        "kernel_proof_accepted",
        "axiom_closure_empty",
        "audit_metadata_present",
        "demasquerade_clean",
        "mathverse_export_allowed"
      ]
    }
  ]
}"##
        );
    }

    #[test]
    fn stable_markdown_render() {
        let report = PromotionReport::new(vec![audited_kernel_entry()]);

        let markdown = report.to_markdown();

        assert_eq!(
            markdown,
            "# Promotion Report\n\
\n\
Schema: `clean.promotion_report.v1`\n\
\n\
| Theorem | Artifact | Prior | New | Diff | Axioms | Trust | Mathverse | Demasquerade | Reasons |\n\
|---|---|---|---|---|---:|---|---|---|---|\n\
| `S01` | `mathverse://clean-native/S01` | `axiomatized` | `kernel_proved` | `promoted` | 0 | `proof_term_present, kernel_checked, axiom_free, demasquerade_checked, audit_metadata_present, mathverse_export_eligible` | `export` | `clean` | `status_promoted, kernel_proof_accepted, axiom_closure_empty, audit_metadata_present, demasquerade_clean, mathverse_export_allowed` |\n\
\n\
## Findings\n\
None\n"
        );
    }

    #[test]
    fn status_diff_helper_classifies_transitions() {
        assert_eq!(
            status_diff(PromotionStatus::Axiomatized, PromotionStatus::KernelProved),
            StatusDiff::Promoted
        );
        assert_eq!(
            status_diff(PromotionStatus::KernelProved, PromotionStatus::Axiomatized),
            StatusDiff::Regressed
        );
        assert_eq!(
            status_diff(PromotionStatus::KernelProved, PromotionStatus::Demoted),
            StatusDiff::Demoted
        );
        assert_eq!(
            status_diff(PromotionStatus::KernelProved, PromotionStatus::KernelProved),
            StatusDiff::Unchanged
        );
    }

    #[test]
    fn detects_axiomatized_to_kernel_proved_without_audit_metadata() {
        let mut entry = audited_kernel_entry();
        entry.audit = None;
        entry.trust_markers = TrustMarkers::new([
            TrustMarker::KernelChecked,
            TrustMarker::ProofTermPresent,
            TrustMarker::AxiomFree,
        ]);

        let report = PromotionReport::new(vec![entry]);
        let findings = report.regression_findings();

        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].id.theorem_id, "S01");
        assert_eq!(findings[0].severity, PromotionFindingSeverity::Error);
        assert_eq!(
            findings[0].reason_code,
            PromotionReasonCode::AuditMetadataMissing
        );
        assert!(findings[0].message.contains("Axiomatized -> KernelProved"));
    }
}
