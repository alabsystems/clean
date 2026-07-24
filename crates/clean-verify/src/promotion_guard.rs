// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Audit-facing promotion guard for structured promotion reports.
//!
//! This module consumes [`crate::promotion_report::PromotionReport`] and keeps
//! unsafe `KernelProved` claims from passing handoff. It is intentionally pure
//! Rust: callers can wire it into CLI, CI, or dashboard lanes independently.

use crate::promotion_report::{
    DemasqueradeClassification, PromotionFindingSeverity, PromotionReport, PromotionStatus,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use thiserror::Error;

/// The theorem ids guarded by default.
pub const DEFAULT_GUARDED_THEOREM_IDS: [&str; 3] = ["C004", "C006", "T60"];

/// Promotion guard configuration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromotionGuardConfig {
    guarded_theorem_ids: BTreeSet<String>,
}

impl PromotionGuardConfig {
    /// Build a guard config from explicit theorem ids.
    #[must_use]
    pub fn new(ids: impl IntoIterator<Item = impl Into<String>>) -> Self {
        Self {
            guarded_theorem_ids: ids.into_iter().map(Into::into).collect(),
        }
    }

    /// Return true if `theorem_id` is covered by this guard.
    #[must_use]
    pub fn guards(&self, theorem_id: &str) -> bool {
        self.guarded_theorem_ids.contains(theorem_id)
    }

    /// Iterate guarded theorem ids in deterministic order.
    pub fn guarded_theorem_ids(&self) -> impl Iterator<Item = &str> {
        self.guarded_theorem_ids.iter().map(String::as_str)
    }
}

impl Default for PromotionGuardConfig {
    fn default() -> Self {
        Self::new(DEFAULT_GUARDED_THEOREM_IDS)
    }
}

/// Stable reason code for a guard finding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PromotionGuardReasonCode {
    /// A guarded theorem id moved to `KernelProved` without audit metadata.
    GuardedKernelPromotionMissingAudit,
    /// The underlying promotion report already emitted a fatal finding.
    RegressionFindingError,
    /// A `KernelProved` entry has a non-clean demasquerade classification or rule hits.
    UnsafeDemasqueradeKernelPromotion,
}

impl PromotionGuardReasonCode {
    /// Stable machine-readable reason string.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::GuardedKernelPromotionMissingAudit => "guarded_kernel_promotion_missing_audit",
            Self::RegressionFindingError => "regression_finding_error",
            Self::UnsafeDemasqueradeKernelPromotion => "unsafe_demasquerade_kernel_promotion",
        }
    }
}

/// One deterministic guard finding.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PromotionGuardFinding {
    /// The theorem id that triggered the finding.
    pub theorem_id: String,
    /// Optional artifact id from the promotion report entry.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifact_id: Option<String>,
    /// Stable reason code.
    pub reason_code: PromotionGuardReasonCode,
    /// Human-readable deterministic message.
    pub message: String,
}

/// Result of evaluating the promotion guard.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PromotionGuardOutcome {
    /// Blocking findings. Empty means the report is allowed.
    pub findings: Vec<PromotionGuardFinding>,
}

impl PromotionGuardOutcome {
    /// True when the promotion report may proceed.
    #[must_use]
    pub fn is_allowed(&self) -> bool {
        self.findings.is_empty()
    }

    /// Convert the outcome into a blocking result.
    ///
    /// # Errors
    ///
    /// Returns [`PromotionGuardError::Blocked`] when guard findings exist.
    pub fn into_result(self) -> Result<(), PromotionGuardError> {
        if self.is_allowed() {
            Ok(())
        } else {
            Err(PromotionGuardError::Blocked(self))
        }
    }
}

/// Promotion guard failure.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum PromotionGuardError {
    /// The promotion report has one or more blocking findings.
    #[error("promotion guard blocked report with {finding_count} finding(s)", finding_count = .0.findings.len())]
    Blocked(PromotionGuardOutcome),
}

/// Evaluate `report` with the default guarded theorem set.
#[must_use]
pub fn evaluate_default_promotion_guard(report: &PromotionReport) -> PromotionGuardOutcome {
    evaluate_promotion_guard(report, &PromotionGuardConfig::default())
}

/// Enforce the default promotion guard.
///
/// # Errors
///
/// Returns [`PromotionGuardError::Blocked`] when the report contains unsafe
/// promotions.
pub fn enforce_default_promotion_guard(
    report: &PromotionReport,
) -> Result<(), PromotionGuardError> {
    evaluate_default_promotion_guard(report).into_result()
}

/// Evaluate `report` against `config`.
#[must_use]
pub fn evaluate_promotion_guard(
    report: &PromotionReport,
    config: &PromotionGuardConfig,
) -> PromotionGuardOutcome {
    let mut findings = Vec::new();

    for finding in report.regression_findings() {
        if finding.severity == PromotionFindingSeverity::Error {
            findings.push(PromotionGuardFinding {
                theorem_id: finding.id.theorem_id,
                artifact_id: finding.id.artifact_id,
                reason_code: PromotionGuardReasonCode::RegressionFindingError,
                message: format!(
                    "promotion_report.regression_findings emitted error `{}`: {}",
                    finding.reason_code.as_str(),
                    finding.message
                ),
            });
        }
    }

    for entry in &report.entries {
        if config.guards(&entry.id.theorem_id)
            && entry.prior_status != PromotionStatus::KernelProved
            && entry.new_status == PromotionStatus::KernelProved
            && !entry.has_audit_metadata()
        {
            findings.push(PromotionGuardFinding {
                theorem_id: entry.id.theorem_id.clone(),
                artifact_id: entry.id.artifact_id.clone(),
                reason_code: PromotionGuardReasonCode::GuardedKernelPromotionMissingAudit,
                message: format!(
                    "guarded theorem `{}` cannot be promoted to KernelProved without substantive audit metadata",
                    entry.id.theorem_id
                ),
            });
        }

        if entry.new_status == PromotionStatus::KernelProved
            && is_demasquerade_unsafe_for_kernel_proved(entry.demasquerade.classification)
        {
            findings.push(PromotionGuardFinding {
                theorem_id: entry.id.theorem_id.clone(),
                artifact_id: entry.id.artifact_id.clone(),
                reason_code: PromotionGuardReasonCode::UnsafeDemasqueradeKernelPromotion,
                message: format!(
                    "KernelProved entry `{}` requires demasquerade classification `clean`; found `{}`",
                    entry.id.theorem_id,
                    entry.demasquerade.classification.as_str()
                ),
            });
        }

        if entry.new_status == PromotionStatus::KernelProved
            && !entry.demasquerade.rule_hits.is_empty()
        {
            findings.push(PromotionGuardFinding {
                theorem_id: entry.id.theorem_id.clone(),
                artifact_id: entry.id.artifact_id.clone(),
                reason_code: PromotionGuardReasonCode::UnsafeDemasqueradeKernelPromotion,
                message: format!(
                    "KernelProved entry `{}` has demasquerade rule hits despite promotion",
                    entry.id.theorem_id
                ),
            });
        }
    }

    findings.sort_by(|lhs, rhs| {
        lhs.theorem_id
            .cmp(&rhs.theorem_id)
            .then(lhs.artifact_id.cmp(&rhs.artifact_id))
            .then(lhs.reason_code.cmp(&rhs.reason_code))
            .then(lhs.message.cmp(&rhs.message))
    });
    findings.dedup();

    PromotionGuardOutcome { findings }
}

/// Enforce `report` against `config`.
///
/// # Errors
///
/// Returns [`PromotionGuardError::Blocked`] when the report contains unsafe
/// promotions.
pub fn enforce_promotion_guard(
    report: &PromotionReport,
    config: &PromotionGuardConfig,
) -> Result<(), PromotionGuardError> {
    evaluate_promotion_guard(report, config).into_result()
}

fn is_demasquerade_unsafe_for_kernel_proved(classification: DemasqueradeClassification) -> bool {
    !matches!(classification, DemasqueradeClassification::Clean)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::promotion_report::{
        AxiomClosure, DemasqueradeResult, DemasqueradeRule, MathverseExportAction,
        MathverseExportDecision, MathverseExportTier, PromotionArtifactId, PromotionAuditMetadata,
        PromotionEntry, PromotionReasonCode, TrustMarker, TrustMarkers,
    };

    #[test]
    fn default_config_guards_c004_c006_t60() {
        let config = PromotionGuardConfig::default();
        let ids: Vec<_> = config.guarded_theorem_ids().collect();

        assert_eq!(ids, ["C004", "C006", "T60"]);
        assert!(config.guards("C004"));
        assert!(config.guards("C006"));
        assert!(config.guards("T60"));
        assert!(!config.guards("S01"));
    }

    #[test]
    fn allows_guarded_kernel_promotion_with_audit_and_clean_demasquerade() {
        let report = PromotionReport::new(vec![entry(
            "C004",
            PromotionStatus::Axiomatized,
            PromotionStatus::KernelProved,
            DemasqueradeClassification::Clean,
            Vec::new(),
            audit_metadata(),
            AxiomClosure::default(),
        )]);

        let outcome = evaluate_default_promotion_guard(&report);

        assert!(outcome.is_allowed(), "{outcome:?}");
        enforce_default_promotion_guard(&report).expect("guard should allow report");
    }

    #[test]
    fn blocks_guarded_kernel_promotion_without_audit() {
        let report = PromotionReport::new(vec![entry(
            "C006",
            PromotionStatus::Axiomatized,
            PromotionStatus::KernelProved,
            DemasqueradeClassification::Clean,
            Vec::new(),
            None,
            AxiomClosure::default(),
        )]);

        let outcome = evaluate_default_promotion_guard(&report);

        assert_eq!(outcome.findings.len(), 2);
        assert!(outcome.findings.iter().any(|finding| {
            finding.reason_code == PromotionGuardReasonCode::GuardedKernelPromotionMissingAudit
                && finding.theorem_id == "C006"
                && finding.message
                    == "guarded theorem `C006` cannot be promoted to KernelProved without substantive audit metadata"
        }));
        assert!(outcome.findings.iter().any(|finding| {
            finding.reason_code == PromotionGuardReasonCode::RegressionFindingError
                && finding.theorem_id == "C006"
                && finding.message
                    == "promotion_report.regression_findings emitted error `audit_metadata_missing`: Axiomatized -> KernelProved promotion requires audit metadata"
        }));
    }

    #[test]
    fn blocks_regression_finding_errors() {
        let report = PromotionReport::new(vec![entry(
            "S01",
            PromotionStatus::Axiomatized,
            PromotionStatus::KernelProved,
            DemasqueradeClassification::Clean,
            Vec::new(),
            None,
            AxiomClosure::default(),
        )]);

        let outcome = evaluate_default_promotion_guard(&report);

        assert_eq!(outcome.findings.len(), 1);
        assert_eq!(outcome.findings[0].theorem_id, "S01");
        assert_eq!(
            outcome.findings[0].reason_code,
            PromotionGuardReasonCode::RegressionFindingError
        );
    }

    #[test]
    fn blocks_kernel_proved_with_masquerade_classification() {
        let report = PromotionReport::new(vec![entry(
            "S01",
            PromotionStatus::SourceVerified,
            PromotionStatus::KernelProved,
            DemasqueradeClassification::MasqueradeDetected,
            [DemasqueradeRule::M1AliasCollapse],
            audit_metadata(),
            AxiomClosure::default(),
        )]);

        let outcome = evaluate_default_promotion_guard(&report);

        assert_eq!(outcome.findings.len(), 2);
        assert!(outcome.findings.iter().any(|finding| {
            finding.reason_code == PromotionGuardReasonCode::UnsafeDemasqueradeKernelPromotion
                && finding.message
                    == "KernelProved entry `S01` requires demasquerade classification `clean`; found `masquerade_detected`"
        }));
        assert!(outcome.findings.iter().any(|finding| {
            finding.reason_code == PromotionGuardReasonCode::UnsafeDemasqueradeKernelPromotion
                && finding.message
                    == "KernelProved entry `S01` has demasquerade rule hits despite promotion"
        }));
    }

    #[test]
    fn blocks_kernel_proved_when_demasquerade_not_checked() {
        let report = PromotionReport::new(vec![entry(
            "S02",
            PromotionStatus::SourceVerified,
            PromotionStatus::KernelProved,
            DemasqueradeClassification::NotChecked,
            Vec::new(),
            audit_metadata(),
            AxiomClosure::default(),
        )]);

        let outcome = evaluate_default_promotion_guard(&report);

        assert_eq!(outcome.findings.len(), 1);
        assert_eq!(
            outcome.findings[0].reason_code,
            PromotionGuardReasonCode::UnsafeDemasqueradeKernelPromotion
        );
        assert_eq!(
            outcome.findings[0].message,
            "KernelProved entry `S02` requires demasquerade classification `clean`; found `not_checked`"
        );
    }

    #[test]
    fn allows_guarded_unchanged_kernel_proved_without_requiring_new_audit() {
        let report = PromotionReport::new(vec![entry(
            "T60",
            PromotionStatus::KernelProved,
            PromotionStatus::KernelProved,
            DemasqueradeClassification::Clean,
            Vec::new(),
            None,
            AxiomClosure::default(),
        )]);

        let outcome = evaluate_default_promotion_guard(&report);

        assert!(outcome.is_allowed(), "{outcome:?}");
    }

    #[test]
    fn enforce_returns_blocked_error() {
        let report = PromotionReport::new(vec![entry(
            "T60",
            PromotionStatus::Axiomatized,
            PromotionStatus::KernelProved,
            DemasqueradeClassification::NeedsReview,
            Vec::new(),
            None,
            AxiomClosure::default(),
        )]);

        let err = enforce_default_promotion_guard(&report).expect_err("guard should block");

        match err {
            PromotionGuardError::Blocked(outcome) => {
                assert_eq!(outcome.findings.len(), 3);
            }
        }
    }

    fn entry(
        theorem_id: &str,
        prior_status: PromotionStatus,
        new_status: PromotionStatus,
        classification: DemasqueradeClassification,
        rule_hits: impl IntoIterator<Item = DemasqueradeRule>,
        audit: Option<PromotionAuditMetadata>,
        axiom_closure: AxiomClosure,
    ) -> PromotionEntry {
        PromotionEntry {
            id: PromotionArtifactId::new(theorem_id),
            prior_status,
            new_status,
            axiom_closure,
            trust_markers: TrustMarkers::new([
                TrustMarker::ProofTermPresent,
                TrustMarker::KernelChecked,
                TrustMarker::AxiomFree,
                TrustMarker::DemasqueradeChecked,
            ]),
            mathverse_export: MathverseExportDecision::new(
                MathverseExportAction::Defer,
                MathverseExportTier::None,
                [PromotionReasonCode::MathverseExportDeferred],
            ),
            demasquerade: DemasqueradeResult::new(classification, rule_hits, ["test evidence"]),
            audit,
            reason_codes: vec![PromotionReasonCode::StatusPromoted],
        }
    }

    fn audit_metadata() -> Option<PromotionAuditMetadata> {
        Some(PromotionAuditMetadata {
            issue: Some("#3675".to_owned()),
            auditor: Some("promotion-guard-test".to_owned()),
            evidence: vec!["proof-hash:test".to_owned()],
            reviewed_at: Some("2026-04-23".to_owned()),
        })
    }
}
