// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Audit reporting for the Mathverse trust pipeline.
//!
//! Provides structured reports summarizing the trust landscape of an imported
//! constant set: how many constants exist at each trust level, what fraction
//! have axiom profiles, how many are exportable for training, and what trust
//! violations were detected.

use hashbrown::{HashMap, HashSet};
use serde::{Deserialize, Serialize};

use super::graph_gate::TrustViolation;
use crate::types::{AxiomProfile, TrustLevel};

/// Kernel whose trust boundary is being described by a finding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum KernelAuditKernel {
    /// Lean's kernel or Lake/Lean project boundary.
    Lean,
    /// Clean's kernel.
    Clean,
}

impl KernelAuditKernel {
    #[must_use]
    fn tag(self) -> &'static str {
        match self {
            Self::Lean => "lean",
            Self::Clean => "clean",
        }
    }

    #[must_use]
    fn from_tag(tag: &str) -> Option<Self> {
        match tag {
            "lean" => Some(Self::Lean),
            "clean" => Some(Self::Clean),
            _ => None,
        }
    }
}

/// Structured category metadata for audit findings.
///
/// [`AuditFinding::category`] remains a string for compatibility with existing
/// callers. New code can use this enum and its legacy tag encoding for
/// machine-readable trust findings without forcing every existing struct
/// literal to grow another field.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[non_exhaustive]
pub enum AuditFindingCategory {
    /// Trust boundary or proof-quality issue in a kernel.
    KernelTrust { kernel: KernelAuditKernel },
    /// Certificate provenance for replayed or unreplayed proof objects.
    CertificateProvenance { format: String, replayed: bool },
    /// Generated declaration/code provenance.
    GeneratedCode {
        generator: String,
        deterministic: bool,
    },
    /// Declaration marked unsafe.
    UnsafeDeclaration,
    /// Opaque constant that blocks unfolding/audit transparency.
    OpaqueConstant,
    /// Axiom declaration, including domain-specific axioms.
    AxiomDeclaration,
    /// Trusted external solver bridge.
    ExternalSolver { solver: String },
    /// Backward-compatible catch-all for legacy category strings.
    Other { tag: String },
}

impl AuditFindingCategory {
    /// Encode the structured category into the compatibility string stored on
    /// [`AuditFinding::category`].
    #[must_use]
    pub fn legacy_tag(&self) -> String {
        match self {
            Self::KernelTrust { kernel } => format!("kernel-trust:{}", kernel.tag()),
            Self::CertificateProvenance { format, replayed } => format!(
                "certificate-provenance:{}:{}",
                format,
                if *replayed { "replayed" } else { "unreplayed" }
            ),
            Self::GeneratedCode {
                generator,
                deterministic,
            } => format!(
                "generated-code:{}:{}",
                generator,
                if *deterministic {
                    "deterministic"
                } else {
                    "nondeterministic"
                }
            ),
            Self::UnsafeDeclaration => "unsafe-declaration".to_owned(),
            Self::OpaqueConstant => "opaque-constant".to_owned(),
            Self::AxiomDeclaration => "axiom-declaration".to_owned(),
            Self::ExternalSolver { solver } => format!("external-solver:{solver}"),
            Self::Other { tag } => tag.clone(),
        }
    }

    /// Decode a compatibility category string into structured metadata.
    #[must_use]
    pub fn from_legacy_tag(tag: &str) -> Self {
        if let Some(kernel) = tag
            .strip_prefix("kernel-trust:")
            .and_then(KernelAuditKernel::from_tag)
        {
            return Self::KernelTrust { kernel };
        }

        if let Some(rest) = tag.strip_prefix("certificate-provenance:") {
            if let Some((format, replayed)) = rest.rsplit_once(':') {
                return Self::CertificateProvenance {
                    format: format.to_owned(),
                    replayed: replayed == "replayed",
                };
            }
        }

        if let Some(rest) = tag.strip_prefix("generated-code:") {
            if let Some((generator, deterministic)) = rest.rsplit_once(':') {
                return Self::GeneratedCode {
                    generator: generator.to_owned(),
                    deterministic: deterministic == "deterministic",
                };
            }
        }

        if tag == "unsafe-declaration" {
            return Self::UnsafeDeclaration;
        }
        if tag == "opaque-constant" {
            return Self::OpaqueConstant;
        }
        if tag == "axiom-declaration" {
            return Self::AxiomDeclaration;
        }
        if let Some(solver) = tag.strip_prefix("external-solver:") {
            return Self::ExternalSolver {
                solver: solver.to_owned(),
            };
        }

        Self::Other {
            tag: tag.to_owned(),
        }
    }
}

/// Severity level for an audit finding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AuditSeverity {
    /// Informational observation, no action required.
    Info,
    /// Potential issue that should be reviewed.
    Warning,
    /// Definite problem that needs correction.
    Error,
    /// Fundamental soundness issue requiring immediate attention.
    Critical,
}

/// A single finding from an audit pass.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuditFinding {
    /// Severity of this finding.
    pub severity: AuditSeverity,
    /// Category tag (e.g., "trust-leak", "axiom-gap", "training-contamination").
    pub category: String,
    /// Human-readable description of the finding.
    pub message: String,
    /// Node indices relevant to this finding (may be empty for global findings).
    pub node_indices: Vec<u32>,
    /// Optional remediation recommendation.
    pub recommendation: Option<String>,
}

impl AuditFinding {
    /// Construct a finding from a structured category while preserving the
    /// legacy string category field.
    #[must_use]
    pub fn structured(
        severity: AuditSeverity,
        category: AuditFindingCategory,
        message: impl Into<String>,
        node_indices: Vec<u32>,
        recommendation: Option<String>,
    ) -> Self {
        Self {
            severity,
            category: category.legacy_tag(),
            message: message.into(),
            node_indices,
            recommendation,
        }
    }

    /// Return the structured interpretation of this finding's category tag.
    #[must_use]
    pub fn structured_category(&self) -> AuditFindingCategory {
        AuditFindingCategory::from_legacy_tag(&self.category)
    }
}

/// A cross-system finding comparing two source systems.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrossSystemFinding {
    /// First system involved.
    pub system_a: String,
    /// Second system involved.
    pub system_b: String,
    /// Description of the cross-system issue.
    pub issue: String,
}

/// Complete audit report for a set of imported constants.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AuditReport {
    /// Total number of constants audited.
    pub total_constants: usize,
    /// Breakdown by trust level.
    pub by_trust_level: HashMap<TrustLevel, usize>,
    /// Breakdown by source system name.
    pub by_source_system: HashMap<String, usize>,
    /// Fraction of constants with a non-empty AxiomProfile (0.0..=1.0).
    pub axiom_coverage: f64,
    /// Fraction of constants that are kernel-verified (0.0..=1.0).
    pub kernel_verified_fraction: f64,
    /// Trust violations detected during audit.
    pub trust_violations: Vec<TrustViolation>,
    /// Additional audit findings.
    pub findings: Vec<AuditFinding>,
    /// Number of constants exportable for AI proof-generation training.
    pub exportable_for_training: usize,
    /// Cross-system findings (interactions between different proof systems).
    pub cross_system_findings: Vec<CrossSystemFinding>,
}

impl AuditReport {
    /// Produce a human-readable summary of this audit report.
    #[must_use]
    pub fn summary(&self) -> String {
        let mut lines = Vec::with_capacity(16);
        lines.push("=== Mathverse Trust Audit Report ===".to_string());
        lines.push(format!("Total constants: {}", self.total_constants));
        lines.push(format!(
            "Axiom coverage: {:.1}%",
            self.axiom_coverage * 100.0
        ));
        lines.push(format!(
            "Kernel-verified: {:.1}%",
            self.kernel_verified_fraction * 100.0
        ));
        lines.push(format!(
            "Exportable for training: {}",
            self.exportable_for_training
        ));

        if !self.by_trust_level.is_empty() {
            lines.push("Trust level breakdown:".to_owned());
            // Sort by trust level for deterministic output.
            let mut levels: Vec<_> = self.by_trust_level.iter().collect();
            levels.sort_by_key(|(level, _)| **level);
            for (level, count) in levels {
                lines.push(format!("  {:?}: {}", level, count));
            }
        }

        lines.push(format!("Trust violations: {}", self.trust_violations.len()));
        lines.push(format!("Findings: {}", self.findings.len()));

        let critical_count = self
            .findings
            .iter()
            .filter(|f| f.severity == AuditSeverity::Critical)
            .count();
        let error_count = self
            .findings
            .iter()
            .filter(|f| f.severity == AuditSeverity::Error)
            .count();
        if critical_count > 0 || error_count > 0 {
            lines.push(format!(
                "  Critical: {}, Error: {}",
                critical_count, error_count
            ));
        }

        let status = if self.is_clean() {
            "CLEAN"
        } else {
            "ISSUES FOUND"
        };
        lines.push(format!("Status: {}", status));

        lines.join("\n")
    }

    /// Returns `true` if the audit found no violations and no Error/Critical findings.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.trust_violations.is_empty()
            && !self.findings.iter().any(|f| {
                f.severity == AuditSeverity::Error || f.severity == AuditSeverity::Critical
            })
    }

    /// Compute the trust-relevant delta from `self` (pre) to `new` (post).
    ///
    /// This is the input to authority gates that must decide whether a patch
    /// introduced trust debt that the producer did not declare.
    #[must_use]
    pub fn diff(&self, new: &AuditReport) -> AuditDelta {
        AuditDelta::between(self, new)
    }
}

/// Trust-relevant changes between two audit reports.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuditDelta {
    /// Axiom declarations newly present in the newer report.
    pub added_axioms: Vec<String>,
    /// Axiom declarations no longer present in the newer report.
    pub removed_axioms: Vec<String>,
    /// Opaque constants newly present in the newer report.
    pub added_opaques: Vec<String>,
    /// Opaque constants no longer present in the newer report.
    pub removed_opaques: Vec<String>,
    /// Unsafe declarations newly present in the newer report.
    pub added_unsafe: Vec<String>,
    /// Unsafe declarations no longer present in the newer report.
    pub removed_unsafe: Vec<String>,
    /// External solver trust boundaries newly present in the newer report.
    pub added_external_solvers: Vec<String>,
    /// External solver trust boundaries no longer present in the newer report.
    pub removed_external_solvers: Vec<String>,
    /// Critical findings newly present in the newer report.
    pub added_critical_findings: Vec<String>,
    /// Critical findings no longer present in the newer report.
    pub removed_critical_findings: Vec<String>,
}

impl AuditDelta {
    /// Compute a trust-relevant delta from `old` to `new`.
    #[must_use]
    pub fn between(old: &AuditReport, new: &AuditReport) -> Self {
        Self {
            added_axioms: added_items(old, new, is_axiom_finding),
            removed_axioms: removed_items(old, new, is_axiom_finding),
            added_opaques: added_items(old, new, is_opaque_finding),
            removed_opaques: removed_items(old, new, is_opaque_finding),
            added_unsafe: added_items(old, new, is_unsafe_finding),
            removed_unsafe: removed_items(old, new, is_unsafe_finding),
            added_external_solvers: added_items(old, new, is_external_solver_finding),
            removed_external_solvers: removed_items(old, new, is_external_solver_finding),
            added_critical_findings: added_items(old, new, is_critical_finding),
            removed_critical_findings: removed_items(old, new, is_critical_finding),
        }
    }

    /// Whether the delta introduced any new trust debt.
    #[must_use]
    pub fn has_new_trust_debt(&self) -> bool {
        !self.added_axioms.is_empty()
            || !self.added_opaques.is_empty()
            || !self.added_unsafe.is_empty()
            || !self.added_external_solvers.is_empty()
            || !self.added_critical_findings.is_empty()
    }
}

fn added_items(
    old: &AuditReport,
    new: &AuditReport,
    predicate: fn(&AuditFinding) -> bool,
) -> Vec<String> {
    let old_items = finding_items(old, predicate);
    let new_items = finding_items(new, predicate);
    sorted_difference(&new_items, &old_items)
}

fn removed_items(
    old: &AuditReport,
    new: &AuditReport,
    predicate: fn(&AuditFinding) -> bool,
) -> Vec<String> {
    let old_items = finding_items(old, predicate);
    let new_items = finding_items(new, predicate);
    sorted_difference(&old_items, &new_items)
}

fn finding_items(report: &AuditReport, predicate: fn(&AuditFinding) -> bool) -> HashSet<String> {
    report
        .findings
        .iter()
        .filter(|finding| predicate(finding))
        .map(finding_identity)
        .collect()
}

fn sorted_difference(left: &HashSet<String>, right: &HashSet<String>) -> Vec<String> {
    let mut items: Vec<_> = left.difference(right).cloned().collect();
    items.sort();
    items
}

fn finding_identity(finding: &AuditFinding) -> String {
    format!("{}: {}", finding.category, finding.message)
}

fn is_axiom_finding(finding: &AuditFinding) -> bool {
    matches!(
        finding.structured_category(),
        AuditFindingCategory::AxiomDeclaration
    )
}

fn is_opaque_finding(finding: &AuditFinding) -> bool {
    matches!(
        finding.structured_category(),
        AuditFindingCategory::OpaqueConstant
    )
}

fn is_unsafe_finding(finding: &AuditFinding) -> bool {
    matches!(
        finding.structured_category(),
        AuditFindingCategory::UnsafeDeclaration
    )
}

fn is_external_solver_finding(finding: &AuditFinding) -> bool {
    matches!(
        finding.structured_category(),
        AuditFindingCategory::ExternalSolver { .. }
    )
}

fn is_critical_finding(finding: &AuditFinding) -> bool {
    finding.severity == AuditSeverity::Critical
}

/// Builder for constructing an [`AuditReport`] incrementally.
#[must_use]
pub struct AuditReportBuilder {
    total_constants: usize,
    by_trust_level: HashMap<TrustLevel, usize>,
    by_source_system: HashMap<String, usize>,
    has_profile_count: usize,
    kernel_verified_count: usize,
    trust_violations: Vec<TrustViolation>,
    findings: Vec<AuditFinding>,
    exportable_for_training: usize,
    cross_system_findings: Vec<CrossSystemFinding>,
}

impl AuditReportBuilder {
    /// Create a new empty report builder.
    pub fn new() -> Self {
        Self {
            total_constants: 0,
            by_trust_level: HashMap::new(),
            by_source_system: HashMap::new(),
            has_profile_count: 0,
            kernel_verified_count: 0,
            trust_violations: Vec::new(),
            findings: Vec::new(),
            exportable_for_training: 0,
            cross_system_findings: Vec::new(),
        }
    }

    /// Register a constant with its trust level, source system, and axiom profile.
    pub fn add_constant(&mut self, trust: TrustLevel, source: &str, profile: AxiomProfile) {
        self.total_constants += 1;
        *self.by_trust_level.entry(trust).or_insert(0) += 1;
        *self.by_source_system.entry(source.to_owned()).or_insert(0) += 1;

        // KernelVerified + NONE means explicitly verified to have no axiom deps.
        if profile != AxiomProfile::NONE || trust == TrustLevel::KernelVerified {
            self.has_profile_count += 1;
        }

        if trust == TrustLevel::KernelVerified && profile.is_kernel_verified() {
            self.kernel_verified_count += 1;
            self.exportable_for_training += 1;
        }
    }

    /// Record a trust violation.
    pub fn add_violation(&mut self, v: TrustViolation) {
        self.trust_violations.push(v);
    }

    /// Record an audit finding.
    pub fn add_finding(&mut self, f: AuditFinding) {
        self.findings.push(f);
    }

    /// Record a cross-system finding between two proof systems.
    pub fn add_cross_system_finding(&mut self, system_a: &str, system_b: &str, issue: &str) {
        self.cross_system_findings.push(CrossSystemFinding {
            system_a: system_a.to_owned(),
            system_b: system_b.to_owned(),
            issue: issue.to_owned(),
        });
    }

    /// Consume the builder and produce the final [`AuditReport`].
    pub fn build(self) -> AuditReport {
        let axiom_coverage = if self.total_constants > 0 {
            self.has_profile_count as f64 / self.total_constants as f64
        } else {
            0.0
        };

        let kernel_verified_fraction = if self.total_constants > 0 {
            self.kernel_verified_count as f64 / self.total_constants as f64
        } else {
            0.0
        };

        AuditReport {
            total_constants: self.total_constants,
            by_trust_level: self.by_trust_level,
            by_source_system: self.by_source_system,
            axiom_coverage,
            kernel_verified_fraction,
            trust_violations: self.trust_violations,
            findings: self.findings,
            exportable_for_training: self.exportable_for_training,
            cross_system_findings: self.cross_system_findings,
        }
    }
}

impl Default for AuditReportBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Report formatting
// ---------------------------------------------------------------------------

/// Output format for audit reports.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum AuditReportFormat {
    /// Plain text (the default `summary()` format).
    Text,
    /// JSON suitable for machine consumption.
    Json,
    /// Markdown suitable for issue comments or documentation.
    Markdown,
}

impl AuditReport {
    /// Format the report in the requested format.
    #[must_use]
    pub fn format(&self, fmt: AuditReportFormat) -> String {
        match fmt {
            AuditReportFormat::Text => self.summary(),
            AuditReportFormat::Json => self.to_json(),
            AuditReportFormat::Markdown => self.to_markdown(),
        }
    }

    /// Serialize the report to a JSON string.
    #[must_use]
    pub fn to_json(&self) -> String {
        // Build a deterministic JSON representation.
        // We avoid serde_json::to_string on the struct directly because
        // HashMap iteration order is nondeterministic; instead we build
        // sorted key-value pairs.
        let mut parts = Vec::with_capacity(16);
        parts.push(format!("  \"total_constants\": {}", self.total_constants));
        parts.push(format!("  \"axiom_coverage\": {:.4}", self.axiom_coverage));
        parts.push(format!(
            "  \"kernel_verified_fraction\": {:.4}",
            self.kernel_verified_fraction
        ));
        parts.push(format!(
            "  \"exportable_for_training\": {}",
            self.exportable_for_training
        ));
        parts.push(format!(
            "  \"trust_violations_count\": {}",
            self.trust_violations.len()
        ));
        parts.push(format!("  \"findings_count\": {}", self.findings.len()));

        // Trust level breakdown (sorted).
        let mut levels: Vec<_> = self.by_trust_level.iter().collect();
        levels.sort_by_key(|(level, _)| **level);
        let level_entries: Vec<String> = levels
            .iter()
            .map(|(level, count)| format!("    \"{:?}\": {}", level, count))
            .collect();
        parts.push(format!(
            "  \"by_trust_level\": {{\n{}\n  }}",
            level_entries.join(",\n")
        ));

        // Source system breakdown (sorted).
        let mut sources: Vec<_> = self.by_source_system.iter().collect();
        sources.sort_by_key(|(left, _)| *left);
        let source_entries: Vec<String> = sources
            .iter()
            .map(|(name, count)| format!("    \"{}\": {}", name, count))
            .collect();
        parts.push(format!(
            "  \"by_source_system\": {{\n{}\n  }}",
            source_entries.join(",\n")
        ));

        // Findings summary by severity.
        let critical = self
            .findings
            .iter()
            .filter(|f| f.severity == AuditSeverity::Critical)
            .count();
        let error = self
            .findings
            .iter()
            .filter(|f| f.severity == AuditSeverity::Error)
            .count();
        let warning = self
            .findings
            .iter()
            .filter(|f| f.severity == AuditSeverity::Warning)
            .count();
        let info = self
            .findings
            .iter()
            .filter(|f| f.severity == AuditSeverity::Info)
            .count();
        parts.push(format!(
            "  \"findings_by_severity\": {{\n    \
             \"critical\": {},\n    \
             \"error\": {},\n    \
             \"warning\": {},\n    \
             \"info\": {}\n  }}",
            critical, error, warning, info
        ));

        let status = if self.is_clean() {
            "CLEAN"
        } else {
            "ISSUES_FOUND"
        };
        parts.push(format!("  \"status\": \"{}\"", status));

        format!("{{\n{}\n}}", parts.join(",\n"))
    }

    /// Render the report as a Markdown document.
    #[must_use]
    pub fn to_markdown(&self) -> String {
        let mut lines = Vec::with_capacity(32);

        let status = if self.is_clean() {
            "CLEAN"
        } else {
            "ISSUES FOUND"
        };
        lines.push("# Mathverse Trust Audit Report".to_string());
        lines.push(String::new());
        lines.push(format!("**Status:** {}", status));
        lines.push(String::new());

        lines.push("## Summary".to_owned());
        lines.push(String::new());
        lines.push("| Metric | Value |".to_string());
        lines.push("|--------|-------|".to_string());
        lines.push(format!("| Total constants | {} |", self.total_constants));
        lines.push(format!(
            "| Axiom coverage | {:.1}% |",
            self.axiom_coverage * 100.0
        ));
        lines.push(format!(
            "| Kernel-verified | {:.1}% |",
            self.kernel_verified_fraction * 100.0
        ));
        lines.push(format!(
            "| Exportable for training | {} |",
            self.exportable_for_training
        ));
        lines.push(format!(
            "| Trust violations | {} |",
            self.trust_violations.len()
        ));
        lines.push(format!("| Findings | {} |", self.findings.len()));
        lines.push(String::new());

        // Trust level breakdown.
        if !self.by_trust_level.is_empty() {
            lines.push("## Trust Level Breakdown".to_owned());
            lines.push(String::new());
            lines.push("| Trust Level | Count |".to_owned());
            lines.push("|-------------|-------|".to_owned());
            let mut levels: Vec<_> = self.by_trust_level.iter().collect();
            levels.sort_by_key(|(level, _)| **level);
            for (level, count) in levels {
                lines.push(format!("| {:?} | {} |", level, count));
            }
            lines.push(String::new());
        }

        // Findings.
        if !self.findings.is_empty() {
            lines.push("## Findings".to_owned());
            lines.push(String::new());
            for (i, finding) in self.findings.iter().enumerate() {
                lines.push(format!(
                    "{}. **[{:?}]** `{}`: {}",
                    i + 1,
                    finding.severity,
                    finding.category,
                    finding.message
                ));
                if let Some(ref rec) = finding.recommendation {
                    lines.push(format!("   - *Recommendation:* {}", rec));
                }
            }
            lines.push(String::new());
        }

        // Trust violations.
        if !self.trust_violations.is_empty() {
            lines.push("## Trust Violations".to_owned());
            lines.push(String::new());
            for v in &self.trust_violations {
                lines.push(format!(
                    "- Node {} ({:?}) -> Node {} ({:?}): {}",
                    v.parent_idx, v.parent_trust, v.child_idx, v.child_trust, v.violation
                ));
            }
            lines.push(String::new());
        }

        // Cross-system findings.
        if !self.cross_system_findings.is_empty() {
            lines.push("## Cross-System Findings".to_owned());
            lines.push(String::new());
            for csf in &self.cross_system_findings {
                lines.push(format!(
                    "- **{} / {}**: {}",
                    csf.system_a, csf.system_b, csf.issue
                ));
            }
            lines.push(String::new());
        }

        // Recommendations.
        let recs = self.generate_recommendations();
        if !recs.is_empty() {
            lines.push("## Recommendations".to_owned());
            lines.push(String::new());
            for (i, rec) in recs.iter().enumerate() {
                lines.push(format!("{}. {}", i + 1, rec));
            }
            lines.push(String::new());
        }

        lines.join("\n")
    }

    /// Generate actionable recommendations based on the audit findings.
    ///
    /// Analyzes trust violations, finding severity, axiom coverage,
    /// kernel-verified fraction, training exportability, and cross-system
    /// issues to produce prioritized recommendation strings.
    #[must_use]
    pub fn generate_recommendations(&self) -> Vec<String> {
        let mut recs = Vec::new();

        // Trust violations are always top priority.
        if !self.trust_violations.is_empty() {
            recs.push(format!(
                "CRITICAL: {} trust violation(s) detected. \
                 Review dependency edges to ensure no high-trust constant \
                 depends on a lower-trust constant without explicit justification.",
                self.trust_violations.len()
            ));
        }

        // Critical findings need immediate attention.
        let critical_count = self
            .findings
            .iter()
            .filter(|f| f.severity == AuditSeverity::Critical)
            .count();
        if critical_count > 0 {
            recs.push(format!(
                "CRITICAL: {} critical finding(s) require immediate investigation. \
                 Check for soundness issues, trust leaks, or axiom contamination.",
                critical_count
            ));
        }

        // Error findings.
        let error_count = self
            .findings
            .iter()
            .filter(|f| f.severity == AuditSeverity::Error)
            .count();
        if error_count > 0 {
            recs.push(format!(
                "HIGH: {} error-level finding(s) need correction \
                 before the next import batch.",
                error_count
            ));
        }

        // Low kernel-verified fraction.
        if self.total_constants > 0 && self.kernel_verified_fraction < 0.5 {
            recs.push(format!(
                "MEDIUM: Only {:.1}% of constants are kernel-verified. \
                 Consider re-checking imported constants through the kernel \
                 or strengthening trust-level assignment criteria.",
                self.kernel_verified_fraction * 100.0
            ));
        }

        // No training-exportable constants.
        if self.total_constants > 0 && self.exportable_for_training == 0 {
            recs.push(
                "MEDIUM: No constants are exportable for AI training. \
                 Training export requires KernelVerified trust with an empty \
                 axiom profile. Review import pipeline trust assignment."
                    .to_owned(),
            );
        }

        // Low axiom coverage.
        if self.total_constants > 0 && self.axiom_coverage < 0.5 {
            recs.push(format!(
                "LOW: Axiom coverage is {:.1}%. Many constants lack axiom profiles, \
                 making it harder to reason about their foundational assumptions. \
                 Run axiom propagation to fill in transitive profiles.",
                self.axiom_coverage * 100.0
            ));
        }

        // Cross-system findings.
        if !self.cross_system_findings.is_empty() {
            recs.push(format!(
                "HIGH: {} cross-system issue(s) detected. \
                 Verify that axiom profiles from different proof systems \
                 (HOL, Mizar, etc.) do not contain conflicting assumptions.",
                self.cross_system_findings.len()
            ));
        }

        recs
    }
}

// ---------------------------------------------------------------------------
// Report comparison (regression detection)
// ---------------------------------------------------------------------------

/// Result of comparing two audit reports.
#[derive(Clone, Debug)]
pub struct AuditComparison {
    /// Absolute change in total constants (new - old).
    pub constants_delta: i64,
    /// Absolute change in exportable count (new - old).
    pub exportable_delta: i64,
    /// Absolute change in trust violation count (new - old).
    pub violations_delta: i64,
    /// Absolute change in finding count (new - old).
    pub findings_delta: i64,
    /// Change in axiom coverage (new - old).
    pub axiom_coverage_delta: f64,
    /// Change in kernel-verified fraction (new - old).
    pub kernel_verified_delta: f64,
    /// Whether the new report is a regression (more violations or critical findings).
    pub is_regression: bool,
    /// Whether the new report is an improvement (fewer violations/findings, or higher coverage).
    pub is_improvement: bool,
    /// New categories of findings that did not exist in the old report.
    pub new_finding_categories: Vec<String>,
    /// Categories of findings that were resolved (present in old, absent in new).
    pub resolved_finding_categories: Vec<String>,
}

/// Compare two audit reports for regression detection.
///
/// Returns a structured comparison indicating what changed between the
/// `old` and `new` reports.
#[must_use]
pub fn compare_reports(old: &AuditReport, new: &AuditReport) -> AuditComparison {
    let constants_delta = new.total_constants as i64 - old.total_constants as i64;
    let exportable_delta = new.exportable_for_training as i64 - old.exportable_for_training as i64;
    let violations_delta = new.trust_violations.len() as i64 - old.trust_violations.len() as i64;
    let findings_delta = new.findings.len() as i64 - old.findings.len() as i64;
    let axiom_coverage_delta = new.axiom_coverage - old.axiom_coverage;
    let kernel_verified_delta = new.kernel_verified_fraction - old.kernel_verified_fraction;

    // Categorize findings.
    let old_categories: HashSet<String> = old.findings.iter().map(|f| f.category.clone()).collect();
    let new_categories: HashSet<String> = new.findings.iter().map(|f| f.category.clone()).collect();

    let new_finding_categories: Vec<String> = new_categories
        .difference(&old_categories)
        .cloned()
        .collect();
    let resolved_finding_categories: Vec<String> = old_categories
        .difference(&new_categories)
        .cloned()
        .collect();

    // Determine regression: more violations, or new Critical/Error findings.
    let old_critical_error = old
        .findings
        .iter()
        .filter(|f| f.severity >= AuditSeverity::Error)
        .count();
    let new_critical_error = new
        .findings
        .iter()
        .filter(|f| f.severity >= AuditSeverity::Error)
        .count();

    let is_regression = violations_delta > 0
        || new_critical_error > old_critical_error
        || (!new_finding_categories.is_empty()
            && new.findings.iter().any(|f| {
                new_finding_categories.contains(&f.category) && f.severity >= AuditSeverity::Error
            }));

    // Determine improvement: fewer violations, better coverage, or resolved findings.
    let is_improvement = violations_delta < 0
        || new_critical_error < old_critical_error
        || kernel_verified_delta > 0.0
        || !resolved_finding_categories.is_empty();

    AuditComparison {
        constants_delta,
        exportable_delta,
        violations_delta,
        findings_delta,
        axiom_coverage_delta,
        kernel_verified_delta,
        is_regression,
        is_improvement,
        new_finding_categories,
        resolved_finding_categories,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_audit_report_builder_empty() {
        let report = AuditReportBuilder::new().build();
        assert_eq!(report.total_constants, 0);
        assert!(report.by_trust_level.is_empty());
        assert!(report.by_source_system.is_empty());
        assert_eq!(report.axiom_coverage, 0.0);
        assert_eq!(report.kernel_verified_fraction, 0.0);
        assert!(report.trust_violations.is_empty());
        assert!(report.findings.is_empty());
        assert_eq!(report.exportable_for_training, 0);
        assert!(report.is_clean());
    }

    #[test]
    fn test_audit_report_builder_add_constants() {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        builder.add_constant(TrustLevel::AxiomDependent, "Coq", AxiomProfile::CLASSICAL);
        builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);

        let report = builder.build();
        assert_eq!(report.total_constants, 3);
        assert_eq!(report.by_trust_level[&TrustLevel::KernelVerified], 2);
        assert_eq!(report.by_trust_level[&TrustLevel::AxiomDependent], 1);
        assert_eq!(report.by_source_system["Lean4"], 2);
        assert_eq!(report.by_source_system["Coq"], 1);
        // 3 out of 3 have profile (KernelVerified counts as having explicit empty profile)
        assert!((report.axiom_coverage - 1.0).abs() < 1e-10);
        // 2 out of 3 are kernel-verified with empty profile
        assert!((report.kernel_verified_fraction - 2.0 / 3.0).abs() < 1e-10);
        assert_eq!(report.exportable_for_training, 2);
        assert!(report.is_clean());
    }

    #[test]
    fn test_audit_report_is_clean_with_violations() {
        let mut builder = AuditReportBuilder::new();
        builder.add_violation(TrustViolation {
            parent_idx: 1,
            parent_trust: TrustLevel::KernelVerified,
            child_idx: 0,
            child_trust: TrustLevel::TrustedOracle,
            violation: "test violation".to_owned(),
        });
        let report = builder.build();
        assert!(!report.is_clean());
    }

    #[test]
    fn test_audit_report_is_clean_with_error_finding() {
        let mut builder = AuditReportBuilder::new();
        builder.add_finding(AuditFinding {
            severity: AuditSeverity::Error,
            category: "test".to_owned(),
            message: "something is wrong".to_owned(),
            node_indices: vec![0],
            recommendation: Some("fix it".to_owned()),
        });
        let report = builder.build();
        assert!(!report.is_clean());
    }

    #[test]
    fn test_audit_report_is_clean_with_warning_only() {
        let mut builder = AuditReportBuilder::new();
        builder.add_finding(AuditFinding {
            severity: AuditSeverity::Warning,
            category: "style".to_owned(),
            message: "minor concern".to_owned(),
            node_indices: vec![],
            recommendation: None,
        });
        let report = builder.build();
        assert!(report.is_clean());
    }

    #[test]
    fn test_audit_report_is_clean_with_critical_finding() {
        let mut builder = AuditReportBuilder::new();
        builder.add_finding(AuditFinding {
            severity: AuditSeverity::Critical,
            category: "soundness".to_owned(),
            message: "trust leak detected".to_owned(),
            node_indices: vec![1, 2],
            recommendation: Some("remove dependency".to_owned()),
        });
        let report = builder.build();
        assert!(!report.is_clean());
    }

    #[test]
    fn test_audit_report_summary_contains_key_info() {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        builder.add_constant(TrustLevel::TrustedOracle, "SMT", AxiomProfile::SMT_ORACLE);
        let report = builder.build();

        let summary = report.summary();
        assert!(summary.contains("Total constants: 2"));
        assert!(summary.contains("Exportable for training: 1"));
        assert!(summary.contains("CLEAN"));
    }

    #[test]
    fn test_audit_report_summary_shows_issues() {
        let mut builder = AuditReportBuilder::new();
        builder.add_violation(TrustViolation {
            parent_idx: 0,
            parent_trust: TrustLevel::KernelVerified,
            child_idx: 1,
            child_trust: TrustLevel::TrustedOracle,
            violation: "bad dep".to_owned(),
        });
        builder.add_finding(AuditFinding {
            severity: AuditSeverity::Critical,
            category: "soundness".to_owned(),
            message: "leak".to_owned(),
            node_indices: vec![],
            recommendation: None,
        });
        let report = builder.build();

        let summary = report.summary();
        assert!(summary.contains("Trust violations: 1"));
        assert!(summary.contains("Critical: 1"));
        assert!(summary.contains("ISSUES FOUND"));
    }

    #[test]
    fn test_audit_severity_ordering() {
        assert!(AuditSeverity::Info < AuditSeverity::Warning);
        assert!(AuditSeverity::Warning < AuditSeverity::Error);
        assert!(AuditSeverity::Error < AuditSeverity::Critical);
    }

    // -----------------------------------------------------------------------
    // Structured category tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_structured_finding_preserves_legacy_category_string() {
        let finding = AuditFinding::structured(
            AuditSeverity::Warning,
            AuditFindingCategory::KernelTrust {
                kernel: KernelAuditKernel::Clean,
            },
            "kernel trust debt",
            vec![3],
            None,
        );
        assert_eq!(finding.category, "kernel-trust:clean");
        assert_eq!(
            finding.structured_category(),
            AuditFindingCategory::KernelTrust {
                kernel: KernelAuditKernel::Clean,
            }
        );
    }

    #[test]
    fn test_audit_finding_category_legacy_tag_round_trip() {
        let categories = [
            AuditFindingCategory::KernelTrust {
                kernel: KernelAuditKernel::Lean,
            },
            AuditFindingCategory::CertificateProvenance {
                format: "clean-kernel-proof-term".to_owned(),
                replayed: false,
            },
            AuditFindingCategory::GeneratedCode {
                generator: "lean4-kernel".to_owned(),
                deterministic: true,
            },
            AuditFindingCategory::UnsafeDeclaration,
            AuditFindingCategory::OpaqueConstant,
            AuditFindingCategory::AxiomDeclaration,
            AuditFindingCategory::ExternalSolver {
                solver: "trustedArith".to_owned(),
            },
        ];
        for category in categories {
            let tag = category.legacy_tag();
            assert_eq!(AuditFindingCategory::from_legacy_tag(&tag), category);
        }
    }

    #[test]
    fn test_unknown_legacy_tag_decodes_to_other() {
        assert_eq!(
            AuditFindingCategory::from_legacy_tag("training-contamination"),
            AuditFindingCategory::Other {
                tag: "training-contamination".to_owned(),
            }
        );
    }

    // -----------------------------------------------------------------------
    // Cross-system finding tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_add_cross_system_finding() {
        let mut builder = AuditReportBuilder::new();
        builder.add_cross_system_finding(
            "HOL",
            "Mizar",
            "HOL_EMBEDDING and MIZAR_SOFT_TYPE overlap in constant X",
        );
        builder.add_cross_system_finding(
            "Lean4",
            "Coq",
            "Propositional extensionality assumption mismatch",
        );
        let report = builder.build();
        assert_eq!(report.cross_system_findings.len(), 2);
        assert_eq!(report.cross_system_findings[0].system_a, "HOL");
        assert_eq!(report.cross_system_findings[0].system_b, "Mizar");
        assert!(report.cross_system_findings[0].issue.contains("overlap"));
        assert_eq!(report.cross_system_findings[1].system_a, "Lean4");
    }

    #[test]
    fn test_cross_system_findings_in_markdown() {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "HOL", AxiomProfile::NONE);
        builder.add_cross_system_finding("HOL", "Mizar", "Axiom profile contains conflicting bits");
        let report = builder.build();
        let md = report.to_markdown();
        assert!(md.contains("## Cross-System Findings"));
        assert!(md.contains("**HOL / Mizar**"));
        assert!(md.contains("conflicting bits"));
    }

    #[test]
    fn test_empty_report_no_cross_system_section() {
        let report = AuditReportBuilder::new().build();
        let md = report.to_markdown();
        assert!(!md.contains("Cross-System Findings"));
    }

    // -----------------------------------------------------------------------
    // generate_recommendations tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_recommendations_clean_report() {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        let report = builder.build();
        let recs = report.generate_recommendations();
        assert!(
            recs.is_empty(),
            "clean report should have no recommendations"
        );
    }

    #[test]
    fn test_recommendations_trust_violations() {
        let mut builder = AuditReportBuilder::new();
        builder.add_violation(TrustViolation {
            parent_idx: 0,
            parent_trust: TrustLevel::KernelVerified,
            child_idx: 1,
            child_trust: TrustLevel::TrustedOracle,
            violation: "trust leak".to_owned(),
        });
        let report = builder.build();
        let recs = report.generate_recommendations();
        assert!(!recs.is_empty());
        assert!(recs[0].contains("CRITICAL"));
        assert!(recs[0].contains("trust violation"));
    }

    #[test]
    fn test_recommendations_low_kernel_verified() {
        let mut builder = AuditReportBuilder::new();
        // 1 kernel-verified, 4 oracle -> 20% kernel-verified
        builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        for _ in 0..4 {
            builder.add_constant(TrustLevel::TrustedOracle, "SMT", AxiomProfile::SMT_ORACLE);
        }
        let report = builder.build();
        let recs = report.generate_recommendations();
        assert!(
            recs.iter().any(|r| r.contains("kernel-verified")),
            "Should recommend improving kernel-verified fraction"
        );
    }

    #[test]
    fn test_recommendations_no_training_exportable() {
        let mut builder = AuditReportBuilder::new();
        // Axiom-dependent constants are not exportable.
        builder.add_constant(TrustLevel::AxiomDependent, "Coq", AxiomProfile::CLASSICAL);
        builder.add_constant(TrustLevel::TrustedOracle, "SMT", AxiomProfile::SMT_ORACLE);
        let report = builder.build();
        let recs = report.generate_recommendations();
        assert!(
            recs.iter()
                .any(|r| r.contains("exportable for AI training")),
            "Should recommend addressing zero training-exportable constants"
        );
    }

    #[test]
    fn test_recommendations_critical_findings() {
        let mut builder = AuditReportBuilder::new();
        builder.add_finding(AuditFinding {
            severity: AuditSeverity::Critical,
            category: "soundness".to_owned(),
            message: "axiom contamination".to_owned(),
            node_indices: vec![],
            recommendation: None,
        });
        let report = builder.build();
        let recs = report.generate_recommendations();
        assert!(recs.iter().any(|r| r.contains("critical finding")));
    }

    #[test]
    fn test_recommendations_cross_system_issues() {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "HOL", AxiomProfile::NONE);
        builder.add_cross_system_finding("HOL", "Mizar", "Conflicting axiom bits");
        let report = builder.build();
        let recs = report.generate_recommendations();
        assert!(
            recs.iter().any(|r| r.contains("cross-system")),
            "Should recommend addressing cross-system issues"
        );
    }

    #[test]
    fn test_recommendations_error_findings() {
        let mut builder = AuditReportBuilder::new();
        builder.add_finding(AuditFinding {
            severity: AuditSeverity::Error,
            category: "trust-leak".to_owned(),
            message: "edge from KernelVerified to TrustedOracle".to_owned(),
            node_indices: vec![0, 1],
            recommendation: Some("remove edge".to_owned()),
        });
        let report = builder.build();
        let recs = report.generate_recommendations();
        assert!(recs.iter().any(|r| r.contains("error-level finding")));
    }

    // -----------------------------------------------------------------------
    // Markdown rendering tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_to_markdown_clean_report() {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        let report = builder.build();
        let md = report.to_markdown();
        assert!(md.contains("# Mathverse Trust Audit Report"));
        assert!(md.contains("**Status:** CLEAN"));
        assert!(md.contains("| Total constants | 1 |"));
        assert!(md.contains("| Kernel-verified | 100.0% |"));
    }

    #[test]
    fn test_to_markdown_with_findings_and_violations() {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::TrustedOracle, "SMT", AxiomProfile::SMT_ORACLE);
        builder.add_violation(TrustViolation {
            parent_idx: 0,
            parent_trust: TrustLevel::KernelVerified,
            child_idx: 1,
            child_trust: TrustLevel::TrustedOracle,
            violation: "bad dep".to_owned(),
        });
        builder.add_finding(AuditFinding {
            severity: AuditSeverity::Warning,
            category: "axiom-gap".to_owned(),
            message: "missing profile".to_owned(),
            node_indices: vec![],
            recommendation: Some("run propagation".to_owned()),
        });
        let report = builder.build();
        let md = report.to_markdown();
        assert!(md.contains("**Status:** ISSUES FOUND"));
        assert!(md.contains("## Findings"));
        assert!(md.contains("`axiom-gap`"));
        assert!(md.contains("*Recommendation:* run propagation"));
        assert!(md.contains("## Trust Violations"));
        assert!(md.contains("bad dep"));
        // Should have recommendations section too.
        assert!(md.contains("## Recommendations"));
    }

    #[test]
    fn test_to_markdown_recommendations_section() {
        let mut builder = AuditReportBuilder::new();
        builder.add_cross_system_finding("HOL", "Mizar", "profile conflict");
        builder.add_constant(TrustLevel::KernelVerified, "HOL", AxiomProfile::NONE);
        let report = builder.build();
        let md = report.to_markdown();
        assert!(md.contains("## Recommendations"));
        assert!(md.contains("cross-system"));
    }

    // -----------------------------------------------------------------------
    // JSON rendering tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_to_json_basic_structure() {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        let report = builder.build();
        let json = report.to_json();
        assert!(json.contains("\"total_constants\": 1"));
        assert!(json.contains("\"status\": \"CLEAN\""));
        assert!(json.contains("\"exportable_for_training\": 1"));
    }

    // -----------------------------------------------------------------------
    // Report comparison tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_compare_reports_improvement() {
        let old = {
            let mut b = AuditReportBuilder::new();
            b.add_constant(TrustLevel::TrustedOracle, "SMT", AxiomProfile::SMT_ORACLE);
            b.add_violation(TrustViolation {
                parent_idx: 0,
                parent_trust: TrustLevel::KernelVerified,
                child_idx: 1,
                child_trust: TrustLevel::TrustedOracle,
                violation: "leak".to_owned(),
            });
            b.build()
        };
        let new = {
            let mut b = AuditReportBuilder::new();
            b.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
            b.build()
        };
        let cmp = compare_reports(&old, &new);
        assert!(cmp.is_improvement);
        assert!(!cmp.is_regression);
        assert_eq!(cmp.violations_delta, -1);
    }

    #[test]
    fn test_compare_reports_regression() {
        let old = {
            let mut b = AuditReportBuilder::new();
            b.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
            b.build()
        };
        let new = {
            let mut b = AuditReportBuilder::new();
            b.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
            b.add_violation(TrustViolation {
                parent_idx: 0,
                parent_trust: TrustLevel::KernelVerified,
                child_idx: 1,
                child_trust: TrustLevel::TrustedOracle,
                violation: "new leak".to_owned(),
            });
            b.build()
        };
        let cmp = compare_reports(&old, &new);
        assert!(cmp.is_regression);
        assert_eq!(cmp.violations_delta, 1);
    }

    #[test]
    fn test_compare_reports_new_finding_category() {
        let old = AuditReportBuilder::new().build();
        let new = {
            let mut b = AuditReportBuilder::new();
            b.add_finding(AuditFinding {
                severity: AuditSeverity::Error,
                category: "trust-leak".to_owned(),
                message: "new category".to_owned(),
                node_indices: vec![],
                recommendation: None,
            });
            b.build()
        };
        let cmp = compare_reports(&old, &new);
        assert!(cmp.is_regression);
        assert!(cmp
            .new_finding_categories
            .contains(&"trust-leak".to_owned()));
    }

    #[test]
    fn test_format_dispatches_correctly() {
        let report = AuditReportBuilder::new().build();
        let text = report.format(AuditReportFormat::Text);
        let json = report.format(AuditReportFormat::Json);
        let md = report.format(AuditReportFormat::Markdown);
        assert!(text.contains("==="));
        assert!(json.contains("{"));
        assert!(md.contains("#"));
    }
}
