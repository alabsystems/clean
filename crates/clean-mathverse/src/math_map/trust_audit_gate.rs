// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MathMap trust-audit gate policy.
//!
//! This is the typed policy layer for the ingest contract's trust-audit step.
//! It consumes Clean audit reports (pre- and post-patch) plus the bundle's
//! declared trust envelope; it does not run Lake, drift, or the audit itself.

use hashbrown::HashSet;
use serde::{Deserialize, Serialize};

use super::manifest::DeclaredTrust;
use crate::trust::audit_report::{AuditDelta, AuditReport};

/// Result of evaluating the MathMap trust-audit gate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustAuditGateDecision {
    /// Trust-relevant delta from the pre-patch report to the post-patch report.
    pub delta: AuditDelta,
    /// Rejection reasons. Empty means the gate accepted the audit delta.
    pub rejection_reasons: Vec<String>,
}

impl TrustAuditGateDecision {
    /// Whether the gate accepted the post-patch audit.
    #[must_use]
    pub fn is_accepted(&self) -> bool {
        self.rejection_reasons.is_empty()
    }
}

/// Evaluate MathMap's trust-audit gate.
///
/// This is fail-closed for missing declaration booleans: `None` is not "no",
/// it is "undeclared", and undeclared trust debt rejects. A declaration can
/// EXPLAIN newly introduced trust debt, but it can never bypass recursive trust
/// violations reported by the Clean trust gate.
#[must_use]
pub fn evaluate_trust_audit_gate(
    before: &AuditReport,
    after: &AuditReport,
    declared: &DeclaredTrust,
) -> TrustAuditGateDecision {
    let delta = before.diff(after);
    let mut rejection_reasons = Vec::new();

    if !delta.added_axioms.is_empty() && declared.introduces_new_axioms != Some(true) {
        rejection_reasons.push(format!(
            "new axioms were not declared: {}",
            delta.added_axioms.join("; ")
        ));
    }

    if !delta.added_opaques.is_empty() && declared.introduces_new_opaques != Some(true) {
        rejection_reasons.push(format!(
            "new opaque constants were not declared: {}",
            delta.added_opaques.join("; ")
        ));
    }

    if !delta.added_unsafe.is_empty() && declared.introduces_unsafe != Some(true) {
        rejection_reasons.push(format!(
            "new unsafe declarations were not declared: {}",
            delta.added_unsafe.join("; ")
        ));
    }

    let allowed_solvers: HashSet<&str> = declared
        .external_solvers
        .iter()
        .map(String::as_str)
        .collect();
    let unlisted_solvers: Vec<_> = delta
        .added_external_solvers
        .iter()
        .filter_map(|finding| external_solver_name(finding).map(|solver| (solver, finding)))
        .filter(|(solver, _)| !allowed_solvers.contains(*solver))
        .map(|(_, finding)| finding.clone())
        .collect();
    if !unlisted_solvers.is_empty() {
        rejection_reasons.push(format!(
            "new external solver trust was not declared: {}",
            unlisted_solvers.join("; ")
        ));
    }

    if !delta.added_critical_findings.is_empty() {
        rejection_reasons.push(format!(
            "new critical audit findings: {}",
            delta.added_critical_findings.join("; ")
        ));
    }

    if !after.trust_violations.is_empty() {
        rejection_reasons.push(format!(
            "post-patch report contains recursive trust violations: {}",
            after.trust_violations.len()
        ));
    }

    TrustAuditGateDecision {
        delta,
        rejection_reasons,
    }
}

fn external_solver_name(finding_identity: &str) -> Option<&str> {
    finding_identity
        .strip_prefix("external-solver:")
        .and_then(|rest| rest.split(':').next())
        .filter(|solver| !solver.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trust::audit_report::{
        AuditFinding, AuditFindingCategory, AuditReportBuilder, AuditSeverity,
    };
    use crate::trust::graph_gate::TrustViolation;
    use crate::types::{AxiomProfile, TrustLevel};

    fn declared_clean() -> DeclaredTrust {
        DeclaredTrust {
            introduces_new_axioms: Some(false),
            introduces_new_opaques: Some(false),
            introduces_unsafe: Some(false),
            external_solvers: Vec::new(),
            generated_proof_terms: Some(true),
        }
    }

    #[test]
    fn test_trust_audit_gate_rejects_undeclared_new_axioms() {
        let before = AuditReportBuilder::new().build();
        let after = {
            let mut builder = AuditReportBuilder::new();
            builder.add_finding(AuditFinding::structured(
                AuditSeverity::Warning,
                AuditFindingCategory::AxiomDeclaration,
                "Axiom declaration: Foo.bad",
                vec![],
                None,
            ));
            builder.build()
        };

        let decision = evaluate_trust_audit_gate(&before, &after, &declared_clean());

        assert!(!decision.is_accepted());
        assert!(decision.rejection_reasons[0].contains("new axioms"));
    }

    #[test]
    fn test_trust_audit_gate_rejects_undeclared_new_axioms_when_declaration_is_absent() {
        let before = AuditReportBuilder::new().build();
        let after = {
            let mut builder = AuditReportBuilder::new();
            builder.add_finding(AuditFinding::structured(
                AuditSeverity::Warning,
                AuditFindingCategory::AxiomDeclaration,
                "Axiom declaration: Foo.bad",
                vec![],
                None,
            ));
            builder.build()
        };
        let mut declared = declared_clean();
        // Fail-closed: `None` is "undeclared", not "declared false".
        declared.introduces_new_axioms = None;

        let decision = evaluate_trust_audit_gate(&before, &after, &declared);

        assert!(!decision.is_accepted());
    }

    #[test]
    fn test_trust_audit_gate_accepts_declared_new_opaques_without_other_debt() {
        let before = AuditReportBuilder::new().build();
        let after = {
            let mut builder = AuditReportBuilder::new();
            builder.add_finding(AuditFinding::structured(
                AuditSeverity::Warning,
                AuditFindingCategory::OpaqueConstant,
                "Opaque constant: Foo.hidden",
                vec![],
                None,
            ));
            builder.build()
        };
        let mut declared = declared_clean();
        declared.introduces_new_opaques = Some(true);

        let decision = evaluate_trust_audit_gate(&before, &after, &declared);

        assert!(decision.is_accepted(), "{decision:?}");
    }

    #[test]
    fn test_trust_audit_gate_rejects_unlisted_external_solver() {
        let before = AuditReportBuilder::new().build();
        let after = {
            let mut builder = AuditReportBuilder::new();
            builder.add_finding(AuditFinding::structured(
                AuditSeverity::Warning,
                AuditFindingCategory::ExternalSolver {
                    solver: "trustedZ4".to_owned(),
                },
                "External solver trust marker: Foo.z4",
                vec![],
                None,
            ));
            builder.build()
        };

        let decision = evaluate_trust_audit_gate(&before, &after, &declared_clean());

        assert!(!decision.is_accepted());
        assert!(decision.rejection_reasons[0].contains("external solver"));
    }

    #[test]
    fn test_trust_audit_gate_accepts_listed_external_solver() {
        let before = AuditReportBuilder::new().build();
        let after = {
            let mut builder = AuditReportBuilder::new();
            builder.add_finding(AuditFinding::structured(
                AuditSeverity::Warning,
                AuditFindingCategory::ExternalSolver {
                    solver: "trustedArith".to_owned(),
                },
                "External solver trust marker: Foo.arith",
                vec![],
                None,
            ));
            builder.build()
        };
        let mut declared = declared_clean();
        declared.external_solvers = vec!["trustedArith".to_owned()];

        let decision = evaluate_trust_audit_gate(&before, &after, &declared);

        assert!(decision.is_accepted(), "{decision:?}");
    }

    #[test]
    fn test_trust_audit_gate_rejects_new_critical_findings() {
        let before = AuditReportBuilder::new().build();
        let after = {
            let mut builder = AuditReportBuilder::new();
            builder.add_finding(AuditFinding {
                severity: AuditSeverity::Critical,
                category: "frontier-claim".to_owned(),
                message: "frontier claim outside target set".to_owned(),
                node_indices: vec![],
                recommendation: None,
            });
            builder.build()
        };

        let decision = evaluate_trust_audit_gate(&before, &after, &declared_clean());

        assert!(!decision.is_accepted());
        assert!(decision.rejection_reasons[0].contains("critical"));
    }

    #[test]
    fn test_trust_audit_gate_declared_solver_still_rejects_recursive_trust_violation() {
        let before = AuditReportBuilder::new().build();
        let after = {
            let mut builder = AuditReportBuilder::new();
            builder.add_constant(TrustLevel::KernelVerified, "Clean", AxiomProfile::NONE);
            builder.add_constant(TrustLevel::TrustedOracle, "SMT", AxiomProfile::SMT_ORACLE);
            builder.add_violation(TrustViolation {
                parent_idx: 0,
                parent_trust: TrustLevel::KernelVerified,
                child_idx: 1,
                child_trust: TrustLevel::TrustedOracle,
                violation: "KernelVerified cannot depend on TrustedOracle".to_owned(),
            });
            builder.build()
        };
        let mut declared = declared_clean();
        declared.external_solvers = vec!["trustedZ4".to_owned()];

        let decision = evaluate_trust_audit_gate(&before, &after, &declared);

        assert!(!decision.is_accepted());
        assert!(decision
            .rejection_reasons
            .iter()
            .any(|reason| reason.contains("recursive trust")));
    }
}
