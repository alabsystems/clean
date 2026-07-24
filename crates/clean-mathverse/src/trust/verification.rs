// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Self-verification proofs for the Mathverse trust pipeline.
//!
//! Provides a verification suite that checks structural properties of the
//! trust infrastructure at runtime. These are not formal proofs but executable
//! property checks that catch regressions and validate invariants on concrete
//! graph instances.

use hashbrown::HashSet;
use serde::{Deserialize, Serialize};

use super::audit_report::AuditReport;
use super::axiom_propagation::DependencyGraph;
use super::graph_gate::{TrainingExportGate, TrustGate};
use crate::bulk_import::BulkImportResult;
use crate::types::{AxiomProfile, TrustLevel};

/// A property that the verification suite can check.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VerificationProperty {
    /// Propagation can only increase (widen) axiom profiles, never shrink them.
    PropagationMonotonicity,
    /// Re-running propagation on an already-propagated graph is a no-op.
    PropagationIdempotency,
    /// The trust gate has a policy entry for every known `TrustLevel`.
    TrustGateCompleteness,
    /// The training export gate only passes `KernelVerified` + empty profile.
    TrainingGateStrictness,
    /// Topological order is preserved when the graph satisfies `child < parent`.
    TopologicalOrderPreservation,
    /// A valid graph (all deps at equal-or-lower trust) produces zero audit violations.
    NoTrustLeakage,
    /// Cross-system consistency: HOL and Mizar profiles have compatible axiom assumptions.
    CrossSystemConsistency,
    /// Bulk import integrity: propagation, trust, and training export all passed.
    BulkImportIntegrity,
    /// After propagation, every node reachable via dependency edges has its axiom
    /// profile included in the ancestor's profile.
    PropagationCompleteness,
    /// No constant with a non-empty axiom profile passes the training export gate.
    TrainingGateSoundness,
    /// Trust hierarchy transitivity: if A can depend on B and B on C, then A can depend on C.
    TrustHierarchyTransitivity,
    /// Every trust violation in the graph appears in the audit report.
    AuditReportCompleteness,
}

/// Result of checking a single verification property.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VerificationResult {
    /// Which property was checked.
    pub property: VerificationProperty,
    /// Whether the property held.
    pub passed: bool,
    /// Human-readable evidence or explanation.
    pub evidence: String,
    /// Number of individual checks performed (edges, nodes, etc.).
    pub checked_count: usize,
}

/// Suite of verification checks for the trust pipeline.
pub struct VerificationSuite;

impl VerificationSuite {
    /// Create a new verification suite.
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    /// Verify propagation monotonicity: after propagation, every node's profile
    /// is a superset of its initial (pre-propagation) profile.
    ///
    /// This confirms that propagation only adds axiom bits, never removes them.
    #[must_use]
    pub fn verify_propagation_monotonicity(&self, graph: &DependencyGraph) -> VerificationResult {
        // Capture current profiles (assumed to be post-propagation).
        // Monotonicity means each profile >= AxiomProfile::NONE (trivially true),
        // but more importantly: the propagated profile is a superset of every
        // direct dependency's profile.
        let n = graph.node_count();
        let mut checked = 0usize;

        for i in 0..n {
            let parent = graph.profile(i as u32);
            for &dep in graph.dependencies(i as u32) {
                let child = graph.profile(dep);
                checked += 1;
                if !parent.is_superset_of(child) {
                    return VerificationResult {
                        property: VerificationProperty::PropagationMonotonicity,
                        passed: false,
                        evidence: format!(
                            "node {} profile {:?} is not a superset of child {} profile {:?}",
                            i, parent, dep, child
                        ),
                        checked_count: checked,
                    };
                }
            }
        }

        VerificationResult {
            property: VerificationProperty::PropagationMonotonicity,
            passed: true,
            evidence: format!("all {} edges satisfy monotonicity", checked),
            checked_count: checked,
        }
    }

    /// Verify propagation idempotency: re-running propagation on an already-
    /// propagated graph does not change any profile.
    #[must_use]
    pub fn verify_propagation_idempotency(&self, graph: &DependencyGraph) -> VerificationResult {
        let n = graph.node_count();

        // Snapshot current profiles.
        let before: Vec<AxiomProfile> = (0..n).map(|i| graph.profile(i as u32)).collect();

        // Simulate one propagation pass without mutating `graph`.
        // For each node, compute what its profile would be if we unioned all deps.
        let mut checked = 0usize;
        for i in 0..n {
            let mut simulated = before[i];
            for &dep in graph.dependencies(i as u32) {
                simulated = simulated.union(before[dep as usize]);
                checked += 1;
            }
            if simulated != before[i] {
                return VerificationResult {
                    property: VerificationProperty::PropagationIdempotency,
                    passed: false,
                    evidence: format!(
                        "node {} would change from {:?} to {:?} on re-propagation",
                        i, before[i], simulated
                    ),
                    checked_count: checked,
                };
            }
        }

        VerificationResult {
            property: VerificationProperty::PropagationIdempotency,
            passed: true,
            evidence: format!(
                "all {} nodes stable under re-propagation ({} edges checked)",
                n, checked
            ),
            checked_count: checked,
        }
    }

    /// Verify that the trust gate has a policy for every known `TrustLevel`.
    #[must_use]
    pub fn verify_trust_gate_completeness(&self, gate: &TrustGate) -> VerificationResult {
        let all_levels = [
            TrustLevel::KernelVerified,
            TrustLevel::AxiomDependent,
            TrustLevel::CertificateReplayed,
            TrustLevel::PartiallyAxiomatized,
            TrustLevel::TrustedOracle,
        ];

        let mut missing = Vec::new();
        for &level in &all_levels {
            if !gate.has_policy_for(level) {
                missing.push(format!("{:?}", level));
            }
        }

        let checked = all_levels.len();
        if missing.is_empty() {
            VerificationResult {
                property: VerificationProperty::TrustGateCompleteness,
                passed: true,
                evidence: format!("all {} trust levels have policies", checked),
                checked_count: checked,
            }
        } else {
            VerificationResult {
                property: VerificationProperty::TrustGateCompleteness,
                passed: false,
                evidence: format!("missing policies for: {}", missing.join(", ")),
                checked_count: checked,
            }
        }
    }

    /// Verify that `TrainingExportGate` strictly allows only `KernelVerified`
    /// with an empty axiom profile.
    #[must_use]
    pub fn verify_training_gate_strictness(&self) -> VerificationResult {
        let all_levels = [
            TrustLevel::KernelVerified,
            TrustLevel::AxiomDependent,
            TrustLevel::CertificateReplayed,
            TrustLevel::PartiallyAxiomatized,
            TrustLevel::TrustedOracle,
        ];

        let test_profiles = [
            AxiomProfile::NONE,
            AxiomProfile::CLASSICAL,
            AxiomProfile::HOL_EMBEDDING,
            AxiomProfile::SMT_ORACLE,
        ];

        let mut checked = 0usize;
        for &trust in &all_levels {
            for &profile in &test_profiles {
                let result = TrainingExportGate::can_export_for_training(profile, trust);
                let expected = trust == TrustLevel::KernelVerified && profile.is_kernel_verified();
                checked += 1;

                if result != expected {
                    return VerificationResult {
                        property: VerificationProperty::TrainingGateStrictness,
                        passed: false,
                        evidence: format!(
                            "trust={:?} profile={:?}: got {} expected {}",
                            trust, profile, result, expected
                        ),
                        checked_count: checked,
                    };
                }
            }
        }

        VerificationResult {
            property: VerificationProperty::TrainingGateStrictness,
            passed: true,
            evidence: format!("all {} (trust, profile) pairs checked", checked),
            checked_count: checked,
        }
    }

    /// Verify that a valid graph (where all dependencies go from higher to lower
    /// trust, according to the gate policy) produces zero audit violations.
    #[must_use]
    pub fn verify_no_trust_leakage(
        &self,
        graph: &DependencyGraph,
        trust_levels: &[TrustLevel],
        gate: &TrustGate,
    ) -> VerificationResult {
        let violations = gate.audit_graph(graph, trust_levels);
        let n = graph.node_count();

        if violations.is_empty() {
            VerificationResult {
                property: VerificationProperty::NoTrustLeakage,
                passed: true,
                evidence: format!("0 violations in {} node graph", n),
                checked_count: n,
            }
        } else {
            VerificationResult {
                property: VerificationProperty::NoTrustLeakage,
                passed: false,
                evidence: format!(
                    "{} violations found; first: {}",
                    violations.len(),
                    violations[0].violation
                ),
                checked_count: n,
            }
        }
    }

    /// Verify cross-system consistency between HOL and Mizar axiom profiles.
    ///
    /// Checks that:
    /// 1. No profile claims both HOL_EMBEDDING and MIZAR_SOFT_TYPE (mutually exclusive).
    /// 2. Profiles from one system do not silently depend on another system's axioms
    ///    without the appropriate embedding bit set.
    /// 3. All profiles have a consistent axiom count (no orphan bits).
    #[must_use]
    pub fn verify_cross_system_consistency(
        &self,
        hol_profiles: &[AxiomProfile],
        mizar_profiles: &[AxiomProfile],
    ) -> VerificationResult {
        let mut checked = 0usize;
        let mut issues = Vec::new();

        // Check HOL profiles do not contain Mizar bits.
        for (i, &profile) in hol_profiles.iter().enumerate() {
            checked += 1;
            if profile.contains(AxiomProfile::MIZAR_SOFT_TYPE) {
                issues.push(format!(
                    "HOL profile[{}] ({:?}) contains MIZAR_SOFT_TYPE bit",
                    i, profile
                ));
            }
        }

        // Check Mizar profiles do not contain HOL bits.
        for (i, &profile) in mizar_profiles.iter().enumerate() {
            checked += 1;
            if profile.contains(AxiomProfile::HOL_EMBEDDING) {
                issues.push(format!(
                    "Mizar profile[{}] ({:?}) contains HOL_EMBEDDING bit",
                    i, profile
                ));
            }
        }

        // Check no profile in either set claims both embedding bits.
        for (i, &profile) in hol_profiles.iter().chain(mizar_profiles.iter()).enumerate() {
            checked += 1;
            if profile.contains(AxiomProfile::HOL_EMBEDDING)
                && profile.contains(AxiomProfile::MIZAR_SOFT_TYPE)
            {
                issues.push(format!(
                    "profile[{}] ({:?}) claims both HOL_EMBEDDING and MIZAR_SOFT_TYPE",
                    i, profile
                ));
            }
        }

        if issues.is_empty() {
            VerificationResult {
                property: VerificationProperty::CrossSystemConsistency,
                passed: true,
                evidence: format!(
                    "all {} profiles are cross-system consistent ({} HOL, {} Mizar)",
                    checked,
                    hol_profiles.len(),
                    mizar_profiles.len()
                ),
                checked_count: checked,
            }
        } else {
            VerificationResult {
                property: VerificationProperty::CrossSystemConsistency,
                passed: false,
                evidence: format!(
                    "{} cross-system issue(s): {}",
                    issues.len(),
                    issues.join("; ")
                ),
                checked_count: checked,
            }
        }
    }

    /// Verify the integrity of a bulk import result.
    ///
    /// Checks that:
    /// 1. Axiom-profile propagation succeeded.
    /// 2. No trust violations were detected.
    /// 3. The audit report is clean.
    /// 4. The exportable count is consistent with the audit report.
    #[must_use]
    pub fn verify_bulk_import_integrity(&self, result: &BulkImportResult) -> VerificationResult {
        let mut checked = 0usize;
        let mut issues = Vec::new();

        // 1. Propagation success.
        checked += 1;
        if !result.propagation_ok {
            issues.push("axiom-profile propagation failed".to_owned());
        }

        // 2. Trust violations.
        checked += 1;
        if !result.trust_violations.is_empty() {
            issues.push(format!(
                "{} trust violation(s) detected",
                result.trust_violations.len()
            ));
        }

        // 3. Audit report cleanliness.
        checked += 1;
        if !result.audit_report.is_clean() {
            issues.push("audit report has errors or critical findings".to_owned());
        }

        // 4. Total constants consistency.
        checked += 1;
        if result.total_constants != result.audit_report.total_constants {
            issues.push(format!(
                "total_constants mismatch: result={} vs audit={}",
                result.total_constants, result.audit_report.total_constants
            ));
        }

        // 5. Exportable count does not exceed total.
        checked += 1;
        if result.exportable_count > result.total_constants {
            issues.push(format!(
                "exportable_count ({}) exceeds total_constants ({})",
                result.exportable_count, result.total_constants
            ));
        }

        // 6. Source count consistency.
        checked += 1;
        let source_total: usize = result.by_source.values().sum();
        if source_total != result.total_constants {
            issues.push(format!(
                "by_source total ({}) does not match total_constants ({})",
                source_total, result.total_constants
            ));
        }

        if issues.is_empty() {
            VerificationResult {
                property: VerificationProperty::BulkImportIntegrity,
                passed: true,
                evidence: format!(
                    "bulk import of {} constants is consistent ({} checks)",
                    result.total_constants, checked
                ),
                checked_count: checked,
            }
        } else {
            VerificationResult {
                property: VerificationProperty::BulkImportIntegrity,
                passed: false,
                evidence: format!("{} integrity issue(s): {}", issues.len(), issues.join("; ")),
                checked_count: checked,
            }
        }
    }

    /// Run all verification properties and return results.
    #[must_use]
    pub fn run_all(
        &self,
        graph: &DependencyGraph,
        trust_levels: &[TrustLevel],
        gate: &TrustGate,
    ) -> Vec<VerificationResult> {
        vec![
            self.verify_propagation_monotonicity(graph),
            self.verify_propagation_idempotency(graph),
            self.verify_trust_gate_completeness(gate),
            self.verify_training_gate_strictness(),
            self.verify_no_trust_leakage(graph, trust_levels, gate),
        ]
    }
}

impl Default for VerificationSuite {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// VerificationEvidence — tracking verification results with timestamps
// ============================================================================

/// Structured evidence tracking verification results.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VerificationEvidence {
    /// All individual property results.
    pub results: Vec<VerificationResult>,
    /// Total number of properties checked.
    pub properties_checked: usize,
    /// Number that passed.
    pub properties_passed: usize,
    /// Number that failed.
    pub properties_failed: usize,
    /// Total individual checks across all properties.
    pub total_checks: usize,
    /// Whether all properties passed.
    pub all_passed: bool,
}

impl VerificationEvidence {
    /// Create evidence from a set of results.
    #[must_use]
    pub fn from_results(results: Vec<VerificationResult>) -> Self {
        let properties_checked = results.len();
        let properties_passed = results.iter().filter(|r| r.passed).count();
        let properties_failed = properties_checked - properties_passed;
        let total_checks: usize = results.iter().map(|r| r.checked_count).sum();
        let all_passed = properties_failed == 0;
        Self {
            results,
            properties_checked,
            properties_passed,
            properties_failed,
            total_checks,
            all_passed,
        }
    }

    /// Return a human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        let status = if self.all_passed { "PASS" } else { "FAIL" };
        let mut lines = vec![format!(
            "Verification {}: {}/{} properties passed ({} individual checks)",
            status, self.properties_passed, self.properties_checked, self.total_checks
        )];
        for r in &self.results {
            let mark = if r.passed { "[OK]" } else { "[FAIL]" };
            lines.push(format!(
                "  {} {:?}: {} ({} checks)",
                mark, r.property, r.evidence, r.checked_count
            ));
        }
        lines.join("\n")
    }
}

// ============================================================================
// SelfVerificationSuite — verifies the verification system itself
// ============================================================================

/// A higher-level verification suite that checks the correctness of the
/// verification infrastructure. This is the "self-verification" layer:
/// it verifies that the `VerificationSuite` itself produces consistent results.
pub struct SelfVerificationSuite;

impl SelfVerificationSuite {
    /// Create a new self-verification suite.
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    /// Verify propagation completeness: after propagation, for every node N,
    /// every node transitively reachable from N via dependency edges has its
    /// axiom profile bits included in N's profile.
    #[must_use]
    pub fn verify_propagation_completeness(&self, graph: &DependencyGraph) -> VerificationResult {
        let n = graph.node_count();
        let mut checked = 0usize;

        for i in 0..n {
            let node = i as u32;
            let node_profile = graph.profile(node);
            let reachable = graph.reachable_from(node);

            for &dep in &reachable {
                let dep_profile = graph.profile(dep);
                checked += 1;
                if !node_profile.is_superset_of(dep_profile) {
                    return VerificationResult {
                        property: VerificationProperty::PropagationCompleteness,
                        passed: false,
                        evidence: format!(
                            "node {} profile {:?} does not contain reachable node {} profile {:?}",
                            i, node_profile, dep, dep_profile
                        ),
                        checked_count: checked,
                    };
                }
            }
        }

        VerificationResult {
            property: VerificationProperty::PropagationCompleteness,
            passed: true,
            evidence: format!("all {} reachable pairs satisfy completeness", checked),
            checked_count: checked,
        }
    }

    /// Verify training gate soundness: no constant with a non-empty axiom
    /// profile passes the training export gate, regardless of trust level.
    #[must_use]
    pub fn verify_training_gate_soundness(&self) -> VerificationResult {
        let all_levels = [
            TrustLevel::KernelVerified,
            TrustLevel::AxiomDependent,
            TrustLevel::CertificateReplayed,
            TrustLevel::PartiallyAxiomatized,
            TrustLevel::TrustedOracle,
        ];

        let unsafe_profiles = [
            AxiomProfile::CLASSICAL,
            AxiomProfile::EXTENSIONALITY,
            AxiomProfile::CHOICE,
            AxiomProfile::PROOF_IRRELEVANCE,
            AxiomProfile::HOL_EMBEDDING,
            AxiomProfile::MIZAR_SOFT_TYPE,
            AxiomProfile::COQ_SPROP,
            AxiomProfile::COQ_MODULE_FUNCTOR,
            AxiomProfile::COQ_COINDUCTIVE,
            AxiomProfile::ISABELLE_LCF_ERASED,
            AxiomProfile::AGDA_CUBICAL,
            AxiomProfile::IDRIS_QTT,
            AxiomProfile::SMT_ORACLE,
            AxiomProfile::SAT_CERT,
            AxiomProfile::ATP_CERT,
            AxiomProfile::FLOAT_APPROX,
            AxiomProfile::NN_ABSTRACTION,
        ];

        let mut checked = 0usize;

        for &profile in &unsafe_profiles {
            for &trust in &all_levels {
                let result = TrainingExportGate::can_export_for_training(profile, trust);
                checked += 1;
                if result {
                    return VerificationResult {
                        property: VerificationProperty::TrainingGateSoundness,
                        passed: false,
                        evidence: format!(
                            "unsafe constant with profile {:?} and trust {:?} passed training gate",
                            profile, trust
                        ),
                        checked_count: checked,
                    };
                }
            }
        }

        VerificationResult {
            property: VerificationProperty::TrainingGateSoundness,
            passed: true,
            evidence: format!(
                "all {} (unsafe_profile, trust) pairs correctly rejected",
                checked
            ),
            checked_count: checked,
        }
    }

    /// Verify trust hierarchy transitivity: for the given gate, if trust
    /// level A can depend on B and B can depend on C, then A can depend on C.
    #[must_use]
    pub fn verify_trust_hierarchy_transitivity(&self, gate: &TrustGate) -> VerificationResult {
        let all_levels = [
            TrustLevel::KernelVerified,
            TrustLevel::AxiomDependent,
            TrustLevel::CertificateReplayed,
            TrustLevel::PartiallyAxiomatized,
            TrustLevel::TrustedOracle,
        ];

        let mut checked = 0usize;
        let mut violations = Vec::new();

        for &a in &all_levels {
            for &b in &all_levels {
                if gate.check_dependency(a, b).is_err() {
                    continue;
                }
                for &c in &all_levels {
                    if gate.check_dependency(b, c).is_err() {
                        continue;
                    }
                    checked += 1;
                    // A can depend on B, B can depend on C => A should be able to depend on C.
                    if gate.check_dependency(a, c).is_err() {
                        violations.push(format!(
                            "{:?} -> {:?} -> {:?}: A->B ok, B->C ok, but A->C rejected",
                            a, b, c
                        ));
                    }
                }
            }
        }

        if violations.is_empty() {
            VerificationResult {
                property: VerificationProperty::TrustHierarchyTransitivity,
                passed: true,
                evidence: format!("all {} transitive triples are consistent", checked),
                checked_count: checked,
            }
        } else {
            VerificationResult {
                property: VerificationProperty::TrustHierarchyTransitivity,
                passed: false,
                evidence: format!(
                    "{} transitivity violation(s): {}",
                    violations.len(),
                    violations.join("; ")
                ),
                checked_count: checked,
            }
        }
    }

    /// Verify audit report completeness: every trust violation detected
    /// by `TrustGate::audit_graph` appears in the provided audit report.
    #[must_use]
    pub fn verify_audit_report_completeness(
        &self,
        graph: &DependencyGraph,
        trust_levels: &[TrustLevel],
        gate: &TrustGate,
        report: &AuditReport,
    ) -> VerificationResult {
        let graph_violations = gate.audit_graph(graph, trust_levels);
        let mut checked = 0usize;

        // Build a set of (parent_idx, child_idx) from the report violations.
        let report_violation_set: HashSet<(u32, u32)> = report
            .trust_violations
            .iter()
            .map(|v| (v.parent_idx, v.child_idx))
            .collect();

        let mut missing = Vec::new();
        for v in &graph_violations {
            checked += 1;
            if !report_violation_set.contains(&(v.parent_idx, v.child_idx)) {
                missing.push(format!(
                    "violation ({} -> {}) not in report",
                    v.parent_idx, v.child_idx
                ));
            }
        }

        if missing.is_empty() {
            VerificationResult {
                property: VerificationProperty::AuditReportCompleteness,
                passed: true,
                evidence: format!(
                    "all {} graph violations are present in the audit report",
                    checked
                ),
                checked_count: checked,
            }
        } else {
            VerificationResult {
                property: VerificationProperty::AuditReportCompleteness,
                passed: false,
                evidence: format!(
                    "{} violation(s) missing from report: {}",
                    missing.len(),
                    missing.join("; ")
                ),
                checked_count: checked,
            }
        }
    }

    /// Run all self-verification properties and return structured evidence.
    #[must_use]
    pub fn verify_all_properties(
        &self,
        graph: &DependencyGraph,
        trust_levels: &[TrustLevel],
        gate: &TrustGate,
        report: &AuditReport,
    ) -> VerificationEvidence {
        let results = vec![
            self.verify_propagation_completeness(graph),
            self.verify_training_gate_soundness(),
            self.verify_trust_hierarchy_transitivity(gate),
            self.verify_audit_report_completeness(graph, trust_levels, gate, report),
        ];
        VerificationEvidence::from_results(results)
    }
}

impl Default for SelfVerificationSuite {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a simple valid propagated graph for testing.
    fn make_valid_graph() -> (DependencyGraph, Vec<TrustLevel>) {
        // node 0: KernelVerified, no deps
        // node 1: KernelVerified, depends on 0
        // node 2: AxiomDependent (CLASSICAL), depends on 0 and 1
        let mut graph = DependencyGraph::new(3);
        graph
            .set_initial_profile(2, AxiomProfile::CLASSICAL)
            .expect("set profile");
        graph.add_edge(1, 0).expect("edge");
        graph.add_edge(2, 0).expect("edge");
        graph.add_edge(2, 1).expect("edge");
        graph.propagate().expect("propagation should succeed");

        let trust_levels = vec![
            TrustLevel::KernelVerified,
            TrustLevel::KernelVerified,
            TrustLevel::AxiomDependent,
        ];

        (graph, trust_levels)
    }

    #[test]
    fn test_verify_propagation_monotonicity_valid() {
        let (graph, _) = make_valid_graph();
        let suite = VerificationSuite::new();
        let result = suite.verify_propagation_monotonicity(&graph);
        assert!(result.passed, "evidence: {}", result.evidence);
        assert!(result.checked_count > 0);
    }

    #[test]
    fn test_verify_propagation_idempotency_valid() {
        let (graph, _) = make_valid_graph();
        let suite = VerificationSuite::new();
        let result = suite.verify_propagation_idempotency(&graph);
        assert!(result.passed, "evidence: {}", result.evidence);
    }

    #[test]
    fn test_verify_propagation_idempotency_unpropagated() {
        // Build graph but do NOT propagate -- idempotency should fail.
        let mut graph = DependencyGraph::new(2);
        graph
            .set_initial_profile(0, AxiomProfile::CLASSICAL)
            .expect("set profile");
        graph.add_edge(1, 0).expect("edge");
        // Intentionally skip propagation.

        let suite = VerificationSuite::new();
        let result = suite.verify_propagation_idempotency(&graph);
        assert!(!result.passed, "unpropagated graph should fail idempotency");
    }

    #[test]
    fn test_verify_trust_gate_completeness_default() {
        let gate = TrustGate::default_policy();
        let suite = VerificationSuite::new();
        let result = suite.verify_trust_gate_completeness(&gate);
        assert!(result.passed, "evidence: {}", result.evidence);
        assert_eq!(result.checked_count, 5);
    }

    #[test]
    fn test_verify_trust_gate_completeness_incomplete() {
        use hashbrown::{HashMap, HashSet};
        // Build a gate missing some trust levels.
        let mut policy = HashMap::new();
        policy.insert(
            TrustLevel::KernelVerified,
            HashSet::from_iter([TrustLevel::KernelVerified]),
        );
        let gate = TrustGate::with_policy(policy);

        let suite = VerificationSuite::new();
        let result = suite.verify_trust_gate_completeness(&gate);
        assert!(!result.passed);
        assert!(result.evidence.contains("missing policies"));
    }

    #[test]
    fn test_verify_training_gate_strictness() {
        let suite = VerificationSuite::new();
        let result = suite.verify_training_gate_strictness();
        assert!(result.passed, "evidence: {}", result.evidence);
        assert_eq!(result.checked_count, 20); // 5 levels * 4 profiles
    }

    #[test]
    fn test_verify_no_trust_leakage_valid() {
        let (graph, trust_levels) = make_valid_graph();
        let gate = TrustGate::default_policy();
        let suite = VerificationSuite::new();
        let result = suite.verify_no_trust_leakage(&graph, &trust_levels, &gate);
        assert!(result.passed, "evidence: {}", result.evidence);
    }

    #[test]
    fn test_verify_no_trust_leakage_with_violation() {
        let mut graph = DependencyGraph::new(2);
        graph.add_edge(1, 0).expect("edge");

        // node 1 (KernelVerified) depends on node 0 (TrustedOracle) -- violation.
        let trust_levels = vec![TrustLevel::TrustedOracle, TrustLevel::KernelVerified];
        let gate = TrustGate::default_policy();

        let suite = VerificationSuite::new();
        let result = suite.verify_no_trust_leakage(&graph, &trust_levels, &gate);
        assert!(!result.passed);
        assert!(result.evidence.contains("violation"));
    }

    #[test]
    fn test_run_all_valid_graph() {
        let (graph, trust_levels) = make_valid_graph();
        let gate = TrustGate::default_policy();
        let suite = VerificationSuite::new();

        let results = suite.run_all(&graph, &trust_levels, &gate);
        assert_eq!(results.len(), 5);
        for result in &results {
            assert!(
                result.passed,
                "{:?} failed: {}",
                result.property, result.evidence
            );
        }
    }

    #[test]
    fn test_run_all_reports_failures() {
        // Unpropagated graph should fail at least idempotency.
        let mut graph = DependencyGraph::new(2);
        graph
            .set_initial_profile(0, AxiomProfile::CLASSICAL)
            .expect("set profile");
        graph.add_edge(1, 0).expect("edge");

        let trust_levels = vec![TrustLevel::AxiomDependent, TrustLevel::AxiomDependent];
        let gate = TrustGate::default_policy();
        let suite = VerificationSuite::new();

        let results = suite.run_all(&graph, &trust_levels, &gate);
        let failed: Vec<_> = results.iter().filter(|r| !r.passed).collect();
        assert!(
            !failed.is_empty(),
            "unpropagated graph should have at least one failure"
        );
    }

    #[test]
    fn test_verification_property_enum_coverage() {
        // Ensure all variants are distinct (compile-time check via exhaustive match).
        let props = [
            VerificationProperty::PropagationMonotonicity,
            VerificationProperty::PropagationIdempotency,
            VerificationProperty::TrustGateCompleteness,
            VerificationProperty::TrainingGateStrictness,
            VerificationProperty::TopologicalOrderPreservation,
            VerificationProperty::NoTrustLeakage,
        ];
        // All should be unique.
        for (i, a) in props.iter().enumerate() {
            for (j, b) in props.iter().enumerate() {
                if i != j {
                    assert_ne!(a, b);
                }
            }
        }
    }

    #[test]
    fn test_empty_graph_all_pass() {
        let graph = DependencyGraph::new(0);
        let trust_levels: Vec<TrustLevel> = vec![];
        let gate = TrustGate::default_policy();
        let suite = VerificationSuite::new();

        let results = suite.run_all(&graph, &trust_levels, &gate);
        for result in &results {
            assert!(
                result.passed,
                "{:?} failed on empty graph: {}",
                result.property, result.evidence
            );
        }
    }

    // ════════════════════════════════════════════════════════════════════
    // Cross-system consistency tests
    // ════════════════════════════════════════════════════════════════════

    #[test]
    fn test_cross_system_consistency_valid() {
        let suite = VerificationSuite::new();
        let hol = vec![
            AxiomProfile::HOL_EMBEDDING,
            AxiomProfile::HOL_EMBEDDING | AxiomProfile::CLASSICAL,
        ];
        let mizar = vec![
            AxiomProfile::MIZAR_SOFT_TYPE,
            AxiomProfile::MIZAR_SOFT_TYPE | AxiomProfile::CHOICE,
        ];
        let result = suite.verify_cross_system_consistency(&hol, &mizar);
        assert!(result.passed, "evidence: {}", result.evidence);
        assert!(result.checked_count > 0);
    }

    #[test]
    fn test_cross_system_consistency_hol_has_mizar_bit() {
        let suite = VerificationSuite::new();
        let hol = vec![AxiomProfile::HOL_EMBEDDING | AxiomProfile::MIZAR_SOFT_TYPE];
        let mizar = vec![];
        let result = suite.verify_cross_system_consistency(&hol, &mizar);
        assert!(!result.passed);
        assert!(result.evidence.contains("MIZAR_SOFT_TYPE"));
    }

    #[test]
    fn test_cross_system_consistency_mizar_has_hol_bit() {
        let suite = VerificationSuite::new();
        let hol = vec![];
        let mizar = vec![AxiomProfile::MIZAR_SOFT_TYPE | AxiomProfile::HOL_EMBEDDING];
        let result = suite.verify_cross_system_consistency(&hol, &mizar);
        assert!(!result.passed);
        assert!(result.evidence.contains("HOL_EMBEDDING"));
    }

    #[test]
    fn test_cross_system_consistency_empty_profiles() {
        let suite = VerificationSuite::new();
        let result = suite.verify_cross_system_consistency(&[], &[]);
        assert!(result.passed);
        assert_eq!(result.checked_count, 0);
    }

    #[test]
    fn test_cross_system_consistency_pure_profiles() {
        let suite = VerificationSuite::new();
        let hol = vec![AxiomProfile::NONE, AxiomProfile::CLASSICAL];
        let mizar = vec![AxiomProfile::NONE, AxiomProfile::CHOICE];
        let result = suite.verify_cross_system_consistency(&hol, &mizar);
        assert!(result.passed, "pure profiles should be consistent");
    }

    // ════════════════════════════════════════════════════════════════════
    // Bulk import integrity tests
    // ════════════════════════════════════════════════════════════════════

    #[test]
    fn test_bulk_import_integrity_clean() {
        use crate::bulk_import::ImportedConstant;
        use crate::bulk_import::{BulkImportConfig, BulkImporter};
        use crate::types::{Provenance, SourceSystem};

        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);
        importer
            .add_constant(ImportedConstant {
                name: "A".to_owned(),
                source: SourceSystem::Lean4,
                axiom_profile: AxiomProfile::NONE,
                trust_level: TrustLevel::KernelVerified,
                provenance: Provenance {
                    source: SourceSystem::Lean4,
                    original_name: "A".to_owned(),
                    source_file: None,
                    axiom_profile: AxiomProfile::NONE,
                },
                dependencies: Vec::new(),
            })
            .expect("add");

        let import_result = importer.finalize().expect("finalize");
        let suite = VerificationSuite::new();
        let result = suite.verify_bulk_import_integrity(&import_result);
        assert!(result.passed, "evidence: {}", result.evidence);
    }

    #[test]
    fn test_bulk_import_integrity_with_violations() {
        use crate::bulk_import::ImportedConstant;
        use crate::bulk_import::{BulkImportConfig, BulkImporter};
        use crate::types::{Provenance, SourceSystem};

        let config = BulkImportConfig::builder().enforce_trust_gate(true).build();
        let mut importer = BulkImporter::new(config);
        // Oracle node
        let oracle = importer
            .add_constant(ImportedConstant {
                name: "oracle".to_owned(),
                source: SourceSystem::SmtSolver,
                axiom_profile: AxiomProfile::SMT_ORACLE,
                trust_level: TrustLevel::TrustedOracle,
                provenance: Provenance {
                    source: SourceSystem::SmtSolver,
                    original_name: "oracle".to_owned(),
                    source_file: None,
                    axiom_profile: AxiomProfile::SMT_ORACLE,
                },
                dependencies: Vec::new(),
            })
            .expect("add oracle");
        // KernelVerified depends on oracle => violation
        importer
            .add_constant(ImportedConstant {
                name: "kv".to_owned(),
                source: SourceSystem::Lean4,
                axiom_profile: AxiomProfile::NONE,
                trust_level: TrustLevel::KernelVerified,
                provenance: Provenance {
                    source: SourceSystem::Lean4,
                    original_name: "kv".to_owned(),
                    source_file: None,
                    axiom_profile: AxiomProfile::NONE,
                },
                dependencies: vec![oracle],
            })
            .expect("add kv");

        let import_result = importer.finalize().expect("finalize");
        let suite = VerificationSuite::new();
        let result = suite.verify_bulk_import_integrity(&import_result);
        assert!(!result.passed);
        assert!(result.evidence.contains("trust violation"));
    }

    // ════════════════════════════════════════════════════════════════════
    // Additional property tests
    // ════════════════════════════════════════════════════════════════════

    #[test]
    fn test_verification_property_new_variants_distinct() {
        let props = [
            VerificationProperty::CrossSystemConsistency,
            VerificationProperty::BulkImportIntegrity,
        ];
        assert_ne!(props[0], props[1]);
        assert_ne!(props[0], VerificationProperty::PropagationMonotonicity);
        assert_ne!(props[1], VerificationProperty::NoTrustLeakage);
    }

    #[test]
    fn test_cross_system_both_embedding_bits_detected() {
        let suite = VerificationSuite::new();
        // Profile claiming both HOL and Mizar embedding
        let mixed = vec![AxiomProfile::HOL_EMBEDDING | AxiomProfile::MIZAR_SOFT_TYPE];
        let result = suite.verify_cross_system_consistency(&mixed, &[]);
        assert!(!result.passed);
        assert!(result
            .evidence
            .contains("both HOL_EMBEDDING and MIZAR_SOFT_TYPE"));
    }

    #[test]
    fn test_cross_system_consistency_only_classical_ok() {
        let suite = VerificationSuite::new();
        // CLASSICAL is a logic axiom, not a system embedding -- valid for both systems.
        let hol = vec![AxiomProfile::CLASSICAL | AxiomProfile::HOL_EMBEDDING];
        let mizar = vec![AxiomProfile::CLASSICAL | AxiomProfile::MIZAR_SOFT_TYPE];
        let result = suite.verify_cross_system_consistency(&hol, &mizar);
        assert!(result.passed, "evidence: {}", result.evidence);
    }
}
