// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake-project trust audit aggregation.

use hashbrown::{HashMap, HashSet};

use clean_kernel::expr::ZFCSetExpr;
use clean_kernel::{
    is_foundational_axiom, is_trust_marker, ConstantInfo, ConstantKind, Environment, Expr,
    ExprKind, Name, ProofQuality,
};
use std::path::{Path, PathBuf};

use super::audit_report::{
    AuditFinding, AuditFindingCategory, AuditReport, AuditReportBuilder, AuditSeverity,
    KernelAuditKernel,
};
use super::axiom_propagation::DependencyGraph;
use super::graph_gate::TrustGate;
use serde::Serialize;

use crate::attempt_log::{
    put_artifact, record_authority_gate_attempt, AttemptStatus, AuthorityGateAttempt,
    EnvFingerprint, ProofAttempt,
};
use crate::authority_scope::{authority_gate_goal_hash_from_scope, project_source_tree_digest};
use crate::error::MathverseResult;
use crate::types::{AxiomProfile, TrustLevel};

pub const PROJECT_AUDIT_AUTHORITY_GATE: &str = "trust_audit";
pub const PROJECT_AUDIT_GOAL_SHAPE: &str = "clean audit cake project trust boundary v2";
pub const PROJECT_AUDIT_ARTIFACT_KIND: &str = "authority-gate/trust-audit-report";
const PROJECT_AUDIT_COMMAND_EVIDENCE_SCHEMA: &str = "clean-project-audit-command-evidence-v1";
const PROJECT_AUDIT_COMMAND_EVIDENCE_KIND: &str = "authority-gate/command-evidence";
const PROJECT_TRUST_CACHE_MAX_RECURSION_DEPTH: usize = 2048;

/// Minimal Lake workspace view needed by the trust audit.
///
/// This mirrors the `clean_cake::Workspace` methods used by the audit without
/// forcing `clean-mathverse -> cake`, which currently forms a Cargo cycle
/// through `cake -> clean-elab -> clean-mathverse`.
pub trait ProjectAuditWorkspace {
    /// Get all module names in the project.
    fn all_modules(&self) -> Vec<String>;

    /// Find the source file for a module.
    fn find_module(&self, module_name: &str) -> Option<PathBuf>;
}

/// Audit a Lake workspace against an already-loaded clean kernel environment.
///
/// The current kernel API exposes whole-environment soundness plus per-
/// declaration proof quality and axiom dependencies. This function scopes that
/// data to declarations whose names fall under one of the Lake module prefixes.
#[must_use]
pub fn audit_lake_project<W: ProjectAuditWorkspace + ?Sized>(
    workspace: &W,
    env: &Environment,
) -> AuditReport {
    let mut builder = AuditReportBuilder::new();
    let mut modules = workspace.all_modules();
    modules.sort();

    add_project_scope_findings(&mut builder, workspace, &modules);
    let constants = project_constants(env, &modules);
    let mut trust_cache = ProjectTrustCache::new(env);
    add_soundness_summary(&mut builder, &mut trust_cache);

    let mut index_by_name = HashMap::new();
    for (idx, info) in constants.iter().enumerate() {
        index_by_name.insert(info.name.clone(), idx as u32);
    }

    let mut graph = DependencyGraph::new(constants.len());
    let mut trust_levels = Vec::with_capacity(constants.len());

    for (idx, info) in constants.iter().enumerate() {
        let summary = info.trust_summary();
        let recursive_deps = trust_cache.recursive_trust_deps(info);
        let trust_level = trust_level_for(&mut trust_cache, info, summary, &recursive_deps);
        let profile = axiom_profile_for(&mut trust_cache, info, summary, &recursive_deps);
        trust_levels.push(trust_level);
        builder.add_constant(trust_level, "CleanKernel", profile);
        add_declaration_findings(
            &mut builder,
            workspace,
            &modules,
            &mut trust_cache,
            info,
            idx as u32,
            &recursive_deps,
        );
    }

    for (idx, info) in constants.iter().enumerate() {
        let mut deps: Vec<_> = trust_cache.axiom_deps(info).into_iter().collect();
        deps.sort_by_key(|name| name.to_string());
        for dep in deps {
            if let Some(dep_idx) = index_by_name.get(&dep) {
                let _ = graph.add_edge(idx as u32, *dep_idx);
            }
        }
    }

    let gate = TrustGate::default_policy();
    for violation in gate.audit_graph(&graph, &trust_levels) {
        builder.add_violation(violation);
    }

    builder.build()
}

/// Authority-gate projection for a project trust audit.
///
/// The fields are intentionally shaped to fit [`crate::attempt_log::AuthorityGateAttempt`]
/// without making this helper append to the attempt log.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectAuditAuthorityGateStatus {
    /// Final authority-gate status.
    pub status: AttemptStatus,
    /// Stable failure classification for rejected audits.
    pub failure_mode: Option<String>,
    /// Conservative trust level assigned by the gate.
    pub trust_level: Option<TrustLevel>,
}

impl ProjectAuditAuthorityGateStatus {
    /// Returns `true` when the gate status is accepted.
    #[must_use]
    pub fn is_accepted(&self) -> bool {
        matches!(self.status, AttemptStatus::Accepted)
    }
}

/// Summarize whether a project audit is acceptable as an authority gate.
///
/// This is deliberately stricter than [`AuditReport::is_clean`]: info-only
/// findings are acceptable, but warnings are treated as trust debt. That makes
/// the gate suitable for a strict no-new-debt policy around axioms, opaque
/// declarations, external solvers, unsafe declarations, and critical findings.
#[must_use]
pub fn project_audit_authority_gate_status(
    report: &AuditReport,
) -> ProjectAuditAuthorityGateStatus {
    if let Some(reason) = report.trust_violations.first().map(|violation| {
        format!(
            "project trust audit rejected: {} trust violation(s); first={violation:?}",
            report.trust_violations.len()
        )
    }) {
        return rejected(reason, "trust_violation", TrustLevel::TrustedOracle);
    }

    if let Some(finding) = first_debt_finding(report) {
        let failure_mode = finding_failure_mode(finding);
        let trust_level = gate_trust_level_for_finding(finding, failure_mode);
        return rejected(
            format!(
                "project trust audit rejected: {:?} finding {}: {}",
                finding.severity, finding.category, finding.message
            ),
            failure_mode,
            trust_level,
        );
    }

    if report.total_constants == 0 {
        return rejected(
            "project trust audit rejected: no project constants were reconstructed".to_owned(),
            "empty_project_audit",
            TrustLevel::TrustedOracle,
        );
    }

    ProjectAuditAuthorityGateStatus {
        status: AttemptStatus::Accepted,
        failure_mode: None,
        trust_level: Some(TrustLevel::KernelVerified),
    }
}

/// Build a fail-closed authority-gate status for incomplete environment reconstruction.
#[must_use]
pub fn project_audit_environment_reconstruction_rejected_status(
    reason: impl Into<String>,
) -> ProjectAuditAuthorityGateStatus {
    rejected(
        reason.into(),
        "environment_reconstruction_incomplete",
        TrustLevel::TrustedOracle,
    )
}

/// Record a project audit as an append-only `trust_audit` authority-gate attempt.
pub fn record_project_audit_authority_gate_attempt(
    root: impl AsRef<Path>,
    report: &AuditReport,
    gate_status: &ProjectAuditAuthorityGateStatus,
    wall_time_ms: u64,
) -> MathverseResult<ProofAttempt> {
    let root = root.as_ref();
    let env = EnvFingerprint::capture(root)?;
    let source_digest = project_source_tree_digest(root)?;
    let goal_hash = authority_gate_goal_hash_from_scope(
        PROJECT_AUDIT_AUTHORITY_GATE,
        PROJECT_AUDIT_GOAL_SHAPE,
        &source_digest,
    );
    let report_json = report.to_json();
    let report_bytes = report_json.as_bytes();
    let report_hash = blake3_hex(report_bytes);
    let report_artifact = put_artifact(
        root,
        report_bytes,
        Some(PROJECT_AUDIT_ARTIFACT_KIND),
        Some("project-audit-report.json"),
    )?;

    let mut attempt = AuthorityGateAttempt::new(
        PROJECT_AUDIT_AUTHORITY_GATE,
        goal_hash,
        gate_status.status.clone(),
        report_hash.clone(),
        env,
    );
    attempt.wall_time_ms = wall_time_ms;
    attempt.solver_artifact = Some(report_artifact);
    attempt.failure_mode = gate_status.failure_mode.clone();
    attempt.trust_level = gate_status.trust_level;
    if gate_status.is_accepted() {
        let source_root = root.to_string_lossy();
        let command_evidence = ProjectAuditCommandEvidence {
            schema_version: PROJECT_AUDIT_COMMAND_EVIDENCE_SCHEMA,
            gate: PROJECT_AUDIT_AUTHORITY_GATE,
            gate_scope: PROJECT_AUDIT_GOAL_SHAPE,
            report_hash: &report_hash,
            source_root: &source_root,
            source_digest: &source_digest,
            status: "accepted",
            trust_level: gate_status.trust_level,
        };
        let command_evidence_json = serde_json::to_vec_pretty(&command_evidence)?;
        attempt.command_evidence = Some(put_artifact(
            root,
            &command_evidence_json,
            Some(PROJECT_AUDIT_COMMAND_EVIDENCE_KIND),
            Some("project-audit-command-evidence.json"),
        )?);
    }

    record_authority_gate_attempt(root, attempt)
}

#[derive(Serialize)]
struct ProjectAuditCommandEvidence<'a> {
    schema_version: &'static str,
    gate: &'static str,
    gate_scope: &'static str,
    report_hash: &'a str,
    source_root: &'a str,
    source_digest: &'a str,
    status: &'static str,
    trust_level: Option<TrustLevel>,
}

fn first_debt_finding(report: &AuditReport) -> Option<&AuditFinding> {
    report
        .findings
        .iter()
        .filter(|finding| finding.severity >= AuditSeverity::Warning)
        .max_by_key(|finding| (finding.severity, finding_debt_priority(finding)))
}

fn finding_debt_priority(finding: &AuditFinding) -> u8 {
    match finding_failure_mode(finding) {
        "explicit_sorry" | "synthetic_sorry" | "external_solver_trust" => 8,
        "transitive_trust_marker_dependency" => 7,
        "transitive_unsafe_dependency" => 6,
        "transitive_opaque_dependency" => 5,
        "transitive_axiom_dependency" => 4,
        "axiom_declaration" => 3,
        "unsafe_declaration" | "opaque_constant" => 2,
        _ => 1,
    }
}

fn finding_failure_mode(finding: &AuditFinding) -> &'static str {
    if finding.message.contains("Explicit sorry in declaration") {
        return "explicit_sorry";
    }
    if finding.message.contains("Synthetic sorry in declaration") {
        return "synthetic_sorry";
    }
    if finding.severity == AuditSeverity::Critical {
        return "critical_finding";
    }
    match finding.structured_category() {
        AuditFindingCategory::AxiomDeclaration => "axiom_declaration",
        AuditFindingCategory::OpaqueConstant => "opaque_constant",
        AuditFindingCategory::UnsafeDeclaration => "unsafe_declaration",
        AuditFindingCategory::ExternalSolver { .. } => "external_solver_trust",
        AuditFindingCategory::KernelTrust { .. }
            if finding.message.contains("Transitive unsafe dependency") =>
        {
            "transitive_unsafe_dependency"
        }
        AuditFindingCategory::KernelTrust { .. }
            if finding.message.contains("Transitive opaque dependency") =>
        {
            "transitive_opaque_dependency"
        }
        AuditFindingCategory::KernelTrust { .. }
            if finding.message.contains("Transitive trust dependencies")
                && finding.message.contains("trust markers [") =>
        {
            "transitive_trust_marker_dependency"
        }
        AuditFindingCategory::KernelTrust { .. }
            if finding.message.contains("Transitive trust dependencies") =>
        {
            "transitive_axiom_dependency"
        }
        AuditFindingCategory::KernelTrust { .. } => "kernel_trust_debt",
        AuditFindingCategory::CertificateProvenance { .. } => "certificate_provenance",
        AuditFindingCategory::GeneratedCode { .. } => "generated_code_debt",
        AuditFindingCategory::Other { .. } => "audit_debt",
    }
}

fn gate_trust_level_for_finding(finding: &AuditFinding, failure_mode: &str) -> TrustLevel {
    match failure_mode {
        "explicit_sorry"
        | "synthetic_sorry"
        | "external_solver_trust"
        | "transitive_trust_marker_dependency"
        | "transitive_unsafe_dependency"
        | "unsafe_declaration" => TrustLevel::TrustedOracle,
        _ if finding.severity >= AuditSeverity::Error => TrustLevel::TrustedOracle,
        _ => TrustLevel::AxiomDependent,
    }
}

fn rejected(
    reason: String,
    failure_mode: impl Into<String>,
    trust_level: TrustLevel,
) -> ProjectAuditAuthorityGateStatus {
    ProjectAuditAuthorityGateStatus {
        status: AttemptStatus::Rejected { reason },
        failure_mode: Some(failure_mode.into()),
        trust_level: Some(trust_level),
    }
}

fn blake3_hex(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

fn add_project_scope_findings(
    builder: &mut AuditReportBuilder,
    workspace: &(impl ProjectAuditWorkspace + ?Sized),
    modules: &[String],
) {
    if modules.is_empty() {
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Info,
            AuditFindingCategory::KernelTrust {
                kernel: KernelAuditKernel::Lean,
            },
            "Lake module inventory is empty; no project-scoped declarations were audited",
            vec![],
            None,
        ));
        return;
    }

    for module in modules {
        let source = workspace
            .find_module(module)
            .map(|path| path.display().to_string())
            .unwrap_or_else(|| "<unknown>".to_owned());
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Info,
            AuditFindingCategory::KernelTrust {
                kernel: KernelAuditKernel::Lean,
            },
            format!("Lake module discovered: {module} (source={source})"),
            vec![],
            None,
        ));
    }
}

fn add_soundness_summary(
    builder: &mut AuditReportBuilder,
    trust_cache: &mut ProjectTrustCache<'_>,
) {
    let report = trust_cache.soundness_report();
    builder.add_finding(AuditFinding::structured(
        AuditSeverity::Info,
        AuditFindingCategory::KernelTrust {
            kernel: KernelAuditKernel::Clean,
        },
        format!(
            "clean soundness report: total={}, theorems={}, constructive={}, \
             axiom_dependent={}, axioms={}, opaques={}, unchecked={}, domain_axioms={}",
            report.total_declarations,
            report.theorems,
            report.constructive_theorems,
            report.axiom_dependent_theorems,
            report.axioms,
            report.opaques,
            report.unchecked_declarations,
            report.total_domain_axioms
        ),
        vec![],
        None,
    ));
}

fn project_constants<'env>(env: &'env Environment, modules: &[String]) -> Vec<&'env ConstantInfo> {
    let mut constants: Vec<_> = env
        .constants()
        .filter(|info| constant_in_project(&info.name.to_string(), modules))
        .collect();
    constants.sort_by_key(|info| info.name.to_string());
    constants
}

fn constant_in_project(name: &str, modules: &[String]) -> bool {
    modules
        .iter()
        .any(|module| name == module || name.starts_with(&format!("{module}.")))
}

#[derive(Clone, Debug, Default)]
struct ProjectSoundnessSummary {
    total_declarations: usize,
    theorems: usize,
    axioms: usize,
    opaques: usize,
    constructive_theorems: usize,
    axiom_dependent_theorems: usize,
    unchecked_declarations: usize,
    total_domain_axioms: usize,
}

#[derive(Clone, Debug, Default)]
struct RecursiveTrustDepSets {
    unsafe_deps: HashSet<Name>,
    opaque_deps: HashSet<Name>,
}

impl RecursiveTrustDepSets {
    fn extend(&mut self, other: Self) {
        self.unsafe_deps.extend(other.unsafe_deps);
        self.opaque_deps.extend(other.opaque_deps);
    }

    fn into_sorted(self) -> RecursiveTrustDeps {
        RecursiveTrustDeps {
            unsafe_deps: sorted_names(self.unsafe_deps),
            opaque_deps: sorted_names(self.opaque_deps),
        }
    }
}

impl From<&RecursiveTrustDeps> for RecursiveTrustDepSets {
    fn from(deps: &RecursiveTrustDeps) -> Self {
        Self {
            unsafe_deps: deps.unsafe_deps.iter().cloned().collect(),
            opaque_deps: deps.opaque_deps.iter().cloned().collect(),
        }
    }
}

struct ProjectTrustCache<'env> {
    env: &'env Environment,
    constants_by_name: HashMap<Name, &'env ConstantInfo>,
    direct_refs_by_name: HashMap<Name, Vec<Name>>,
    axiom_refs_by_name: HashMap<Name, Vec<Name>>,
    axiom_deps_by_name: HashMap<Name, HashSet<Name>>,
    proof_quality_by_name: HashMap<Name, ProofQuality>,
    recursive_trust_deps_by_name: HashMap<Name, RecursiveTrustDeps>,
}

impl<'env> ProjectTrustCache<'env> {
    fn new(env: &'env Environment) -> Self {
        Self {
            env,
            constants_by_name: env
                .constants()
                .map(|info| (info.name.clone(), info))
                .collect(),
            direct_refs_by_name: HashMap::new(),
            axiom_refs_by_name: HashMap::new(),
            axiom_deps_by_name: HashMap::new(),
            proof_quality_by_name: HashMap::new(),
            recursive_trust_deps_by_name: HashMap::new(),
        }
    }

    fn is_unsafe(&self, name: &Name) -> bool {
        self.env.is_unsafe(name)
    }

    fn soundness_report(&mut self) -> ProjectSoundnessSummary {
        let mut report = ProjectSoundnessSummary::default();
        let mut all_domain_axioms = HashSet::new();
        let constants: Vec<_> = self.constants_by_name.values().copied().collect();

        report.total_declarations = constants.len();
        for info in constants {
            match info.kind {
                ConstantKind::Theorem => {
                    report.theorems += 1;
                    match self.proof_quality(info) {
                        ProofQuality::Constructive => {
                            report.constructive_theorems += 1;
                        }
                        ProofQuality::AxiomDependent { axioms, .. } => {
                            report.axiom_dependent_theorems += 1;
                            all_domain_axioms.extend(axioms);
                        }
                        ProofQuality::Unchecked => {
                            report.unchecked_declarations += 1;
                        }
                        ProofQuality::NotATheorem => {}
                        _ => {}
                    }
                }
                ConstantKind::Axiom => {
                    report.axioms += 1;
                    if !is_foundational_axiom(&info.name) {
                        all_domain_axioms.insert(info.name.clone());
                    }
                }
                ConstantKind::Definition => {}
                ConstantKind::Opaque => {
                    report.opaques += 1;
                }
            }
        }

        report.total_domain_axioms = all_domain_axioms.len();
        report
    }

    fn proof_quality(&mut self, info: &ConstantInfo) -> ProofQuality {
        if let Some(quality) = self.proof_quality_by_name.get(&info.name) {
            return quality.clone();
        }

        let quality = if info.kind != ConstantKind::Theorem {
            ProofQuality::NotATheorem
        } else if info.value.is_none() {
            ProofQuality::Unchecked
        } else {
            let deps = self.axiom_deps(info);
            if deps.is_empty() {
                ProofQuality::Constructive
            } else {
                let mut axioms: Vec<_> = deps.into_iter().collect();
                axioms.sort_by_key(|name| name.to_string());
                ProofQuality::AxiomDependent {
                    axiom_count: axioms.len(),
                    axioms,
                }
            }
        };

        self.proof_quality_by_name
            .insert(info.name.clone(), quality.clone());
        quality
    }

    fn axiom_deps(&mut self, info: &ConstantInfo) -> HashSet<Name> {
        if let Some(deps) = self.axiom_deps_by_name.get(&info.name) {
            return deps.clone();
        }

        let mut visiting = HashSet::new();
        let (mut deps, complete) = self.axiom_deps_inner(info, &mut visiting);
        deps.remove(&info.name);
        if complete {
            self.axiom_deps_by_name
                .insert(info.name.clone(), deps.clone());
            deps
        } else {
            self.axiom_deps_uncached(info)
        }
    }

    fn axiom_deps_inner(
        &mut self,
        info: &ConstantInfo,
        visiting: &mut HashSet<Name>,
    ) -> (HashSet<Name>, bool) {
        if let Some(deps) = self.axiom_deps_by_name.get(&info.name) {
            return (deps.clone(), true);
        }
        if visiting.len() >= PROJECT_TRUST_CACHE_MAX_RECURSION_DEPTH {
            return (HashSet::new(), false);
        }
        if !visiting.insert(info.name.clone()) {
            return (HashSet::new(), false);
        }

        let mut deps = HashSet::new();
        let mut complete = true;
        for dep_name in self.axiom_refs(info) {
            let Some(dep_info) = self.constants_by_name.get(&dep_name).copied() else {
                continue;
            };
            if dep_info.kind == ConstantKind::Axiom && !is_foundational_axiom(&dep_name) {
                deps.insert(dep_name.clone());
            }
            if visiting.contains(&dep_name) {
                complete = false;
                continue;
            }
            let (dep_deps, dep_complete) = self.axiom_deps_inner(dep_info, visiting);
            deps.extend(dep_deps);
            complete &= dep_complete;
        }

        visiting.remove(&info.name);
        deps.remove(&info.name);
        if complete {
            self.axiom_deps_by_name
                .insert(info.name.clone(), deps.clone());
        }
        (deps, complete)
    }

    fn axiom_deps_uncached(&mut self, root: &ConstantInfo) -> HashSet<Name> {
        let mut deps = HashSet::new();
        let mut visited = HashSet::new();
        let mut stack = self.axiom_refs(root);

        visited.insert(root.name.clone());
        while let Some(name) = stack.pop() {
            if !visited.insert(name.clone()) {
                continue;
            }

            let Some(info) = self.constants_by_name.get(&name).copied() else {
                continue;
            };
            if info.kind == ConstantKind::Axiom && !is_foundational_axiom(&name) {
                deps.insert(name.clone());
            }
            stack.extend(self.axiom_refs(info));
        }

        deps
    }

    fn trust_marker_deps(&mut self, info: &ConstantInfo) -> HashSet<Name> {
        self.axiom_deps(info)
            .into_iter()
            .filter(is_trust_marker)
            .collect()
    }

    fn recursive_trust_deps(&mut self, root: &ConstantInfo) -> RecursiveTrustDeps {
        if let Some(deps) = self.recursive_trust_deps_by_name.get(&root.name) {
            return deps.clone();
        }

        let mut visiting = HashSet::new();
        let (mut deps, complete) = self.recursive_trust_deps_inner(root, &mut visiting);
        deps.unsafe_deps.remove(&root.name);
        deps.opaque_deps.remove(&root.name);

        if complete {
            let sorted = deps.into_sorted();
            self.recursive_trust_deps_by_name
                .insert(root.name.clone(), sorted.clone());
            sorted
        } else {
            self.recursive_trust_deps_uncached(root)
        }
    }

    fn recursive_trust_deps_inner(
        &mut self,
        info: &ConstantInfo,
        visiting: &mut HashSet<Name>,
    ) -> (RecursiveTrustDepSets, bool) {
        if let Some(deps) = self.recursive_trust_deps_by_name.get(&info.name) {
            return (RecursiveTrustDepSets::from(deps), true);
        }
        if visiting.len() >= PROJECT_TRUST_CACHE_MAX_RECURSION_DEPTH {
            return (RecursiveTrustDepSets::default(), false);
        }
        if !visiting.insert(info.name.clone()) {
            return (RecursiveTrustDepSets::default(), false);
        }

        let mut deps = RecursiveTrustDepSets::default();
        let mut complete = true;
        for dep_name in self.direct_refs(info) {
            let Some(dep_info) = self.constants_by_name.get(&dep_name).copied() else {
                continue;
            };
            if self.is_unsafe(&dep_info.name) {
                deps.unsafe_deps.insert(dep_info.name.clone());
            }
            if dep_info.kind == ConstantKind::Opaque {
                deps.opaque_deps.insert(dep_info.name.clone());
            }
            if visiting.contains(&dep_name) {
                complete = false;
                continue;
            }
            let (dep_deps, dep_complete) = self.recursive_trust_deps_inner(dep_info, visiting);
            deps.extend(dep_deps);
            complete &= dep_complete;
        }

        visiting.remove(&info.name);
        deps.unsafe_deps.remove(&info.name);
        deps.opaque_deps.remove(&info.name);
        if complete {
            self.recursive_trust_deps_by_name
                .insert(info.name.clone(), deps.clone().into_sorted());
        }
        (deps, complete)
    }

    fn recursive_trust_deps_uncached(&mut self, root: &ConstantInfo) -> RecursiveTrustDeps {
        let mut visited = HashSet::new();
        let mut unsafe_deps = HashSet::new();
        let mut opaque_deps = HashSet::new();
        let mut stack = self.direct_refs(root);

        visited.insert(root.name.clone());
        while let Some(name) = stack.pop() {
            if !visited.insert(name.clone()) {
                continue;
            }

            let Some(info) = self.constants_by_name.get(&name).copied() else {
                continue;
            };

            if self.is_unsafe(&info.name) {
                unsafe_deps.insert(info.name.clone());
            }
            if info.kind == ConstantKind::Opaque {
                opaque_deps.insert(info.name.clone());
            }

            stack.extend(self.direct_refs(info));
        }

        RecursiveTrustDeps {
            unsafe_deps: sorted_names(unsafe_deps),
            opaque_deps: sorted_names(opaque_deps),
        }
    }

    fn direct_refs(&mut self, info: &ConstantInfo) -> Vec<Name> {
        if let Some(refs) = self.direct_refs_by_name.get(&info.name) {
            return refs.clone();
        }

        let refs = direct_constant_refs(info);
        self.direct_refs_by_name
            .insert(info.name.clone(), refs.clone());
        refs
    }

    fn axiom_refs(&mut self, info: &ConstantInfo) -> Vec<Name> {
        if let Some(refs) = self.axiom_refs_by_name.get(&info.name) {
            return refs.clone();
        }

        let refs = direct_axiom_refs(info);
        self.axiom_refs_by_name
            .insert(info.name.clone(), refs.clone());
        refs
    }
}

fn trust_level_for(
    trust_cache: &mut ProjectTrustCache<'_>,
    info: &ConstantInfo,
    summary: clean_kernel::env::DeclarationTrustSummary,
    recursive_deps: &RecursiveTrustDeps,
) -> TrustLevel {
    if trust_cache.is_unsafe(&info.name)
        || summary.trusted_axiom_count() > 0
        || !recursive_deps.unsafe_deps.is_empty()
    {
        return TrustLevel::TrustedOracle;
    }
    if summary.has_sorry() || !recursive_deps.opaque_deps.is_empty() {
        return TrustLevel::PartiallyAxiomatized;
    }
    if !trust_cache.axiom_deps(info).is_empty() {
        return TrustLevel::AxiomDependent;
    }

    match info.kind {
        ConstantKind::Definition => TrustLevel::KernelVerified,
        ConstantKind::Opaque => TrustLevel::PartiallyAxiomatized,
        ConstantKind::Axiom => TrustLevel::AxiomDependent,
        ConstantKind::Theorem => match trust_cache.proof_quality(info) {
            ProofQuality::Constructive => TrustLevel::KernelVerified,
            ProofQuality::AxiomDependent { .. } => TrustLevel::AxiomDependent,
            ProofQuality::Unchecked => TrustLevel::PartiallyAxiomatized,
            ProofQuality::NotATheorem => TrustLevel::PartiallyAxiomatized,
            _ => TrustLevel::PartiallyAxiomatized,
        },
    }
}

fn axiom_profile_for(
    trust_cache: &mut ProjectTrustCache<'_>,
    info: &ConstantInfo,
    summary: clean_kernel::env::DeclarationTrustSummary,
    recursive_deps: &RecursiveTrustDeps,
) -> AxiomProfile {
    let mut profile = AxiomProfile::NONE;

    if trust_cache.is_unsafe(&info.name)
        || !recursive_deps.unsafe_deps.is_empty()
        || !recursive_deps.opaque_deps.is_empty()
    {
        profile |= AxiomProfile::AXIOMATIZED;
    }
    if info.kind == ConstantKind::Opaque {
        profile |= AxiomProfile::AXIOMATIZED;
    }
    if info.kind == ConstantKind::Axiom && !is_foundational_axiom(&info.name) {
        profile |= AxiomProfile::AXIOMATIZED;
    }
    if summary.has_sorry() {
        profile |= AxiomProfile::AXIOMATIZED;
    }
    if summary.trusted_arith_count > 0 {
        profile |= AxiomProfile::LRA_TRUSTED;
    }
    if summary.trusted_ay_count > 0 {
        profile |= AxiomProfile::SMT_ORACLE;
    }

    for dep in trust_cache.axiom_deps(info) {
        if !is_foundational_axiom(&dep) {
            profile |= AxiomProfile::AXIOMATIZED;
        }
        match dep.to_string().as_str() {
            "trustedArith" => profile |= AxiomProfile::LRA_TRUSTED,
            "trustedAy" => profile |= AxiomProfile::SMT_ORACLE,
            "sorry" | "sorryAx" => profile |= AxiomProfile::AXIOMATIZED,
            _ => {}
        }
    }

    profile
}

fn add_declaration_findings(
    builder: &mut AuditReportBuilder,
    workspace: &(impl ProjectAuditWorkspace + ?Sized),
    modules: &[String],
    trust_cache: &mut ProjectTrustCache<'_>,
    info: &ConstantInfo,
    node_idx: u32,
    recursive_deps: &RecursiveTrustDeps,
) {
    let name = info.name.to_string();
    let source = source_for_name(workspace, modules, &name);

    match info.kind {
        ConstantKind::Axiom => {
            let foundational = is_foundational_axiom(&info.name);
            builder.add_finding(AuditFinding::structured(
                if foundational {
                    AuditSeverity::Info
                } else {
                    AuditSeverity::Warning
                },
                AuditFindingCategory::AxiomDeclaration,
                format!(
                    "Axiom declaration: {name} (kernel=Clean, source={}, foundational={foundational})",
                    source.as_deref().unwrap_or("<unknown>")
                ),
                vec![node_idx],
                if foundational {
                    None
                } else {
                    Some("Replace the axiom with a replayed certificate or kernel proof.".to_owned())
                },
            ));
        }
        ConstantKind::Opaque => {
            builder.add_finding(AuditFinding::structured(
                AuditSeverity::Warning,
                AuditFindingCategory::OpaqueConstant,
                format!(
                    "Opaque constant: {name} (kernel=Clean, source={})",
                    source.as_deref().unwrap_or("<unknown>")
                ),
                vec![node_idx],
                Some("Audit the hidden value or demote dependent declarations.".to_owned()),
            ));
        }
        ConstantKind::Theorem => {
            add_theorem_quality_finding(builder, trust_cache, info, node_idx, &source);
        }
        ConstantKind::Definition => {}
    }

    if trust_cache.is_unsafe(&info.name) {
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Error,
            AuditFindingCategory::UnsafeDeclaration,
            format!(
                "Unsafe declaration: {name} (kernel=Clean, source={})",
                source.as_deref().unwrap_or("<unknown>")
            ),
            vec![node_idx],
            Some("Keep unsafe declarations out of trusted theorem dependencies.".to_owned()),
        ));
    }

    add_transitive_dependency_findings(builder, trust_cache, info, node_idx, &source);
    add_recursive_unsafe_opaque_findings(builder, info, node_idx, &source, recursive_deps);
    add_declaration_trust_summary_findings(builder, info, node_idx, &source);

    if let Some(generator) = generated_declaration_generator(&name) {
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Info,
            AuditFindingCategory::GeneratedCode {
                generator: generator.to_owned(),
                deterministic: true,
            },
            format!(
                "Generated declaration: {name} (generator={generator}, source={})",
                source.as_deref().unwrap_or("<unknown>")
            ),
            vec![node_idx],
            None,
        ));
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct RecursiveTrustDeps {
    unsafe_deps: Vec<Name>,
    opaque_deps: Vec<Name>,
}

fn direct_constant_refs(info: &ConstantInfo) -> Vec<Name> {
    let mut refs = HashSet::new();
    collect_expr_constant_refs(&info.type_, &mut refs);
    if let Some(value) = &info.value {
        collect_expr_constant_refs(value, &mut refs);
    }
    sorted_names(refs)
}

fn direct_axiom_refs(info: &ConstantInfo) -> Vec<Name> {
    let mut refs = HashSet::new();
    collect_axiom_expr_constant_refs(&info.type_, &mut refs);
    if let Some(value) = &info.value {
        collect_axiom_expr_constant_refs(value, &mut refs);
    }
    sorted_names(refs)
}

fn collect_axiom_expr_constant_refs(expr: &Expr, out: &mut HashSet<Name>) {
    let mut stack = vec![expr];
    while let Some(current) = stack.pop() {
        match current.kind() {
            ExprKind::Const(name, _) => {
                out.insert(name.clone());
            }
            ExprKind::App(func, arg) => {
                stack.push(func);
                stack.push(arg);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, value, body, _) => {
                stack.push(ty);
                stack.push(value);
                stack.push(body);
            }
            ExprKind::MData(_, inner) | ExprKind::Squash(inner) | ExprKind::Proj(_, _, inner) => {
                stack.push(inner);
            }
            _ => {}
        }
    }
}

fn collect_expr_constant_refs(expr: &Expr, out: &mut HashSet<Name>) {
    let mut stack = vec![expr];
    while let Some(current) = stack.pop() {
        match current.kind() {
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Lit(_)
            | ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => {}
            ExprKind::Const(name, _) => {
                out.insert(name.clone());
            }
            ExprKind::App(func, arg) => {
                stack.push(arg);
                stack.push(func);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(body);
                stack.push(ty);
            }
            ExprKind::Let(_, ty, value, body, _) => {
                stack.push(body);
                stack.push(value);
                stack.push(ty);
            }
            ExprKind::Proj(struct_name, _, inner) => {
                out.insert(struct_name.clone());
                stack.push(inner);
            }
            ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                stack.push(inner);
            }
            ExprKind::CubicalPath { ty, left, right } => {
                stack.push(right);
                stack.push(left);
                stack.push(ty);
            }
            ExprKind::CubicalPathLam { body } => stack.push(body),
            ExprKind::CubicalPathApp { path, arg } => {
                stack.push(arg);
                stack.push(path);
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                stack.push(base);
                stack.push(u);
                stack.push(phi);
                stack.push(ty);
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                stack.push(base);
                stack.push(phi);
                stack.push(ty);
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                stack.push(base);
                stack.push(s);
                stack.push(r);
                stack.push(ty);
            }
            ExprKind::ZFCSet(set_expr) => push_zfc_set_expr(set_expr, &mut stack),
            ExprKind::ZFCMem { element, set } => {
                stack.push(set);
                stack.push(element);
            }
            ExprKind::ZFCComprehension { domain, pred } => {
                stack.push(pred);
                stack.push(domain);
            }
        }
    }
}

fn push_zfc_set_expr<'a>(set_expr: &'a ZFCSetExpr, stack: &mut Vec<&'a Expr>) {
    match set_expr {
        ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
        ZFCSetExpr::Singleton(expr)
        | ZFCSetExpr::Union(expr)
        | ZFCSetExpr::PowerSet(expr)
        | ZFCSetExpr::Choice(expr) => stack.push(expr),
        ZFCSetExpr::Pair(left, right)
        | ZFCSetExpr::Separation {
            set: left,
            pred: right,
        }
        | ZFCSetExpr::Replacement {
            set: left,
            func: right,
        } => {
            stack.push(right);
            stack.push(left);
        }
    }
}

fn sorted_names(deps: HashSet<Name>) -> Vec<Name> {
    let mut names: Vec<_> = deps.into_iter().collect();
    names.sort_by_key(|name| name.to_string());
    names
}

fn add_theorem_quality_finding(
    builder: &mut AuditReportBuilder,
    trust_cache: &mut ProjectTrustCache<'_>,
    info: &ConstantInfo,
    node_idx: u32,
    source: &Option<String>,
) {
    let name = info.name.to_string();
    match trust_cache.proof_quality(info) {
        ProofQuality::AxiomDependent { axioms, .. } => {
            let mut axiom_names: Vec<_> = axioms.iter().map(ToString::to_string).collect();
            axiom_names.sort();
            builder.add_finding(AuditFinding::structured(
                AuditSeverity::Warning,
                AuditFindingCategory::KernelTrust {
                    kernel: KernelAuditKernel::Clean,
                },
                format!(
                    "Axiom-dependent theorem: {name} depends on [{}] (source={})",
                    axiom_names.join(", "),
                    source.as_deref().unwrap_or("<unknown>")
                ),
                vec![node_idx],
                Some("Discharge or certify the listed axiom dependencies.".to_owned()),
            ));
        }
        ProofQuality::Unchecked => {
            builder.add_finding(AuditFinding::structured(
                AuditSeverity::Error,
                AuditFindingCategory::KernelTrust {
                    kernel: KernelAuditKernel::Clean,
                },
                format!(
                    "Unchecked theorem declaration: {name} (source={})",
                    source.as_deref().unwrap_or("<unknown>")
                ),
                vec![node_idx],
                Some("Replay or re-check this theorem through the kernel.".to_owned()),
            ));
            builder.add_finding(AuditFinding::structured(
                AuditSeverity::Error,
                AuditFindingCategory::CertificateProvenance {
                    format: "clean-kernel-proof-term".to_owned(),
                    replayed: false,
                },
                format!(
                    "Unreplayed theorem certificate provenance: {name} (source={})",
                    source.as_deref().unwrap_or("<unknown>")
                ),
                vec![node_idx],
                Some("Attach replayed certificate provenance or re-check the theorem.".to_owned()),
            ));
        }
        ProofQuality::Constructive | ProofQuality::NotATheorem => {}
        _ => {}
    }
}

fn add_transitive_dependency_findings(
    builder: &mut AuditReportBuilder,
    trust_cache: &mut ProjectTrustCache<'_>,
    info: &ConstantInfo,
    node_idx: u32,
    source: &Option<String>,
) {
    let deps = trust_cache.axiom_deps(info);
    if deps.is_empty() {
        return;
    }

    let trust_markers = trust_cache.trust_marker_deps(info);
    let axiom_names = sorted_dependency_names(deps.difference(&trust_markers).cloned().collect());
    let marker_names = sorted_dependency_names(trust_markers);

    let mut parts = Vec::with_capacity(2);
    if !axiom_names.is_empty() {
        parts.push(format!("axioms [{}]", axiom_names.join(", ")));
    }
    if !marker_names.is_empty() {
        parts.push(format!("trust markers [{}]", marker_names.join(", ")));
    }

    let severity = if marker_names
        .iter()
        .any(|name| name == "sorry" || name == "sorryAx")
    {
        AuditSeverity::Error
    } else {
        AuditSeverity::Warning
    };

    let name = info.name.to_string();
    builder.add_finding(AuditFinding::structured(
        severity,
        AuditFindingCategory::KernelTrust {
            kernel: KernelAuditKernel::Clean,
        },
        format!(
            "Transitive trust dependencies: {name} reaches {} (source={})",
            parts.join(" and "),
            source.as_deref().unwrap_or("<unknown>")
        ),
        vec![node_idx],
        Some("Discharge, certify, or explicitly demote the listed dependency closure.".to_owned()),
    ));
}

fn add_recursive_unsafe_opaque_findings(
    builder: &mut AuditReportBuilder,
    info: &ConstantInfo,
    node_idx: u32,
    source: &Option<String>,
    recursive_deps: &RecursiveTrustDeps,
) {
    let name = info.name.to_string();

    if !recursive_deps.unsafe_deps.is_empty() {
        let deps = recursive_deps
            .unsafe_deps
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Error,
            AuditFindingCategory::KernelTrust {
                kernel: KernelAuditKernel::Clean,
            },
            format!(
                "Transitive unsafe dependency: {name} reaches [{}] (source={})",
                deps.join(", "),
                source.as_deref().unwrap_or("<unknown>")
            ),
            vec![node_idx],
            Some("Remove unsafe declarations from the trusted dependency closure.".to_owned()),
        ));
    }

    if !recursive_deps.opaque_deps.is_empty() {
        let deps = recursive_deps
            .opaque_deps
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Warning,
            AuditFindingCategory::KernelTrust {
                kernel: KernelAuditKernel::Clean,
            },
            format!(
                "Transitive opaque dependency: {name} reaches [{}] (source={})",
                deps.join(", "),
                source.as_deref().unwrap_or("<unknown>")
            ),
            vec![node_idx],
            Some(
                "Expose, certify, or demote opaque dependencies before trusting this closure."
                    .to_owned(),
            ),
        ));
    }
}

fn sorted_dependency_names(deps: HashSet<Name>) -> Vec<String> {
    let mut names: Vec<_> = deps.into_iter().map(|name| name.to_string()).collect();
    names.sort();
    names
}

fn add_declaration_trust_summary_findings(
    builder: &mut AuditReportBuilder,
    info: &ConstantInfo,
    node_idx: u32,
    source: &Option<String>,
) {
    let name = info.name.to_string();
    let summary = info.trust_summary();
    if summary.has_explicit_sorry {
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Critical,
            AuditFindingCategory::KernelTrust {
                kernel: KernelAuditKernel::Clean,
            },
            format!(
                "Explicit sorry in declaration: {name} (source={})",
                source.as_deref().unwrap_or("<unknown>")
            ),
            vec![node_idx],
            Some(
                "Replace the sorry with a checked proof before trusting this declaration."
                    .to_owned(),
            ),
        ));
    }
    if summary.has_synthetic_sorry {
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Error,
            AuditFindingCategory::KernelTrust {
                kernel: KernelAuditKernel::Clean,
            },
            format!(
                "Synthetic sorry in declaration: {name} (source={})",
                source.as_deref().unwrap_or("<unknown>")
            ),
            vec![node_idx],
            Some("Regenerate the declaration without synthetic sorry placeholders.".to_owned()),
        ));
    }
    if summary.trusted_arith_count > 0 {
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Warning,
            AuditFindingCategory::ExternalSolver {
                solver: "trustedArith".to_owned(),
            },
            format!(
                "External solver trust marker: {name} uses trustedArith {} time(s) (source={})",
                summary.trusted_arith_count,
                source.as_deref().unwrap_or("<unknown>")
            ),
            vec![node_idx],
            Some("Attach a replayable arithmetic certificate or demote trust.".to_owned()),
        ));
    }
    if summary.trusted_ay_count > 0 {
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Warning,
            AuditFindingCategory::ExternalSolver {
                solver: "trustedAy".to_owned(),
            },
            format!(
                "External solver trust marker: {name} uses trustedAy {} time(s) (source={})",
                summary.trusted_ay_count,
                source.as_deref().unwrap_or("<unknown>")
            ),
            vec![node_idx],
            Some("Attach a replayable ay certificate or demote trust.".to_owned()),
        ));
    }
}

fn source_for_name(
    workspace: &(impl ProjectAuditWorkspace + ?Sized),
    modules: &[String],
    name: &str,
) -> Option<String> {
    modules
        .iter()
        .filter(|module| name == module.as_str() || name.starts_with(&format!("{module}.")))
        .max_by_key(|module| module.len())
        .and_then(|module| workspace.find_module(module))
        .map(|path| path.display().to_string())
}

fn generated_declaration_generator(name: &str) -> Option<&'static str> {
    let last = name.rsplit('.').next().unwrap_or(name);
    match last {
        "rec" | "recOn" | "casesOn" | "noConfusion" | "noConfusionType" | "below" | "brecOn" => {
            Some("lean4-kernel")
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::{Path, PathBuf};

    use crate::attempt_log::{
        iter_from, read_artifact, AttemptFilter, AttemptStatusFilter, AuthorityReceipt,
    };
    use clean_kernel::sorry::{create_sorry_term, create_sorry_term_with_kind, SorryKind};
    use clean_kernel::{Declaration, Expr, Level};
    use tempfile::TempDir;

    use super::*;

    struct TestWorkspace {
        root: PathBuf,
        modules: Vec<String>,
    }

    impl TestWorkspace {
        fn new(root: &Path, modules: &[&str]) -> Self {
            Self {
                root: root.to_path_buf(),
                modules: modules.iter().map(|module| module.to_string()).collect(),
            }
        }
    }

    impl ProjectAuditWorkspace for TestWorkspace {
        fn all_modules(&self) -> Vec<String> {
            self.modules.clone()
        }

        fn find_module(&self, module_name: &str) -> Option<PathBuf> {
            let rel = module_name.replace('.', "/");
            Some(self.root.join(format!("{rel}.lean")))
        }
    }

    #[test]
    fn project_audit_authority_gate_rejects_empty_and_accepts_info_only_audits() {
        let empty_report = AuditReportBuilder::new().build();
        let empty_status = project_audit_authority_gate_status(&empty_report);
        assert!(!empty_status.is_accepted());
        assert!(matches!(
            empty_status.status,
            AttemptStatus::Rejected { .. }
        ));
        assert_eq!(
            empty_status.failure_mode.as_deref(),
            Some("empty_project_audit")
        );
        assert_eq!(empty_status.trust_level, Some(TrustLevel::TrustedOracle));

        let tmp = TempDir::new().expect("tempdir");
        let workspace = TestWorkspace::new(tmp.path(), &["Project"]);
        let mut env = Environment::new();
        env.add_decl_structural(Declaration::Definition {
            name: Name::from_string("Project.clean_def"),
            level_params: vec![],
            type_: Expr::prop(),
            value: Expr::prop(),
            is_reducible: false,
        })
        .expect("clean definition");

        let clean_report = audit_lake_project(&workspace, &env);
        let clean_status = project_audit_authority_gate_status(&clean_report);
        assert!(clean_status.is_accepted());
        assert_eq!(clean_status.status, AttemptStatus::Accepted);
        assert_eq!(clean_status.failure_mode, None);
        assert_eq!(clean_status.trust_level, Some(TrustLevel::KernelVerified));
    }

    #[test]
    fn project_audit_authority_gate_rejects_transitive_axiom_dependency() {
        let tmp = TempDir::new().expect("tempdir");
        let workspace = TestWorkspace::new(tmp.path(), &["Project"]);

        let mut env = Environment::new();
        let prop = Expr::prop();
        env.add_decl_structural(Declaration::Axiom {
            name: Name::from_string("Project.domain_axiom"),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("axiom");
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("Project.base_theorem"),
            level_params: vec![],
            type_: prop.clone(),
            value: Expr::const_str("Project.domain_axiom"),
        })
        .expect("base theorem");
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("Project.dependent_theorem"),
            level_params: vec![],
            type_: prop,
            value: Expr::const_str("Project.base_theorem"),
        })
        .expect("dependent theorem");

        let report = audit_lake_project(&workspace, &env);
        let status = project_audit_authority_gate_status(&report);

        assert!(!status.is_accepted());
        assert_eq!(
            status.failure_mode.as_deref(),
            Some("transitive_axiom_dependency")
        );
        assert_eq!(status.trust_level, Some(TrustLevel::AxiomDependent));
        assert!(matches!(
            status.status,
            AttemptStatus::Rejected { ref reason }
                if reason.contains("Transitive trust dependencies")
        ));
    }

    #[test]
    fn project_audit_authority_gate_rejects_synthetic_sorry_declaration() {
        let tmp = TempDir::new().expect("tempdir");
        let workspace = TestWorkspace::new(tmp.path(), &["Project"]);

        let mut env = Environment::try_with_prelude().expect("prelude");
        let prop = Expr::prop();
        let proof = create_sorry_term(&env, &prop);
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("Project.synthetic_gap"),
            level_params: vec![],
            type_: prop.clone(),
            value: proof,
        })
        .expect("synthetic sorry theorem");

        let report = audit_lake_project(&workspace, &env);
        let status = project_audit_authority_gate_status(&report);

        assert!(report.findings.iter().any(|finding| finding
            .message
            .contains("Synthetic sorry in declaration: Project.synthetic_gap")));
        assert!(!status.is_accepted());
        assert_eq!(status.failure_mode.as_deref(), Some("synthetic_sorry"));
        assert_eq!(status.trust_level, Some(TrustLevel::TrustedOracle));
        assert!(matches!(
            status.status,
            AttemptStatus::Rejected { ref reason }
                if reason.contains("Synthetic sorry in declaration")
        ));
    }

    #[test]
    fn project_audit_authority_gate_rejects_explicit_sorry_declaration() {
        let tmp = TempDir::new().expect("tempdir");
        let workspace = TestWorkspace::new(tmp.path(), &["Project"]);

        let mut env = Environment::try_with_prelude().expect("prelude");
        let prop = Expr::prop();
        let proof = create_sorry_term_with_kind(&env, &prop, SorryKind::Explicit);
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("Project.explicit_gap"),
            level_params: vec![],
            type_: prop.clone(),
            value: proof,
        })
        .expect("explicit sorry theorem");

        let report = audit_lake_project(&workspace, &env);
        let status = project_audit_authority_gate_status(&report);

        assert!(report.findings.iter().any(|finding| finding
            .message
            .contains("Explicit sorry in declaration: Project.explicit_gap")));
        assert!(!status.is_accepted());
        assert_eq!(status.failure_mode.as_deref(), Some("explicit_sorry"));
        assert_eq!(status.trust_level, Some(TrustLevel::TrustedOracle));
        assert!(matches!(
            status.status,
            AttemptStatus::Rejected { ref reason }
                if reason.contains("Explicit sorry in declaration")
        ));
    }

    #[test]
    fn project_audit_authority_gate_rejects_direct_trusted_placeholder() {
        let tmp = TempDir::new().expect("tempdir");
        let workspace = TestWorkspace::new(tmp.path(), &["Project"]);

        let mut env = Environment::new();
        let prop = Expr::prop();
        let proof = Expr::app(
            Expr::const_(Name::from_string("trustedArith"), vec![Level::zero()]),
            prop.clone(),
        );
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("Project.trusted_placeholder"),
            level_params: vec![],
            type_: prop.clone(),
            value: proof,
        })
        .expect("trusted placeholder theorem");

        let report = audit_lake_project(&workspace, &env);
        let status = project_audit_authority_gate_status(&report);

        assert!(report.findings.iter().any(|finding| finding
            .message
            .contains("Project.trusted_placeholder uses trustedArith")));
        assert!(!status.is_accepted());
        assert_eq!(
            status.failure_mode.as_deref(),
            Some("external_solver_trust")
        );
        assert_eq!(status.trust_level, Some(TrustLevel::TrustedOracle));
    }

    #[test]
    fn audit_lake_project_demotes_definitions_with_axiom_dependencies() {
        let tmp = TempDir::new().expect("tempdir");
        let workspace = TestWorkspace::new(tmp.path(), &["Project"]);

        let mut env = Environment::new();
        let prop = Expr::prop();
        env.add_decl_structural(Declaration::Axiom {
            name: Name::from_string("Project.domain_axiom"),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("axiom");
        env.add_decl_structural(Declaration::Definition {
            name: Name::from_string("Project.axiom_backed_target"),
            level_params: vec![],
            type_: prop.clone(),
            value: Expr::const_str("Project.domain_axiom"),
            is_reducible: false,
        })
        .expect("definition");

        let report = audit_lake_project(&workspace, &env);
        let status = project_audit_authority_gate_status(&report);

        assert!(report.trust_violations.is_empty());
        assert_eq!(
            report.by_trust_level.get(&TrustLevel::AxiomDependent),
            Some(&2)
        );
        assert!(report.findings.iter().any(|finding| {
            finding.message.contains(
                "Transitive trust dependencies: Project.axiom_backed_target reaches axioms [Project.domain_axiom]",
            )
        }));
        assert!(!status.is_accepted());
        assert_eq!(
            status.failure_mode.as_deref(),
            Some("transitive_axiom_dependency")
        );
    }

    #[test]
    fn project_audit_authority_gate_rejects_critical_finding() {
        let mut builder = AuditReportBuilder::new();
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Critical,
            AuditFindingCategory::KernelTrust {
                kernel: KernelAuditKernel::Clean,
            },
            "Explicit sorry in declaration: Project.bad",
            vec![0],
            None,
        ));
        let report = builder.build();

        let status = project_audit_authority_gate_status(&report);

        assert!(!status.is_accepted());
        assert_eq!(status.failure_mode.as_deref(), Some("explicit_sorry"));
        assert_eq!(status.trust_level, Some(TrustLevel::TrustedOracle));
        assert!(matches!(
            status.status,
            AttemptStatus::Rejected { ref reason }
                if reason.contains("Critical finding")
                    && reason.contains("Explicit sorry in declaration")
        ));
    }

    #[test]
    fn project_audit_authority_gate_attempt_record_is_appended_and_queryable() {
        let tmp = TempDir::new().expect("tempdir");
        let mut builder = AuditReportBuilder::new();
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Warning,
            AuditFindingCategory::AxiomDeclaration,
            "axiom declaration found",
            vec![],
            None,
        ));
        let report = builder.build();
        let status = project_audit_authority_gate_status(&report);

        let recorded =
            record_project_audit_authority_gate_attempt(tmp.path(), &report, &status, 23)
                .expect("record project-audit authority gate");

        assert_eq!(recorded.authority_gate.as_deref(), Some("trust_audit"));
        assert!(matches!(recorded.status, AttemptStatus::Rejected { .. }));
        assert_eq!(recorded.failure_mode.as_deref(), Some("axiom_declaration"));
        assert_eq!(recorded.trust_level, Some(TrustLevel::AxiomDependent));
        assert_eq!(recorded.wall_time_ms, 23);
        assert_eq!(recorded.command_evidence, None);

        let queried: Vec<_> = iter_from(
            tmp.path(),
            AttemptFilter {
                authority_gate: Some("trust_audit".to_owned()),
                status: Some(AttemptStatusFilter::Rejected),
                failure_mode: Some("axiom_declaration".to_owned()),
                ..AttemptFilter::default()
            },
        )
        .expect("query trust_audit attempt")
        .collect();
        assert_eq!(queried, vec![recorded.clone()]);

        let artifact = recorded
            .solver_artifact
            .as_ref()
            .expect("project audit report artifact");
        assert_eq!(
            artifact.kind.as_deref(),
            Some("authority-gate/trust-audit-report")
        );
        let artifact_bytes = read_artifact(tmp.path(), artifact).expect("read audit artifact");
        assert_eq!(
            recorded.trust_audit_hash,
            blake3::hash(&artifact_bytes).to_hex().to_string()
        );
    }

    #[test]
    fn accepted_project_audit_authority_gate_attempt_has_command_evidence_receipt() {
        let tmp = TempDir::new().expect("tempdir");
        fs::write(
            tmp.path().join("Project.lean"),
            "def Project.clean_def : Prop := True\n",
        )
        .expect("write project source");
        let workspace = TestWorkspace::new(tmp.path(), &["Project"]);
        let mut env = Environment::new();
        env.add_decl_structural(Declaration::Definition {
            name: Name::from_string("Project.clean_def"),
            level_params: vec![],
            type_: Expr::prop(),
            value: Expr::prop(),
            is_reducible: false,
        })
        .expect("clean definition");
        let report = audit_lake_project(&workspace, &env);
        let status = project_audit_authority_gate_status(&report);

        let recorded =
            record_project_audit_authority_gate_attempt(tmp.path(), &report, &status, 31)
                .expect("record accepted project-audit authority gate");

        assert_eq!(recorded.authority_gate.as_deref(), Some("trust_audit"));
        assert!(matches!(recorded.status, AttemptStatus::Accepted));
        assert_eq!(recorded.trust_level, Some(TrustLevel::KernelVerified));
        let receipt = AuthorityReceipt::from_attempt(&recorded);
        let receipt_command = receipt
            .command_evidence
            .as_ref()
            .expect("receipt command evidence");
        assert_eq!(
            receipt_command.kind.as_deref(),
            Some("authority-gate/command-evidence")
        );

        let command_artifact = recorded
            .command_evidence
            .as_ref()
            .expect("recorded command evidence");
        let command_bytes =
            read_artifact(tmp.path(), command_artifact).expect("read command evidence");
        let command_json: serde_json::Value =
            serde_json::from_slice(&command_bytes).expect("parse command evidence");
        assert_eq!(
            command_json["schema_version"],
            "clean-project-audit-command-evidence-v1"
        );
        assert_eq!(command_json["gate"], "trust_audit");
        assert_eq!(command_json["gate_scope"], PROJECT_AUDIT_GOAL_SHAPE);
        assert_eq!(command_json["report_hash"], recorded.trust_audit_hash);
        assert_eq!(
            command_json["source_root"],
            tmp.path().to_string_lossy().as_ref()
        );
        assert_eq!(command_json["status"], "accepted");
        assert_eq!(command_json["trust_level"], "KernelVerified");
        assert!(command_json["source_digest"]
            .as_str()
            .is_some_and(|digest| digest.len() == 64));
    }

    #[test]
    fn audit_lake_project_surfaces_kernel_trust_findings() {
        let tmp = TempDir::new().expect("tempdir");
        let workspace = TestWorkspace::new(tmp.path(), &["Project"]);

        let mut env = Environment::new();
        let prop = Expr::prop();
        env.add_decl_structural(Declaration::Axiom {
            name: Name::from_string("Project.domain_axiom"),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("axiom");
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("Project.fake_theorem"),
            level_params: vec![],
            type_: prop.clone(),
            value: Expr::const_str("Project.domain_axiom"),
        })
        .expect("theorem");
        env.add_decl_structural(Declaration::Opaque {
            name: Name::from_string("Project.hidden"),
            level_params: vec![],
            type_: prop.clone(),
            value: prop.clone(),
        })
        .expect("opaque");
        let unsafe_name = Name::from_string("Project.unsafe_def");
        env.add_decl_structural(Declaration::Definition {
            name: unsafe_name.clone(),
            level_params: vec![],
            type_: prop.clone(),
            value: prop.clone(),
            is_reducible: false,
        })
        .expect("definition");
        env.mark_unsafe(unsafe_name);
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("Project.z4_theorem"),
            level_params: vec![],
            type_: prop.clone(),
            value: Expr::const_str("trustedAy"),
        })
        .expect("z4 theorem");

        let report = audit_lake_project(&workspace, &env);

        assert_eq!(report.total_constants, 5);
        assert!(report.findings.iter().any(|finding| matches!(
            finding.structured_category(),
            AuditFindingCategory::AxiomDeclaration
        )));
        assert!(report.findings.iter().any(|finding| matches!(
            finding.structured_category(),
            AuditFindingCategory::OpaqueConstant
        )));
        assert!(report.findings.iter().any(|finding| matches!(
            finding.structured_category(),
            AuditFindingCategory::UnsafeDeclaration
        )));
        assert!(report.findings.iter().any(|finding| matches!(
            finding.structured_category(),
            AuditFindingCategory::ExternalSolver { ref solver }
                if solver == "trustedAy"
        )));
        assert!(report
            .findings
            .iter()
            .any(|finding| finding.message.contains("Axiom-dependent theorem")));
    }

    #[test]
    fn audit_lake_project_reports_transitive_axiom_dependency_through_theorem() {
        let tmp = TempDir::new().expect("tempdir");
        let workspace = TestWorkspace::new(tmp.path(), &["Project"]);

        let mut env = Environment::new();
        let prop = Expr::prop();
        env.add_decl_structural(Declaration::Axiom {
            name: Name::from_string("Project.domain_axiom"),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("axiom");
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("Project.base_theorem"),
            level_params: vec![],
            type_: prop.clone(),
            value: Expr::const_str("Project.domain_axiom"),
        })
        .expect("base theorem");
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("Project.dependent_theorem"),
            level_params: vec![],
            type_: prop,
            value: Expr::const_str("Project.base_theorem"),
        })
        .expect("dependent theorem");

        let report = audit_lake_project(&workspace, &env);

        assert_eq!(report.total_constants, 3);
        assert!(report.findings.iter().any(|finding| {
            finding
                .message
                .contains("Axiom-dependent theorem: Project.dependent_theorem depends on [Project.domain_axiom]")
        }));
        assert!(report.findings.iter().any(|finding| {
            finding.message.contains(
                "Transitive trust dependencies: Project.dependent_theorem reaches axioms [Project.domain_axiom]",
            )
        }));
    }

    #[test]
    fn audit_lake_project_reports_recursive_unsafe_dependency() {
        let tmp = TempDir::new().expect("tempdir");
        let workspace = TestWorkspace::new(tmp.path(), &["Project"]);

        let mut env = Environment::new();
        let prop = Expr::prop();
        let unsafe_name = Name::from_string("Project.unsafe_core");
        env.add_decl_structural(Declaration::Definition {
            name: unsafe_name.clone(),
            level_params: vec![],
            type_: prop.clone(),
            value: prop.clone(),
            is_reducible: false,
        })
        .expect("unsafe definition");
        env.mark_unsafe(unsafe_name);
        env.add_decl_structural(Declaration::Definition {
            name: Name::from_string("Project.middle"),
            level_params: vec![],
            type_: prop.clone(),
            value: Expr::const_str("Project.unsafe_core"),
            is_reducible: false,
        })
        .expect("middle definition");
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("Project.dependent_theorem"),
            level_params: vec![],
            type_: prop,
            value: Expr::const_str("Project.middle"),
        })
        .expect("dependent theorem");

        let report = audit_lake_project(&workspace, &env);
        let status = project_audit_authority_gate_status(&report);

        assert!(report.findings.iter().any(|finding| {
            finding
                .message
                .contains("Transitive unsafe dependency: Project.dependent_theorem reaches [Project.unsafe_core]")
        }));
        assert!(!status.is_accepted());
        assert_eq!(
            status.failure_mode.as_deref(),
            Some("transitive_unsafe_dependency")
        );
        assert_eq!(status.trust_level, Some(TrustLevel::TrustedOracle));
    }

    #[test]
    fn audit_lake_project_reports_recursive_opaque_dependency() {
        let tmp = TempDir::new().expect("tempdir");
        let workspace = TestWorkspace::new(tmp.path(), &["Project"]);

        let mut env = Environment::new();
        let prop = Expr::prop();
        env.add_decl_structural(Declaration::Opaque {
            name: Name::from_string("Project.hidden_core"),
            level_params: vec![],
            type_: prop.clone(),
            value: prop.clone(),
        })
        .expect("opaque");
        env.add_decl_structural(Declaration::Definition {
            name: Name::from_string("Project.middle"),
            level_params: vec![],
            type_: prop.clone(),
            value: Expr::const_str("Project.hidden_core"),
            is_reducible: false,
        })
        .expect("middle definition");
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("Project.dependent_theorem"),
            level_params: vec![],
            type_: prop,
            value: Expr::const_str("Project.middle"),
        })
        .expect("dependent theorem");

        let report = audit_lake_project(&workspace, &env);
        let status = project_audit_authority_gate_status(&report);

        assert!(report.findings.iter().any(|finding| {
            finding
                .message
                .contains("Transitive opaque dependency: Project.dependent_theorem reaches [Project.hidden_core]")
        }));
        assert!(!status.is_accepted());
        assert_eq!(
            status.failure_mode.as_deref(),
            Some("transitive_opaque_dependency")
        );
        assert_eq!(status.trust_level, Some(TrustLevel::AxiomDependent));
    }

    #[test]
    fn audit_lake_project_marks_generated_declarations() {
        let tmp = TempDir::new().expect("tempdir");
        let workspace = TestWorkspace::new(tmp.path(), &["Project"]);

        let mut env = Environment::new();
        let prop = Expr::prop();
        env.add_decl_structural(Declaration::Definition {
            name: Name::from_string("Project.rec"),
            level_params: vec![],
            type_: prop.clone(),
            value: prop,
            is_reducible: false,
        })
        .expect("generated declaration");

        let report = audit_lake_project(&workspace, &env);
        assert!(report.findings.iter().any(|finding| matches!(
            finding.structured_category(),
            AuditFindingCategory::GeneratedCode {
                ref generator,
                deterministic: true
            } if generator == "lean4-kernel"
        )));
    }

    #[test]
    fn audit_lake_project_empty_inventory_does_not_claim_env_constants() {
        let tmp = TempDir::new().expect("tempdir");
        let workspace = TestWorkspace::new(tmp.path(), &[]);

        let mut env = Environment::new();
        env.add_decl_structural(Declaration::Axiom {
            name: Name::from_string("Project.domain_axiom"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("axiom");

        let report = audit_lake_project(&workspace, &env);

        assert_eq!(report.total_constants, 0);
        assert!(report
            .findings
            .iter()
            .any(|finding| finding.message.contains("module inventory is empty")));
        assert!(!report.findings.iter().any(|finding| {
            finding
                .message
                .contains("Axiom declaration: Project.domain_axiom")
        }));
    }
}
