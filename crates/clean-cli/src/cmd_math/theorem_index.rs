// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Project-scoped wrapper for factory theorem-index reports.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use clean_math_project::{ArtifactRef, MathObligation};
use serde::Serialize;
use serde_json::Value;

use crate::factory::decl_index::TrustRecord;
use crate::factory::theorem_index::{TheoremCandidate, TheoremIndexReport};
use crate::math_project::{DomainProfile, DomainProfileRegistry, MathProjectManifest, TrustPolicy};

pub(super) const MATH_THEOREM_INDEX_SCHEMA_VERSION: &str = "clean-math-theorem-index-v1";

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct MathTheoremIndexReport {
    pub(super) schema_version: &'static str,
    pub(super) project: MathTheoremIndexProject,
    pub(super) profile: String,
    pub(super) files_scanned: usize,
    pub(super) memory: MathTheoremMemory,
    pub(super) candidates: Vec<ProjectTheoremCandidate>,
    pub(super) factory_report: TheoremIndexReport,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct MathTheoremIndexProject {
    pub(super) schema_version: String,
    pub(super) project_path: String,
    pub(super) project_root: String,
    pub(super) name: String,
    pub(super) domain_profile: String,
    pub(super) owner: String,
    pub(super) trust_policy: String,
    pub(super) require_artifact_replay: bool,
    pub(super) allow_synthetic_sorry: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct MathTheoremMemory {
    pub(super) candidate_count: usize,
    pub(super) local_count: usize,
    pub(super) project_count: usize,
    pub(super) domain_count: usize,
    pub(super) imported_count: usize,
    pub(super) artifact_derived_count: usize,
    pub(super) trust_policy_conforming_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct ProjectTheoremCandidate {
    pub(super) name: String,
    pub(super) source_path: String,
    pub(super) module: String,
    pub(super) candidate_fingerprint: String,
    pub(super) classification: CandidateClassification,
    pub(super) domain_signals: CandidateDomainSignals,
    pub(super) trust_decision: CandidateTrustDecision,
    pub(super) memory: CandidateStructuredMemory,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub(super) struct CandidateStructuredMemory {
    pub(super) normal_form_heads: Vec<String>,
    pub(super) side_condition_kinds: Vec<String>,
    pub(super) artifact_kinds: Vec<String>,
    pub(super) direct_imports: Vec<String>,
    pub(super) import_closure: Vec<String>,
    pub(super) direct_only: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct CandidateClassification {
    pub(super) scope: String,
    pub(super) local: bool,
    pub(super) project: bool,
    pub(super) domain: bool,
    pub(super) imported: bool,
    pub(super) artifact_derived: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct CandidateDomainSignals {
    pub(super) profile: String,
    pub(super) module_match: bool,
    pub(super) semantic_head_matches: Vec<String>,
    pub(super) ranking_signal_matches: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(super) struct CandidateTrustDecision {
    pub(super) policy: String,
    pub(super) conformance: String,
    pub(super) kernel_proof_status: String,
    pub(super) trust_debt: Vec<String>,
    pub(super) promotion_allowed: bool,
    pub(super) reasons: Vec<String>,
}

pub(super) fn wrap_theorem_index_report(
    project_path: &Path,
    manifest: &MathProjectManifest,
    factory_report: TheoremIndexReport,
) -> MathTheoremIndexReport {
    let project_root = project_path.parent().unwrap_or_else(|| Path::new("."));
    let source_texts = read_theorem_pack_texts(project_root, manifest);
    let domain_profile = DomainProfileRegistry::for_project_path(project_path)
        .profile(&manifest.domain_profile)
        .ok();
    let theorem_packs = manifest
        .theorem_packs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let project_imports = factory_report
        .candidates
        .iter()
        .flat_map(|candidate| candidate.imports.iter().map(String::as_str))
        .collect::<BTreeSet<_>>();
    let import_graph = import_graph(&factory_report.candidates);
    let obligation_memory = read_obligation_memory(project_root, manifest);

    let candidates = factory_report
        .candidates
        .iter()
        .map(|candidate| {
            let source_text = source_texts
                .get(candidate.source_path.as_str())
                .map(String::as_str)
                .unwrap_or("");
            let domain_signals =
                domain_signals(candidate, source_text, manifest, domain_profile.as_ref());
            let classification = classify_candidate(
                candidate,
                manifest,
                &theorem_packs,
                &project_imports,
                source_text,
                &domain_signals,
            );
            let trust_decision = trust_decision(candidate, &classification, &manifest.trust_policy);
            let memory = candidate_memory(
                candidate,
                source_text,
                &domain_signals,
                domain_profile.as_ref(),
                &obligation_memory,
                &import_graph,
                manifest,
            );
            ProjectTheoremCandidate {
                name: candidate.name.clone(),
                source_path: candidate.source_path.clone(),
                module: candidate.module.clone(),
                candidate_fingerprint: candidate.candidate_fingerprint.clone(),
                classification,
                domain_signals,
                trust_decision,
                memory,
            }
        })
        .collect::<Vec<_>>();
    let memory = theorem_memory(&candidates);

    MathTheoremIndexReport {
        schema_version: MATH_THEOREM_INDEX_SCHEMA_VERSION,
        project: MathTheoremIndexProject {
            schema_version: manifest.schema_version.clone(),
            project_path: project_path.display().to_string(),
            project_root: project_root.display().to_string(),
            name: manifest.project.clone(),
            domain_profile: manifest.domain_profile.clone(),
            owner: manifest.owner.clone(),
            trust_policy: manifest.trust_policy.name.clone(),
            require_artifact_replay: manifest.trust_policy.require_artifact_replay,
            allow_synthetic_sorry: manifest.trust_policy.allow_synthetic_sorry,
        },
        profile: factory_report.profile.clone(),
        files_scanned: factory_report.files_scanned,
        memory,
        candidates,
        factory_report,
    }
}

fn read_theorem_pack_texts(
    project_root: &Path,
    manifest: &MathProjectManifest,
) -> BTreeMap<String, String> {
    manifest
        .theorem_packs
        .iter()
        .filter_map(|path| {
            fs::read_to_string(project_root.join(path))
                .ok()
                .map(|text| (path.clone(), text))
        })
        .collect()
}

#[derive(Debug, Clone, Default)]
struct ObligationMemory {
    side_condition_kinds: Vec<String>,
    artifact_kinds: Vec<String>,
    obligation_haystacks: Vec<String>,
}

fn read_obligation_memory(project_root: &Path, manifest: &MathProjectManifest) -> ObligationMemory {
    let mut memory = ObligationMemory::default();
    for source in &manifest.obligation_sources {
        let path = project_root.join(source);
        let Ok(text) = fs::read_to_string(&path) else {
            continue;
        };
        let Ok(obligation) = serde_json::from_str::<MathObligation>(&text) else {
            continue;
        };
        memory.side_condition_kinds.extend(
            obligation
                .side_conditions
                .iter()
                .map(|condition| side_condition_kind(condition)),
        );
        memory
            .artifact_kinds
            .extend(obligation.artifact_refs.iter().map(artifact_ref_kind));
        if let Some(kind) = obligation.metadata.get("artifact_kind") {
            memory.artifact_kinds.push(kind.clone());
        }
        memory
            .obligation_haystacks
            .push(normalize_signal(&obligation_haystack(&obligation)));
    }
    for evidence in &manifest.evidence {
        let path = project_root.join(evidence);
        let Ok(text) = fs::read_to_string(&path) else {
            continue;
        };
        let Ok(value) = serde_json::from_str::<Value>(&text) else {
            continue;
        };
        if let Some(kind) = value.get("artifact_kind").and_then(Value::as_str) {
            memory.artifact_kinds.push(kind.to_owned());
        }
    }
    memory
        .artifact_kinds
        .extend(manifest.artifact_formats.clone());
    sort_dedup(&mut memory.side_condition_kinds);
    sort_dedup(&mut memory.artifact_kinds);
    memory
}

fn obligation_haystack(obligation: &MathObligation) -> String {
    let mut parts = vec![
        obligation.project.as_str(),
        obligation.domain_profile.as_str(),
        obligation.goal.pretty.as_str(),
        obligation.producer.system.as_str(),
    ];
    for condition in &obligation.side_conditions {
        parts.push(condition.as_str());
    }
    for binding in &obligation.local_context {
        parts.push(binding.name.as_str());
        parts.push(binding.type_pp.as_str());
        if let Some(type_expr) = &binding.type_expr {
            parts.push(type_expr.as_str());
        }
    }
    for (key, value) in &obligation.metadata {
        parts.push(key.as_str());
        parts.push(value.as_str());
    }
    parts.join(" ")
}

fn artifact_ref_kind(artifact: &ArtifactRef) -> String {
    artifact.kind.clone()
}

fn side_condition_kind(condition: &str) -> String {
    let normalized = normalize_signal(condition);
    if normalized.contains("subsum") {
        "subsumption".to_owned()
    } else if normalized.contains("nonnegative") || normalized.contains("multiplier") {
        "nonnegativity".to_owned()
    } else if normalized.contains("linearcombination") || normalized.contains("cancelsvariable") {
        "linear-combination".to_owned()
    } else if normalized.contains("serializedkernel") {
        "serialized-kernel".to_owned()
    } else if normalized.contains("propositional") || normalized.contains("connective") {
        "propositional-fragment".to_owned()
    } else if normalized.contains("degree") {
        "degree-bound".to_owned()
    } else if normalized.contains("size") || normalized.contains("positive") {
        "size-bound".to_owned()
    } else if normalized.contains("family") {
        "family".to_owned()
    } else {
        condition
            .split_whitespace()
            .take(4)
            .map(|part| {
                part.trim_matches(|ch: char| {
                    !(ch.is_ascii_alphanumeric() || ch == '_' || ch == '-')
                })
                .to_ascii_lowercase()
            })
            .filter(|part| !part.is_empty())
            .collect::<Vec<_>>()
            .join("-")
    }
}

fn import_graph(candidates: &[TheoremCandidate]) -> BTreeMap<String, Vec<String>> {
    let mut graph = BTreeMap::<String, Vec<String>>::new();
    for candidate in candidates {
        graph
            .entry(candidate.module.clone())
            .or_default()
            .extend(candidate.imports.clone());
    }
    for imports in graph.values_mut() {
        sort_dedup(imports);
    }
    graph
}

fn candidate_memory(
    candidate: &TheoremCandidate,
    _source_text: &str,
    domain_signals: &CandidateDomainSignals,
    profile: Option<&DomainProfile>,
    obligation_memory: &ObligationMemory,
    import_graph: &BTreeMap<String, Vec<String>>,
    manifest: &MathProjectManifest,
) -> CandidateStructuredMemory {
    let mut normal_form_heads = Vec::new();
    if let Some(head) = &candidate.conclusion_head {
        normal_form_heads.push(head.clone());
    }
    normal_form_heads.extend(domain_signals.semantic_head_matches.clone());
    if let Some(profile) = profile {
        let semantic_heads = profile
            .semantic_heads
            .iter()
            .map(|head| (normalize_signal(head), head.as_str()))
            .collect::<BTreeMap<_, _>>();
        for symbol in &candidate.symbol_refs {
            if let Some(head) = semantic_heads.get(&normalize_signal(symbol)) {
                normal_form_heads.push((*head).to_owned());
            }
        }
    }
    sort_dedup(&mut normal_form_heads);

    let related_obligation = obligation_memory
        .obligation_haystacks
        .iter()
        .any(|haystack| related_memory_haystack(candidate, haystack));
    let side_condition_kinds = if related_obligation || manifest.obligation_sources.len() == 1 {
        obligation_memory.side_condition_kinds.clone()
    } else {
        Vec::new()
    };
    let artifact_kinds = if related_obligation || manifest.obligation_sources.len() == 1 {
        obligation_memory.artifact_kinds.clone()
    } else {
        manifest.artifact_formats.clone()
    };

    let mut direct_imports = candidate.imports.clone();
    sort_dedup(&mut direct_imports);
    let mut import_closure = import_closure(&direct_imports, import_graph);
    sort_dedup(&mut import_closure);
    let direct_only = import_closure == direct_imports;

    CandidateStructuredMemory {
        normal_form_heads,
        side_condition_kinds,
        artifact_kinds,
        direct_imports,
        import_closure,
        direct_only,
    }
}

fn related_memory_haystack(candidate: &TheoremCandidate, obligation_haystack: &str) -> bool {
    let mut tokens = candidate
        .name
        .split(['.', '_', '-'])
        .chain(candidate.symbol_refs.iter().map(String::as_str))
        .chain(candidate.conclusion_head.iter().map(String::as_str))
        .map(normalize_signal)
        .collect::<Vec<_>>();
    tokens.retain(|token| !matches!(token.as_str(), "sound" | "intro" | "true" | "theorem"));
    tokens
        .iter()
        .map(String::as_str)
        .filter(|token| token.len() >= 5)
        .any(|token| obligation_haystack.contains(token))
}

fn import_closure(
    direct_imports: &[String],
    import_graph: &BTreeMap<String, Vec<String>>,
) -> Vec<String> {
    let mut visited = BTreeSet::<String>::new();
    let mut stack = direct_imports.to_vec();
    while let Some(module) = stack.pop() {
        if !visited.insert(module.clone()) {
            continue;
        }
        if let Some(imports) = import_graph.get(&module) {
            stack.extend(imports.iter().cloned());
        }
    }
    visited.into_iter().collect()
}

fn sort_dedup(values: &mut Vec<String>) {
    values.sort();
    values.dedup();
}

fn classify_candidate(
    candidate: &TheoremCandidate,
    manifest: &MathProjectManifest,
    theorem_packs: &BTreeSet<&str>,
    project_imports: &BTreeSet<&str>,
    source_text: &str,
    domain_signals: &CandidateDomainSignals,
) -> CandidateClassification {
    let local = theorem_packs.contains(candidate.source_path.as_str());
    let imported = !local && project_imports.contains(candidate.module.as_str());
    let artifact_derived = manifest
        .evidence
        .iter()
        .any(|path| path == &candidate.source_path)
        || candidate.source_path.starts_with("artifact")
        || candidate.source_path.contains("/artifact")
        || candidate.source_path.contains("artifact_")
        || candidate.source_path.contains("/generated/")
        || source_text.contains("replayed-artifact-linked");
    let project = local || imported;
    let domain = domain_signals.module_match
        || !domain_signals.semantic_head_matches.is_empty()
        || candidate.module_domain_matches(&manifest.domain_profile);
    CandidateClassification {
        scope: candidate_scope(local, project, domain, imported, artifact_derived).to_owned(),
        local,
        project,
        domain,
        imported,
        artifact_derived,
    }
}

fn candidate_scope(
    local: bool,
    project: bool,
    domain: bool,
    imported: bool,
    artifact_derived: bool,
) -> &'static str {
    if artifact_derived {
        "artifact_derived"
    } else if local {
        "local"
    } else if imported {
        "imported"
    } else if project {
        "project"
    } else if domain {
        "domain"
    } else {
        "external"
    }
}

fn domain_signals(
    candidate: &TheoremCandidate,
    source_text: &str,
    manifest: &MathProjectManifest,
    profile: Option<&DomainProfile>,
) -> CandidateDomainSignals {
    let haystack = normalized_haystack(candidate, source_text);
    let semantic_head_matches = profile
        .map(|profile| matching_profile_items(&profile.semantic_heads, &haystack))
        .unwrap_or_default();
    let ranking_signal_matches = profile
        .map(|profile| ranking_signal_matches(candidate, source_text, profile, &haystack))
        .unwrap_or_default();

    CandidateDomainSignals {
        profile: manifest.domain_profile.clone(),
        module_match: candidate.module_domain_matches(&manifest.domain_profile),
        semantic_head_matches,
        ranking_signal_matches,
    }
}

fn normalized_haystack(candidate: &TheoremCandidate, source_text: &str) -> String {
    let mut parts = Vec::new();
    parts.push(candidate.name.as_str());
    parts.push(candidate.module.as_str());
    parts.push(candidate.source_path.as_str());
    if let Some(head) = &candidate.conclusion_head {
        parts.push(head.as_str());
    }
    parts.extend(candidate.symbol_refs.iter().map(String::as_str));
    parts.push(source_text);
    normalize_signal(&parts.join(" "))
}

fn matching_profile_items(items: &[String], haystack: &str) -> Vec<String> {
    items
        .iter()
        .filter(|item| haystack.contains(&normalize_signal(item)))
        .cloned()
        .collect()
}

fn ranking_signal_matches(
    candidate: &TheoremCandidate,
    source_text: &str,
    profile: &DomainProfile,
    haystack: &str,
) -> Vec<String> {
    profile
        .ranking_signals
        .iter()
        .filter(|signal| ranking_signal_matches_candidate(signal, candidate, source_text, haystack))
        .cloned()
        .collect()
}

fn ranking_signal_matches_candidate(
    signal: &str,
    candidate: &TheoremCandidate,
    source_text: &str,
    haystack: &str,
) -> bool {
    match signal {
        "artifact_kind" => source_text.contains("replayed-artifact-linked"),
        "bound_tightness" => haystack.contains("bound") || haystack.contains("tightness"),
        "conclusion_head" => candidate.conclusion_head.is_some(),
        "relu_stability" => haystack.contains("relu") || haystack.contains("stability"),
        "trust_blocker" => candidate_trust_debt(&candidate.trust).next().is_some(),
        other => haystack.contains(&normalize_signal(other)),
    }
}

fn normalize_signal(value: &str) -> String {
    value
        .chars()
        .filter(|ch| ch.is_ascii_alphanumeric())
        .flat_map(char::to_lowercase)
        .collect()
}

fn theorem_memory(candidates: &[ProjectTheoremCandidate]) -> MathTheoremMemory {
    MathTheoremMemory {
        candidate_count: candidates.len(),
        local_count: candidates
            .iter()
            .filter(|candidate| candidate.classification.local)
            .count(),
        project_count: candidates
            .iter()
            .filter(|candidate| candidate.classification.project)
            .count(),
        domain_count: candidates
            .iter()
            .filter(|candidate| candidate.classification.domain)
            .count(),
        imported_count: candidates
            .iter()
            .filter(|candidate| candidate.classification.imported)
            .count(),
        artifact_derived_count: candidates
            .iter()
            .filter(|candidate| candidate.classification.artifact_derived)
            .count(),
        trust_policy_conforming_count: candidates
            .iter()
            .filter(|candidate| candidate.trust_decision.promotion_allowed)
            .count(),
    }
}

trait CandidateDomain {
    fn module_domain_matches(&self, domain_profile: &str) -> bool;
}

impl CandidateDomain for TheoremCandidate {
    fn module_domain_matches(&self, domain_profile: &str) -> bool {
        let normalized_domain = domain_profile.replace('-', "").to_ascii_lowercase();
        let normalized_module = self
            .module
            .replace(['_', '-', '.'], "")
            .to_ascii_lowercase();
        normalized_module.contains(&normalized_domain)
    }
}

fn trust_decision(
    candidate: &TheoremCandidate,
    classification: &CandidateClassification,
    trust_policy: &TrustPolicy,
) -> CandidateTrustDecision {
    let mut reasons = trust_policy_blockers(&candidate.name, &candidate.trust, trust_policy);
    if classification.artifact_derived && trust_policy.require_artifact_replay {
        reasons.push(
            "artifact-derived candidate requires replay evidence before promotion".to_owned(),
        );
    }
    let promotion_allowed = reasons.is_empty();

    CandidateTrustDecision {
        policy: trust_policy.name.clone(),
        conformance: if promotion_allowed {
            "conforming".to_owned()
        } else {
            "blocked".to_owned()
        },
        kernel_proof_status: "not_claimed".to_owned(),
        trust_debt: candidate_trust_debt(&candidate.trust).collect(),
        promotion_allowed,
        reasons,
    }
}

fn candidate_trust_debt(trust: &TrustRecord) -> impl Iterator<Item = String> + '_ {
    let mut labels = Vec::new();
    if trust.explicit_sorry {
        labels.push("explicit_sorry".to_owned());
    }
    if trust.synthetic_sorry {
        labels.push("synthetic_sorry".to_owned());
    }
    if trust.trusted_arith > 0 {
        labels.push(format!("trusted_arith:{}", trust.trusted_arith));
    }
    if trust.trusted_ay > 0 {
        labels.push(format!("trusted_ay:{}", trust.trusted_ay));
    }
    if trust.unsafe_declaration {
        labels.push("unsafe".to_owned());
    }
    if trust.axiom_declaration {
        labels.push("axiom".to_owned());
    }
    labels.into_iter()
}

fn trust_policy_blockers(
    candidate_name: &str,
    trust: &TrustRecord,
    trust_policy: &TrustPolicy,
) -> Vec<String> {
    let forbidden = trust_policy
        .forbidden_trust_markers
        .iter()
        .map(|marker| marker.as_str())
        .collect::<BTreeSet<_>>();
    let mut blockers = Vec::new();

    if trust.explicit_sorry && forbidden.contains("sorry") {
        blockers.push("explicit sorry is forbidden by trust policy".to_owned());
    }
    if trust.synthetic_sorry
        && (forbidden.contains("synthetic_sorry") || forbidden.contains("sorryAx"))
    {
        blockers.push("synthetic sorry is forbidden by trust policy".to_owned());
    }
    if trust.trusted_arith > 0
        && (forbidden.contains("trustedArith") || forbidden.contains("trusted_arith"))
    {
        blockers.push("trustedArith is forbidden by trust policy".to_owned());
    }
    if trust.trusted_ay > 0 && (forbidden.contains("trustedAy") || forbidden.contains("trusted_ay"))
    {
        blockers.push("trustedAy is forbidden by trust policy".to_owned());
    }
    if trust.unsafe_declaration && forbidden.contains("unsafe") {
        blockers.push("unsafe declaration is forbidden by trust policy".to_owned());
    }
    if trust.axiom_declaration && !axiom_allowed(candidate_name, trust_policy) {
        blockers.push("axiom declaration is not allowed by trust policy".to_owned());
    }

    blockers
}

fn axiom_allowed(candidate_name: &str, trust_policy: &TrustPolicy) -> bool {
    trust_policy
        .allowed_axioms
        .iter()
        .any(|allowed| allowed == "*" || allowed == candidate_name)
}
