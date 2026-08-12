// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared model for `clean math` project manifests and obligations.

pub mod task_lifecycle;
pub mod theorem_index;

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::ops::Deref;
use std::path::{Path, PathBuf};

use clean_kernel::Expr;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_json::Value;
use sha2::{Digest, Sha256};

pub const MATH_PROJECT_SCHEMA_VERSION: &str = "clean-math-project-v1";
pub const DOMAIN_PROFILE_SCHEMA_VERSION: &str = "clean-domain-profile-v1";
pub const OBLIGATION_SCHEMA_VERSION: &str = "clean-obligation-v1";
pub const STATUS_SCHEMA_VERSION: &str = "clean-math-project-status-v1";
pub const HYGIENE_SCHEMA_VERSION: &str = "clean-math-project-hygiene-v1";
pub const OBLIGATION_REPORT_SCHEMA_VERSION: &str = "clean-obligation-report-v1";
pub const OPEN_OBLIGATION_SCHEMA_VERSION: &str = "clean-open-obligation-report-v1";
pub const ARTIFACT_REPLAY_SCHEMA_VERSION: &str = "clean-artifact-replay-report-v1";
pub const ARTIFACT_REPLAY_REGISTRY_SCHEMA_VERSION: &str = "clean-artifact-replay-registry-v1";
pub const CERTIFICATE_SCHEMA_VERSION: &str = "clean-math-certificate-v1";
pub const KERNEL_PROOF_EVIDENCE_SCHEMA_VERSION: &str = "clean-math-kernel-evidence-v1";
pub const PROOF_FAILURE_DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION: &str =
    "clean-math-proof-failure-diagnostic-v1";
pub const ISSUE_PLAN_SCHEMA_VERSION: &str = "clean-math-issue-plan-v2";
pub const DASHBOARD_SCHEMA_VERSION: &str = "clean-math-project-dashboard-v1";
pub const REPLAY_CACHE_INDEX_SCHEMA_VERSION: &str = "clean-artifact-replay-cache-index-v1";
pub const REPLAY_CACHE_ROOTS_SCHEMA_VERSION: &str = "clean-artifact-replay-cache-roots-v1";
pub const DEFAULT_REPLAY_CACHE_ROOT: &str = ".clean/replay-cache";
const THEOREM_PACK_TRUST_MARKERS: &[&str] = &[
    "sorry",
    "sorryAx",
    "synthetic_sorry",
    "trustedArith",
    "trustedAy",
    "replayed-artifact-linked",
];
const PRETTY_ONLY_TRUST_MARKERS: &[&str] = &[
    "sorryAx",
    "synthetic_sorry",
    "trustedArith",
    "trustedAy",
    "replayed-artifact-linked",
];

#[derive(Debug, thiserror::Error)]
pub enum MathProjectError {
    #[error("math project I/O error at {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("math project JSON error at {path}: {source}")]
    Json {
        path: PathBuf,
        #[source]
        source: serde_json::Error,
    },
    #[error("unknown math domain profile `{0}`")]
    UnknownDomain(String),
    #[error("math project validation failed: {0}")]
    Validation(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MathProjectManifest {
    pub schema_version: String,
    pub project: String,
    pub domain_profile: String,
    pub owner: String,
    #[serde(default)]
    pub theorem_packs: Vec<String>,
    #[serde(default)]
    pub obligation_sources: Vec<String>,
    #[serde(default)]
    pub artifact_formats: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub certificate_extractors: Vec<String>,
    pub trust_policy: TrustPolicy,
    #[serde(default)]
    pub normalizers: Vec<String>,
    #[serde(default)]
    pub evidence: Vec<String>,
    #[serde(default)]
    pub issue_routing: IssueRouting,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TrustPolicy {
    pub name: String,
    #[serde(default)]
    pub allowed_axioms: Vec<String>,
    #[serde(default)]
    pub forbidden_trust_markers: Vec<String>,
    #[serde(default)]
    pub require_artifact_replay: bool,
    #[serde(default)]
    pub allow_synthetic_sorry: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IssueRouting {
    #[serde(default)]
    pub labels: Vec<String>,
    #[serde(default)]
    pub owners: Vec<String>,
    #[serde(default)]
    pub blocking_categories: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DomainProfile {
    pub schema_version: String,
    pub name: String,
    pub description: String,
    pub semantic_heads: Vec<String>,
    pub normalizers: Vec<String>,
    pub tactic_recommendations: Vec<String>,
    pub artifact_formats: Vec<String>,
    #[serde(default)]
    pub artifact_replay_adapters: Vec<ArtifactReplayAdapterDescriptor>,
    pub certificate_extractors: Vec<String>,
    pub ranking_signals: Vec<String>,
    pub blocker_kinds: Vec<String>,
}

impl DomainProfile {
    pub fn tactic_normalizer_plan(&self) -> DomainTacticNormalizerPlan {
        tactic_normalizer_plan(self)
    }

    pub fn artifact_replay_registry(&self) -> ArtifactReplayAdapterRegistry {
        artifact_replay_registry(self)
    }

    pub fn replay_adapter_for_artifact_kind(
        &self,
        artifact_kind: &str,
    ) -> Option<&ArtifactReplayAdapterDescriptor> {
        self.artifact_replay_adapters
            .iter()
            .find(|adapter| adapter.matches_artifact_kind(artifact_kind))
    }

    pub fn replay_adapters_for_artifact_format(
        &self,
        artifact_format: &str,
    ) -> Vec<&ArtifactReplayAdapterDescriptor> {
        self.artifact_replay_adapters
            .iter()
            .filter(|adapter| adapter.matches_artifact_format(artifact_format))
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactReplayAdapterRegistry {
    pub schema_version: String,
    pub domain_profile: String,
    pub adapters: Vec<ArtifactReplayAdapterDescriptor>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactReplayAdapterDescriptor {
    pub id: String,
    pub label: String,
    pub domain_profile: String,
    pub source_systems: Vec<String>,
    pub artifact_formats: Vec<String>,
    pub artifact_kinds: Vec<String>,
    pub replay_contract: String,
    pub availability: ArtifactReplayAdapterAvailability,
    pub trust: ArtifactReplayAdapterTrust,
    pub status: ArtifactReplayAdapterStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArtifactReplayDispatchDescriptor {
    pub adapter_id: &'static str,
    pub domain_profile: &'static str,
    pub source_system: &'static str,
    pub artifact_kind: &'static str,
    pub artifact_format: &'static str,
}

impl ArtifactReplayAdapterDescriptor {
    pub fn matches_artifact_kind(&self, artifact_kind: &str) -> bool {
        self.artifact_kinds.iter().any(|kind| kind == artifact_kind)
    }

    pub fn matches_artifact_format(&self, artifact_format: &str) -> bool {
        self.artifact_formats
            .iter()
            .any(|format| format == artifact_format)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactReplayAdapterAvailability {
    pub source: String,
    pub executor: String,
    pub requires_external_tool: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub feature_gate: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactReplayAdapterTrust {
    pub evidence_kind: String,
    pub kernel_certified: bool,
    pub allowed_trusted_assumptions: Vec<String>,
    pub requires_envelope_validation: bool,
    pub requires_problem_hash: bool,
    pub links_obligation_fingerprint: bool,
    pub required_report_fields: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactReplayAdapterStatus {
    pub phase: String,
    pub lifecycle: String,
    pub blocker_kind: String,
    pub report_schema_version: String,
    pub replay_status_values: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DomainTacticNormalizerPlan {
    pub schema_version: String,
    pub domain_profile: String,
    pub normalizers: Vec<NormalizerDescriptor>,
    pub tactic_recommendations: Vec<TacticDescriptor>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NormalizerDescriptor {
    pub name: String,
    pub rank: usize,
    pub source: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TacticDescriptor {
    pub name: String,
    pub rank: usize,
    pub source: String,
    pub uses_profile_normalizer: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MathObligation {
    pub schema_version: String,
    pub project: String,
    pub domain_profile: String,
    pub producer: ObligationProducer,
    pub goal: ObligationGoal,
    #[serde(default)]
    pub local_context: Vec<ObligationBinding>,
    #[serde(default)]
    pub side_conditions: Vec<String>,
    #[serde(default)]
    pub artifact_refs: Vec<ArtifactRef>,
    #[serde(default)]
    pub metadata: BTreeMap<String, String>,
    pub trust_policy: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ObligationProducer {
    pub system: String,
    pub commit: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub command: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ObligationGoal {
    pub expr: GoalExpr,
    pub pretty: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GoalExpr {
    PrettyOrSerializedString {
        raw: String,
        canonical_kernel_json: Option<String>,
    },
    SerializedKernelExpr {
        expr: Expr,
        canonical_json: String,
    },
}

impl GoalExpr {
    pub fn string(value: impl Into<String>) -> Self {
        let raw = value.into();
        let canonical_kernel_json = canonical_kernel_expr_json_from_str(&raw);
        GoalExpr::PrettyOrSerializedString {
            raw,
            canonical_kernel_json,
        }
    }

    fn canonical_fingerprint_payload(&self) -> &str {
        match self {
            GoalExpr::PrettyOrSerializedString {
                raw,
                canonical_kernel_json,
            } => canonical_kernel_json.as_deref().unwrap_or(raw),
            GoalExpr::SerializedKernelExpr { canonical_json, .. } => canonical_json,
        }
    }
}

impl Deref for GoalExpr {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.canonical_fingerprint_payload()
    }
}

impl Serialize for GoalExpr {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            GoalExpr::PrettyOrSerializedString { raw, .. } => serializer.serialize_str(raw),
            GoalExpr::SerializedKernelExpr { expr, .. } => expr.serialize(serializer),
        }
    }
}

impl<'de> Deserialize<'de> for GoalExpr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = Value::deserialize(deserializer)?;
        match value {
            Value::String(value) => Ok(GoalExpr::string(value)),
            value => {
                let expr = Expr::deserialize(value.clone()).map_err(serde::de::Error::custom)?;
                let canonical_json =
                    serde_json::to_string(&expr).map_err(serde::de::Error::custom)?;
                Ok(GoalExpr::SerializedKernelExpr {
                    expr,
                    canonical_json,
                })
            }
        }
    }
}

fn canonical_kernel_expr_json_from_str(value: &str) -> Option<String> {
    serde_json::from_str::<Expr>(value)
        .ok()
        .and_then(|expr| serde_json::to_string(&expr).ok())
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ObligationBinding {
    pub name: String,
    pub type_pp: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub type_expr: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactRef {
    pub kind: String,
    pub path: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hash: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct CanonicalObligationFingerprintInput {
    domain_profile: String,
    goal: CanonicalObligationGoal,
    local_context: Vec<CanonicalObligationBinding>,
    side_conditions: Vec<String>,
    artifact_refs: Vec<CanonicalArtifactRef>,
    trust_policy: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct CanonicalObligationGoal {
    expr: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct CanonicalObligationBinding {
    name: String,
    type_identity: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct CanonicalArtifactRef {
    kind: String,
    hash: Option<String>,
    path: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ValidationViolation {
    pub code: &'static str,
    pub severity: &'static str,
    pub path: String,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ArtifactReplayDiagnostic {
    pub code: &'static str,
    pub severity: &'static str,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MathProjectStatusReport {
    pub schema_version: &'static str,
    pub project_path: String,
    pub project_root: String,
    pub project: String,
    pub domain_profile: String,
    pub owner: String,
    pub status: &'static str,
    pub theorem_packs: usize,
    pub obligation_sources: usize,
    pub artifact_formats: Vec<String>,
    pub certificate_extractors: Vec<String>,
    pub normalizers: Vec<String>,
    pub evidence: Vec<String>,
    pub replay_cache: ReplayCacheSummary,
    pub trust_policy: TrustPolicy,
    pub violations: Vec<ValidationViolation>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ObligationValidationReport {
    pub schema_version: &'static str,
    pub path: String,
    pub project: String,
    pub domain_profile: String,
    pub fingerprint: String,
    pub status: &'static str,
    pub artifact_refs: Vec<ArtifactRef>,
    pub violations: Vec<ValidationViolation>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct OpenObligationReport {
    pub schema_version: &'static str,
    pub project: String,
    pub domain_profile: String,
    pub obligation_fingerprint: String,
    pub state_id: String,
    pub persistence: &'static str,
    pub status: &'static str,
    pub warnings: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ArtifactReplayReport {
    pub schema_version: &'static str,
    pub artifact_path: String,
    pub project: Option<String>,
    pub source_system: String,
    pub artifact_kind: String,
    pub problem_hash: String,
    pub proof_hash: String,
    pub certificate_format: String,
    pub evidence_kind: &'static str,
    pub kernel_certified: bool,
    pub replay_status: &'static str,
    pub replay_adapter: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub adapter_descriptor_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub adapter_lifecycle: Option<String>,
    pub linked_obligations: Vec<String>,
    pub trusted_assumptions: Vec<String>,
    pub details: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<ArtifactReplayDiagnostic>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cache: Option<ReplayCacheWrite>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ReplayCacheWrite {
    pub cache_dir: String,
    pub index_path: String,
    pub report_path: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReplayCacheRoots {
    pub schema_version: String,
    pub project: String,
    pub roots: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReplayCacheIndex {
    pub schema_version: String,
    pub project: String,
    pub project_root: String,
    pub reports: Vec<ReplayCacheEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReplayCacheEntry {
    pub report_path: String,
    pub artifact_path: String,
    pub proof_hash: String,
    pub replay_status: String,
    pub replay_adapter: String,
    pub linked_obligations: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct ReplayCacheSummary {
    pub roots: Vec<String>,
    pub cached_reports: usize,
    pub pass: usize,
    pub fail: usize,
    pub blocked: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MathProjectDashboardReport {
    pub schema_version: &'static str,
    pub project: String,
    pub project_root: String,
    pub status: &'static str,
    pub obligations: DashboardObligations,
    pub replay: DashboardReplay,
    pub hygiene: DashboardHygiene,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DashboardObligations {
    pub total: usize,
    pub with_artifacts: usize,
    pub invalid: usize,
    pub fingerprints: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DashboardReplay {
    pub cache_roots: Vec<String>,
    pub cached_reports: usize,
    pub pass: usize,
    pub fail: usize,
    pub blocked: usize,
    pub missing_artifact_replay: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DashboardHygiene {
    pub status: &'static str,
    pub blockers: Vec<ValidationViolation>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertificateSummary {
    pub schema: &'static str,
    pub project: String,
    pub domain_profile: String,
    pub theorem: String,
    pub obligation: String,
    pub artifact: Option<String>,
    pub direction: String,
    pub proof_status: String,
    pub evidence_kind: String,
    pub kernel_certified: bool,
    pub trust_policy: String,
    pub synthetic_sorry: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kernel_evidence: Option<KernelProofEvidence>,
    pub trust_summary: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct KernelProofEvidence {
    pub theorem: String,
    pub proof_hash: String,
    pub checker: String,
    pub source: String,
    pub checked: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofFailureDiagnosticEvidence {
    pub schema_version: String,
    pub obligation_fingerprint: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub evidence_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub run_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub observed_at: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub summary: Option<String>,
    #[serde(default)]
    pub blockers: Vec<String>,
    #[serde(default)]
    pub ranking_signals: Vec<String>,
    #[serde(default)]
    pub score_delta: i64,
    #[serde(default)]
    pub reproduction: IssuePlanReproduction,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct HygieneReport {
    pub schema_version: &'static str,
    pub project: String,
    pub status: &'static str,
    pub gate: HygieneGate,
    pub checks: Vec<HygieneCheck>,
    pub violations: Vec<ValidationViolation>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct HygieneGate {
    pub command: String,
    pub pass_status: &'static str,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct HygieneCheck {
    pub name: &'static str,
    pub status: &'static str,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct IssuePlanReport {
    pub schema_version: &'static str,
    pub project: String,
    pub domain_profile: String,
    pub filing_guidance: IssuePlanFilingGuidance,
    pub phases: Vec<IssuePlanPhase>,
    pub workstreams: Vec<IssuePlanWorkstream>,
    pub rows: Vec<IssuePlanRow>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct IssuePlanFilingGuidance {
    pub rule: &'static str,
    pub grouping: Vec<&'static str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct IssuePlanPhase {
    pub id: &'static str,
    pub title: &'static str,
    pub row_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct IssuePlanWorkstream {
    pub id: String,
    pub title: String,
    pub row_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct IssuePlanRow {
    pub filing_key: String,
    pub dedupe_key: String,
    pub dedupe_status: String,
    pub ranking: IssuePlanRankingSignals,
    pub phase: &'static str,
    pub phase_title: &'static str,
    pub workstream: String,
    pub title: String,
    pub priority: &'static str,
    pub scope: String,
    pub files: Vec<String>,
    pub labels: Vec<String>,
    pub owners: Vec<String>,
    pub blocking_categories: Vec<String>,
    pub filing_metadata: IssuePlanFilingMetadata,
    pub dependencies: Vec<String>,
    pub acceptance: Vec<String>,
    pub verification_command: String,
    pub issue_body: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IssuePlanFilingMetadata {
    pub labels: Vec<String>,
    pub owner: Option<String>,
    pub blockers: Vec<String>,
    pub reproduction: IssuePlanReproduction,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IssuePlanReproduction {
    pub commands: Vec<String>,
    pub files: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IssuePlanRankingSignals {
    pub rank: usize,
    pub score: i64,
    pub domain_profile: String,
    pub artifact_kinds: Vec<String>,
    pub replay_status: String,
    pub replay_cache_present: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub benchmark: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub benchmark_family: Option<String>,
    pub proof_gap: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub proof_failure_diagnostics: Vec<String>,
    pub signals: Vec<String>,
}

pub fn load_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, MathProjectError> {
    let contents = fs::read_to_string(path).map_err(|source| MathProjectError::Io {
        path: path.to_owned(),
        source,
    })?;
    serde_json::from_str(&contents).map_err(|source| MathProjectError::Json {
        path: path.to_owned(),
        source,
    })
}

pub fn write_json<T: Serialize>(path: &Path, value: &T) -> Result<(), MathProjectError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|source| MathProjectError::Io {
            path: parent.to_owned(),
            source,
        })?;
    }
    let contents =
        serde_json::to_string_pretty(value).map_err(|source| MathProjectError::Json {
            path: path.to_owned(),
            source,
        })?;
    fs::write(path, format!("{contents}\n")).map_err(|source| MathProjectError::Io {
        path: path.to_owned(),
        source,
    })
}

pub fn load_project(path: &Path) -> Result<MathProjectManifest, MathProjectError> {
    load_json(path)
}

pub fn resolve_project_path(path: &Path) -> PathBuf {
    if path.is_dir() {
        path.join("math-project.json")
    } else {
        path.to_owned()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DomainProfileRegistry {
    root: PathBuf,
}

impl DomainProfileRegistry {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    pub fn for_project_path(project_path: &Path) -> Self {
        Self::new(project_path.parent().unwrap_or_else(|| Path::new(".")))
    }

    pub fn profile(&self, domain: &str) -> Result<DomainProfile, MathProjectError> {
        if let Ok(profile) = built_in_profile(domain) {
            return Ok(profile);
        }
        self.local_profile(domain)
    }

    pub fn local_profile_path(&self, domain: &str) -> Option<PathBuf> {
        domain_profile_file_name(domain).map(|file_name| {
            self.root
                .join("domain_profiles")
                .join(format!("{file_name}.json"))
        })
    }

    fn local_profile(&self, domain: &str) -> Result<DomainProfile, MathProjectError> {
        let Some(path) = self.local_profile_path(domain) else {
            return Err(MathProjectError::UnknownDomain(domain.to_owned()));
        };
        if !path.exists() {
            return Err(MathProjectError::UnknownDomain(domain.to_owned()));
        }
        let profile = load_json::<DomainProfile>(&path)?;
        validate_loaded_domain_profile(&profile, domain).map_err(MathProjectError::Validation)?;
        Ok(profile)
    }
}

pub fn project_domain_profile(
    project_path: &Path,
    domain: &str,
) -> Result<DomainProfile, MathProjectError> {
    DomainProfileRegistry::for_project_path(project_path).profile(domain)
}

fn domain_profile_file_name(domain: &str) -> Option<&str> {
    if domain.trim() != domain || domain.is_empty() || domain == "." || domain == ".." {
        return None;
    }
    if domain
        .chars()
        .all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit() || ch == '-' || ch == '_')
    {
        Some(domain)
    } else {
        None
    }
}

fn validate_loaded_domain_profile(
    profile: &DomainProfile,
    expected_name: &str,
) -> Result<(), String> {
    let mut errors = Vec::new();
    if profile.schema_version != DOMAIN_PROFILE_SCHEMA_VERSION {
        errors.push(format!(
            "schema_version must be `{DOMAIN_PROFILE_SCHEMA_VERSION}`, got `{}`",
            profile.schema_version
        ));
    }
    if profile.name != expected_name {
        errors.push(format!(
            "name `{}` must match requested domain profile `{expected_name}`",
            profile.name
        ));
    }
    validate_profile_string_field("name", &profile.name, &mut errors);
    validate_profile_string_field("description", &profile.description, &mut errors);
    validate_profile_string_list("semantic_heads", &profile.semantic_heads, &mut errors);
    validate_profile_string_list("normalizers", &profile.normalizers, &mut errors);
    validate_profile_string_list(
        "tactic_recommendations",
        &profile.tactic_recommendations,
        &mut errors,
    );
    validate_profile_string_list("artifact_formats", &profile.artifact_formats, &mut errors);
    validate_profile_string_list(
        "certificate_extractors",
        &profile.certificate_extractors,
        &mut errors,
    );
    validate_profile_string_list("ranking_signals", &profile.ranking_signals, &mut errors);
    validate_profile_string_list("blocker_kinds", &profile.blocker_kinds, &mut errors);
    validate_profile_replay_adapters(profile, &mut errors);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.join("; "))
    }
}

fn validate_profile_string_field(path: &str, value: &str, errors: &mut Vec<String>) {
    if value.trim().is_empty() {
        errors.push(format!("{path} must not be empty"));
    } else if value.trim() != value {
        errors.push(format!(
            "{path} `{value}` must not have surrounding whitespace"
        ));
    }
}

fn validate_profile_string_list(path: &str, values: &[String], errors: &mut Vec<String>) {
    let mut seen = BTreeSet::new();
    for (idx, value) in values.iter().enumerate() {
        let item_path = format!("{path}[{idx}]");
        validate_profile_string_field(&item_path, value, errors);
        if !seen.insert(value.as_str()) {
            errors.push(format!("{item_path} `{value}` is duplicated"));
        }
    }
}

fn validate_profile_replay_adapters(profile: &DomainProfile, errors: &mut Vec<String>) {
    let mut seen = BTreeSet::new();
    for (idx, adapter) in profile.artifact_replay_adapters.iter().enumerate() {
        let path = format!("artifact_replay_adapters[{idx}]");
        validate_profile_string_field(&format!("{path}.id"), &adapter.id, errors);
        validate_profile_string_field(&format!("{path}.label"), &adapter.label, errors);
        if !seen.insert(adapter.id.as_str()) {
            errors.push(format!("{path}.id `{}` is duplicated", adapter.id));
        }
        if adapter.domain_profile != profile.name {
            errors.push(format!(
                "{path}.domain_profile `{}` must match profile `{}`",
                adapter.domain_profile, profile.name
            ));
        }
        validate_profile_string_list(
            &format!("{path}.source_systems"),
            &adapter.source_systems,
            errors,
        );
        validate_profile_string_list(
            &format!("{path}.artifact_formats"),
            &adapter.artifact_formats,
            errors,
        );
        validate_profile_string_list(
            &format!("{path}.artifact_kinds"),
            &adapter.artifact_kinds,
            errors,
        );
        validate_profile_string_field(
            &format!("{path}.replay_contract"),
            &adapter.replay_contract,
            errors,
        );
        validate_profile_string_field(
            &format!("{path}.availability.source"),
            &adapter.availability.source,
            errors,
        );
        validate_profile_string_field(
            &format!("{path}.availability.executor"),
            &adapter.availability.executor,
            errors,
        );
        validate_profile_string_field(
            &format!("{path}.trust.evidence_kind"),
            &adapter.trust.evidence_kind,
            errors,
        );
        validate_profile_string_list(
            &format!("{path}.trust.required_report_fields"),
            &adapter.trust.required_report_fields,
            errors,
        );
        validate_profile_string_field(
            &format!("{path}.status.phase"),
            &adapter.status.phase,
            errors,
        );
        validate_profile_string_field(
            &format!("{path}.status.lifecycle"),
            &adapter.status.lifecycle,
            errors,
        );
        if adapter.status.report_schema_version != ARTIFACT_REPLAY_SCHEMA_VERSION {
            errors.push(format!(
                "{path}.status.report_schema_version must be `{ARTIFACT_REPLAY_SCHEMA_VERSION}`"
            ));
        }
        validate_profile_string_list(
            &format!("{path}.status.replay_status_values"),
            &adapter.status.replay_status_values,
            errors,
        );
        if adapter.status.lifecycle != "planned"
            && !adapter_has_matching_executable_dispatch(profile, adapter)
        {
            errors.push(format!(
                "{path}.id `{}` declares lifecycle `{}` but no matching executable replay dispatch is wired",
                adapter.id, adapter.status.lifecycle
            ));
        }
    }
}

fn adapter_has_matching_executable_dispatch(
    profile: &DomainProfile,
    adapter: &ArtifactReplayAdapterDescriptor,
) -> bool {
    executable_replay_dispatch_descriptors()
        .iter()
        .any(|dispatch| {
            dispatch.adapter_id == adapter.id
                && dispatch.domain_profile == profile.name
                && adapter
                    .source_systems
                    .iter()
                    .any(|source| source == dispatch.source_system)
                && adapter.matches_artifact_kind(dispatch.artifact_kind)
                && adapter.matches_artifact_format(dispatch.artifact_format)
        })
}

pub fn built_in_profile(domain: &str) -> Result<DomainProfile, MathProjectError> {
    let profile = match domain {
        "sat-pb" => DomainProfile {
            schema_version: DOMAIN_PROFILE_SCHEMA_VERSION.to_owned(),
            name: "sat-pb".to_owned(),
            description: "SAT, pseudo-Boolean, cardinality, LRAT/DRAT/VeriPB, and Ay theorem-export obligations".to_owned(),
            semantic_heads: strings(&[
                "CNF",
                "Clause",
                "Literal",
                "Assignment",
                "PBConstraint",
                "Cardinality",
                "Resolution",
                "Subsumption",
            ]),
            normalizers: strings(&["cert_simp", "cert_mathverse", "sat_pb_nf"]),
            tactic_recommendations: strings(&["cert_simp", "cert_mathverse", "simp", "mathverse"]),
            artifact_formats: strings(&[
                "lrat",
                "drat",
                "veripb",
                "ay-theorem-export",
                "ay-alethe-envelope-v1",
                "proof-artifact-v1",
            ]),
            artifact_replay_adapters: sat_pb_replay_adapters(),
            certificate_extractors: strings(&["sat-pb-certificate-summary-v1"]),
            ranking_signals: strings(&[
                "artifact_kind",
                "conclusion_head",
                "missing_rewrite",
                "trust_blocker",
            ]),
            blocker_kinds: strings(&["missing-theorem", "artifact-replay", "trust-policy", "normalizer-gap"]),
        },
        "nn-verify" => DomainProfile {
            schema_version: DOMAIN_PROFILE_SCHEMA_VERSION.to_owned(),
            name: "nn-verify".to_owned(),
            description: "Neural-network verification obligations for intervals, CROWN, Farkas certificates, and Gamma-Crown artifacts".to_owned(),
            semantic_heads: strings(&[
                "Interval",
                "AffineForm",
                "Zonotope",
                "IBP",
                "CROWN",
                "LayerNorm",
                "ReLU",
                "ExternalFarkasCert",
            ]),
            normalizers: strings(&["cert_simp", "cert_mathverse", "nn_interval_nf"]),
            tactic_recommendations: strings(&["cert_simp", "cert_mathverse", "linarith", "simp"]),
            artifact_formats: strings(&[
                "gamma-crown-farkas-v1",
                "gamma-crown-linear-entailment-v1",
                "proof-artifact-v1",
            ]),
            artifact_replay_adapters: nn_verify_replay_adapters(),
            certificate_extractors: strings(&["nn-verify-certificate-summary-v1"]),
            ranking_signals: strings(&[
                "artifact_kind",
                "relu_stability",
                "bound_tightness",
                "trust_blocker",
            ]),
            blocker_kinds: strings(&["carrier-theorem", "artifact-replay", "trust-policy", "interval-gap"]),
        },
        "proof-complexity" => DomainProfile {
            schema_version: DOMAIN_PROFILE_SCHEMA_VERSION.to_owned(),
            name: "proof-complexity".to_owned(),
            description: "Resolution, cutting planes, GF(2), polynomial calculus, and lower-bound family obligations".to_owned(),
            semantic_heads: strings(&[
                "Resolution",
                "CuttingPlanes",
                "PolynomialCalculus",
                "FourierBoolean",
                "LowerBoundFamily",
            ]),
            normalizers: strings(&["cert_simp", "proof_complexity_nf"]),
            tactic_recommendations: strings(&["cert_simp", "simp", "mathverse"]),
            artifact_formats: strings(&["proof-artifact-v1"]),
            artifact_replay_adapters: Vec::new(),
            certificate_extractors: strings(&["proof-complexity-certificate-summary-v1"]),
            ranking_signals: strings(&["family", "degree", "size", "missing_combinatorial_lemma"]),
            blocker_kinds: strings(&["missing-family-theorem", "trust-policy", "normalizer-gap"]),
        },
        other => return Err(MathProjectError::UnknownDomain(other.to_owned())),
    };
    Ok(profile)
}

pub fn built_in_artifact_replay_registry(
    domain: &str,
) -> Result<ArtifactReplayAdapterRegistry, MathProjectError> {
    Ok(built_in_profile(domain)?.artifact_replay_registry())
}

pub fn artifact_replay_registry(profile: &DomainProfile) -> ArtifactReplayAdapterRegistry {
    ArtifactReplayAdapterRegistry {
        schema_version: ARTIFACT_REPLAY_REGISTRY_SCHEMA_VERSION.to_owned(),
        domain_profile: profile.name.clone(),
        adapters: profile.artifact_replay_adapters.clone(),
    }
}

pub fn executable_replay_dispatch_descriptors() -> &'static [ArtifactReplayDispatchDescriptor] {
    &[
        ArtifactReplayDispatchDescriptor {
            adapter_id: "sat-pb-drat-v1",
            domain_profile: "sat-pb",
            source_system: "sat-pb",
            artifact_kind: "drat",
            artifact_format: "drat",
        },
        ArtifactReplayDispatchDescriptor {
            adapter_id: "sat-pb-lrat-v1",
            domain_profile: "sat-pb",
            source_system: "sat-pb",
            artifact_kind: "lrat",
            artifact_format: "lrat",
        },
        ArtifactReplayDispatchDescriptor {
            adapter_id: "sat-pb-veripb-v1",
            domain_profile: "sat-pb",
            source_system: "sat-pb",
            artifact_kind: "veripb",
            artifact_format: "veripb",
        },
        ArtifactReplayDispatchDescriptor {
            adapter_id: "gamma-crown-farkas-v1",
            domain_profile: "nn-verify",
            source_system: "gamma-crown",
            artifact_kind: "gamma_crown_farkas",
            artifact_format: "gamma-crown-farkas-v1",
        },
        ArtifactReplayDispatchDescriptor {
            adapter_id: "gamma-crown-linear-entailment-v1",
            domain_profile: "nn-verify",
            source_system: "gamma-crown",
            artifact_kind: "gamma_crown_entailment",
            artifact_format: "gamma-crown-linear-entailment-v1",
        },
        ArtifactReplayDispatchDescriptor {
            adapter_id: "ay-alethe-v1",
            domain_profile: "sat-pb",
            source_system: "ay",
            artifact_kind: "ay_alethe_envelope",
            artifact_format: "ay-alethe-envelope-v1",
        },
    ]
}

pub fn executable_replay_dispatch_descriptor(
    adapter_id: &str,
) -> Option<&'static ArtifactReplayDispatchDescriptor> {
    executable_replay_dispatch_descriptors()
        .iter()
        .find(|descriptor| descriptor.adapter_id == adapter_id)
}

fn sat_pb_replay_adapters() -> Vec<ArtifactReplayAdapterDescriptor> {
    vec![
        replay_adapter_descriptor(
            "sat-pb-lrat-v1",
            "SAT/PB LRAT replay",
            "sat-pb",
            &["lrat"],
            &["lrat"],
            &["sat-pb"],
            "Replay an LRAT refutation against the referenced SAT/PB problem and emit replay-only evidence.",
            "available",
            false,
            None,
        ),
        replay_adapter_descriptor(
            "sat-pb-drat-v1",
            "SAT/PB DRAT replay",
            "sat-pb",
            &["drat"],
            &["drat"],
            &["sat-pb"],
            "Replay a DRAT refutation against the referenced SAT/PB problem and emit replay-only evidence.",
            "available",
            false,
            None,
        ),
        replay_adapter_descriptor(
            "sat-pb-veripb-v1",
            "SAT/PB VeriPB replay",
            "sat-pb",
            &["veripb"],
            &["veripb"],
            &["sat-pb"],
            "Check VeriPB proof commands against pseudo-Boolean constraints and report partial replay status until the full checker is wired.",
            "partial",
            false,
            None,
        ),
        replay_adapter_descriptor(
            "sat-pb-ay-theorem-export-v1",
            "SAT/PB theorem-export replay",
            "sat-pb",
            &["ay-theorem-export"],
            &["ay-theorem-export", "ay_theorem_export"],
            &["ay"],
            "Validate Ay theorem-export artifacts as SAT/PB obligations before linking replay evidence to project fingerprints.",
            "planned",
            false,
            None,
        ),
        replay_adapter_descriptor(
            "ay-alethe-v1",
            "Alethe replay for SAT/PB obligations",
            "sat-pb",
            &["ay-alethe-envelope-v1"],
            &["ay_alethe_envelope", "alethe"],
            &["ay"],
            "Replay an Alethe certificate exported through proof-artifact-v1 and link replay-only evidence to SAT/PB obligations.",
            "feature-gated",
            false,
            Some("carcara-verify"),
        ),
    ]
}

fn nn_verify_replay_adapters() -> Vec<ArtifactReplayAdapterDescriptor> {
    vec![
        replay_adapter_descriptor(
            "gamma-crown-farkas-v1",
            "Gamma-Crown Farkas replay",
            "nn-verify",
            &["gamma-crown-farkas-v1"],
            &[
                "gamma_crown_farkas",
                "farkas_certificate",
                "gamma-crown-farkas-v1",
            ],
            &["gamma-crown"],
            "Replay Farkas contradiction certificates for neural-network verification obligations.",
            "available",
            false,
            None,
        ),
        replay_adapter_descriptor(
            "gamma-crown-linear-entailment-v1",
            "Gamma-Crown linear-entailment replay",
            "nn-verify",
            &["gamma-crown-linear-entailment-v1"],
            &[
                "gamma_crown_entailment",
                "gamma_crown_linear_entailment",
                "linear_entailment_certificate",
                "gamma-crown-linear-entailment-v1",
            ],
            &["gamma-crown"],
            "Replay linear entailment certificates for bound-propagation obligations.",
            "available",
            false,
            None,
        ),
    ]
}

fn replay_adapter_descriptor(
    id: &str,
    label: &str,
    domain_profile: &str,
    artifact_formats: &[&str],
    artifact_kinds: &[&str],
    source_systems: &[&str],
    replay_contract: &str,
    lifecycle: &str,
    requires_external_tool: bool,
    feature_gate: Option<&str>,
) -> ArtifactReplayAdapterDescriptor {
    ArtifactReplayAdapterDescriptor {
        id: id.to_owned(),
        label: label.to_owned(),
        domain_profile: domain_profile.to_owned(),
        source_systems: strings(source_systems),
        artifact_formats: strings(artifact_formats),
        artifact_kinds: strings(artifact_kinds),
        replay_contract: replay_contract.to_owned(),
        availability: ArtifactReplayAdapterAvailability {
            source: "built-in-profile".to_owned(),
            executor: "clean math artifact replay".to_owned(),
            requires_external_tool,
            feature_gate: feature_gate.map(str::to_owned),
        },
        trust: ArtifactReplayAdapterTrust {
            evidence_kind: "replay_only".to_owned(),
            kernel_certified: false,
            allowed_trusted_assumptions: Vec::new(),
            requires_envelope_validation: true,
            requires_problem_hash: true,
            links_obligation_fingerprint: true,
            required_report_fields: strings(&[
                "artifact_path",
                "problem_hash",
                "proof_hash",
                "replay_status",
                "linked_obligations",
                "trusted_assumptions",
            ]),
        },
        status: ArtifactReplayAdapterStatus {
            phase: "Phase 6".to_owned(),
            lifecycle: lifecycle.to_owned(),
            blocker_kind: "artifact-replay".to_owned(),
            report_schema_version: ARTIFACT_REPLAY_SCHEMA_VERSION.to_owned(),
            replay_status_values: strings(&["pass", "fail", "blocked"]),
        },
    }
}

pub fn built_in_tactic_normalizer_plan(
    domain: &str,
) -> Result<DomainTacticNormalizerPlan, MathProjectError> {
    Ok(built_in_profile(domain)?.tactic_normalizer_plan())
}

pub fn tactic_normalizer_plan(profile: &DomainProfile) -> DomainTacticNormalizerPlan {
    let profile_source = format!("domain-profile:{}", profile.name);
    let profile_normalizers = profile
        .normalizers
        .iter()
        .enumerate()
        .map(|(idx, name)| NormalizerDescriptor {
            name: name.clone(),
            rank: idx + 1,
            source: profile_source.clone(),
        })
        .collect::<Vec<_>>();
    let normalizer_names = profile
        .normalizers
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let tactics = profile
        .tactic_recommendations
        .iter()
        .enumerate()
        .map(|(idx, name)| TacticDescriptor {
            name: name.clone(),
            rank: idx + 1,
            source: profile_source.clone(),
            uses_profile_normalizer: normalizer_names.contains(name.as_str()),
        })
        .collect::<Vec<_>>();

    DomainTacticNormalizerPlan {
        schema_version: DOMAIN_PROFILE_SCHEMA_VERSION.to_owned(),
        domain_profile: profile.name.clone(),
        normalizers: profile_normalizers,
        tactic_recommendations: tactics,
    }
}

pub fn pilot_manifest(
    domain: &str,
    project: &str,
) -> Result<MathProjectManifest, MathProjectError> {
    let profile = built_in_profile(domain)?;
    Ok(MathProjectManifest {
        schema_version: MATH_PROJECT_SCHEMA_VERSION.to_owned(),
        project: project.to_owned(),
        domain_profile: domain.to_owned(),
        owner: "clean-math-factory".to_owned(),
        theorem_packs: vec!["theorem_packs/Pilot.lean".to_owned()],
        obligation_sources: vec!["obligations/pilot.json".to_owned()],
        artifact_formats: profile.artifact_formats,
        certificate_extractors: profile.certificate_extractors,
        trust_policy: TrustPolicy {
            name: "constructive-only".to_owned(),
            allowed_axioms: Vec::new(),
            forbidden_trust_markers: strings(&[
                "sorry",
                "sorryAx",
                "trustedArith",
                "synthetic_sorry",
            ]),
            require_artifact_replay: true,
            allow_synthetic_sorry: false,
        },
        normalizers: profile.normalizers,
        evidence: Vec::new(),
        issue_routing: IssueRouting {
            labels: strings(&["math-project", domain]),
            owners: Vec::new(),
            blocking_categories: strings(&["manifest", "obligation", "artifact", "trust"]),
        },
    })
}

pub fn validate_project(path: &Path, manifest: &MathProjectManifest) -> Vec<ValidationViolation> {
    let mut violations = Vec::new();
    let root = path.parent().unwrap_or_else(|| Path::new("."));
    require_eq(
        &mut violations,
        "MP001",
        "schema_version",
        &manifest.schema_version,
        MATH_PROJECT_SCHEMA_VERSION,
    );
    require_non_empty(&mut violations, "MP002", "project", &manifest.project);
    require_non_empty(
        &mut violations,
        "MP003",
        "domain_profile",
        &manifest.domain_profile,
    );
    require_non_empty(&mut violations, "MP004", "owner", &manifest.owner);
    require_non_empty(
        &mut violations,
        "MP005",
        "trust_policy.name",
        &manifest.trust_policy.name,
    );
    let profile = match DomainProfileRegistry::new(root).profile(&manifest.domain_profile) {
        Ok(profile) => Some(profile),
        Err(err) => {
            violations.push(error(
                "MP006",
                "domain_profile",
                format!(
                    "unknown or invalid domain profile `{}`: {err}",
                    manifest.domain_profile
                ),
            ));
            None
        }
    };
    if let Some(profile) = profile.as_ref() {
        validate_manifest_profile_compatibility(manifest, profile, &mut violations);
    }
    if manifest.theorem_packs.is_empty() {
        violations.push(warn(
            "MP007",
            "theorem_packs",
            "project has no theorem packs".to_owned(),
        ));
    }
    if manifest.obligation_sources.is_empty() {
        violations.push(warn(
            "MP008",
            "obligation_sources",
            "project has no obligation sources".to_owned(),
        ));
    }
    for (idx, item) in manifest.theorem_packs.iter().enumerate() {
        let theorem_pack_exists = check_relative_path(
            root,
            item,
            "MP009",
            &format!("theorem_packs[{idx}]"),
            &mut violations,
        );
        if !item.trim().is_empty() && !theorem_pack_exists {
            violations.push(error(
                "MP025",
                &format!("theorem_packs[{idx}]"),
                format!(
                    "theorem pack `{}` is not theorem-indexable because the referenced path is missing",
                    root.join(item).display()
                ),
            ));
        }
    }
    for (idx, item) in manifest.obligation_sources.iter().enumerate() {
        let source_exists = check_relative_path(
            root,
            item,
            "MP010",
            &format!("obligation_sources[{idx}]"),
            &mut violations,
        );
        if source_exists {
            validate_obligation_source(root, manifest, item, idx, &mut violations);
        }
    }
    if !manifest.trust_policy.allow_synthetic_sorry
        && !manifest
            .trust_policy
            .forbidden_trust_markers
            .iter()
            .any(|marker| marker == "synthetic_sorry" || marker == "sorryAx")
    {
        violations.push(warn(
            "MP011",
            "trust_policy.forbidden_trust_markers",
            "constructive projects should forbid synthetic sorry or sorryAx".to_owned(),
        ));
    }
    for (idx, item) in manifest.evidence.iter().enumerate() {
        check_required_relative_path(
            root,
            item,
            "MP012",
            &format!("evidence[{idx}]"),
            &mut violations,
        );
    }
    for (idx, item) in manifest.theorem_packs.iter().enumerate() {
        validate_theorem_pack_trust(root, item, idx, &manifest.trust_policy, &mut violations);
        validate_theorem_pack_indexability(
            root,
            item,
            idx,
            &manifest.trust_policy,
            &mut violations,
        );
    }
    if manifest.trust_policy.require_artifact_replay {
        validate_project_replay_evidence(root, manifest, &mut violations);
    }
    violations
}

fn validate_manifest_profile_compatibility(
    manifest: &MathProjectManifest,
    profile: &DomainProfile,
    violations: &mut Vec<ValidationViolation>,
) {
    validate_profile_list(
        &manifest.artifact_formats,
        &profile.artifact_formats,
        "MP019",
        "artifact_formats",
        "artifact format",
        violations,
    );
    validate_profile_list(
        &manifest.normalizers,
        &profile.normalizers,
        "MP020",
        "normalizers",
        "normalizer",
        violations,
    );
    validate_profile_list(
        &manifest.certificate_extractors,
        &profile.certificate_extractors,
        "MP021",
        "certificate_extractors",
        "certificate extractor",
        violations,
    );
    validate_issue_labels(&manifest.issue_routing.labels, violations);
    validate_issue_categories(&manifest.issue_routing.blocking_categories, violations);
}

fn validate_profile_list(
    values: &[String],
    allowed: &[String],
    code: &'static str,
    path: &str,
    noun: &str,
    violations: &mut Vec<ValidationViolation>,
) {
    let mut seen = Vec::<&str>::new();
    for (idx, value) in values.iter().enumerate() {
        let item_path = format!("{path}[{idx}]");
        if value.trim().is_empty() {
            violations.push(error(code, &item_path, format!("{noun} must not be empty")));
        } else if value.trim() != value {
            violations.push(error(
                code,
                &item_path,
                format!("{noun} `{value}` must not have surrounding whitespace"),
            ));
        } else if !allowed.iter().any(|allowed| allowed == value) {
            violations.push(error(
                code,
                &item_path,
                format!(
                    "{noun} `{value}` is not supported; allowed values are {}",
                    allowed.join(", ")
                ),
            ));
        } else if seen.contains(&value.as_str()) {
            violations.push(error(
                code,
                &item_path,
                format!("{noun} `{value}` is duplicated"),
            ));
        }
        seen.push(value);
    }
}

fn validate_issue_labels(labels: &[String], violations: &mut Vec<ValidationViolation>) {
    let mut seen = Vec::<&str>::new();
    for (idx, label) in labels.iter().enumerate() {
        let path = format!("issue_routing.labels[{idx}]");
        if label.trim().is_empty() {
            violations.push(error("MP022", &path, "label must not be empty".to_owned()));
        } else if label.trim() != label {
            violations.push(error(
                "MP022",
                &path,
                format!("label `{label}` must not have surrounding whitespace"),
            ));
        } else if !label
            .chars()
            .all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit() || ch == '-' || ch == '_')
        {
            violations.push(error(
                "MP022",
                &path,
                format!(
                    "label `{label}` must use lowercase ASCII letters, digits, hyphens, or underscores"
                ),
            ));
        } else if seen.contains(&label.as_str()) {
            violations.push(error(
                "MP022",
                &path,
                format!("label `{label}` is duplicated"),
            ));
        }
        seen.push(label);
    }
}

fn validate_issue_categories(categories: &[String], violations: &mut Vec<ValidationViolation>) {
    const ALLOWED: &[&str] = &["manifest", "obligation", "artifact", "trust"];
    let mut seen = Vec::<&str>::new();
    for (idx, category) in categories.iter().enumerate() {
        let path = format!("issue_routing.blocking_categories[{idx}]");
        if category.trim().is_empty() {
            violations.push(error(
                "MP023",
                &path,
                "blocking category must not be empty".to_owned(),
            ));
        } else if !ALLOWED.contains(&category.as_str()) {
            violations.push(error(
                "MP023",
                &path,
                format!(
                    "blocking category `{category}` must be one of {}",
                    ALLOWED.join(", ")
                ),
            ));
        } else if seen.contains(&category.as_str()) {
            violations.push(error(
                "MP023",
                &path,
                format!("blocking category `{category}` is duplicated"),
            ));
        }
        seen.push(category);
    }
}

pub fn project_status_report(
    path: &Path,
    manifest: &MathProjectManifest,
) -> MathProjectStatusReport {
    let violations = validate_project(path, manifest);
    let status = status_from_violations(&violations);
    let root = path.parent().unwrap_or_else(|| Path::new("."));
    MathProjectStatusReport {
        schema_version: STATUS_SCHEMA_VERSION,
        project_path: path.display().to_string(),
        project_root: root.display().to_string(),
        project: manifest.project.clone(),
        domain_profile: manifest.domain_profile.clone(),
        owner: manifest.owner.clone(),
        status,
        theorem_packs: manifest.theorem_packs.len(),
        obligation_sources: manifest.obligation_sources.len(),
        artifact_formats: manifest.artifact_formats.clone(),
        certificate_extractors: manifest.certificate_extractors.clone(),
        normalizers: manifest.normalizers.clone(),
        evidence: manifest.evidence.clone(),
        replay_cache: replay_cache_summary(root, manifest),
        trust_policy: manifest.trust_policy.clone(),
        violations,
    }
}

pub fn validate_obligation(
    obligation: &MathObligation,
    project: Option<&MathProjectManifest>,
) -> Vec<ValidationViolation> {
    validate_obligation_with_artifact_root(None, obligation, project)
}

pub fn validate_obligation_with_artifact_root(
    artifact_root: Option<&Path>,
    obligation: &MathObligation,
    project: Option<&MathProjectManifest>,
) -> Vec<ValidationViolation> {
    let mut violations = Vec::new();
    require_eq(
        &mut violations,
        "OB001",
        "schema_version",
        &obligation.schema_version,
        OBLIGATION_SCHEMA_VERSION,
    );
    require_non_empty(&mut violations, "OB002", "project", &obligation.project);
    require_non_empty(
        &mut violations,
        "OB003",
        "domain_profile",
        &obligation.domain_profile,
    );
    require_non_empty(
        &mut violations,
        "OB004",
        "producer.system",
        &obligation.producer.system,
    );
    require_non_empty(
        &mut violations,
        "OB005",
        "producer.commit",
        &obligation.producer.commit,
    );
    require_non_empty(&mut violations, "OB006", "goal.expr", &obligation.goal.expr);
    require_non_empty(
        &mut violations,
        "OB007",
        "goal.pretty",
        &obligation.goal.pretty,
    );
    require_non_empty(
        &mut violations,
        "OB008",
        "trust_policy",
        &obligation.trust_policy,
    );
    if obligation_domain_profile(artifact_root, &obligation.domain_profile).is_err() {
        violations.push(error(
            "OB009",
            "domain_profile",
            format!("unknown domain profile `{}`", obligation.domain_profile),
        ));
    }
    for (idx, local) in obligation.local_context.iter().enumerate() {
        require_non_empty(
            &mut violations,
            "OB010",
            &format!("local_context[{idx}].name"),
            &local.name,
        );
        require_non_empty(
            &mut violations,
            "OB011",
            &format!("local_context[{idx}].type_pp"),
            &local.type_pp,
        );
    }
    if let Some(project) = project {
        if obligation.project != project.project {
            violations.push(error(
                "OB012",
                "project",
                format!(
                    "obligation project `{}` does not match manifest `{}`",
                    obligation.project, project.project
                ),
            ));
        }
        if obligation.domain_profile != project.domain_profile {
            violations.push(error(
                "OB013",
                "domain_profile",
                format!(
                    "obligation domain `{}` does not match manifest `{}`",
                    obligation.domain_profile, project.domain_profile
                ),
            ));
        }
        if obligation.trust_policy != project.trust_policy.name {
            violations.push(error(
                "OB014",
                "trust_policy",
                format!(
                    "obligation trust policy `{}` does not match manifest `{}`",
                    obligation.trust_policy, project.trust_policy.name
                ),
            ));
        }
        validate_pretty_only_trust_claims(obligation, project, &mut violations);
    }
    if obligation
        .metadata
        .values()
        .any(|value| value.contains("synthetic_sorry"))
    {
        violations.push(error(
            "OB015",
            "metadata",
            "obligation metadata contains synthetic_sorry".to_owned(),
        ));
    }
    validate_obligation_hidden_trust_markers(obligation, project, &mut violations);
    validate_artifact_refs(artifact_root, obligation, &mut violations);
    violations
}

fn obligation_domain_profile(
    artifact_root: Option<&Path>,
    domain: &str,
) -> Result<DomainProfile, MathProjectError> {
    if let Some(root) = artifact_root {
        DomainProfileRegistry::new(root).profile(domain)
    } else {
        built_in_profile(domain)
    }
}

pub fn obligation_report(
    path: &Path,
    obligation: &MathObligation,
    project: Option<&MathProjectManifest>,
) -> ObligationValidationReport {
    let violations = validate_obligation(obligation, project);
    ObligationValidationReport {
        schema_version: OBLIGATION_REPORT_SCHEMA_VERSION,
        path: path.display().to_string(),
        project: obligation.project.clone(),
        domain_profile: obligation.domain_profile.clone(),
        fingerprint: obligation_fingerprint(obligation),
        status: status_from_violations(&violations),
        artifact_refs: obligation.artifact_refs.clone(),
        violations,
    }
}

pub fn open_obligation_report(
    project: &MathProjectManifest,
    obligation: &MathObligation,
) -> OpenObligationReport {
    let fingerprint = obligation_fingerprint(obligation);
    OpenObligationReport {
        schema_version: OPEN_OBLIGATION_SCHEMA_VERSION,
        project: project.project.clone(),
        domain_profile: project.domain_profile.clone(),
        state_id: format!("math-obligation:{fingerprint}"),
        obligation_fingerprint: fingerprint,
        persistence: "ephemeral-cli-state",
        status: "opened-adapter",
        warnings: vec![
            "CLI-local proof states are deterministic handles, not persistent server sessions yet"
                .to_owned(),
            "Use the server-backed proofState.openObligation follow-up for tactic lifecycle reuse"
                .to_owned(),
        ],
    }
}

pub fn hygiene_report(path: &Path, manifest: &MathProjectManifest) -> HygieneReport {
    let violations = validate_project(path, manifest);
    let mut checks = Vec::new();
    checks.push(check(
        "manifest",
        status_from_violations(&violations),
        format!("{} manifest diagnostics", violations.len()),
    ));
    checks.push(check(
        "trust-policy",
        if manifest.trust_policy.allow_synthetic_sorry {
            "fail"
        } else {
            "pass"
        },
        "synthetic sorry must be rejected for project promotion".to_owned(),
    ));
    checks.push(check(
        "artifact-replay-policy",
        if manifest.trust_policy.require_artifact_replay {
            "pass"
        } else {
            "warn"
        },
        "external artifacts should replay before certificate extraction".to_owned(),
    ));
    let status = hygiene_status_from_project_violations(&violations, manifest);
    HygieneReport {
        schema_version: HYGIENE_SCHEMA_VERSION,
        project: manifest.project.clone(),
        status,
        gate: hygiene_gate(path),
        checks,
        violations,
    }
}

fn hygiene_status_from_project_violations(
    violations: &[ValidationViolation],
    manifest: &MathProjectManifest,
) -> &'static str {
    if violations.iter().any(|v| v.severity == "error")
        || manifest.trust_policy.allow_synthetic_sorry
    {
        "fail"
    } else if violations.iter().any(|v| v.severity == "warn")
        || !manifest.trust_policy.require_artifact_replay
    {
        "warn"
    } else {
        "pass"
    }
}

pub fn hygiene_gate(project_path: &Path) -> HygieneGate {
    HygieneGate {
        command: hygiene_gate_command(project_path),
        pass_status: "pass",
    }
}

pub fn hygiene_gate_command(project_path: &Path) -> String {
    format!(
        "clean math project hygiene --project {} --json",
        project_path.display()
    )
}

pub fn issue_plan_report(project_path: &Path, manifest: &MathProjectManifest) -> IssuePlanReport {
    let root = project_path.parent().unwrap_or_else(|| Path::new("."));
    let proof_failure_diagnostics = load_proof_failure_diagnostic_evidence(root, manifest);
    let mut rows = Vec::new();
    for violation in validate_project(project_path, manifest) {
        if violation.severity == "error" {
            rows.push(hygiene_violation_issue_row(
                project_path,
                manifest,
                &violation,
            ));
        }
    }
    for source in &manifest.obligation_sources {
        let path = root.join(source);
        let row = if let Ok(obligation) = load_json::<MathObligation>(&path) {
            let violations =
                validate_obligation_with_artifact_root(Some(root), &obligation, Some(manifest));
            if has_error(&violations) {
                Some(invalid_obligation_issue_row(
                    project_path,
                    manifest,
                    source,
                    &path,
                    &violations,
                ))
            } else if non_filing_obligation(&obligation) {
                None
            } else {
                Some(valid_obligation_issue_row(
                    project_path,
                    manifest,
                    source,
                    &path,
                    &obligation,
                    proof_failure_diagnostics
                        .get(&obligation_fingerprint(&obligation))
                        .map(Vec::as_slice)
                        .unwrap_or(&[]),
                ))
            }
        } else {
            Some(obligation_source_repair_issue_row(
                project_path,
                manifest,
                source,
                &path,
            ))
        };
        if let Some(row) = row {
            rows.push(row);
        }
    }
    if rows.is_empty() && manifest.obligation_sources.is_empty() {
        rows.push(seed_obligation_issue_row(project_path, manifest));
    }
    finalize_issue_plan_rows(&mut rows);
    let phases = issue_plan_phases(&rows);
    let workstreams = issue_plan_workstreams(&rows);
    IssuePlanReport {
        schema_version: ISSUE_PLAN_SCHEMA_VERSION,
        project: manifest.project.clone(),
        domain_profile: manifest.domain_profile.clone(),
        filing_guidance: IssuePlanFilingGuidance {
            rule: "File one GitHub issue per row unless two adjacent rows share the same phase, workstream, and verification command.",
            grouping: vec!["phase", "workstream", "filing_key"],
        },
        phases,
        workstreams,
        rows,
    }
}

fn non_filing_obligation(obligation: &MathObligation) -> bool {
    let issue_plan_non_filing = obligation.metadata.get("issue_plan").is_some_and(|value| {
        matches!(
            value.trim().to_ascii_lowercase().as_str(),
            "non-filing" | "non_filing" | "skip" | "exclude"
        )
    });
    let fixture_role_is_smoke = obligation
        .metadata
        .get("fixture_role")
        .is_some_and(|value| {
            matches!(
                value.trim().to_ascii_lowercase().as_str(),
                "proof-state-smoke" | "theorem-index-smoke"
            )
        });
    issue_plan_non_filing && fixture_role_is_smoke
}

pub fn project_dashboard_report(
    project_path: &Path,
    manifest: &MathProjectManifest,
) -> MathProjectDashboardReport {
    let root = project_path.parent().unwrap_or_else(|| Path::new("."));
    let violations = validate_project(project_path, manifest);
    let hygiene_status = hygiene_status_from_project_violations(&violations, manifest);
    let replay_cache = replay_cache_summary(root, manifest);
    let mut total = 0;
    let mut with_artifacts = 0;
    let mut invalid = 0;
    let mut fingerprints = Vec::new();

    for source in &manifest.obligation_sources {
        let path = root.join(source);
        let Ok(obligation) = load_json::<MathObligation>(&path) else {
            invalid += 1;
            continue;
        };
        total += 1;
        if !obligation.artifact_refs.is_empty() {
            with_artifacts += 1;
        }
        let obligation_violations =
            validate_obligation_with_artifact_root(Some(root), &obligation, Some(manifest));
        if has_error(&obligation_violations) {
            invalid += 1;
        }
        fingerprints.push(obligation_fingerprint(&obligation));
    }
    fingerprints.sort();

    let missing_artifact_replay = violations
        .iter()
        .filter(|violation| violation.code == "MP016")
        .count();
    let blockers = violations
        .iter()
        .filter(|violation| violation.severity == "error")
        .cloned()
        .collect::<Vec<_>>();
    MathProjectDashboardReport {
        schema_version: DASHBOARD_SCHEMA_VERSION,
        project: manifest.project.clone(),
        project_root: root.display().to_string(),
        status: status_from_violations(&violations),
        obligations: DashboardObligations {
            total,
            with_artifacts,
            invalid,
            fingerprints,
        },
        replay: DashboardReplay {
            cache_roots: replay_cache.roots,
            cached_reports: replay_cache.cached_reports,
            pass: replay_cache.pass,
            fail: replay_cache.fail,
            blocked: replay_cache.blocked,
            missing_artifact_replay,
        },
        hygiene: DashboardHygiene {
            status: hygiene_status,
            blockers,
        },
    }
}

pub fn apply_issue_plan_open_dedupe(report: &mut IssuePlanReport, snapshot: &Value) {
    let open_issues = collect_open_issue_summaries(snapshot);
    for row in &mut report.rows {
        let mut matches = 0usize;
        for issue in &open_issues {
            if issue.matches(row) {
                matches += 1;
            }
        }
        row.dedupe_status = match matches {
            0 => "new",
            1 => "matched_open",
            _ => "ambiguous",
        }
        .to_owned();
    }
}

fn finalize_issue_plan_rows(rows: &mut [IssuePlanRow]) {
    rows.sort_by(issue_plan_row_order);
    for (idx, row) in rows.iter_mut().enumerate() {
        row.ranking.rank = idx + 1;
        let dedupe_key = issue_plan_dedupe_key(row);
        row.dedupe_key = dedupe_key;
        row.dedupe_status = "new".to_owned();
        if !row.issue_body.contains(&row.dedupe_key) {
            row.issue_body.push_str("\n## Dedupe\n");
            row.issue_body
                .push_str(&format!("- Key: `{}`\n", row.dedupe_key));
        }
    }
}

fn issue_plan_row_order(left: &IssuePlanRow, right: &IssuePlanRow) -> std::cmp::Ordering {
    right
        .ranking
        .score
        .cmp(&left.ranking.score)
        .then_with(|| left.phase.cmp(right.phase))
        .then_with(|| left.workstream.cmp(&right.workstream))
        .then_with(|| left.filing_key.cmp(&right.filing_key))
        .then_with(|| left.title.cmp(&right.title))
}

fn issue_plan_dedupe_key(row: &IssuePlanRow) -> String {
    let payload = serde_json::json!({
        "schema_version": ISSUE_PLAN_SCHEMA_VERSION,
        "phase": row.phase,
        "workstream": row.workstream,
        "filing_key": row.filing_key,
        "title": row.title,
        "verification_command": row.verification_command,
    });
    let canonical = serde_json::to_string(&payload).expect("issue-plan dedupe payload serializes");
    let mut hasher = Sha256::new();
    hasher.update(canonical.as_bytes());
    let digest = hasher.finalize();
    format!("clean-math-issue-{}", hex_lower(&digest[..12]))
}

fn issue_plan_filing_metadata(
    manifest: &MathProjectManifest,
    files: &[String],
    row_blockers: &[String],
    verification_command: &str,
) -> IssuePlanFilingMetadata {
    IssuePlanFilingMetadata {
        labels: stable_unique_trimmed(&manifest.issue_routing.labels),
        owner: issue_plan_filing_owner(manifest),
        blockers: issue_plan_filing_blockers(
            &manifest.issue_routing.blocking_categories,
            row_blockers,
        ),
        reproduction: IssuePlanReproduction {
            commands: vec![verification_command.to_owned()],
            files: files.to_owned(),
        },
    }
}

fn issue_plan_filing_owner(manifest: &MathProjectManifest) -> Option<String> {
    manifest
        .issue_routing
        .owners
        .iter()
        .find_map(|owner| non_empty_trimmed(owner))
        .or_else(|| non_empty_trimmed(&manifest.owner))
}

fn issue_plan_filing_blockers(categories: &[String], row_blockers: &[String]) -> Vec<String> {
    let mut blockers = stable_unique_trimmed(categories);
    for blocker in row_blockers {
        if let Some(blocker) = non_empty_trimmed(blocker) {
            if !blockers.iter().any(|existing| existing == &blocker) {
                blockers.push(blocker);
            }
        }
    }
    blockers
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LoadedProofFailureDiagnosticEvidence {
    path: PathBuf,
    evidence: ProofFailureDiagnosticEvidence,
}

fn load_proof_failure_diagnostic_evidence(
    root: &Path,
    manifest: &MathProjectManifest,
) -> BTreeMap<String, Vec<LoadedProofFailureDiagnosticEvidence>> {
    let mut by_fingerprint: BTreeMap<String, Vec<LoadedProofFailureDiagnosticEvidence>> =
        BTreeMap::new();
    for rel in &manifest.evidence {
        let path = root.join(rel);
        let Ok(evidence) = load_json::<ProofFailureDiagnosticEvidence>(&path) else {
            continue;
        };
        if evidence.schema_version != PROOF_FAILURE_DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION {
            continue;
        }
        if evidence.obligation_fingerprint.trim().is_empty() {
            continue;
        }
        by_fingerprint
            .entry(evidence.obligation_fingerprint.clone())
            .or_default()
            .push(LoadedProofFailureDiagnosticEvidence { path, evidence });
    }
    for diagnostics in by_fingerprint.values_mut() {
        diagnostics.sort_by(|left, right| {
            proof_failure_diagnostic_order_key(left).cmp(&proof_failure_diagnostic_order_key(right))
        });
    }
    by_fingerprint
}

fn proof_failure_diagnostic_order_key(
    diagnostic: &LoadedProofFailureDiagnosticEvidence,
) -> (
    String,
    Vec<String>,
    Vec<String>,
    i64,
    Vec<String>,
    Vec<String>,
    String,
) {
    (
        diagnostic.evidence.summary.clone().unwrap_or_default(),
        stable_unique_trimmed(&diagnostic.evidence.blockers),
        stable_unique_trimmed(&diagnostic.evidence.ranking_signals),
        diagnostic.evidence.score_delta,
        stable_unique_trimmed(&diagnostic.evidence.reproduction.commands),
        stable_unique_trimmed(&diagnostic.evidence.reproduction.files),
        diagnostic.path.display().to_string(),
    )
}

fn proof_failure_diagnostic_blockers(
    diagnostics: &[LoadedProofFailureDiagnosticEvidence],
    proof_gap: &str,
) -> Vec<String> {
    let mut blockers = vec![proof_gap.to_owned()];
    for diagnostic in diagnostics {
        blockers.extend(stable_unique_trimmed(&diagnostic.evidence.blockers));
    }
    stable_unique_trimmed(&blockers)
}

fn proof_failure_diagnostic_summaries(
    diagnostics: &[LoadedProofFailureDiagnosticEvidence],
) -> Vec<String> {
    let summaries = diagnostics
        .iter()
        .filter_map(|diagnostic| {
            diagnostic
                .evidence
                .summary
                .as_deref()
                .and_then(non_empty_trimmed)
        })
        .collect::<Vec<_>>();
    stable_unique_trimmed(&summaries)
}

fn enrich_filing_metadata_with_proof_failure_diagnostics(
    metadata: &mut IssuePlanFilingMetadata,
    diagnostics: &[LoadedProofFailureDiagnosticEvidence],
) {
    for diagnostic in diagnostics {
        for command in stable_unique_trimmed(&diagnostic.evidence.reproduction.commands) {
            if !metadata.reproduction.commands.contains(&command) {
                metadata.reproduction.commands.push(command);
            }
        }
        for file in stable_unique_trimmed(&diagnostic.evidence.reproduction.files) {
            if !metadata.reproduction.files.contains(&file) {
                metadata.reproduction.files.push(file);
            }
        }
    }
}

fn append_proof_failure_diagnostics_to_issue_body(
    body: &mut String,
    diagnostics: &[LoadedProofFailureDiagnosticEvidence],
) {
    if diagnostics.is_empty() {
        return;
    }
    body.push_str("\n## Proof Failure Diagnostics\n");
    for diagnostic in diagnostics {
        body.push_str(&format!("- Evidence: `{}`\n", diagnostic.path.display()));
        if let Some(summary) = diagnostic
            .evidence
            .summary
            .as_deref()
            .and_then(non_empty_trimmed)
        {
            body.push_str(&format!("  Summary: {summary}\n"));
        }
        let blockers = stable_unique_trimmed(&diagnostic.evidence.blockers);
        if !blockers.is_empty() {
            body.push_str(&format!("  Blockers: {}\n", blockers.join(", ")));
        }
        let signals = stable_unique_trimmed(&diagnostic.evidence.ranking_signals);
        if !signals.is_empty() {
            body.push_str(&format!("  Ranking signals: {}\n", signals.join(", ")));
        }
    }
}

fn stable_unique_trimmed(values: &[String]) -> Vec<String> {
    let mut unique = Vec::new();
    for value in values {
        if let Some(trimmed) = non_empty_trimmed(value) {
            if !unique.iter().any(|existing| existing == &trimmed) {
                unique.push(trimmed);
            }
        }
    }
    unique
}

fn non_empty_trimmed(value: &str) -> Option<String> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        None
    } else {
        Some(trimmed.to_owned())
    }
}

#[derive(Debug)]
struct OpenIssueSummary {
    title: Option<String>,
    body: Option<String>,
    dedupe_keys: BTreeSet<String>,
}

impl OpenIssueSummary {
    fn matches(&self, row: &IssuePlanRow) -> bool {
        self.dedupe_keys.contains(&row.dedupe_key)
            || self
                .body
                .as_deref()
                .is_some_and(|body| body.contains(&row.dedupe_key))
            || self.title.as_deref() == Some(row.title.as_str())
    }
}

fn collect_open_issue_summaries(snapshot: &Value) -> Vec<OpenIssueSummary> {
    let mut issues = Vec::new();
    collect_open_issue_summaries_into(snapshot, &mut issues);
    issues
}

fn collect_open_issue_summaries_into(value: &Value, issues: &mut Vec<OpenIssueSummary>) {
    match value {
        Value::Array(values) => {
            for value in values {
                collect_open_issue_summaries_into(value, issues);
            }
        }
        Value::Object(object) => {
            if let Some(issue) = open_issue_summary(value) {
                issues.push(issue);
                return;
            }
            for value in object.values() {
                collect_open_issue_summaries_into(value, issues);
            }
        }
        _ => {}
    }
}

fn open_issue_summary(value: &Value) -> Option<OpenIssueSummary> {
    let object = value.as_object()?;
    if object.contains_key("pull_request") {
        return None;
    }
    let title = object
        .get("title")
        .and_then(Value::as_str)
        .map(str::to_owned);
    let body = object
        .get("body")
        .and_then(Value::as_str)
        .map(str::to_owned);
    if title.is_none() && body.is_none() && object.get("dedupe_key").is_none() {
        return None;
    }
    if !issue_state_is_open(object.get("state")) {
        return None;
    }
    let mut dedupe_keys = BTreeSet::new();
    if let Some(key) = object.get("dedupe_key").and_then(Value::as_str) {
        dedupe_keys.insert(key.to_owned());
    }
    for key in object
        .get("dedupe_keys")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
    {
        dedupe_keys.insert(key.to_owned());
    }
    Some(OpenIssueSummary {
        title,
        body,
        dedupe_keys,
    })
}

fn issue_state_is_open(state: Option<&Value>) -> bool {
    match state.and_then(Value::as_str) {
        None => true,
        Some(state) => state.eq_ignore_ascii_case("open"),
    }
}

fn obligation_ranking_signals(
    root: &Path,
    manifest: &MathProjectManifest,
    obligation: &MathObligation,
    diagnostics: &[LoadedProofFailureDiagnosticEvidence],
) -> IssuePlanRankingSignals {
    let fingerprint = obligation_fingerprint(obligation);
    let artifact_kinds = obligation_artifact_kinds(obligation);
    let linked_reports = load_replay_evidence(root, manifest)
        .into_iter()
        .filter(|(_, report)| replay_evidence_links_obligation(report, &fingerprint))
        .map(|(_, report)| report)
        .collect::<Vec<_>>();
    let replay_cache_present = replay_cache_report_paths(root, manifest)
        .into_iter()
        .filter_map(|path| load_json::<Value>(&path).ok())
        .any(|report| replay_evidence_links_obligation(&report, &fingerprint));
    let replay_status = obligation_replay_status(obligation, &linked_reports);
    let proof_gap = obligation_proof_gap(obligation, &linked_reports);
    let benchmark =
        first_metadata_value(obligation, &["benchmark", "benchmark_name", "benchmark_id"]);
    let benchmark_family = first_metadata_value(obligation, &["benchmark_family", "family"]);
    let mut score = obligation_ranking_score(
        manifest,
        &artifact_kinds,
        benchmark.as_deref(),
        benchmark_family.as_deref(),
        &proof_gap,
    );
    let mut signals = ranking_signal_strings(
        manifest,
        &artifact_kinds,
        &replay_status,
        replay_cache_present,
        benchmark.as_deref(),
        benchmark_family.as_deref(),
        &proof_gap,
    );
    let proof_failure_diagnostics = proof_failure_diagnostic_summaries(diagnostics);
    for diagnostic in diagnostics {
        score += diagnostic.evidence.score_delta;
        for signal in stable_unique_trimmed(&diagnostic.evidence.ranking_signals) {
            signals.push(format!("proof-failure:{signal}"));
        }
    }
    signals = stable_unique_trimmed(&signals);
    IssuePlanRankingSignals {
        rank: 0,
        score,
        domain_profile: manifest.domain_profile.clone(),
        artifact_kinds,
        replay_status,
        replay_cache_present,
        benchmark,
        benchmark_family,
        proof_gap,
        proof_failure_diagnostics,
        signals,
    }
}

fn fixed_ranking_signals(
    manifest: &MathProjectManifest,
    score: i64,
    proof_gap: &str,
) -> IssuePlanRankingSignals {
    let replay_status = "not-applicable".to_owned();
    IssuePlanRankingSignals {
        rank: 0,
        score,
        domain_profile: manifest.domain_profile.clone(),
        artifact_kinds: Vec::new(),
        replay_status: replay_status.clone(),
        replay_cache_present: false,
        benchmark: None,
        benchmark_family: None,
        proof_gap: proof_gap.to_owned(),
        proof_failure_diagnostics: Vec::new(),
        signals: ranking_signal_strings(
            manifest,
            &[],
            &replay_status,
            false,
            None,
            None,
            proof_gap,
        ),
    }
}

fn obligation_artifact_kinds(obligation: &MathObligation) -> Vec<String> {
    let mut kinds = BTreeSet::new();
    if let Some(kind) = obligation.metadata.get("artifact_kind") {
        kinds.insert(kind.clone());
    }
    for artifact in &obligation.artifact_refs {
        kinds.insert(artifact.kind.clone());
    }
    kinds.into_iter().collect()
}

fn first_metadata_value(obligation: &MathObligation, keys: &[&str]) -> Option<String> {
    keys.iter()
        .find_map(|key| obligation.metadata.get(*key))
        .filter(|value| !value.trim().is_empty())
        .cloned()
}

fn obligation_replay_status(obligation: &MathObligation, linked_reports: &[Value]) -> String {
    if obligation.artifact_refs.is_empty() {
        return "not-applicable".to_owned();
    }
    let mut statuses = linked_reports
        .iter()
        .filter_map(replay_status)
        .map(str::to_owned)
        .collect::<Vec<_>>();
    statuses.sort();
    statuses.dedup();
    if statuses.is_empty() {
        "missing".to_owned()
    } else {
        statuses.join("+")
    }
}

fn obligation_proof_gap(obligation: &MathObligation, linked_reports: &[Value]) -> String {
    if obligation.artifact_refs.is_empty() {
        return "missing-kernel-proof".to_owned();
    }
    if linked_reports
        .iter()
        .any(|report| replay_status(report) == Some("pass"))
    {
        "none".to_owned()
    } else {
        "missing-replay-evidence".to_owned()
    }
}

fn obligation_ranking_score(
    manifest: &MathProjectManifest,
    artifact_kinds: &[String],
    benchmark: Option<&str>,
    benchmark_family: Option<&str>,
    proof_gap: &str,
) -> i64 {
    let mut score = match proof_gap {
        "missing-replay-evidence" => 800,
        "missing-kernel-proof" => 700,
        "none" => 500,
        _ => 100,
    };
    if manifest.domain_profile == "sat-pb" {
        score += 50;
    }
    if artifact_kinds
        .iter()
        .any(|kind| is_sat_pb_replay_artifact(kind))
    {
        score += 100;
    }
    if benchmark.is_some() {
        score += 10;
    }
    if benchmark_family.is_some() {
        score += 10;
    }
    score
}

fn is_sat_pb_replay_artifact(kind: &str) -> bool {
    matches!(kind, "lrat" | "drat" | "veripb")
}

fn ranking_signal_strings(
    manifest: &MathProjectManifest,
    artifact_kinds: &[String],
    replay_status: &str,
    replay_cache_present: bool,
    benchmark: Option<&str>,
    benchmark_family: Option<&str>,
    proof_gap: &str,
) -> Vec<String> {
    let mut signals = Vec::new();
    signals.push(format!("domain:{}", manifest.domain_profile));
    for kind in artifact_kinds {
        signals.push(format!("artifact:{kind}"));
    }
    signals.push(format!("replay:{replay_status}"));
    signals.push(format!(
        "replay-cache:{}",
        if replay_cache_present {
            "present"
        } else {
            "absent"
        }
    ));
    if let Some(benchmark) = benchmark {
        signals.push(format!("benchmark:{benchmark}"));
    }
    if let Some(benchmark_family) = benchmark_family {
        signals.push(format!("benchmark-family:{benchmark_family}"));
    }
    signals.push(format!("proof-gap:{proof_gap}"));
    signals
}

fn valid_obligation_issue_row(
    project_path: &Path,
    manifest: &MathProjectManifest,
    source: &str,
    path: &Path,
    obligation: &MathObligation,
    diagnostics: &[LoadedProofFailureDiagnosticEvidence],
) -> IssuePlanRow {
    let root = project_path.parent().unwrap_or_else(|| Path::new("."));
    let fingerprint = obligation_fingerprint(obligation);
    let short = short_fingerprint(&fingerprint);
    let (phase, phase_title) = if obligation.artifact_refs.is_empty() {
        ("Phase 7", "Certificate extraction")
    } else {
        ("Phase 6", "Artifact replay")
    };
    let workstream = obligation_workstream(manifest, obligation);
    let verification_command = valid_obligation_closure_command(project_path, path, obligation);
    let acceptance = valid_obligation_acceptance(obligation);
    let files = vec![source.to_owned()];
    let ranking = obligation_ranking_signals(root, manifest, obligation, diagnostics);
    let blockers = proof_failure_diagnostic_blockers(diagnostics, &ranking.proof_gap);
    let title = format!(
        "[{}][{}] close obligation {}",
        manifest.domain_profile, workstream, short
    );
    let mut filing_metadata = issue_plan_filing_metadata(
        manifest,
        &[source.to_owned()],
        &blockers,
        &verification_command,
    );
    enrich_filing_metadata_with_proof_failure_diagnostics(&mut filing_metadata, diagnostics);
    let mut issue_body = issue_body(
        phase,
        phase_title,
        &workstream,
        "Close the generated math-project obligation with explicit trust accounting.",
        &[source.to_owned()],
        &manifest.issue_routing.blocking_categories,
        &acceptance,
        &verification_command,
    );
    append_proof_failure_diagnostics_to_issue_body(&mut issue_body, diagnostics);
    IssuePlanRow {
        filing_key: format!("{phase}/{workstream}/{short}"),
        dedupe_key: String::new(),
        dedupe_status: String::new(),
        ranking,
        phase,
        phase_title,
        workstream: workstream.clone(),
        title,
        priority: "P1",
        scope: "proof-obligation".to_owned(),
        files,
        labels: manifest.issue_routing.labels.clone(),
        owners: manifest.issue_routing.owners.clone(),
        blocking_categories: manifest.issue_routing.blocking_categories.clone(),
        filing_metadata,
        dependencies: Vec::new(),
        acceptance: acceptance.clone(),
        verification_command: verification_command.clone(),
        issue_body,
    }
}

fn valid_obligation_closure_command(
    project_path: &Path,
    obligation_path: &Path,
    obligation: &MathObligation,
) -> String {
    if obligation.artifact_refs.is_empty() {
        let extract = format!(
            "clean math certificate extract --project {} --obligation {} --json",
            shell_arg_path(project_path),
            shell_arg_path(obligation_path)
        );
        return format!(
            "{extract} | python3 -c 'import json, sys; report = json.load(sys.stdin); assert report.get(\"proof_status\") == \"closed\" and report.get(\"kernel_certified\") is True'"
        );
    }

    let root = project_path.parent().unwrap_or_else(|| Path::new("."));
    let mut commands = obligation
        .artifact_refs
        .iter()
        .map(|artifact| {
            let artifact_path = root.join(&artifact.path);
            format!(
                "clean math artifact replay --project {} --cache --cache-dir .clean/replay-cache {} --json",
                shell_arg_path(project_path),
                shell_arg_path(&artifact_path)
            )
        })
        .collect::<Vec<_>>();
    commands.push(format!(
        "clean math project hygiene --project {} --json",
        shell_arg_path(project_path)
    ));
    commands.join(" && ")
}

fn valid_obligation_acceptance(obligation: &MathObligation) -> Vec<String> {
    if obligation.artifact_refs.is_empty() {
        vec![
            "certificate extraction reports proof_status closed".to_owned(),
            "certificate extraction reports kernel_certified true from checked kernel evidence"
                .to_owned(),
            "proof result has explicit trust accounting".to_owned(),
        ]
    } else {
        vec![
            "all referenced artifacts replay through clean math artifact replay".to_owned(),
            "project-local replay cache links passing replay evidence to the obligation".to_owned(),
            "project hygiene remains pass or produces only acknowledged warnings".to_owned(),
        ]
    }
}

fn shell_arg_path(path: &Path) -> String {
    shell_arg(&path.display().to_string())
}

fn shell_arg(value: &str) -> String {
    format!("'{}'", value.replace('\'', "'\\''"))
}

fn obligation_source_repair_issue_row(
    project_path: &Path,
    manifest: &MathProjectManifest,
    source: &str,
    path: &Path,
) -> IssuePlanRow {
    let phase = "Phase 3";
    let phase_title = "Generic obligation ABI";
    let workstream = format!("{}/obligation-source-repair", manifest.domain_profile);
    let files = vec![source.to_owned()];
    let acceptance = vec![
        "obligation source is valid clean-obligation-v1 JSON".to_owned(),
        "obligation validates through clean math obligation validate".to_owned(),
    ];
    let verification_command = format!(
        "clean math obligation validate {} --project {} --json",
        path.display(),
        project_path.display()
    );
    IssuePlanRow {
        filing_key: format!("{phase}/{workstream}/{source}"),
        dedupe_key: String::new(),
        dedupe_status: String::new(),
        ranking: fixed_ranking_signals(manifest, 400, "source-repair"),
        phase,
        phase_title,
        workstream: workstream.clone(),
        title: format!(
            "[{}][{}] repair obligation source {}",
            manifest.domain_profile, workstream, source
        ),
        priority: "P1",
        scope: "obligation-source-repair".to_owned(),
        files,
        labels: manifest.issue_routing.labels.clone(),
        owners: manifest.issue_routing.owners.clone(),
        blocking_categories: manifest.issue_routing.blocking_categories.clone(),
        filing_metadata: issue_plan_filing_metadata(
            manifest,
            &[source.to_owned()],
            &["source-repair".to_owned()],
            &verification_command,
        ),
        dependencies: Vec::new(),
        acceptance: acceptance.clone(),
        verification_command: verification_command.clone(),
        issue_body: issue_body(
            phase,
            phase_title,
            &workstream,
            "Repair the listed obligation source so the project can generate proof work.",
            &[source.to_owned()],
            &manifest.issue_routing.blocking_categories,
            &acceptance,
            &verification_command,
        ),
    }
}

fn invalid_obligation_issue_row(
    project_path: &Path,
    manifest: &MathProjectManifest,
    source: &str,
    path: &Path,
    violations: &[ValidationViolation],
) -> IssuePlanRow {
    let phase = "Phase 3";
    let phase_title = "Generic obligation ABI";
    let workstream = format!("{}/obligation-source-repair", manifest.domain_profile);
    let files = vec![source.to_owned()];
    let codes = unique_violation_codes(violations);
    let code_suffix = if codes.is_empty() {
        "invalid".to_owned()
    } else {
        codes.join("+")
    };
    let blockers = codes
        .iter()
        .map(|code| (*code).to_owned())
        .collect::<Vec<_>>();
    let violation_summary = violations
        .iter()
        .filter(|violation| violation.severity == "error")
        .map(|violation| {
            format!(
                "- {} at `{}`: {}",
                violation.code, violation.path, violation.message
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let acceptance = vec![
        "obligation source is valid clean-obligation-v1 JSON".to_owned(),
        "obligation validates without error-level violations".to_owned(),
        "issue plan no longer routes this source as obligation closure work".to_owned(),
    ];
    let verification_command = format!(
        "clean math obligation validate {} --project {} --json",
        path.display(),
        project_path.display()
    );
    let scope = format!(
        "Repair semantic validation violations in obligation source `{source}`.\n\n{}",
        violation_summary
    );
    IssuePlanRow {
        filing_key: format!("{phase}/{workstream}/{source}/{code_suffix}"),
        dedupe_key: String::new(),
        dedupe_status: String::new(),
        ranking: fixed_ranking_signals(manifest, 450, "invalid-obligation"),
        phase,
        phase_title,
        workstream: workstream.clone(),
        title: format!(
            "[{}][{}] repair invalid obligation source {} ({})",
            manifest.domain_profile, workstream, source, code_suffix
        ),
        priority: "P1",
        scope: scope.clone(),
        files: files.clone(),
        labels: manifest.issue_routing.labels.clone(),
        owners: manifest.issue_routing.owners.clone(),
        blocking_categories: manifest.issue_routing.blocking_categories.clone(),
        filing_metadata: issue_plan_filing_metadata(
            manifest,
            &files,
            &blockers,
            &verification_command,
        ),
        dependencies: Vec::new(),
        acceptance: acceptance.clone(),
        verification_command: verification_command.clone(),
        issue_body: issue_body(
            phase,
            phase_title,
            &workstream,
            &scope,
            &files,
            &manifest.issue_routing.blocking_categories,
            &acceptance,
            &verification_command,
        ),
    }
}

fn unique_violation_codes(violations: &[ValidationViolation]) -> Vec<&'static str> {
    let mut codes = violations
        .iter()
        .filter(|violation| violation.severity == "error")
        .map(|violation| violation.code)
        .collect::<Vec<_>>();
    codes.sort_unstable();
    codes.dedup();
    codes
}

fn seed_obligation_issue_row(project_path: &Path, manifest: &MathProjectManifest) -> IssuePlanRow {
    let phase = "Phase 1";
    let phase_title = "Manifest and project status";
    let workstream = format!("{}/project-setup", manifest.domain_profile);
    let project_file = project_path.display().to_string();
    let acceptance = vec!["manifest lists at least one obligation source".to_owned()];
    let verification_command = format!(
        "clean math project status --project {} --json",
        project_path.display()
    );
    IssuePlanRow {
        filing_key: format!("{phase}/{workstream}/seed-obligation"),
        dedupe_key: String::new(),
        dedupe_status: String::new(),
        ranking: fixed_ranking_signals(manifest, 100, "seed-obligation"),
        phase,
        phase_title,
        workstream: workstream.clone(),
        title: format!(
            "[{}][{}] seed first project obligation",
            manifest.domain_profile, workstream
        ),
        priority: "P2",
        scope: "project-setup".to_owned(),
        files: vec![project_file.clone()],
        labels: manifest.issue_routing.labels.clone(),
        owners: manifest.issue_routing.owners.clone(),
        blocking_categories: manifest.issue_routing.blocking_categories.clone(),
        filing_metadata: issue_plan_filing_metadata(
            manifest,
            std::slice::from_ref(&project_file),
            &["seed-obligation".to_owned()],
            &verification_command,
        ),
        dependencies: Vec::new(),
        acceptance: acceptance.clone(),
        verification_command: verification_command.clone(),
        issue_body: issue_body(
            phase,
            phase_title,
            &workstream,
            "Add the first obligation source to make project proof work fileable.",
            &[project_file],
            &manifest.issue_routing.blocking_categories,
            &acceptance,
            &verification_command,
        ),
    }
}

fn hygiene_violation_issue_row(
    project_path: &Path,
    manifest: &MathProjectManifest,
    violation: &ValidationViolation,
) -> IssuePlanRow {
    let phase = "Phase 8";
    let phase_title = "Project hygiene";
    let workstream = "framework/hygiene-gate".to_owned();
    let file = if violation.path.starts_with("obligation_sources[") {
        violation.path.clone()
    } else {
        project_path.display().to_string()
    };
    let files = vec![file];
    let acceptance = vec![
        format!("hygiene violation {} no longer appears", violation.code),
        "clean math project hygiene reports pass".to_owned(),
    ];
    let verification_command = hygiene_gate_command(project_path);
    IssuePlanRow {
        filing_key: format!("{phase}/{workstream}/{}", violation.code),
        dedupe_key: String::new(),
        dedupe_status: String::new(),
        ranking: fixed_ranking_signals(manifest, 1000, violation.code),
        phase,
        phase_title,
        workstream: workstream.clone(),
        title: format!(
            "[{}][{}] clear hygiene violation {}",
            manifest.domain_profile, workstream, violation.code
        ),
        priority: "P0",
        scope: format!(
            "promotion-gate hygiene violation {} at {}: {}",
            violation.code, violation.path, violation.message
        ),
        files: files.clone(),
        labels: manifest.issue_routing.labels.clone(),
        owners: manifest.issue_routing.owners.clone(),
        blocking_categories: manifest.issue_routing.blocking_categories.clone(),
        filing_metadata: issue_plan_filing_metadata(
            manifest,
            &files,
            &[violation.code.to_owned()],
            &verification_command,
        ),
        dependencies: Vec::new(),
        acceptance: acceptance.clone(),
        verification_command: verification_command.clone(),
        issue_body: issue_body(
            phase,
            phase_title,
            &workstream,
            &format!(
                "Clear promotion-gate hygiene violation {} at `{}`.\n\n{}",
                violation.code, violation.path, violation.message
            ),
            &files,
            &manifest.issue_routing.blocking_categories,
            &acceptance,
            &verification_command,
        ),
    }
}

fn obligation_workstream(manifest: &MathProjectManifest, obligation: &MathObligation) -> String {
    let suffix = obligation
        .metadata
        .get("artifact_kind")
        .or_else(|| obligation.metadata.get("transformation"))
        .or_else(|| obligation.metadata.get("benchmark_family"))
        .cloned()
        .or_else(|| {
            obligation
                .artifact_refs
                .first()
                .map(|artifact| artifact.kind.clone())
        })
        .unwrap_or_else(|| "proof-closure".to_owned());
    let workstream = format!("{}/{}", obligation.producer.system, suffix)
        .replace('_', "-")
        .trim_matches('/')
        .to_owned();
    if workstream.is_empty() {
        format!("{}/proof-closure", manifest.domain_profile)
    } else {
        workstream
    }
}

fn issue_plan_phases(rows: &[IssuePlanRow]) -> Vec<IssuePlanPhase> {
    let mut counts: BTreeMap<(&'static str, &'static str), usize> = BTreeMap::new();
    for row in rows {
        *counts.entry((row.phase, row.phase_title)).or_default() += 1;
    }
    counts
        .into_iter()
        .map(|((id, title), row_count)| IssuePlanPhase {
            id,
            title,
            row_count,
        })
        .collect()
}

fn issue_plan_workstreams(rows: &[IssuePlanRow]) -> Vec<IssuePlanWorkstream> {
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    for row in rows {
        *counts.entry(row.workstream.clone()).or_default() += 1;
    }
    counts
        .into_iter()
        .map(|(id, row_count)| IssuePlanWorkstream {
            title: id.clone(),
            id,
            row_count,
        })
        .collect()
}

fn issue_body(
    phase: &str,
    phase_title: &str,
    workstream: &str,
    scope: &str,
    files: &[String],
    blockers: &[String],
    acceptance: &[String],
    verification_command: &str,
) -> String {
    let mut body = String::new();
    body.push_str("## Routing\n");
    body.push_str(&format!("- Phase: {phase} - {phase_title}\n"));
    body.push_str(&format!("- Workstream: {workstream}\n"));
    if !blockers.is_empty() {
        body.push_str(&format!("- Blocking categories: {}\n", blockers.join(", ")));
    }
    body.push_str("\n## Scope\n");
    body.push_str(scope);
    body.push_str("\n\n## Files\n");
    for file in files {
        body.push_str(&format!("- `{file}`\n"));
    }
    body.push_str("\n## Acceptance\n");
    for item in acceptance {
        body.push_str(&format!("- {item}\n"));
    }
    body.push_str("\n## Verification\n");
    body.push_str("```sh\n");
    body.push_str(verification_command);
    body.push_str("\n```\n");
    body
}

pub fn certificate_summary(
    manifest: &MathProjectManifest,
    obligation_id: &str,
    artifact_hash: Option<String>,
) -> CertificateSummary {
    let mut trust_summary = BTreeMap::new();
    trust_summary.insert(
        "allowed_axioms".to_owned(),
        Value::Array(
            manifest
                .trust_policy
                .allowed_axioms
                .iter()
                .map(|s| Value::String(s.clone()))
                .collect(),
        ),
    );
    trust_summary.insert(
        "forbidden_trust_markers".to_owned(),
        Value::Array(
            manifest
                .trust_policy
                .forbidden_trust_markers
                .iter()
                .map(|s| Value::String(s.clone()))
                .collect(),
        ),
    );
    trust_summary.insert(
        "require_artifact_replay".to_owned(),
        Value::Bool(manifest.trust_policy.require_artifact_replay),
    );
    trust_summary.insert("evidence_kind".to_owned(), Value::String("none".to_owned()));
    trust_summary.insert("kernel_certified".to_owned(), Value::Bool(false));
    CertificateSummary {
        schema: CERTIFICATE_SCHEMA_VERSION,
        project: manifest.project.clone(),
        domain_profile: manifest.domain_profile.clone(),
        theorem: "pending-kernel-theorem".to_owned(),
        obligation: obligation_id.to_owned(),
        artifact: artifact_hash,
        direction: "soundness".to_owned(),
        proof_status: "blocked-until-kernel-proof-or-replay".to_owned(),
        evidence_kind: "none".to_owned(),
        kernel_certified: false,
        trust_policy: manifest.trust_policy.name.clone(),
        synthetic_sorry: false,
        kernel_evidence: None,
        trust_summary,
    }
}

pub fn obligation_fingerprint(obligation: &MathObligation) -> String {
    fingerprint_json(&canonical_obligation_fingerprint_input(obligation))
}

pub fn fingerprint_json<T: Serialize>(value: &T) -> String {
    let bytes = serde_json::to_vec(value).expect("serializing fingerprint input should not fail");
    let digest = Sha256::digest(&bytes);
    format!("sha256:{}", hex_lower(&digest))
}

fn canonical_obligation_fingerprint_input(
    obligation: &MathObligation,
) -> CanonicalObligationFingerprintInput {
    let mut local_context = obligation
        .local_context
        .iter()
        .map(canonical_obligation_binding)
        .collect::<Vec<_>>();
    local_context.sort_by(|left, right| {
        left.name
            .cmp(&right.name)
            .then_with(|| left.type_identity.cmp(&right.type_identity))
    });

    let mut side_conditions = obligation.side_conditions.clone();
    side_conditions.sort();

    let mut artifact_refs = obligation
        .artifact_refs
        .iter()
        .map(canonical_artifact_ref)
        .collect::<Vec<_>>();
    artifact_refs.sort_by(|left, right| {
        left.kind
            .cmp(&right.kind)
            .then_with(|| left.hash.cmp(&right.hash))
            .then_with(|| left.path.cmp(&right.path))
    });

    CanonicalObligationFingerprintInput {
        domain_profile: obligation.domain_profile.clone(),
        goal: CanonicalObligationGoal {
            expr: obligation
                .goal
                .expr
                .canonical_fingerprint_payload()
                .to_owned(),
        },
        local_context,
        side_conditions,
        artifact_refs,
        trust_policy: obligation.trust_policy.clone(),
    }
}

fn canonical_obligation_binding(binding: &ObligationBinding) -> CanonicalObligationBinding {
    let raw_type = binding
        .type_expr
        .as_deref()
        .unwrap_or(binding.type_pp.as_str());
    let type_identity = canonical_kernel_expr_json_from_str(raw_type).unwrap_or_else(|| {
        binding
            .type_expr
            .clone()
            .unwrap_or_else(|| binding.type_pp.clone())
    });
    CanonicalObligationBinding {
        name: binding.name.clone(),
        type_identity,
    }
}

fn canonical_artifact_ref(artifact: &ArtifactRef) -> CanonicalArtifactRef {
    CanonicalArtifactRef {
        kind: artifact.kind.clone(),
        hash: artifact.hash.clone(),
        path: artifact
            .hash
            .as_ref()
            .is_none()
            .then(|| artifact.path.clone()),
    }
}

pub fn has_error(violations: &[ValidationViolation]) -> bool {
    violations.iter().any(|v| v.severity == "error")
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_owned()).collect()
}

fn require_non_empty(
    violations: &mut Vec<ValidationViolation>,
    code: &'static str,
    path: &str,
    value: &str,
) {
    if value.trim().is_empty() {
        violations.push(error(code, path, "field must not be empty".to_owned()));
    }
}

fn require_eq(
    violations: &mut Vec<ValidationViolation>,
    code: &'static str,
    path: &str,
    found: &str,
    expected: &str,
) {
    if found != expected {
        violations.push(error(
            code,
            path,
            format!("expected `{expected}`, found `{found}`"),
        ));
    }
}

fn check_relative_path(
    root: &Path,
    value: &str,
    code: &'static str,
    path: &str,
    violations: &mut Vec<ValidationViolation>,
) -> bool {
    if value.trim().is_empty() {
        violations.push(error(code, path, "path must not be empty".to_owned()));
        return false;
    }
    if !root.join(value).exists() {
        violations.push(warn(
            code,
            path,
            format!(
                "referenced path `{}` does not exist",
                root.join(value).display()
            ),
        ));
        return false;
    }
    true
}

fn check_required_relative_path(
    root: &Path,
    value: &str,
    code: &'static str,
    path: &str,
    violations: &mut Vec<ValidationViolation>,
) -> bool {
    if value.trim().is_empty() {
        violations.push(error(code, path, "path must not be empty".to_owned()));
        return false;
    }
    if !root.join(value).exists() {
        violations.push(error(
            code,
            path,
            format!(
                "referenced path `{}` does not exist",
                root.join(value).display()
            ),
        ));
        return false;
    }
    true
}

fn validate_obligation_source(
    root: &Path,
    manifest: &MathProjectManifest,
    source: &str,
    idx: usize,
    violations: &mut Vec<ValidationViolation>,
) {
    let source_path = root.join(source);
    match load_json::<MathObligation>(&source_path) {
        Ok(obligation) => {
            violations.extend(
                validate_obligation_with_artifact_root(Some(root), &obligation, Some(manifest))
                    .into_iter()
                    .map(|violation| {
                        contextual_violation(violation, &format!("obligation_sources[{idx}]"))
                    }),
            );
        }
        Err(err) => violations.push(error(
            "MP013",
            &format!("obligation_sources[{idx}]"),
            format!(
                "failed to load obligation source `{}`: {err}",
                source_path.display()
            ),
        )),
    }
}

fn validate_theorem_pack_trust(
    root: &Path,
    theorem_pack: &str,
    idx: usize,
    trust_policy: &TrustPolicy,
    violations: &mut Vec<ValidationViolation>,
) {
    if theorem_pack.trim().is_empty() {
        return;
    }
    let path = root.join(theorem_pack);
    if !path.exists() {
        return;
    }
    let contents = match fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(source) => {
            violations.push(error(
                "MP014",
                &format!("theorem_packs[{idx}]"),
                format!("failed to read theorem pack `{}`: {source}", path.display()),
            ));
            return;
        }
    };
    for marker in THEOREM_PACK_TRUST_MARKERS {
        if trust_policy
            .forbidden_trust_markers
            .iter()
            .any(|forbidden| forbidden == marker)
            && contains_trust_marker(&contents, marker)
        {
            violations.push(error(
                "MP015",
                &format!("theorem_packs[{idx}]"),
                format!(
                    "forbidden trust marker `{marker}` found in theorem pack `{}`",
                    path.display()
                ),
            ));
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TheoremPackDeclKind {
    Theorem,
    Axiom,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TheoremPackCandidate {
    name: String,
    kind: TheoremPackDeclKind,
    line: usize,
    unsafe_declaration: bool,
    text: String,
}

fn validate_theorem_pack_indexability(
    root: &Path,
    theorem_pack: &str,
    idx: usize,
    trust_policy: &TrustPolicy,
    violations: &mut Vec<ValidationViolation>,
) {
    if theorem_pack.trim().is_empty() {
        return;
    }
    let violation_path = format!("theorem_packs[{idx}]");
    let path = root.join(theorem_pack);
    if !path.exists() {
        return;
    }
    if path.extension().and_then(|ext| ext.to_str()) != Some("lean") {
        violations.push(error(
            "MP025",
            &violation_path,
            format!(
                "theorem pack `{}` is not theorem-indexable because it is not a .lean source file",
                path.display()
            ),
        ));
        return;
    }
    let contents = match fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(source) => {
            violations.push(error(
                "MP026",
                &violation_path,
                format!(
                    "theorem-index diagnostic for theorem pack `{}`: failed to read source text: {source}",
                    path.display()
                ),
            ));
            return;
        }
    };
    let (candidates, diagnostics) = theorem_pack_candidates(&contents);
    violations.extend(diagnostics.into_iter().map(|message| {
        error(
            "MP026",
            &violation_path,
            format!(
                "theorem-index diagnostic for theorem pack `{}`: {message}",
                path.display()
            ),
        )
    }));
    if candidates.is_empty() {
        violations.push(error(
            "MP025",
            &violation_path,
            format!(
                "theorem pack `{}` has no theorem-indexable theorem or axiom declarations",
                path.display()
            ),
        ));
    }
    for candidate in candidates {
        validate_theorem_pack_candidate_trust(
            &candidate,
            trust_policy,
            &violation_path,
            violations,
        );
    }
}

fn theorem_pack_candidates(contents: &str) -> (Vec<TheoremPackCandidate>, Vec<String>) {
    let mut candidates = Vec::new();
    let mut diagnostics = Vec::new();
    let mut namespace = Vec::<String>::new();
    let mut current = None::<TheoremPackCandidate>;

    for (line_idx, raw_line) in contents.lines().enumerate() {
        let line_no = line_idx + 1;
        let source_line = raw_line.split("--").next().unwrap_or("");
        let trimmed = source_line.trim();
        if trimmed.is_empty() {
            if let Some(candidate) = current.as_mut() {
                candidate.text.push('\n');
            }
            continue;
        }
        if let Some(rest) = trimmed.strip_prefix("namespace ") {
            if let Some(name) = take_theorem_pack_decl_name(rest) {
                namespace.push(name.to_owned());
            }
        } else if trimmed == "end" || trimmed.starts_with("end ") {
            namespace.pop();
        }

        match parse_theorem_pack_header(trimmed, &namespace) {
            TheoremPackHeader::Candidate {
                name,
                kind,
                unsafe_declaration,
            } => {
                if let Some(candidate) = current.take() {
                    candidates.push(candidate);
                }
                current = Some(TheoremPackCandidate {
                    name,
                    kind,
                    line: line_no,
                    unsafe_declaration,
                    text: source_line.to_owned(),
                });
            }
            TheoremPackHeader::Malformed(message) => {
                diagnostics.push(format!("{message} on line {line_no}"))
            }
            TheoremPackHeader::None => {
                if let Some(candidate) = current.as_mut() {
                    candidate.text.push('\n');
                    candidate.text.push_str(source_line);
                }
            }
        }
    }
    if let Some(candidate) = current {
        candidates.push(candidate);
    }
    (candidates, diagnostics)
}

enum TheoremPackHeader {
    Candidate {
        name: String,
        kind: TheoremPackDeclKind,
        unsafe_declaration: bool,
    },
    Malformed(String),
    None,
}

fn parse_theorem_pack_header(line: &str, namespace: &[String]) -> TheoremPackHeader {
    let mut rest = line.trim_start();
    let mut unsafe_declaration = false;
    loop {
        let Some((modifier, after)) = split_first_word(rest) else {
            return TheoremPackHeader::None;
        };
        match modifier {
            "unsafe" => {
                unsafe_declaration = true;
                rest = after.trim_start();
            }
            "private" | "protected" | "noncomputable" | "partial" => {
                rest = after.trim_start();
            }
            _ => break,
        }
    }

    for (keyword, kind) in [
        ("theorem", TheoremPackDeclKind::Theorem),
        ("axiom", TheoremPackDeclKind::Axiom),
    ] {
        let Some(after_keyword) = rest.strip_prefix(keyword) else {
            continue;
        };
        if !after_keyword
            .chars()
            .next()
            .is_some_and(char::is_whitespace)
        {
            continue;
        }
        let name_rest = after_keyword.trim_start();
        let Some(name) = take_theorem_pack_decl_name(name_rest) else {
            return TheoremPackHeader::Malformed(format!(
                "`{keyword}` declaration is missing an indexable name"
            ));
        };
        let full_name = if name.contains('.') || namespace.is_empty() {
            name.to_owned()
        } else {
            format!("{}.{}", namespace.join("."), name)
        };
        return TheoremPackHeader::Candidate {
            name: full_name,
            kind,
            unsafe_declaration,
        };
    }
    TheoremPackHeader::None
}

fn split_first_word(value: &str) -> Option<(&str, &str)> {
    let value = value.trim_start();
    let end = value.find(char::is_whitespace)?;
    Some((&value[..end], &value[end..]))
}

fn take_theorem_pack_decl_name(value: &str) -> Option<&str> {
    let end = value
        .char_indices()
        .take_while(|(_, ch)| is_theorem_pack_ident_char(*ch))
        .map(|(idx, ch)| idx + ch.len_utf8())
        .last()
        .unwrap_or(0);
    if end == 0 {
        None
    } else {
        Some(&value[..end])
    }
}

fn is_theorem_pack_ident_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_' || ch == '\'' || ch == '.'
}

fn validate_theorem_pack_candidate_trust(
    candidate: &TheoremPackCandidate,
    trust_policy: &TrustPolicy,
    pack_path: &str,
    violations: &mut Vec<ValidationViolation>,
) {
    let forbidden = trust_policy
        .forbidden_trust_markers
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let mut reasons = Vec::new();
    let clean_text = candidate
        .text
        .lines()
        .map(|line| line.split("--").next().unwrap_or(""))
        .collect::<Vec<_>>()
        .join(" ");

    if contains_trust_marker(&clean_text, "sorry") && forbidden.contains("sorry") {
        reasons.push("explicit sorry is forbidden by trust policy".to_owned());
    }
    if candidate.unsafe_declaration && forbidden.contains("unsafe") {
        reasons.push("unsafe declaration is forbidden by trust policy".to_owned());
    }
    for marker in ["synthetic_sorry", "sorryAx", "trustedArith", "trustedAy"] {
        if forbidden.contains(marker) && contains_trust_marker(&clean_text, marker) {
            reasons.push(format!("{marker} is forbidden by trust policy"));
        }
    }
    if candidate.kind == TheoremPackDeclKind::Axiom
        && !trust_policy
            .allowed_axioms
            .iter()
            .any(|allowed| allowed == "*" || allowed == &candidate.name)
    {
        reasons.push("axiom declaration is not allowed by trust policy".to_owned());
    }

    for reason in reasons {
        violations.push(error(
            "MP027",
            &format!("{pack_path}.candidates[{}]", candidate.name),
            format!(
                "theorem-index candidate `{}` on line {} is incompatible with trust policy `{}`: {reason}",
                candidate.name, candidate.line, trust_policy.name
            ),
        ));
    }
}

fn validate_project_replay_evidence(
    root: &Path,
    manifest: &MathProjectManifest,
    violations: &mut Vec<ValidationViolation>,
) {
    let evidence = load_replay_evidence(root, manifest);

    for (source_idx, source) in manifest.obligation_sources.iter().enumerate() {
        let source_path = root.join(source);
        let Ok(obligation) = load_json::<MathObligation>(&source_path) else {
            continue;
        };
        if obligation.artifact_refs.is_empty() {
            continue;
        }
        let fingerprint = obligation_fingerprint(&obligation);
        for (artifact_idx, artifact) in obligation.artifact_refs.iter().enumerate() {
            let replay_reports = evidence
                .iter()
                .filter(|(_, value)| {
                    replay_evidence_targets_artifact_ref(root, value, &fingerprint, artifact)
                })
                .collect::<Vec<_>>();
            let violation_path =
                format!("obligation_sources[{source_idx}].artifact_refs[{artifact_idx}]");
            if replay_reports.is_empty() {
                violations.push(error(
                    "MP016",
                    &violation_path,
                    format!(
                        "artifact ref `{}` has no passing replay evidence linked to obligation {fingerprint}",
                        artifact.path
                    ),
                ));
                continue;
            }
            for (evidence_path, report) in replay_reports {
                if replay_status(report) != Some("pass") {
                    violations.push(error(
                        "MP017",
                        &violation_path,
                        format!(
                            "replay evidence `{}` linked to {fingerprint} is not pass",
                            evidence_path.display()
                        ),
                    ));
                }
                if replay_evidence_kind(report) != Some("replay_only")
                    || replay_kernel_certified(report).unwrap_or(true)
                {
                    violations.push(error(
                        "MP024",
                        &violation_path,
                        format!(
                            "replay evidence `{}` linked to {fingerprint} must be replay_only and kernel_certified=false",
                            evidence_path.display()
                        ),
                    ));
                }
                if !replay_trusted_assumptions(report).is_empty() {
                    violations.push(error(
                        "MP018",
                        &violation_path,
                        format!(
                            "replay evidence `{}` linked to {fingerprint} carries trusted assumptions",
                            evidence_path.display()
                        ),
                    ));
                }
                match artifact
                    .hash
                    .as_deref()
                    .filter(|hash| !hash.trim().is_empty())
                {
                    Some(expected_hash) => {
                        if !replay_hashes(report).contains(&expected_hash) {
                            violations.push(error(
                                "MP017",
                                &violation_path,
                                format!(
                                    "replay evidence `{}` is stale for artifact hash `{expected_hash}`",
                                    evidence_path.display()
                                ),
                            ));
                        }
                    }
                    None => {
                        violations.push(error(
                            "MP017",
                            &violation_path,
                            format!(
                                "artifact ref `{}` must declare a non-empty hash before replay evidence `{}` can satisfy it",
                                artifact.path,
                                evidence_path.display(),
                            ),
                        ));
                    }
                }
            }
        }
    }
}

fn load_replay_evidence(root: &Path, manifest: &MathProjectManifest) -> Vec<(PathBuf, Value)> {
    let mut evidence = manifest
        .evidence
        .iter()
        .filter_map(|rel| load_evidence_json(root, rel))
        .collect::<Vec<_>>();
    evidence.extend(
        replay_cache_report_paths(root, manifest)
            .into_iter()
            .filter_map(|path| load_evidence_json_path(&path)),
    );
    evidence
}

fn load_evidence_json(root: &Path, rel: &str) -> Option<(PathBuf, Value)> {
    load_evidence_json_path(&root.join(rel))
}

fn load_evidence_json_path(path: &Path) -> Option<(PathBuf, Value)> {
    let contents = fs::read_to_string(path).ok()?;
    let value = serde_json::from_str::<Value>(&contents).ok()?;
    Some((path.to_owned(), value))
}

pub fn replay_cache_summary(root: &Path, manifest: &MathProjectManifest) -> ReplayCacheSummary {
    let roots = replay_cache_roots(root, manifest);
    let mut summary = ReplayCacheSummary {
        roots: roots
            .iter()
            .map(|path| display_project_relative(root, path))
            .collect(),
        ..ReplayCacheSummary::default()
    };
    for path in replay_cache_report_paths_from_roots(root, &roots) {
        let Some((_, report)) = load_evidence_json_path(&path) else {
            continue;
        };
        summary.cached_reports += 1;
        match replay_status(&report) {
            Some("pass") => summary.pass += 1,
            Some("fail") => summary.fail += 1,
            Some("blocked") => summary.blocked += 1,
            _ => {}
        }
    }
    summary
}

fn replay_cache_report_paths(root: &Path, manifest: &MathProjectManifest) -> Vec<PathBuf> {
    let roots = replay_cache_roots(root, manifest);
    replay_cache_report_paths_from_roots(root, &roots)
}

fn replay_cache_report_paths_from_roots(root: &Path, roots: &[PathBuf]) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    for cache_root in roots {
        let index_path = cache_root.join("index.json");
        let Ok(index) = load_json::<ReplayCacheIndex>(&index_path) else {
            continue;
        };
        if index.schema_version != REPLAY_CACHE_INDEX_SCHEMA_VERSION {
            continue;
        }
        for entry in index.reports {
            let path = PathBuf::from(entry.report_path);
            let path = if path.is_absolute() {
                path
            } else {
                root.join(path)
            };
            if !paths.contains(&path) {
                paths.push(path);
            }
        }
    }
    paths
}

pub fn replay_cache_roots(root: &Path, manifest: &MathProjectManifest) -> Vec<PathBuf> {
    let mut roots = vec![root.join(DEFAULT_REPLAY_CACHE_ROOT)];
    let registry_path = root.join(DEFAULT_REPLAY_CACHE_ROOT).join("roots.json");
    if let Ok(registry) = load_json::<ReplayCacheRoots>(&registry_path) {
        if registry.schema_version == REPLAY_CACHE_ROOTS_SCHEMA_VERSION
            && registry.project == manifest.project
        {
            for cache_root in registry.roots {
                let path = PathBuf::from(cache_root);
                let path = if path.is_absolute() {
                    path
                } else {
                    root.join(path)
                };
                if !roots.contains(&path) {
                    roots.push(path);
                }
            }
        }
    }
    roots
}

pub fn display_project_relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .display()
        .to_string()
}

fn replay_evidence_links_obligation(report: &Value, fingerprint: &str) -> bool {
    report
        .get("schema_version")
        .and_then(Value::as_str)
        .is_some_and(|schema| schema == ARTIFACT_REPLAY_SCHEMA_VERSION)
        && report
            .get("linked_obligations")
            .and_then(Value::as_array)
            .is_some_and(|linked| linked.iter().any(|value| value == fingerprint))
}

fn replay_evidence_targets_artifact_ref(
    root: &Path,
    report: &Value,
    fingerprint: &str,
    artifact: &ArtifactRef,
) -> bool {
    replay_evidence_links_obligation(report, fingerprint)
        && replay_artifact_kind_matches(report, artifact)
        && replay_artifact_path_matches(root, report, artifact)
}

fn replay_artifact_kind_matches(report: &Value, artifact: &ArtifactRef) -> bool {
    let expected_kind = artifact.kind.trim();
    let Some(report_kind) = report
        .get("artifact_kind")
        .and_then(Value::as_str)
        .map(str::trim)
        .filter(|kind| !kind.is_empty())
    else {
        return false;
    };
    report_kind == expected_kind
        || (expected_kind == "proof-artifact-v1"
            && report
                .get("schema_version")
                .and_then(Value::as_str)
                .is_some_and(|schema| schema == ARTIFACT_REPLAY_SCHEMA_VERSION))
}

fn replay_artifact_path_matches(root: &Path, report: &Value, artifact: &ArtifactRef) -> bool {
    let Some(report_path) = report
        .get("artifact_path")
        .and_then(Value::as_str)
        .map(str::trim)
        .filter(|path| !path.is_empty())
    else {
        return false;
    };
    let Ok(expected) = root.join(&artifact.path).canonicalize() else {
        return false;
    };
    let report_path = PathBuf::from(report_path);
    if report_path.is_absolute() {
        return report_path
            .canonicalize()
            .is_ok_and(|path| path == expected);
    }
    [root.join(&report_path), report_path]
        .into_iter()
        .any(|path| path.canonicalize().is_ok_and(|path| path == expected))
}

fn replay_status(report: &Value) -> Option<&str> {
    report.get("replay_status").and_then(Value::as_str)
}

fn replay_evidence_kind(report: &Value) -> Option<&str> {
    report.get("evidence_kind").and_then(Value::as_str)
}

fn replay_kernel_certified(report: &Value) -> Option<bool> {
    report.get("kernel_certified").and_then(Value::as_bool)
}

fn replay_trusted_assumptions(report: &Value) -> Vec<&str> {
    report
        .get("trusted_assumptions")
        .and_then(Value::as_array)
        .map(|assumptions| {
            assumptions
                .iter()
                .filter_map(Value::as_str)
                .collect::<Vec<_>>()
        })
        .unwrap_or_default()
}

fn replay_hashes(report: &Value) -> Vec<&str> {
    ["problem_hash", "proof_hash"]
        .iter()
        .filter_map(|field| report.get(field).and_then(Value::as_str))
        .collect()
}

fn validate_artifact_refs(
    artifact_root: Option<&Path>,
    obligation: &MathObligation,
    violations: &mut Vec<ValidationViolation>,
) {
    for (idx, artifact) in obligation.artifact_refs.iter().enumerate() {
        require_non_empty(
            violations,
            "OB016",
            &format!("artifact_refs[{idx}].kind"),
            &artifact.kind,
        );
        if artifact.path.trim().is_empty() {
            violations.push(error(
                "OB017",
                &format!("artifact_refs[{idx}].path"),
                "path must not be empty".to_owned(),
            ));
            continue;
        }
        if let Some(root) = artifact_root {
            let path = root.join(&artifact.path);
            if !path.exists() {
                violations.push(error(
                    "OB017",
                    &format!("artifact_refs[{idx}].path"),
                    format!("referenced artifact `{}` does not exist", path.display()),
                ));
            }
        }
    }
}

fn validate_pretty_only_trust_claims(
    obligation: &MathObligation,
    project: &MathProjectManifest,
    violations: &mut Vec<ValidationViolation>,
) {
    let mut markers = project
        .trust_policy
        .forbidden_trust_markers
        .iter()
        .map(String::as_str)
        .filter(|marker| *marker != "sorry")
        .collect::<Vec<_>>();
    for marker in PRETTY_ONLY_TRUST_MARKERS {
        if !markers.contains(marker) {
            markers.push(marker);
        }
    }

    for marker in markers {
        if contains_trust_marker(&obligation.goal.pretty, marker) {
            violations.push(error(
                "OB018",
                "goal.pretty",
                format!(
                    "pretty-only field contains trust marker `{marker}`; replay/kernel evidence must be linked structurally"
                ),
            ));
        }
        for (idx, local) in obligation.local_context.iter().enumerate() {
            if contains_trust_marker(&local.type_pp, marker) {
                violations.push(error(
                    "OB018",
                    &format!("local_context[{idx}].type_pp"),
                    format!(
                        "pretty-only field contains trust marker `{marker}`; replay/kernel evidence must be linked structurally"
                    ),
                ));
            }
        }
    }
}

fn validate_obligation_hidden_trust_markers(
    obligation: &MathObligation,
    project: Option<&MathProjectManifest>,
    violations: &mut Vec<ValidationViolation>,
) {
    let mut markers = project
        .map(|manifest| {
            manifest
                .trust_policy
                .forbidden_trust_markers
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    for marker in THEOREM_PACK_TRUST_MARKERS
        .iter()
        .chain(PRETTY_ONLY_TRUST_MARKERS.iter())
    {
        if !markers.contains(marker) {
            markers.push(marker);
        }
    }

    for marker in markers {
        if contains_trust_marker(&obligation.goal.expr, marker) {
            violations.push(error(
                "OB019",
                "goal.expr",
                format!(
                    "obligation kernel field contains hidden trust marker `{marker}`; link replay or kernel evidence structurally"
                ),
            ));
        }
        for (idx, local) in obligation.local_context.iter().enumerate() {
            if local
                .type_expr
                .as_deref()
                .is_some_and(|type_expr| contains_trust_marker(type_expr, marker))
            {
                violations.push(error(
                    "OB019",
                    &format!("local_context[{idx}].type_expr"),
                    format!(
                        "obligation kernel field contains hidden trust marker `{marker}`; link replay or kernel evidence structurally"
                    ),
                ));
            }
        }
        for (idx, condition) in obligation.side_conditions.iter().enumerate() {
            if contains_trust_marker(condition, marker) {
                violations.push(error(
                    "OB019",
                    &format!("side_conditions[{idx}]"),
                    format!(
                        "obligation side condition contains hidden trust marker `{marker}`; link replay or kernel evidence structurally"
                    ),
                ));
            }
        }
        for (key, value) in &obligation.metadata {
            if contains_trust_marker(value, marker) {
                violations.push(error(
                    "OB019",
                    &format!("metadata.{key}"),
                    format!(
                        "obligation metadata contains hidden trust marker `{marker}`; link replay or kernel evidence structurally"
                    ),
                ));
            }
        }
    }
}

fn contextual_violation(mut violation: ValidationViolation, context: &str) -> ValidationViolation {
    violation.path = format!("{context}.{}", violation.path);
    violation
}

fn contains_trust_marker(contents: &str, marker: &str) -> bool {
    if marker != "sorry" {
        return contents.contains(marker);
    }
    contents.match_indices(marker).any(|(start, _)| {
        is_marker_boundary(contents[..start].chars().next_back())
            && is_marker_boundary(contents[start + marker.len()..].chars().next())
    })
}

fn is_marker_boundary(ch: Option<char>) -> bool {
    match ch {
        None => true,
        Some(ch) => !ch.is_ascii_alphanumeric() && ch != '_' && ch != '.',
    }
}

fn status_from_violations(violations: &[ValidationViolation]) -> &'static str {
    if violations.iter().any(|v| v.severity == "error") {
        "fail"
    } else if violations.iter().any(|v| v.severity == "warn") {
        "warn"
    } else {
        "pass"
    }
}

fn check(name: &'static str, status: &'static str, message: String) -> HygieneCheck {
    HygieneCheck {
        name,
        status,
        message,
    }
}

fn error(code: &'static str, path: &str, message: String) -> ValidationViolation {
    ValidationViolation {
        code,
        severity: "error",
        path: path.to_owned(),
        message,
    }
}

fn warn(code: &'static str, path: &str, message: String) -> ValidationViolation {
    ValidationViolation {
        code,
        severity: "warn",
        path: path.to_owned(),
        message,
    }
}

fn short_fingerprint(fingerprint: &str) -> String {
    fingerprint
        .strip_prefix("sha256:")
        .unwrap_or(fingerprint)
        .chars()
        .take(12)
        .collect()
}

fn hex_lower(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn write_theorem_pack(root: &Path, rel: &str, contents: &str) {
        let path = root.join(rel);
        fs::create_dir_all(path.parent().expect("theorem pack parent"))
            .expect("create theorem pack parent");
        fs::write(path, contents).expect("write theorem pack");
    }

    fn write_obligation(root: &Path, rel: &str, obligation: &MathObligation) {
        write_json(&root.join(rel), obligation).expect("write obligation fixture");
    }

    fn write_domain_profile(root: &Path, rel: &str, profile: &DomainProfile) {
        write_json(&root.join(rel), profile).expect("write domain profile fixture");
    }

    fn write_proof_failure_diagnostic(
        root: &Path,
        rel: &str,
        evidence: &ProofFailureDiagnosticEvidence,
    ) {
        write_json(&root.join(rel), evidence).expect("write proof failure diagnostic fixture");
    }

    fn write_artifact(root: &Path, rel: &str) {
        let path = root.join(rel);
        fs::create_dir_all(path.parent().expect("artifact parent"))
            .expect("create artifact parent");
        fs::write(path, "{}\n").expect("write artifact fixture");
    }

    fn sample_manifest() -> MathProjectManifest {
        pilot_manifest("sat-pb", "sat-pb-pilot").expect("profile")
    }

    fn sample_obligation() -> MathObligation {
        MathObligation {
            schema_version: OBLIGATION_SCHEMA_VERSION.to_owned(),
            project: "sat-pb-pilot".to_owned(),
            domain_profile: "sat-pb".to_owned(),
            producer: ObligationProducer {
                system: "ay".to_owned(),
                commit: "fixture".to_owned(),
                command: None,
            },
            goal: ObligationGoal {
                expr: GoalExpr::string("SatPb.subsumption_sound c d"),
                pretty: "subsumption is sound".to_owned(),
            },
            local_context: vec![ObligationBinding {
                name: "h".to_owned(),
                type_pp: "subsumes c d = true".to_owned(),
                type_expr: Some("subsumes c d = true".to_owned()),
            }],
            side_conditions: vec!["subsumes c d".to_owned()],
            artifact_refs: Vec::new(),
            metadata: BTreeMap::new(),
            trust_policy: "constructive-only".to_owned(),
        }
    }

    fn toy_profile(adapters: Vec<ArtifactReplayAdapterDescriptor>) -> DomainProfile {
        DomainProfile {
            schema_version: DOMAIN_PROFILE_SCHEMA_VERSION.to_owned(),
            name: "toy-domain".to_owned(),
            description: "Toy local profile for registry tests".to_owned(),
            semantic_heads: strings(&["ToyHead"]),
            normalizers: strings(&["toy_nf"]),
            tactic_recommendations: strings(&["toy_nf", "simp"]),
            artifact_formats: strings(&["toy-artifact-v1"]),
            artifact_replay_adapters: adapters,
            certificate_extractors: strings(&["toy-certificate-summary-v1"]),
            ranking_signals: strings(&["toy_signal"]),
            blocker_kinds: strings(&["toy-blocker"]),
        }
    }

    fn toy_replay_adapter(lifecycle: &str) -> ArtifactReplayAdapterDescriptor {
        ArtifactReplayAdapterDescriptor {
            id: "toy-replay-v1".to_owned(),
            label: "Toy replay".to_owned(),
            domain_profile: "toy-domain".to_owned(),
            source_systems: strings(&["toy"]),
            artifact_formats: strings(&["toy-artifact-v1"]),
            artifact_kinds: strings(&["toy_artifact"]),
            replay_contract: "Inspect-only toy replay descriptor".to_owned(),
            availability: ArtifactReplayAdapterAvailability {
                source: "project-local-profile".to_owned(),
                executor: "unwired".to_owned(),
                requires_external_tool: false,
                feature_gate: None,
            },
            trust: ArtifactReplayAdapterTrust {
                evidence_kind: "replay_only".to_owned(),
                kernel_certified: false,
                allowed_trusted_assumptions: Vec::new(),
                requires_envelope_validation: true,
                requires_problem_hash: true,
                links_obligation_fingerprint: true,
                required_report_fields: strings(&["linked_obligations", "replay_status"]),
            },
            status: ArtifactReplayAdapterStatus {
                phase: "local".to_owned(),
                lifecycle: lifecycle.to_owned(),
                blocker_kind: "artifact-replay".to_owned(),
                report_schema_version: ARTIFACT_REPLAY_SCHEMA_VERSION.to_owned(),
                replay_status_values: strings(&["pass", "fail", "blocked"]),
            },
        }
    }

    fn toy_manifest() -> MathProjectManifest {
        MathProjectManifest {
            schema_version: MATH_PROJECT_SCHEMA_VERSION.to_owned(),
            project: "toy-project".to_owned(),
            domain_profile: "toy-domain".to_owned(),
            owner: "clean-math-factory".to_owned(),
            theorem_packs: vec!["theorem_packs/Toy.lean".to_owned()],
            obligation_sources: vec!["obligations/toy.json".to_owned()],
            artifact_formats: strings(&["toy-artifact-v1"]),
            certificate_extractors: strings(&["toy-certificate-summary-v1"]),
            trust_policy: TrustPolicy {
                name: "constructive-only".to_owned(),
                allowed_axioms: Vec::new(),
                forbidden_trust_markers: strings(&[
                    "sorry",
                    "sorryAx",
                    "trustedArith",
                    "synthetic_sorry",
                ]),
                require_artifact_replay: false,
                allow_synthetic_sorry: false,
            },
            normalizers: strings(&["toy_nf"]),
            evidence: Vec::new(),
            issue_routing: IssueRouting {
                labels: strings(&["math-project", "toy-domain"]),
                owners: Vec::new(),
                blocking_categories: strings(&["manifest", "obligation", "artifact", "trust"]),
            },
        }
    }

    fn toy_obligation() -> MathObligation {
        let mut obligation = sample_obligation();
        obligation.project = "toy-project".to_owned();
        obligation.domain_profile = "toy-domain".to_owned();
        obligation.producer.system = "toy".to_owned();
        obligation.goal.expr = GoalExpr::string("ToyHead.goal");
        obligation.goal.pretty = "toy goal".to_owned();
        obligation.local_context.clear();
        obligation.side_conditions.clear();
        obligation
    }

    #[test]
    fn manifest_validation_rejects_unknown_schema() {
        let mut manifest = sample_manifest();
        manifest.schema_version = "wrong".to_owned();
        let violations = validate_project(Path::new("math-project.json"), &manifest);
        assert!(violations.iter().any(|v| v.code == "MP001"));
    }

    #[test]
    fn manifest_validation_rejects_profile_incompatible_lists_and_routing() {
        let mut manifest = sample_manifest();
        manifest
            .artifact_formats
            .push("gamma-crown-farkas-v1".to_owned());
        manifest.normalizers.push("nn_interval_nf".to_owned());
        manifest.certificate_extractors = vec!["nn-verify-certificate-summary-v1".to_owned()];
        manifest.issue_routing.labels.push("Bad Label".to_owned());
        manifest
            .issue_routing
            .blocking_categories
            .push("phase-unknown".to_owned());

        let violations = validate_project(Path::new("math-project.json"), &manifest);

        for code in ["MP019", "MP020", "MP021", "MP022", "MP023"] {
            assert!(
                violations.iter().any(|v| v.code == code),
                "missing {code} in {violations:#?}"
            );
        }
    }

    #[test]
    fn local_domain_profile_registry_validates_and_inspects_custom_profile() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let manifest = toy_manifest();
        let profile = toy_profile(vec![toy_replay_adapter("planned")]);
        write_domain_profile(temp.path(), "domain_profiles/toy-domain.json", &profile);
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Toy.lean",
            "theorem toy_clean : True := True.intro\n",
        );
        write_obligation(temp.path(), "obligations/toy.json", &toy_obligation());

        let project_path = temp.path().join("math-project.json");
        let registry = DomainProfileRegistry::for_project_path(&project_path);
        let loaded = registry.profile("toy-domain").expect("custom profile");

        assert_eq!(loaded.name, "toy-domain");
        assert_eq!(loaded.tactic_normalizer_plan().domain_profile, "toy-domain");
        assert_eq!(
            loaded.artifact_replay_registry().adapters[0].id,
            "toy-replay-v1"
        );
        let violations = validate_project(&project_path, &manifest);
        assert!(
            !violations
                .iter()
                .any(|violation| violation.severity == "error"),
            "custom profile manifest should validate without errors: {violations:#?}"
        );
    }

    #[test]
    fn local_domain_profile_registry_fails_closed_without_profile_file() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let manifest = toy_manifest();
        write_domain_profile(
            temp.path(),
            "domain_profiles/toy-domain.json",
            &toy_profile(Vec::new()),
        );
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Toy.lean",
            "theorem toy_clean : True := True.intro\n",
        );
        write_obligation(temp.path(), "obligations/toy.json", &toy_obligation());
        fs::remove_file(temp.path().join("domain_profiles/toy-domain.json"))
            .expect("remove custom profile");

        let violations = validate_project(&temp.path().join("math-project.json"), &manifest);

        assert!(
            violations
                .iter()
                .any(|violation| violation.code == "MP006" && violation.severity == "error"),
            "missing local profile must fail closed: {violations:#?}"
        );
    }

    #[test]
    fn local_domain_profile_rejects_unwired_executable_adapter() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let manifest = toy_manifest();
        write_domain_profile(
            temp.path(),
            "domain_profiles/toy-domain.json",
            &toy_profile(vec![toy_replay_adapter("available")]),
        );
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Toy.lean",
            "theorem toy_clean : True := True.intro\n",
        );
        write_obligation(temp.path(), "obligations/toy.json", &toy_obligation());

        let violations = validate_project(&temp.path().join("math-project.json"), &manifest);

        assert!(
            violations.iter().any(|violation| {
                violation.code == "MP006"
                    && violation
                        .message
                        .contains("no matching executable replay dispatch is wired")
            }),
            "unwired non-planned adapter must fail closed: {violations:#?}"
        );
    }

    #[test]
    fn profile_tactic_normalizer_plan_derives_cert_recommendations() {
        for domain in ["sat-pb", "nn-verify"] {
            let profile = built_in_profile(domain).expect("profile");
            let plan = profile.tactic_normalizer_plan();

            assert_eq!(plan.schema_version, DOMAIN_PROFILE_SCHEMA_VERSION);
            assert_eq!(plan.domain_profile, domain);
            assert_eq!(plan.tactic_recommendations[0].name, "cert_simp");
            assert_eq!(plan.tactic_recommendations[0].rank, 1);
            assert_eq!(
                plan.tactic_recommendations[0].source,
                format!("domain-profile:{domain}")
            );
            assert!(plan.tactic_recommendations[0].uses_profile_normalizer);
            assert_eq!(plan.tactic_recommendations[1].name, "cert_mathverse");
            assert_eq!(plan.tactic_recommendations[1].rank, 2);
            assert!(plan.tactic_recommendations[1].uses_profile_normalizer);
            assert_eq!(plan.normalizers[0].name, "cert_simp");
            assert_eq!(plan.normalizers[1].name, "cert_mathverse");
        }
    }

    #[test]
    fn built_in_profiles_include_artifact_replay_adapter_descriptors() {
        let sat = built_in_profile("sat-pb").expect("sat-pb profile");
        let sat_ids = sat
            .artifact_replay_adapters
            .iter()
            .map(|adapter| adapter.id.as_str())
            .collect::<Vec<_>>();
        assert_eq!(
            sat_ids,
            vec![
                "sat-pb-lrat-v1",
                "sat-pb-drat-v1",
                "sat-pb-veripb-v1",
                "sat-pb-ay-theorem-export-v1",
                "ay-alethe-v1",
            ]
        );
        assert!(sat
            .artifact_formats
            .contains(&"ay-alethe-envelope-v1".to_owned()));

        let lrat = sat
            .replay_adapter_for_artifact_kind("lrat")
            .expect("lrat adapter");
        assert_eq!(lrat.domain_profile, "sat-pb");
        assert_eq!(lrat.artifact_formats, vec!["lrat"]);
        assert_eq!(lrat.status.lifecycle, "available");
        assert_eq!(lrat.trust.evidence_kind, "replay_only");
        assert!(!lrat.trust.kernel_certified);
        assert!(lrat.trust.requires_envelope_validation);
        assert!(lrat.trust.links_obligation_fingerprint);
        assert!(lrat.trust.allowed_trusted_assumptions.is_empty());

        let alethe = sat
            .replay_adapter_for_artifact_kind("ay_alethe_envelope")
            .expect("alethe adapter");
        assert_eq!(alethe.id, "ay-alethe-v1");
        assert_eq!(alethe.source_systems, vec!["ay"]);
        assert_eq!(alethe.status.lifecycle, "feature-gated");
        assert_eq!(
            alethe.availability.feature_gate.as_deref(),
            Some("carcara-verify")
        );

        let nn = built_in_profile("nn-verify").expect("nn profile");
        let nn_ids = nn
            .artifact_replay_adapters
            .iter()
            .map(|adapter| adapter.id.as_str())
            .collect::<Vec<_>>();
        assert_eq!(
            nn_ids,
            vec!["gamma-crown-farkas-v1", "gamma-crown-linear-entailment-v1",]
        );
        assert_eq!(
            nn.replay_adapter_for_artifact_kind("gamma_crown_entailment")
                .expect("entailment adapter")
                .id,
            "gamma-crown-linear-entailment-v1"
        );
        assert!(nn.replay_adapter_for_artifact_kind("lrat").is_none());
    }

    #[test]
    fn artifact_replay_registry_serializes_profile_inspection_contract() {
        let registry = built_in_artifact_replay_registry("nn-verify").expect("registry");
        assert_eq!(
            registry.schema_version,
            ARTIFACT_REPLAY_REGISTRY_SCHEMA_VERSION
        );
        assert_eq!(registry.domain_profile, "nn-verify");

        let profile = built_in_profile("nn-verify").expect("profile");
        assert_eq!(profile.artifact_replay_registry(), registry);
        let value = serde_json::to_value(&profile).expect("profile serializes");
        let adapters = value["artifact_replay_adapters"]
            .as_array()
            .expect("artifact replay adapters");
        assert_eq!(adapters.len(), 2);
        assert!(adapters.iter().any(|adapter| {
            adapter["artifact_formats"]
                .as_array()
                .expect("artifact formats")
                .contains(&serde_json::json!("gamma-crown-farkas-v1"))
                && adapter["status"]["report_schema_version"] == ARTIFACT_REPLAY_SCHEMA_VERSION
                && adapter["trust"]["required_report_fields"]
                    .as_array()
                    .expect("required report fields")
                    .contains(&serde_json::json!("linked_obligations"))
        }));
        assert!(built_in_artifact_replay_registry("unknown-domain").is_err());
    }

    #[test]
    fn built_in_replay_registry_matches_executable_dispatch_descriptors() {
        let mut dispatch_ids = BTreeSet::new();
        for dispatch in executable_replay_dispatch_descriptors() {
            assert!(
                dispatch_ids.insert(dispatch.adapter_id),
                "duplicate executable replay dispatch id {}",
                dispatch.adapter_id
            );

            let profile = built_in_profile(dispatch.domain_profile).expect("dispatch profile");
            let adapter = profile
                .artifact_replay_adapters
                .iter()
                .find(|adapter| adapter.id == dispatch.adapter_id)
                .unwrap_or_else(|| {
                    panic!(
                        "executable replay dispatch {} is missing from profile {}",
                        dispatch.adapter_id, dispatch.domain_profile
                    )
                });

            assert!(
                adapter
                    .source_systems
                    .iter()
                    .any(|source| source == dispatch.source_system),
                "{} registry source systems {:?} do not include executable source {}",
                dispatch.adapter_id,
                adapter.source_systems,
                dispatch.source_system
            );
            assert!(
                adapter.matches_artifact_kind(dispatch.artifact_kind),
                "{} registry artifact kinds {:?} do not include executable kind {}",
                dispatch.adapter_id,
                adapter.artifact_kinds,
                dispatch.artifact_kind
            );
            assert!(
                adapter.matches_artifact_format(dispatch.artifact_format),
                "{} registry artifact formats {:?} do not include executable format {}",
                dispatch.adapter_id,
                adapter.artifact_formats,
                dispatch.artifact_format
            );
        }

        for domain in ["sat-pb", "nn-verify"] {
            let profile = built_in_profile(domain).expect("profile");
            for adapter in &profile.artifact_replay_adapters {
                if adapter.status.lifecycle == "planned" {
                    continue;
                }
                assert!(
                    executable_replay_dispatch_descriptor(&adapter.id).is_some(),
                    "profile adapter {} with lifecycle {} has no executable dispatch descriptor",
                    adapter.id,
                    adapter.status.lifecycle
                );
            }
        }
    }

    #[test]
    fn obligation_fingerprint_is_stable() {
        let obligation = sample_obligation();
        assert_eq!(
            obligation_fingerprint(&obligation),
            obligation_fingerprint(&obligation)
        );
        assert!(obligation_fingerprint(&obligation).starts_with("sha256:"));
    }

    #[test]
    fn obligation_fingerprint_ignores_producer_and_metadata() {
        let obligation = sample_obligation();
        let baseline = obligation_fingerprint(&obligation);

        let mut changed = obligation.clone();
        changed.producer = ObligationProducer {
            system: "different-producer".to_owned(),
            commit: "different-commit".to_owned(),
            command: Some("different command".to_owned()),
        };
        changed
            .metadata
            .insert("trace_id".to_owned(), "different-metadata".to_owned());

        assert_eq!(baseline, obligation_fingerprint(&changed));
    }

    #[test]
    fn obligation_fingerprint_changes_for_canonical_identity_fields() {
        let obligation = sample_obligation();
        let baseline = obligation_fingerprint(&obligation);

        let mut changed_goal = obligation.clone();
        changed_goal.goal.expr = GoalExpr::string("SatPb.other_goal c d");
        assert_ne!(baseline, obligation_fingerprint(&changed_goal));

        let mut changed_side_condition = obligation.clone();
        changed_side_condition
            .side_conditions
            .push("coefficients_nonnegative c".to_owned());
        assert_ne!(baseline, obligation_fingerprint(&changed_side_condition));

        let mut changed_artifact = obligation.clone();
        changed_artifact.artifact_refs.push(ArtifactRef {
            kind: "proof-artifact-v1".to_owned(),
            path: "artifacts/subsumption.json".to_owned(),
            hash: Some("sha256:fixture".to_owned()),
        });
        assert_ne!(baseline, obligation_fingerprint(&changed_artifact));
    }

    #[test]
    fn obligation_fingerprint_sorts_canonical_collections() {
        let mut left = sample_obligation();
        left.local_context.push(ObligationBinding {
            name: "a".to_owned(),
            type_pp: "Clause".to_owned(),
            type_expr: Some("Clause".to_owned()),
        });
        left.side_conditions = vec!["z-condition".to_owned(), "a-condition".to_owned()];
        left.artifact_refs = vec![
            ArtifactRef {
                kind: "proof-artifact-v1".to_owned(),
                path: "artifacts/z.json".to_owned(),
                hash: Some("sha256:z".to_owned()),
            },
            ArtifactRef {
                kind: "proof-artifact-v1".to_owned(),
                path: "artifacts/a.json".to_owned(),
                hash: Some("sha256:a".to_owned()),
            },
        ];

        let mut right = left.clone();
        right.local_context.reverse();
        right.side_conditions.reverse();
        right.artifact_refs.reverse();

        assert_eq!(
            obligation_fingerprint(&left),
            obligation_fingerprint(&right)
        );
    }

    #[test]
    fn obligation_rejects_synthetic_sorry_marker() {
        let mut obligation = sample_obligation();
        obligation
            .metadata
            .insert("source".to_owned(), "synthetic_sorry".to_owned());
        let violations = validate_obligation(&obligation, Some(&sample_manifest()));
        assert!(violations.iter().any(|v| v.code == "OB015"));
    }

    #[test]
    fn manifest_validation_rejects_missing_evidence_path() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let mut manifest = sample_manifest();
        manifest.evidence = vec!["evidence/missing.json".to_owned()];
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );
        write_obligation(temp.path(), "obligations/pilot.json", &sample_obligation());

        let violations = validate_project(&temp.path().join("project.json"), &manifest);
        assert!(violations
            .iter()
            .any(|v| v.code == "MP012" && v.path == "evidence[0]"));
    }

    #[test]
    fn project_validation_matches_replay_evidence_per_artifact_ref_and_requires_hash() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let mut manifest = sample_manifest();
        manifest.evidence = vec![
            "evidence/left-replay.json".to_owned(),
            "evidence/right-replay.json".to_owned(),
        ];
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );
        write_artifact(temp.path(), "artifacts/left.lrat");
        write_artifact(temp.path(), "artifacts/right.lrat");

        let mut obligation = sample_obligation();
        obligation.artifact_refs = vec![
            ArtifactRef {
                kind: "lrat".to_owned(),
                path: "artifacts/left.lrat".to_owned(),
                hash: Some("blake3:left-proof".to_owned()),
            },
            ArtifactRef {
                kind: "lrat".to_owned(),
                path: "artifacts/right.lrat".to_owned(),
                hash: None,
            },
        ];
        let fingerprint = obligation_fingerprint(&obligation);
        write_obligation(temp.path(), "obligations/pilot.json", &obligation);

        for (stem, artifact_path, proof_hash) in [
            ("left", "artifacts/left.lrat", "blake3:left-proof"),
            ("right", "artifacts/right.lrat", "blake3:right-proof"),
        ] {
            write_json(
                &temp.path().join(format!("evidence/{stem}-replay.json")),
                &serde_json::json!({
                    "schema_version": ARTIFACT_REPLAY_SCHEMA_VERSION,
                    "artifact_path": artifact_path,
                    "project": manifest.project.clone(),
                    "source_system": "ay",
                    "artifact_kind": "lrat",
                    "problem_hash": fingerprint.clone(),
                    "proof_hash": proof_hash,
                    "certificate_format": "lrat",
                    "evidence_kind": "replay_only",
                    "kernel_certified": false,
                    "replay_status": "pass",
                    "replay_adapter": "lrat-drat-replay",
                    "linked_obligations": [fingerprint.clone()],
                    "trusted_assumptions": [],
                    "details": []
                }),
            )
            .expect("write replay evidence");
        }

        let violations = validate_project(&temp.path().join("project.json"), &manifest);
        assert!(!violations.iter().any(|violation| {
            violation.path == "obligation_sources[0].artifact_refs[0]"
                && matches!(violation.code, "MP016" | "MP017" | "MP018" | "MP024")
        }));
        assert!(violations.iter().any(|violation| {
            violation.code == "MP017" && violation.path == "obligation_sources[0].artifact_refs[1]"
        }));
    }

    #[test]
    fn manifest_validation_rejects_forbidden_theorem_pack_marker() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let manifest = sample_manifest();
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem hole : True := by sorry\n",
        );
        write_obligation(temp.path(), "obligations/pilot.json", &sample_obligation());

        let violations = validate_project(&temp.path().join("project.json"), &manifest);
        assert!(violations
            .iter()
            .any(|v| v.code == "MP015" && v.path == "theorem_packs[0]"));
    }

    #[test]
    fn manifest_validation_rejects_theorem_pack_without_indexable_candidates() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let manifest = sample_manifest();
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "def helper : True := True.intro\n",
        );
        write_obligation(temp.path(), "obligations/pilot.json", &sample_obligation());

        let violations = validate_project(&temp.path().join("project.json"), &manifest);
        assert!(violations
            .iter()
            .any(|v| v.code == "MP025" && v.path == "theorem_packs[0]"));
    }

    #[test]
    fn manifest_validation_rejects_theorem_pack_index_diagnostics() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let manifest = sample_manifest();
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem : True := True.intro\n",
        );
        write_obligation(temp.path(), "obligations/pilot.json", &sample_obligation());

        let violations = validate_project(&temp.path().join("project.json"), &manifest);
        assert!(violations
            .iter()
            .any(|v| v.code == "MP026" && v.path == "theorem_packs[0]"));
    }

    #[test]
    fn project_validation_rejects_missing_obligation_artifact_ref() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let manifest = sample_manifest();
        let mut obligation = sample_obligation();
        obligation.artifact_refs = vec![ArtifactRef {
            kind: "proof-artifact-v1".to_owned(),
            path: "artifacts/missing.json".to_owned(),
            hash: None,
        }];
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );
        write_obligation(temp.path(), "obligations/pilot.json", &obligation);

        let violations = validate_project(&temp.path().join("project.json"), &manifest);
        assert!(violations.iter().any(|v| {
            v.code == "OB017" && v.path == "obligation_sources[0].artifact_refs[0].path"
        }));
    }

    #[test]
    fn issue_plan_skips_non_filing_valid_phase_6_and_7_obligations_without_seed_row() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let mut manifest = sample_manifest();
        manifest.trust_policy.require_artifact_replay = false;
        manifest.obligation_sources = vec![
            "obligations/artifact.json".to_owned(),
            "obligations/kernel.json".to_owned(),
        ];
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );
        write_artifact(temp.path(), "artifacts/pilot.lrat");

        let mut artifact_obligation = sample_obligation();
        artifact_obligation.artifact_refs = vec![ArtifactRef {
            kind: "lrat".to_owned(),
            path: "artifacts/pilot.lrat".to_owned(),
            hash: None,
        }];
        artifact_obligation
            .metadata
            .insert("issue_plan".to_owned(), "non-filing".to_owned());
        artifact_obligation
            .metadata
            .insert("fixture_role".to_owned(), "proof-state-smoke".to_owned());
        write_obligation(
            temp.path(),
            "obligations/artifact.json",
            &artifact_obligation,
        );

        let mut kernel_obligation = sample_obligation();
        kernel_obligation
            .metadata
            .insert("issue_plan".to_owned(), "non-filing".to_owned());
        kernel_obligation
            .metadata
            .insert("fixture_role".to_owned(), "theorem-index-smoke".to_owned());
        write_obligation(temp.path(), "obligations/kernel.json", &kernel_obligation);

        let report = issue_plan_report(&temp.path().join("project.json"), &manifest);

        assert!(
            !report
                .rows
                .iter()
                .any(|row| row.phase == "Phase 6" || row.phase == "Phase 7"),
            "non-filing obligations must not create closure rows: {:#?}",
            report.rows
        );
        assert!(
            !report.rows.iter().any(|row| row.scope == "project-setup"),
            "non-empty obligation_sources must not receive a seed row: {:#?}",
            report.rows
        );
        assert!(
            report.rows.is_empty(),
            "valid non-filing obligations should leave no issue rows: {:#?}",
            report.rows
        );
    }

    #[test]
    fn issue_plan_does_not_skip_non_smoke_obligations_with_non_filing_metadata() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let mut manifest = sample_manifest();
        manifest.trust_policy.require_artifact_replay = false;
        manifest.obligation_sources = vec!["obligations/kernel.json".to_owned()];
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );

        let mut obligation = sample_obligation();
        obligation
            .metadata
            .insert("issue_plan".to_owned(), "non-filing".to_owned());
        write_obligation(temp.path(), "obligations/kernel.json", &obligation);

        let report = issue_plan_report(&temp.path().join("project.json"), &manifest);

        assert!(
            report.rows.iter().any(|row| {
                row.phase == "Phase 7" && row.files == vec!["obligations/kernel.json".to_owned()]
            }),
            "non-filing metadata without an explicit smoke fixture role must not hide proof work: {:#?}",
            report.rows
        );
    }

    #[test]
    fn issue_plan_valid_closure_rows_use_phase_specific_commands() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let mut manifest = sample_manifest();
        manifest.trust_policy.require_artifact_replay = false;
        manifest.obligation_sources = vec![
            "obligations/artifact.json".to_owned(),
            "obligations/kernel.json".to_owned(),
        ];
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );
        write_artifact(temp.path(), "artifacts/pilot.lrat");

        let mut artifact_obligation = sample_obligation();
        artifact_obligation.artifact_refs = vec![ArtifactRef {
            kind: "lrat".to_owned(),
            path: "artifacts/pilot.lrat".to_owned(),
            hash: None,
        }];
        write_obligation(
            temp.path(),
            "obligations/artifact.json",
            &artifact_obligation,
        );
        write_obligation(temp.path(), "obligations/kernel.json", &sample_obligation());

        let report = issue_plan_report(&temp.path().join("project.json"), &manifest);
        let phase_6 = report
            .rows
            .iter()
            .find(|row| row.phase == "Phase 6")
            .expect("phase 6 closure row");
        let phase_7 = report
            .rows
            .iter()
            .find(|row| row.phase == "Phase 7")
            .expect("phase 7 closure row");

        assert!(phase_6
            .verification_command
            .contains("clean math artifact replay"));
        assert!(phase_6
            .verification_command
            .contains("clean math project hygiene"));
        assert!(!phase_6
            .verification_command
            .contains("clean math obligation validate"));
        assert!(phase_6
            .acceptance
            .iter()
            .any(|item| item.contains("referenced artifacts replay")));

        assert!(phase_7
            .verification_command
            .contains("clean math certificate extract"));
        assert!(phase_7.verification_command.contains("kernel_certified"));
        assert!(!phase_7
            .verification_command
            .contains("clean math obligation validate"));
        assert!(phase_7
            .acceptance
            .iter()
            .any(|item| item.contains("kernel_certified true")));
    }

    #[test]
    fn issue_plan_routes_invalid_non_filing_obligation_to_phase_3_repair() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let mut manifest = sample_manifest();
        manifest.trust_policy.require_artifact_replay = false;
        manifest.obligation_sources = vec!["obligations/invalid.json".to_owned()];
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );

        let mut obligation = sample_obligation();
        obligation.project = "different-project".to_owned();
        obligation
            .metadata
            .insert("issue_plan".to_owned(), "non-filing".to_owned());
        write_obligation(temp.path(), "obligations/invalid.json", &obligation);

        let report = issue_plan_report(&temp.path().join("project.json"), &manifest);
        let repair_row = report
            .rows
            .iter()
            .find(|row| {
                row.phase == "Phase 3"
                    && row
                        .scope
                        .starts_with("Repair semantic validation violations in obligation source")
                    && row.files == vec!["obligations/invalid.json".to_owned()]
            })
            .expect("invalid non-filing obligation repair row");

        assert_eq!(repair_row.phase_title, "Generic obligation ABI");
        assert!(repair_row.filing_key.ends_with("/OB012"));
        assert!(
            !report.rows.iter().any(|row| {
                row.files == vec!["obligations/invalid.json".to_owned()]
                    && (row.phase == "Phase 6" || row.phase == "Phase 7")
            }),
            "invalid non-filing obligations must not create closure rows: {:#?}",
            report.rows
        );
    }

    #[test]
    fn non_filing_issue_plan_metadata_does_not_change_hygiene_validation() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let mut manifest = sample_manifest();
        manifest.obligation_sources = vec!["obligations/artifact.json".to_owned()];
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );
        write_artifact(temp.path(), "artifacts/pilot.lrat");

        let mut obligation = sample_obligation();
        obligation.artifact_refs = vec![ArtifactRef {
            kind: "lrat".to_owned(),
            path: "artifacts/pilot.lrat".to_owned(),
            hash: None,
        }];
        obligation
            .metadata
            .insert("issue_plan".to_owned(), "non-filing".to_owned());
        obligation
            .metadata
            .insert("fixture_role".to_owned(), "proof-state-smoke".to_owned());
        write_obligation(temp.path(), "obligations/artifact.json", &obligation);

        let project_path = temp.path().join("project.json");
        let violations = validate_project(&project_path, &manifest);
        assert!(
            violations.iter().any(|violation| {
                violation.code == "MP016"
                    && violation.path == "obligation_sources[0].artifact_refs[0]"
            }),
            "non-filing metadata must not suppress replay hygiene: {violations:#?}"
        );

        let hygiene = hygiene_report(&project_path, &manifest);
        assert_eq!(hygiene.status, "fail");
        assert!(hygiene
            .violations
            .iter()
            .any(|violation| violation.code == "MP016"));

        let report = issue_plan_report(&project_path, &manifest);
        assert!(report.rows.iter().any(|row| {
            row.phase == "Phase 8" && row.filing_key == "Phase 8/framework/hygiene-gate/MP016"
        }));
        assert!(
            !report.rows.iter().any(|row| {
                row.files == vec!["obligations/artifact.json".to_owned()]
                    && (row.phase == "Phase 6" || row.phase == "Phase 7")
            }),
            "hygiene failures should not re-enable non-filing closure rows: {:#?}",
            report.rows
        );
    }

    #[test]
    fn issue_plan_seed_row_only_when_manifest_obligation_sources_is_empty() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let mut manifest = sample_manifest();
        manifest.obligation_sources.clear();
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );

        let report = issue_plan_report(&temp.path().join("project.json"), &manifest);

        assert_eq!(report.rows.len(), 1);
        assert_eq!(report.rows[0].scope, "project-setup");
        assert_eq!(
            report.rows[0].filing_key,
            "Phase 1/sat-pb/project-setup/seed-obligation"
        );
    }

    #[test]
    fn sat_pb_lrat_drat_missing_replay_ranks_ahead_of_seed_row() {
        for kind in ["lrat", "drat"] {
            let temp = tempfile::TempDir::new().expect("tempdir");
            let manifest = sample_manifest();
            write_theorem_pack(
                temp.path(),
                "theorem_packs/Pilot.lean",
                "theorem clean : True := True.intro\n",
            );
            let artifact_path = format!("artifacts/pilot.{kind}");
            write_artifact(temp.path(), &artifact_path);
            let mut obligation = sample_obligation();
            obligation.artifact_refs = vec![ArtifactRef {
                kind: kind.to_owned(),
                path: artifact_path,
                hash: None,
            }];
            obligation
                .metadata
                .insert("benchmark_family".to_owned(), "pigeonhole".to_owned());
            obligation
                .metadata
                .insert("benchmark".to_owned(), "php-3-2".to_owned());
            write_obligation(temp.path(), "obligations/pilot.json", &obligation);

            let project_path = temp.path().join("project.json");
            let report = issue_plan_report(&project_path, &manifest);
            let obligation_row = report
                .rows
                .iter()
                .find(|row| row.scope == "proof-obligation")
                .expect("obligation row");

            assert_eq!(obligation_row.ranking.domain_profile, "sat-pb");
            assert_eq!(obligation_row.ranking.artifact_kinds, vec![kind]);
            assert_eq!(obligation_row.ranking.replay_status, "missing");
            assert!(!obligation_row.ranking.replay_cache_present);
            assert_eq!(obligation_row.ranking.proof_gap, "missing-replay-evidence");
            assert_eq!(
                obligation_row.ranking.benchmark_family.as_deref(),
                Some("pigeonhole")
            );
            assert!(obligation_row
                .ranking
                .signals
                .contains(&format!("artifact:{kind}")));

            let mut rows = vec![
                seed_obligation_issue_row(&project_path, &manifest),
                obligation_row.clone(),
            ];
            finalize_issue_plan_rows(&mut rows);
            assert_eq!(rows[0].ranking.proof_gap, "missing-replay-evidence");
            assert_eq!(rows[0].ranking.rank, 1);
            assert_eq!(rows[1].ranking.proof_gap, "seed-obligation");
            assert_eq!(rows[1].ranking.rank, 2);
        }
    }

    #[test]
    fn sat_pb_kernel_proof_gap_ranks_ahead_of_seed_row() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let manifest = sample_manifest();
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );
        let mut obligation = sample_obligation();
        obligation
            .metadata
            .insert("benchmark_family".to_owned(), "cardinality".to_owned());
        write_obligation(temp.path(), "obligations/pilot.json", &obligation);

        let project_path = temp.path().join("project.json");
        let report = issue_plan_report(&project_path, &manifest);
        let obligation_row = report
            .rows
            .iter()
            .find(|row| row.scope == "proof-obligation")
            .expect("obligation row");

        assert_eq!(obligation_row.ranking.replay_status, "not-applicable");
        assert_eq!(obligation_row.ranking.proof_gap, "missing-kernel-proof");
        assert_eq!(
            obligation_row.ranking.benchmark_family.as_deref(),
            Some("cardinality")
        );

        let mut rows = vec![
            seed_obligation_issue_row(&project_path, &manifest),
            obligation_row.clone(),
        ];
        finalize_issue_plan_rows(&mut rows);
        assert_eq!(rows[0].ranking.proof_gap, "missing-kernel-proof");
        assert_eq!(rows[0].ranking.rank, 1);
        assert_eq!(rows[1].ranking.proof_gap, "seed-obligation");
        assert_eq!(rows[1].ranking.rank, 2);
    }

    #[test]
    fn issue_plan_rows_expose_filing_metadata_from_routing_and_blockers() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let mut manifest = sample_manifest();
        manifest.issue_routing.labels = strings(&["math-project", "sat-pb", "proof-factory"]);
        manifest.issue_routing.owners = strings(&["worker-c"]);
        manifest.issue_routing.blocking_categories = strings(&["artifact", "trust"]);
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );
        write_artifact(temp.path(), "artifacts/pilot.lrat");
        let mut obligation = sample_obligation();
        obligation.artifact_refs = vec![ArtifactRef {
            kind: "lrat".to_owned(),
            path: "artifacts/pilot.lrat".to_owned(),
            hash: None,
        }];
        write_obligation(temp.path(), "obligations/pilot.json", &obligation);

        let project_path = temp.path().join("project.json");
        let report = issue_plan_report(&project_path, &manifest);
        let value = serde_json::to_value(&report).expect("issue-plan serializes");
        let rows = value["rows"].as_array().expect("rows");

        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0]["phase"], "Phase 8");
        assert_eq!(rows[0]["ranking"]["rank"], 1);
        assert_eq!(rows[1]["scope"], "proof-obligation");
        assert_eq!(rows[1]["ranking"]["rank"], 2);
        assert_eq!(
            rows[0]["filing_metadata"]["labels"],
            serde_json::json!(["math-project", "sat-pb", "proof-factory"])
        );
        assert_eq!(rows[0]["filing_metadata"]["owner"], "worker-c");
        assert_eq!(
            rows[0]["filing_metadata"]["blockers"],
            serde_json::json!(["artifact", "trust", "MP016"])
        );
        assert_eq!(
            rows[1]["filing_metadata"]["blockers"],
            serde_json::json!(["artifact", "trust", "missing-replay-evidence"])
        );
        assert!(rows[0]["filing_metadata"]["reproduction"]["commands"][0]
            .as_str()
            .expect("hygiene reproduction command")
            .contains("clean math project hygiene"));
        assert!(rows[1]["filing_metadata"]["reproduction"]["commands"][0]
            .as_str()
            .expect("obligation reproduction command")
            .contains("clean math artifact replay"));
        assert_eq!(
            rows[0]["labels"],
            serde_json::json!(["math-project", "sat-pb", "proof-factory"])
        );
        assert_eq!(rows[0]["owners"], serde_json::json!(["worker-c"]));
        assert_eq!(
            rows[0]["blocking_categories"],
            serde_json::json!(["artifact", "trust"])
        );
    }

    #[test]
    fn proof_failure_diagnostics_enrich_issue_plan_rows() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let mut manifest = sample_manifest();
        manifest.trust_policy.require_artifact_replay = false;
        manifest.evidence = vec!["evidence/proof-failure.json".to_owned()];
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );
        let obligation = sample_obligation();
        let fingerprint = obligation_fingerprint(&obligation);
        write_obligation(temp.path(), "obligations/pilot.json", &obligation);
        write_proof_failure_diagnostic(
            temp.path(),
            "evidence/proof-failure.json",
            &ProofFailureDiagnosticEvidence {
                schema_version: PROOF_FAILURE_DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION.to_owned(),
                obligation_fingerprint: fingerprint,
                evidence_id: Some("volatile-evidence-id".to_owned()),
                run_id: Some("volatile-run-id".to_owned()),
                observed_at: Some("2026-04-27T12:00:00Z".to_owned()),
                summary: Some("elaboration fails before theorem candidate closes".to_owned()),
                blockers: strings(&["unknown-constant", "missing-local-instance"]),
                ranking_signals: strings(&["unknown-constant", "pre-kernel-elab"]),
                score_delta: 33,
                reproduction: IssuePlanReproduction {
                    commands: vec!["clean proof-state replay --state proof-failure".to_owned()],
                    files: vec!["proofs/Pilot.lean".to_owned()],
                },
            },
        );

        let report = issue_plan_report(&temp.path().join("project.json"), &manifest);
        let row = report
            .rows
            .iter()
            .find(|row| row.scope == "proof-obligation")
            .expect("proof obligation row");

        assert_eq!(
            row.ranking.proof_failure_diagnostics,
            vec!["elaboration fails before theorem candidate closes".to_owned()]
        );
        assert!(row
            .ranking
            .signals
            .contains(&"proof-failure:unknown-constant".to_owned()));
        assert!(row.ranking.score > 750);
        assert_eq!(
            row.filing_metadata.blockers,
            vec![
                "manifest".to_owned(),
                "obligation".to_owned(),
                "artifact".to_owned(),
                "trust".to_owned(),
                "missing-kernel-proof".to_owned(),
                "unknown-constant".to_owned(),
                "missing-local-instance".to_owned(),
            ]
        );
        assert!(row
            .filing_metadata
            .reproduction
            .commands
            .iter()
            .any(|command| command == "clean proof-state replay --state proof-failure"));
        assert!(row
            .filing_metadata
            .reproduction
            .files
            .contains(&"proofs/Pilot.lean".to_owned()));
        assert!(row.issue_body.contains("## Proof Failure Diagnostics"));
        assert!(row
            .issue_body
            .contains("elaboration fails before theorem candidate closes"));
    }

    #[test]
    fn proof_failure_diagnostic_volatile_fields_and_manifest_order_do_not_affect_dedupe() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let mut manifest = sample_manifest();
        manifest.trust_policy.require_artifact_replay = false;
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );
        let obligation = sample_obligation();
        let fingerprint = obligation_fingerprint(&obligation);
        write_obligation(temp.path(), "obligations/pilot.json", &obligation);

        let diagnostic_a = |evidence_id: &str, observed_at: &str| ProofFailureDiagnosticEvidence {
            schema_version: PROOF_FAILURE_DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION.to_owned(),
            obligation_fingerprint: fingerprint.clone(),
            evidence_id: Some(evidence_id.to_owned()),
            run_id: Some(format!("{evidence_id}-run")),
            observed_at: Some(observed_at.to_owned()),
            summary: Some("alpha diagnostic".to_owned()),
            blockers: strings(&["alpha-blocker"]),
            ranking_signals: strings(&["alpha-signal"]),
            score_delta: 5,
            reproduction: IssuePlanReproduction {
                commands: vec!["clean alpha repro".to_owned()],
                files: vec!["alpha.lean".to_owned()],
            },
        };
        let diagnostic_b = |evidence_id: &str, observed_at: &str| ProofFailureDiagnosticEvidence {
            schema_version: PROOF_FAILURE_DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION.to_owned(),
            obligation_fingerprint: fingerprint.clone(),
            evidence_id: Some(evidence_id.to_owned()),
            run_id: Some(format!("{evidence_id}-run")),
            observed_at: Some(observed_at.to_owned()),
            summary: Some("beta diagnostic".to_owned()),
            blockers: strings(&["beta-blocker"]),
            ranking_signals: strings(&["beta-signal"]),
            score_delta: 7,
            reproduction: IssuePlanReproduction {
                commands: vec!["clean beta repro".to_owned()],
                files: vec!["beta.lean".to_owned()],
            },
        };

        manifest.evidence = vec![
            "evidence/beta.json".to_owned(),
            "evidence/alpha.json".to_owned(),
        ];
        write_proof_failure_diagnostic(
            temp.path(),
            "evidence/alpha.json",
            &diagnostic_a("first-alpha-id", "2026-04-27T12:00:00Z"),
        );
        write_proof_failure_diagnostic(
            temp.path(),
            "evidence/beta.json",
            &diagnostic_b("first-beta-id", "2026-04-27T12:01:00Z"),
        );
        let first_report = issue_plan_report(&temp.path().join("project.json"), &manifest);
        let first_row = first_report
            .rows
            .iter()
            .find(|row| row.scope == "proof-obligation")
            .expect("first proof obligation row");
        let first_dedupe = first_row.dedupe_key.clone();
        let first_summaries = first_row.ranking.proof_failure_diagnostics.clone();

        manifest.evidence = vec![
            "evidence/alpha.json".to_owned(),
            "evidence/beta.json".to_owned(),
        ];
        write_proof_failure_diagnostic(
            temp.path(),
            "evidence/alpha.json",
            &diagnostic_a("second-alpha-id", "2026-04-27T13:00:00Z"),
        );
        write_proof_failure_diagnostic(
            temp.path(),
            "evidence/beta.json",
            &diagnostic_b("second-beta-id", "2026-04-27T13:01:00Z"),
        );
        let second_report = issue_plan_report(&temp.path().join("project.json"), &manifest);
        let second_row = second_report
            .rows
            .iter()
            .find(|row| row.scope == "proof-obligation")
            .expect("second proof obligation row");

        assert_eq!(first_dedupe, second_row.dedupe_key);
        assert_eq!(
            first_summaries,
            vec!["alpha diagnostic".to_owned(), "beta diagnostic".to_owned()]
        );
        assert_eq!(
            second_row.ranking.proof_failure_diagnostics,
            first_summaries
        );
        assert!(!second_row.issue_body.contains("second-alpha-id"));
        assert!(!second_row.issue_body.contains("second-beta-id"));
    }

    #[test]
    fn task_projection_exposes_issue_ranking_signals() {
        let temp = tempfile::TempDir::new().expect("tempdir");
        let manifest = sample_manifest();
        write_theorem_pack(
            temp.path(),
            "theorem_packs/Pilot.lean",
            "theorem clean : True := True.intro\n",
        );
        write_obligation(temp.path(), "obligations/pilot.json", &sample_obligation());

        let report = task_lifecycle::list_tasks(&temp.path().join("project.json"), &manifest)
            .expect("list tasks");
        let task = report
            .tasks
            .iter()
            .find(|task| task.issue.scope == "proof-obligation")
            .expect("proof task");

        assert_eq!(task.issue.ranking.domain_profile, "sat-pb");
        assert_eq!(task.issue.ranking.replay_status, "not-applicable");
        assert_eq!(task.issue.ranking.proof_gap, "missing-kernel-proof");
        assert!(task
            .issue
            .ranking
            .signals
            .contains(&"proof-gap:missing-kernel-proof".to_owned()));
        assert_eq!(
            task.issue.filing_metadata.owner.as_deref(),
            Some("clean-math-factory")
        );
        assert_eq!(
            task.issue.filing_metadata.reproduction.commands.len(),
            1,
            "task projection keeps filing reproduction commands"
        );
    }
}
