// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Append-only proof-attempt log and content-addressed artifacts.
//!
//! New records and artifacts are written under `.cake/`; the legacy
//! `.mathverse/` directory is still read for back-compat (write new,
//! read both).

use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};

pub use crate::env_fingerprint::EnvFingerprint;
use crate::error::{MathverseError, MathverseResult};
use crate::types::TrustLevel;

/// Attempt-log directory written by current tooling.
pub(crate) const ATTEMPT_LOG_DIR: &str = ".cake";
/// Legacy attempt-log directory; still read for back-compat.
pub(crate) const LEGACY_ATTEMPT_LOG_DIR: &str = ".mathverse";
const ATTEMPTS_DIR: &str = "attempts";
const ARTIFACTS_DIR: &str = "artifacts";
const ATTEMPT_LOG_LOCK: &str = ".attempt-log.lock";
const NS_PER_SECOND: u64 = 1_000_000_000;
const SECONDS_PER_DAY: u64 = 86_400;

static ATTEMPT_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Hex-encoded BLAKE3 digest.
pub type Blake3Hash = String;

/// UUIDv7-shaped identifier for one proof attempt.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct AttemptId(String);

impl AttemptId {
    /// Generate a UUIDv7-shaped attempt id.
    pub fn new_v7() -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default();
        let millis = (now.as_millis().min(0xffff_ffff_ffff) as u64) & 0xffff_ffff_ffff;
        let counter = ATTEMPT_COUNTER.fetch_add(1, Ordering::Relaxed);

        let mut hasher = blake3::Hasher::new();
        hasher.update(&now.as_nanos().to_be_bytes());
        hasher.update(&std::process::id().to_be_bytes());
        hasher.update(&counter.to_be_bytes());
        let random = hasher.finalize();

        let mut bytes = [0u8; 16];
        bytes[0] = (millis >> 40) as u8;
        bytes[1] = (millis >> 32) as u8;
        bytes[2] = (millis >> 24) as u8;
        bytes[3] = (millis >> 16) as u8;
        bytes[4] = (millis >> 8) as u8;
        bytes[5] = millis as u8;
        bytes[6..].copy_from_slice(&random.as_bytes()[..10]);
        bytes[6] = (bytes[6] & 0x0f) | 0x70;
        bytes[8] = (bytes[8] & 0x3f) | 0x80;

        Self(format_uuid(&bytes))
    }

    /// Borrow the string form.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for AttemptId {
    fn from(value: &str) -> Self {
        Self(value.to_owned())
    }
}

impl From<String> for AttemptId {
    fn from(value: String) -> Self {
        Self(value)
    }
}

impl std::fmt::Display for AttemptId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// Opaque proof-state identifier recorded by the producer.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct StateId(String);

impl StateId {
    /// Borrow the string form.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for StateId {
    fn from(value: &str) -> Self {
        Self(value.to_owned())
    }
}

impl From<String> for StateId {
    fn from(value: String) -> Self {
        Self(value)
    }
}

/// Content-addressed artifact reference under `.cake/artifacts/<blake3>`
/// (legacy `.mathverse/artifacts/<blake3>` is still read).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArtifactRef {
    /// Hex-encoded BLAKE3 content digest.
    pub blake3: Blake3Hash,
    /// Artifact size in bytes.
    pub byte_len: u64,
    /// Producer-defined artifact kind, for example `solver/drat`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    /// Optional original or logical filename.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub logical_name: Option<String>,
}

/// Attempt outcome.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AttemptStatus {
    /// Proof was accepted by the configured audit path.
    Accepted,
    /// Proof was rejected with a stable diagnostic.
    Rejected {
        /// Rejection reason.
        reason: String,
    },
    /// Attempt exceeded its wall-clock budget.
    Timeout {
        /// Timeout budget in milliseconds.
        after_ms: u64,
    },
}

impl AttemptStatus {
    /// Return the status class without status-specific payload fields.
    pub fn kind(&self) -> AttemptStatusFilter {
        self.filter_kind()
    }

    fn filter_kind(&self) -> AttemptStatusFilter {
        match self {
            AttemptStatus::Accepted => AttemptStatusFilter::Accepted,
            AttemptStatus::Rejected { .. } => AttemptStatusFilter::Rejected,
            AttemptStatus::Timeout { .. } => AttemptStatusFilter::Timeout,
        }
    }
}

/// Status-only filter for attempt queries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AttemptStatusFilter {
    /// Accepted attempts.
    Accepted,
    /// Rejected attempts.
    Rejected,
    /// Timed-out attempts.
    Timeout,
}

impl AttemptStatusFilter {
    /// Stable lowercase CLI/JSON spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
            Self::Timeout => "timeout",
        }
    }
}

impl std::fmt::Display for AttemptStatusFilter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for AttemptStatusFilter {
    type Err = MathverseError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let normalized = value.trim().to_ascii_lowercase();
        match normalized.as_str() {
            "accepted" | "accept" | "pass" | "passed" | "success" => Ok(Self::Accepted),
            "rejected" | "reject" | "fail" | "failed" | "failure" => Ok(Self::Rejected),
            "timeout" | "timed_out" | "timed-out" => Ok(Self::Timeout),
            "" => Err(MathverseError::Kernel(
                "attempt status filter must not be empty".to_owned(),
            )),
            other => Err(MathverseError::Kernel(format!(
                "unknown attempt status filter `{other}`; expected accepted, rejected, or timeout"
            ))),
        }
    }
}

/// Optional per-attempt resource accounting and budget metadata.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttemptBudget {
    /// Wall-clock budget allocated to this attempt, in milliseconds.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub wall_time_ms: Option<u64>,
    /// Solver/checker time spent by this attempt, in milliseconds.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub solver_ms: Option<u64>,
    /// Model/service tokens consumed by this attempt.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tokens: Option<u64>,
    /// Producer-defined hardware label used for capacity accounting.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hardware: Option<String>,
}

/// Generic class of a proof-attempt producer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProducerKind {
    /// A language/model service or model runtime.
    Model,
    /// A solver or proof-search binary.
    Solver,
    /// A tactic or in-process proof procedure.
    Tactic,
    /// A human-authored attempt.
    Human,
    /// A service or orchestration layer.
    Service,
    /// Producer kind is known to the caller but not represented above.
    Other,
}

impl ProducerKind {
    /// Stable lowercase CLI/JSON spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Model => "model",
            Self::Solver => "solver",
            Self::Tactic => "tactic",
            Self::Human => "human",
            Self::Service => "service",
            Self::Other => "other",
        }
    }
}

/// Generic metadata describing who or what produced a proof attempt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttemptProducer {
    /// Generic producer class.
    pub producer_kind: ProducerKind,
    /// Provider or organization responsible for the producer.
    pub provider: String,
    /// Producer name.
    pub name: String,
    /// Optional producer version.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
    /// Optional BLAKE3 digest of the exact command or invocation envelope.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub command_digest: Option<Blake3Hash>,
}

/// Generic external context associated with a proof attempt.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttemptContext {
    /// External run identifier assigned by the producer or orchestrator.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub external_run_id: Option<String>,
    /// External task identifier assigned by the producer or orchestrator.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub external_task_id: Option<String>,
    /// Optional BLAKE3 digest of the prompt or request envelope.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub prompt_digest: Option<Blake3Hash>,
    /// Optional content-addressed patch artifact produced by the attempt.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub patch_artifact: Option<ArtifactRef>,
}

/// Query filter for reading the attempt log.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttemptFilter {
    /// Return one attempt id.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub attempt_id: Option<AttemptId>,
    /// Return attempts matching one goal hash.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub goal_hash: Option<Blake3Hash>,
    /// Return attempts matching one status class.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub status: Option<AttemptStatusFilter>,
    /// Inclusive lower bound on `created_at` nanoseconds.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub since_ns: Option<u64>,
    /// Inclusive upper bound on `created_at` nanoseconds.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub until_ns: Option<u64>,
    /// Return attempts emitted by one authority gate.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub authority_gate: Option<String>,
    /// Return attempts with one stable failure mode.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub failure_mode: Option<String>,
    /// Return attempts with one trust level.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_level: Option<TrustLevel>,
    /// Return attempts with one producer kind.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub producer_kind: Option<ProducerKind>,
    /// Return attempts from one producer provider.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub producer_provider: Option<String>,
    /// Return attempts from one producer name.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub producer: Option<String>,
    /// Return attempts with one external task id.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub external_task_id: Option<String>,
}

impl AttemptFilter {
    fn matches(&self, attempt: &ProofAttempt) -> bool {
        if self
            .attempt_id
            .as_ref()
            .is_some_and(|id| id != &attempt.attempt_id)
        {
            return false;
        }
        if self
            .goal_hash
            .as_ref()
            .is_some_and(|hash| hash != &attempt.goal_hash)
        {
            return false;
        }
        if self
            .status
            .is_some_and(|status| status != attempt.status.filter_kind())
        {
            return false;
        }
        if self
            .since_ns
            .is_some_and(|since| attempt.created_at < since)
        {
            return false;
        }
        if self
            .until_ns
            .is_some_and(|until| attempt.created_at > until)
        {
            return false;
        }
        if self
            .authority_gate
            .as_ref()
            .is_some_and(|gate| attempt.authority_gate.as_ref() != Some(gate))
        {
            return false;
        }
        if self
            .failure_mode
            .as_ref()
            .is_some_and(|mode| attempt.failure_mode.as_ref() != Some(mode))
        {
            return false;
        }
        if self
            .trust_level
            .is_some_and(|level| attempt.trust_level != Some(level))
        {
            return false;
        }
        if self.producer_kind.is_some_and(|kind| {
            attempt
                .producer
                .as_ref()
                .map(|producer| producer.producer_kind)
                != Some(kind)
        }) {
            return false;
        }
        if self.producer_provider.as_ref().is_some_and(|provider| {
            attempt
                .producer
                .as_ref()
                .map(|producer| producer.provider.as_str())
                != Some(provider.as_str())
        }) {
            return false;
        }
        if self.producer.as_ref().is_some_and(|name| {
            attempt
                .producer
                .as_ref()
                .map(|producer| producer.name.as_str())
                != Some(name.as_str())
        }) {
            return false;
        }
        if self.external_task_id.as_ref().is_some_and(|task_id| {
            attempt
                .context
                .as_ref()
                .and_then(|context| context.external_task_id.as_deref())
                != Some(task_id.as_str())
        }) {
            return false;
        }
        true
    }
}

/// JSON-safe attempt query output.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttemptQueryReport {
    /// Filter used to read the log.
    pub filter: AttemptFilter,
    /// Number of attempts matching the filter before any caller limit.
    pub total: usize,
    /// Number of attempts returned in this report.
    pub returned: usize,
    /// Deterministic count summary over all matches before any caller limit.
    #[serde(default)]
    pub summary: AttemptQuerySummary,
    /// Matching attempts in log-file order.
    pub attempts: Vec<ProofAttempt>,
}

/// Stable string-keyed count summary for an attempt query.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttemptQuerySummary {
    /// Counts by status class.
    pub by_status: BTreeMap<String, usize>,
    /// Counts by authority gate for attempts that recorded one.
    pub by_authority_gate: BTreeMap<String, usize>,
    /// Counts by failure mode for attempts that recorded one.
    pub by_failure_mode: BTreeMap<String, usize>,
    /// Counts by trust level for attempts that recorded one.
    pub by_trust_level: BTreeMap<String, usize>,
    /// Counts by producer kind for attempts that recorded producer metadata.
    #[serde(default)]
    pub by_producer_kind: BTreeMap<String, usize>,
    /// Counts by producer name for attempts that recorded producer metadata.
    #[serde(default)]
    pub by_producer: BTreeMap<String, usize>,
    /// Counts by producer provider for attempts that recorded producer metadata.
    #[serde(default)]
    pub by_producer_provider: BTreeMap<String, usize>,
    /// Counts by external task id for attempts that recorded one.
    #[serde(default)]
    pub by_external_task_id: BTreeMap<String, usize>,
    /// Attempts with no authority gate metadata.
    pub without_authority_gate: usize,
    /// Attempts with no failure mode metadata.
    pub without_failure_mode: usize,
    /// Attempts with no trust level metadata.
    pub without_trust_level: usize,
    /// Attempts with no producer metadata.
    #[serde(default)]
    pub without_producer: usize,
    /// Attempts with no external task id metadata.
    #[serde(default)]
    pub without_external_task_id: usize,
}

impl AttemptQuerySummary {
    fn from_attempts(attempts: &[ProofAttempt]) -> Self {
        let mut summary = Self::default();
        for attempt in attempts {
            *summary
                .by_status
                .entry(attempt.status.filter_kind().as_str().to_owned())
                .or_insert(0) += 1;

            match &attempt.authority_gate {
                Some(gate) => {
                    *summary.by_authority_gate.entry(gate.clone()).or_insert(0) += 1;
                }
                None => summary.without_authority_gate += 1,
            }

            match &attempt.failure_mode {
                Some(mode) => {
                    *summary.by_failure_mode.entry(mode.clone()).or_insert(0) += 1;
                }
                None => summary.without_failure_mode += 1,
            }

            match attempt.trust_level {
                Some(level) => {
                    *summary
                        .by_trust_level
                        .entry(trust_level_report_key(level).to_owned())
                        .or_insert(0) += 1;
                }
                None => summary.without_trust_level += 1,
            }

            match &attempt.producer {
                Some(producer) => {
                    *summary
                        .by_producer_kind
                        .entry(producer.producer_kind.as_str().to_owned())
                        .or_insert(0) += 1;
                    *summary
                        .by_producer
                        .entry(producer.name.clone())
                        .or_insert(0) += 1;
                    *summary
                        .by_producer_provider
                        .entry(producer.provider.clone())
                        .or_insert(0) += 1;
                }
                None => summary.without_producer += 1,
            }

            match attempt
                .context
                .as_ref()
                .and_then(|context| context.external_task_id.as_ref())
            {
                Some(task_id) => {
                    *summary
                        .by_external_task_id
                        .entry(task_id.clone())
                        .or_insert(0) += 1;
                }
                None => summary.without_external_task_id += 1,
            }
        }
        summary
    }
}

/// One persisted proof attempt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofAttempt {
    /// UUIDv7-shaped attempt id.
    pub attempt_id: AttemptId,
    /// BLAKE3 hash of the goal or normalized goal shape.
    pub goal_hash: Blake3Hash,
    /// Final status.
    pub status: AttemptStatus,
    /// BLAKE3 hash of the trust/audit report for this attempt.
    pub trust_audit_hash: Blake3Hash,
    /// Optional solver proof/certificate/log artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub solver_artifact: Option<ArtifactRef>,
    /// Proof state before the attempt.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_state_before: Option<StateId>,
    /// Proof state after the attempt.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_state_after: Option<StateId>,
    /// Optional model or LLM response artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model_response: Option<ArtifactRef>,
    /// Optional command transcript or invocation evidence artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub command_evidence: Option<ArtifactRef>,
    /// Reproducible execution fingerprint.
    pub env: EnvFingerprint,
    /// Nanoseconds since Unix epoch.
    pub created_at: u64,
    /// Wall-clock duration in milliseconds.
    pub wall_time_ms: u64,
    /// Optional authority gate that produced this attempt record.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub authority_gate: Option<String>,
    /// Stable failure-mode classification for rejected/timeout attempts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub failure_mode: Option<String>,
    /// Trust level assigned by the accepted audit path, when known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_level: Option<TrustLevel>,
    /// Optional resource accounting and attempt-budget metadata.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub budget: Option<AttemptBudget>,
    /// Generic producer metadata.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub producer: Option<AttemptProducer>,
    /// Generic external context metadata.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub context: Option<AttemptContext>,
    /// Original attempt id when this record is a replay.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replayed_from: Option<AttemptId>,
}

impl ProofAttempt {
    /// Build a new attempt record with generated id and current timestamp.
    pub fn new(
        goal_hash: Blake3Hash,
        status: AttemptStatus,
        trust_audit_hash: Blake3Hash,
        env: EnvFingerprint,
    ) -> Self {
        Self {
            attempt_id: AttemptId::new_v7(),
            goal_hash,
            status,
            trust_audit_hash,
            solver_artifact: None,
            proof_state_before: None,
            proof_state_after: None,
            model_response: None,
            command_evidence: None,
            env,
            created_at: now_unix_ns(),
            wall_time_ms: 0,
            authority_gate: None,
            failure_mode: None,
            trust_level: None,
            budget: None,
            producer: None,
            context: None,
            replayed_from: None,
        }
    }

    /// Return all content-addressed artifacts referenced by this attempt.
    pub fn artifact_refs(&self) -> Vec<&ArtifactRef> {
        let mut refs = Vec::with_capacity(4);
        if let Some(artifact) = &self.solver_artifact {
            refs.push(artifact);
        }
        if let Some(artifact) = &self.model_response {
            refs.push(artifact);
        }
        if let Some(artifact) = &self.command_evidence {
            refs.push(artifact);
        }
        if let Some(artifact) = self
            .context
            .as_ref()
            .and_then(|context| context.patch_artifact.as_ref())
        {
            refs.push(artifact);
        }
        refs
    }
}

/// Stable JSON receipt for one authority-gate attempt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AuthorityReceipt {
    pub schema_version: &'static str,
    pub attempt_id: String,
    pub authority_gate: String,
    pub status: &'static str,
    pub goal_hash: Blake3Hash,
    pub trust_audit_hash: Blake3Hash,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub solver_artifact: Option<AuthorityReceiptArtifact>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub command_evidence: Option<AuthorityReceiptArtifact>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub failure_mode: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_level: Option<TrustLevel>,
    pub wall_time_ms: u64,
    pub created_at: u64,
}

/// Content-addressed artifact included in an authority receipt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AuthorityReceiptArtifact {
    pub blake3: Blake3Hash,
    pub byte_len: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub logical_name: Option<String>,
}

impl AuthorityReceipt {
    /// Build a stable receipt from a persisted proof attempt.
    pub fn from_attempt(attempt: &ProofAttempt) -> Self {
        Self {
            schema_version: "Clean-authority-receipt-v1",
            attempt_id: attempt.attempt_id.to_string(),
            authority_gate: attempt
                .authority_gate
                .clone()
                .unwrap_or_else(|| "unknown".to_owned()),
            status: attempt_status_label(&attempt.status),
            goal_hash: attempt.goal_hash.clone(),
            trust_audit_hash: attempt.trust_audit_hash.clone(),
            solver_artifact: attempt.solver_artifact.as_ref().map(artifact_receipt),
            command_evidence: attempt.command_evidence.as_ref().map(artifact_receipt),
            failure_mode: attempt.failure_mode.clone(),
            trust_level: attempt.trust_level,
            wall_time_ms: attempt.wall_time_ms,
            created_at: attempt.created_at,
        }
    }
}

fn artifact_receipt(artifact: &ArtifactRef) -> AuthorityReceiptArtifact {
    AuthorityReceiptArtifact {
        blake3: artifact.blake3.clone(),
        byte_len: artifact.byte_len,
        kind: artifact.kind.clone(),
        logical_name: artifact.logical_name.clone(),
    }
}

fn attempt_status_label(status: &AttemptStatus) -> &'static str {
    match status {
        AttemptStatus::Accepted => "accepted",
        AttemptStatus::Rejected { .. } => "rejected",
        AttemptStatus::Timeout { .. } => "timeout",
    }
}

/// Replay preflight policy.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReplayOptions {
    /// Permit replay under a non-identical live environment.
    pub allow_mismatch: bool,
    /// Required explanation when `allow_mismatch` is true and the environment differs.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mismatch_explanation: Option<String>,
}

/// Replay preflight output.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReplayPlan {
    /// Original attempt to replay.
    pub original: ProofAttempt,
    /// Captured live environment.
    pub live_env: EnvFingerprint,
    /// Whether `live_env` exactly matches `original.env`.
    pub env_matches: bool,
    /// Operator explanation when a mismatch was allowed.
    pub mismatch_explanation: Option<String>,
}

/// Caller-supplied replay result used to append a new linked attempt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReplayAttemptResult {
    /// Final replay status.
    pub status: AttemptStatus,
    /// BLAKE3 hash of the replay trust/audit report.
    pub trust_audit_hash: Blake3Hash,
    /// Optional solver proof/certificate/log artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub solver_artifact: Option<ArtifactRef>,
    /// Proof state before replay. Defaults to the original attempt's before-state when omitted.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_state_before: Option<StateId>,
    /// Proof state after replay.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_state_after: Option<StateId>,
    /// Optional model or LLM response artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model_response: Option<ArtifactRef>,
    /// Optional command transcript or invocation evidence artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub command_evidence: Option<ArtifactRef>,
    /// Wall-clock replay duration in milliseconds.
    pub wall_time_ms: u64,
    /// Stable failure-mode classification for rejected/timeout replay attempts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub failure_mode: Option<String>,
    /// Trust level assigned by the replay audit path, when known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_level: Option<TrustLevel>,
    /// Optional replay resource accounting and budget metadata.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub budget: Option<AttemptBudget>,
    /// Authority gate that produced this replay attempt. Defaults to the original attempt's gate.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub authority_gate: Option<String>,
    /// Generic producer metadata for this replay attempt.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub producer: Option<AttemptProducer>,
    /// Generic external context metadata for this replay attempt.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub context: Option<AttemptContext>,
}

impl ReplayAttemptResult {
    /// Build a replay result with no optional artifacts or proof-state override.
    pub fn new(status: AttemptStatus, trust_audit_hash: Blake3Hash) -> Self {
        Self {
            status,
            trust_audit_hash,
            solver_artifact: None,
            proof_state_before: None,
            proof_state_after: None,
            model_response: None,
            command_evidence: None,
            wall_time_ms: 0,
            failure_mode: None,
            trust_level: None,
            budget: None,
            authority_gate: None,
            producer: None,
            context: None,
        }
    }
}

/// Caller-supplied authority-gate result to persist as a proof attempt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthorityGateAttempt {
    /// Stable gate name, for example `trust_audit` or `statement_preservation`.
    pub gate: String,
    /// BLAKE3 hash of the goal or normalized goal shape.
    pub goal_hash: Blake3Hash,
    /// Final gate status.
    pub status: AttemptStatus,
    /// BLAKE3 hash of the trust/audit report for this gate result.
    pub trust_audit_hash: Blake3Hash,
    /// Reproducible execution fingerprint.
    pub env: EnvFingerprint,
    /// Wall-clock duration in milliseconds.
    pub wall_time_ms: u64,
    /// Optional solver proof/certificate/log artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub solver_artifact: Option<ArtifactRef>,
    /// Proof state before the gate.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_state_before: Option<StateId>,
    /// Proof state after the gate.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_state_after: Option<StateId>,
    /// Optional model or LLM response artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model_response: Option<ArtifactRef>,
    /// Optional command transcript or invocation evidence artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub command_evidence: Option<ArtifactRef>,
    /// Stable failure-mode classification for rejected/timeout gate attempts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub failure_mode: Option<String>,
    /// Trust level assigned by the gate, when known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_level: Option<TrustLevel>,
    /// Optional resource accounting and gate-budget metadata.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub budget: Option<AttemptBudget>,
    /// Generic producer metadata.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub producer: Option<AttemptProducer>,
    /// Generic external context metadata.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub context: Option<AttemptContext>,
}

impl AuthorityGateAttempt {
    /// Build an authority-gate attempt with no optional artifacts or metadata.
    pub fn new(
        gate: impl Into<String>,
        goal_hash: Blake3Hash,
        status: AttemptStatus,
        trust_audit_hash: Blake3Hash,
        env: EnvFingerprint,
    ) -> Self {
        Self {
            gate: gate.into(),
            goal_hash,
            status,
            trust_audit_hash,
            env,
            wall_time_ms: 0,
            solver_artifact: None,
            proof_state_before: None,
            proof_state_after: None,
            model_response: None,
            command_evidence: None,
            failure_mode: None,
            trust_level: None,
            budget: None,
            producer: None,
            context: None,
        }
    }
}

/// JSON-safe replay preflight output, optionally including an appended replay attempt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReplayAttemptReport {
    /// Replay preflight plan.
    pub plan: ReplayPlan,
    /// Newly appended replay attempt when the caller supplied a replay result.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub recorded_replay: Option<ProofAttempt>,
}

/// Policy for validating replay-binding metadata on proof attempts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ReplayBindingValidationOptions {
    /// Accept rejected or timed-out attempts without requiring replay-binding fields.
    #[serde(default)]
    pub allow_non_accepted: bool,
    /// Require caller-visible policy metadata on accepted attempts.
    #[serde(default)]
    pub require_policy_metadata: bool,
}

/// Append an attempt under `.cake/attempts/yyyy-mm-dd.jsonl` in the current directory.
pub fn append(attempt: &ProofAttempt) -> MathverseResult<()> {
    let current_dir = std::env::current_dir()?;
    append_to(current_dir, attempt)
}

/// Append an attempt under `.cake/attempts/yyyy-mm-dd.jsonl` in `root`.
pub fn append_to(root: impl AsRef<Path>, attempt: &ProofAttempt) -> MathverseResult<()> {
    let path = attempt_log_path(root.as_ref(), attempt.created_at);
    let attempts_dir = path.parent().ok_or_else(|| {
        MathverseError::Kernel(format!(
            "attempt log path `{}` has no parent directory",
            path.display()
        ))
    })?;
    fs::create_dir_all(attempts_dir)?;

    let mut record = serde_json::to_vec(attempt)?;
    record.push(b'\n');

    let lock_file = attempt_log_lock_file(attempts_dir)?;
    let mut lock = fd_lock::RwLock::new(lock_file);
    let _guard = lock.write()?;

    let mut file = OpenOptions::new().create(true).append(true).open(path)?;
    file.write_all(&record)?;
    Ok(())
}

/// Validate and append an authority-gate attempt under `.cake/attempts/yyyy-mm-dd.jsonl`.
///
/// This is the strict append path for accepted/gated authority rows. Use [`append_to`] for raw
/// diagnostic records that intentionally preserve incomplete producer output.
pub fn append_authority_attempt_to(
    root: impl AsRef<Path>,
    attempt: &ProofAttempt,
) -> MathverseResult<()> {
    validate_authority_attempt(attempt)?;
    if matches!(attempt.status, AttemptStatus::Accepted) {
        validate_replay_binding(
            attempt,
            ReplayBindingValidationOptions {
                allow_non_accepted: false,
                require_policy_metadata: true,
            },
        )?;
    }
    append_to(root, attempt)
}

/// Build and append a proof attempt for an authority-gate result.
pub fn record_authority_gate_attempt(
    root: impl AsRef<Path>,
    result: AuthorityGateAttempt,
) -> MathverseResult<ProofAttempt> {
    let gate = result.gate.trim();
    if gate.is_empty() {
        return Err(MathverseError::Kernel(
            "authority gate attempt requires a non-empty gate name".to_owned(),
        ));
    }

    let mut attempt = ProofAttempt::new(
        result.goal_hash,
        result.status,
        result.trust_audit_hash,
        result.env,
    );
    attempt.wall_time_ms = result.wall_time_ms;
    attempt.authority_gate = Some(gate.to_owned());
    attempt.solver_artifact = result.solver_artifact;
    attempt.proof_state_before = result.proof_state_before;
    attempt.proof_state_after = result.proof_state_after;
    attempt.model_response = result.model_response;
    attempt.command_evidence = result.command_evidence;
    attempt.failure_mode = result.failure_mode;
    attempt.trust_level = result.trust_level;
    attempt.budget = result.budget;
    attempt.producer = result.producer;
    attempt.context = result.context;
    append_authority_attempt_to(root, &attempt)?;
    Ok(attempt)
}

/// Iterate attempts from the current directory.
pub fn iter(filter: AttemptFilter) -> MathverseResult<std::vec::IntoIter<ProofAttempt>> {
    let current_dir = std::env::current_dir()?;
    iter_from(current_dir, filter)
}

/// Iterate attempts from `root` in log-file order, reading the legacy
/// `.mathverse/attempts` directory first and then the current
/// `.cake/attempts` directory.
pub fn iter_from(
    root: impl AsRef<Path>,
    filter: AttemptFilter,
) -> MathverseResult<std::vec::IntoIter<ProofAttempt>> {
    let mut attempts = Vec::new();
    for log_dir in [LEGACY_ATTEMPT_LOG_DIR, ATTEMPT_LOG_DIR] {
        let dir = root.as_ref().join(log_dir).join(ATTEMPTS_DIR);
        if !dir.exists() {
            continue;
        }

        let lock_file = attempt_log_lock_file(&dir)?;
        let lock = fd_lock::RwLock::new(lock_file);
        let _guard = lock.read()?;

        let mut files = Vec::new();
        for entry in fs::read_dir(dir)? {
            let path = entry?.path();
            if path.extension().is_some_and(|ext| ext == "jsonl") {
                files.push(path);
            }
        }
        files.sort();

        for path in files {
            let content = fs::read_to_string(&path)?;
            for (line_index, line) in content.lines().enumerate() {
                if line.trim().is_empty() {
                    continue;
                }
                let attempt: ProofAttempt = serde_json::from_str(line).map_err(|err| {
                    MathverseError::Json(err).with_context(&format!(
                        "while parsing attempt log `{}` line {}",
                        path.display(),
                        line_index + 1
                    ))
                })?;
                if filter.matches(&attempt) {
                    attempts.push(attempt);
                }
            }
        }
    }

    Ok(attempts.into_iter())
}

/// Return a JSON-safe attempt query report for all matches.
pub(crate) fn query_attempts(
    root: impl AsRef<Path>,
    filter: AttemptFilter,
) -> MathverseResult<AttemptQueryReport> {
    query_attempts_limited(root, filter, None)
}

/// Return a JSON-safe attempt query report, optionally truncating returned rows.
pub fn query_attempts_limited(
    root: impl AsRef<Path>,
    filter: AttemptFilter,
    limit: Option<usize>,
) -> MathverseResult<AttemptQueryReport> {
    let mut attempts: Vec<_> = iter_from(root, filter.clone())?.collect();
    let total = attempts.len();
    let summary = AttemptQuerySummary::from_attempts(&attempts);
    if let Some(limit) = limit {
        attempts.truncate(limit);
    }
    Ok(AttemptQueryReport {
        filter,
        total,
        returned: attempts.len(),
        summary,
        attempts,
    })
}

/// Find one attempt by id under `root`.
pub(crate) fn find_attempt(
    root: impl AsRef<Path>,
    attempt_id: &AttemptId,
) -> MathverseResult<Option<ProofAttempt>> {
    let filter = AttemptFilter {
        attempt_id: Some(attempt_id.clone()),
        ..AttemptFilter::default()
    };
    Ok(iter_from(root, filter)?.next())
}

/// Store an artifact under `.cake/artifacts/<blake3>` and return its reference.
pub fn put_artifact(
    root: impl AsRef<Path>,
    bytes: &[u8],
    kind: Option<&str>,
    logical_name: Option<&str>,
) -> MathverseResult<ArtifactRef> {
    let digest = blake3::hash(bytes).to_hex().to_string();
    let dir = root.as_ref().join(ATTEMPT_LOG_DIR).join(ARTIFACTS_DIR);
    fs::create_dir_all(&dir)?;
    let path = dir.join(&digest);

    match OpenOptions::new().write(true).create_new(true).open(&path) {
        Ok(mut file) => file.write_all(bytes)?,
        Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists && path.is_file() => {}
        Err(err) => return Err(err.into()),
    }

    Ok(ArtifactRef {
        blake3: digest,
        byte_len: bytes.len() as u64,
        kind: kind.map(str::to_owned),
        logical_name: logical_name.map(str::to_owned),
    })
}

/// Return the filesystem path for an artifact reference.
///
/// Prefers the current `.cake/artifacts` store; falls back to the legacy
/// `.mathverse/artifacts` store when the artifact only exists there.
pub fn artifact_path(root: impl AsRef<Path>, artifact: &ArtifactRef) -> PathBuf {
    let current = root
        .as_ref()
        .join(ATTEMPT_LOG_DIR)
        .join(ARTIFACTS_DIR)
        .join(&artifact.blake3);
    if current.is_file() {
        return current;
    }
    let legacy = root
        .as_ref()
        .join(LEGACY_ATTEMPT_LOG_DIR)
        .join(ARTIFACTS_DIR)
        .join(&artifact.blake3);
    if legacy.is_file() {
        legacy
    } else {
        current
    }
}

/// Read and validate an artifact by reference.
pub fn read_artifact(root: impl AsRef<Path>, artifact: &ArtifactRef) -> MathverseResult<Vec<u8>> {
    let path = artifact_path(root, artifact);
    let bytes = fs::read(&path)?;
    let actual = blake3::hash(&bytes).to_hex().to_string();
    if actual != artifact.blake3 {
        return Err(MathverseError::Kernel(format!(
            "artifact hash mismatch for `{}`: expected {}, got {}",
            path.display(),
            artifact.blake3,
            actual
        )));
    }
    if bytes.len() as u64 != artifact.byte_len {
        return Err(MathverseError::Kernel(format!(
            "artifact size mismatch for `{}`: expected {}, got {}",
            path.display(),
            artifact.byte_len,
            bytes.len()
        )));
    }
    Ok(bytes)
}

/// Prepare an attempt replay by capturing the live environment.
pub(crate) fn prepare_replay_attempt(
    root: impl AsRef<Path>,
    attempt_id: &AttemptId,
    options: ReplayOptions,
) -> MathverseResult<ReplayPlan> {
    let root = root.as_ref();
    let live_env = EnvFingerprint::capture(root)?;
    prepare_replay_attempt_with_env(root, attempt_id, live_env, options)
}

/// Prepare an attempt replay using a caller-supplied live environment.
pub fn prepare_replay_attempt_with_env(
    root: impl AsRef<Path>,
    attempt_id: &AttemptId,
    live_env: EnvFingerprint,
    options: ReplayOptions,
) -> MathverseResult<ReplayPlan> {
    let root = root.as_ref();
    let original = find_attempt(root, attempt_id)?.ok_or_else(|| {
        MathverseError::Kernel(format!(
            "attempt `{attempt_id}` was not found in Mathverse attempt log"
        ))
    })?;

    for artifact in original.artifact_refs() {
        read_artifact(root, artifact)?;
    }

    let env_matches = original.env == live_env;
    let mismatch_explanation = if env_matches {
        None
    } else if options.allow_mismatch {
        let explanation = options
            .mismatch_explanation
            .as_ref()
            .map(|s| s.trim())
            .filter(|s| !s.is_empty())
            .ok_or_else(|| {
                MathverseError::Kernel(
                    "replay environment mismatch requires a non-empty explanation".to_owned(),
                )
            })?;
        Some(explanation.to_owned())
    } else {
        return Err(MathverseError::Kernel(format!(
            "replay environment mismatch for attempt `{attempt_id}`"
        )));
    };

    Ok(ReplayPlan {
        original,
        live_env,
        env_matches,
        mismatch_explanation,
    })
}

/// Prepare replay and append a replay attempt only when `result` is supplied.
pub(crate) fn prepare_replay_attempt_with_result(
    root: impl AsRef<Path>,
    attempt_id: &AttemptId,
    options: ReplayOptions,
    result: Option<ReplayAttemptResult>,
) -> MathverseResult<ReplayAttemptReport> {
    let root = root.as_ref();
    let plan = prepare_replay_attempt(root, attempt_id, options)?;
    record_optional_replay_result(root, plan, result)
}

/// Deterministic variant of [`prepare_replay_attempt_with_result`] for tests and callers
/// that already captured the environment.
pub fn prepare_replay_attempt_with_env_and_result(
    root: impl AsRef<Path>,
    attempt_id: &AttemptId,
    live_env: EnvFingerprint,
    options: ReplayOptions,
    result: Option<ReplayAttemptResult>,
) -> MathverseResult<ReplayAttemptReport> {
    let root = root.as_ref();
    let plan = prepare_replay_attempt_with_env(root, attempt_id, live_env, options)?;
    record_optional_replay_result(root, plan, result)
}

/// Append a replay result after setting `replayed_from`.
pub fn record_replay_attempt(
    root: impl AsRef<Path>,
    original_id: &AttemptId,
    mut replay_attempt: ProofAttempt,
) -> MathverseResult<ProofAttempt> {
    replay_attempt.replayed_from = Some(original_id.clone());
    append_to(root, &replay_attempt)?;
    Ok(replay_attempt)
}

/// Build a replay attempt from a preflight plan and caller-supplied result.
pub(crate) fn replay_attempt_from_result(
    plan: &ReplayPlan,
    result: ReplayAttemptResult,
) -> ProofAttempt {
    let ReplayAttemptResult {
        status,
        trust_audit_hash,
        solver_artifact,
        proof_state_before,
        proof_state_after,
        model_response,
        command_evidence,
        wall_time_ms,
        failure_mode,
        trust_level,
        budget,
        authority_gate,
        producer,
        context,
    } = result;

    let mut attempt = ProofAttempt::new(
        plan.original.goal_hash.clone(),
        status,
        trust_audit_hash,
        plan.live_env.clone(),
    );
    attempt.solver_artifact = solver_artifact;
    attempt.proof_state_before =
        proof_state_before.or_else(|| plan.original.proof_state_before.clone());
    attempt.proof_state_after = proof_state_after;
    attempt.model_response = model_response;
    attempt.command_evidence = command_evidence;
    attempt.wall_time_ms = wall_time_ms;
    attempt.failure_mode = failure_mode;
    attempt.trust_level = trust_level;
    attempt.budget = budget;
    attempt.authority_gate = authority_gate.or_else(|| plan.original.authority_gate.clone());
    attempt.producer = producer;
    attempt.context = context;
    attempt
}

/// Append a caller-supplied replay result after linking it to the original attempt.
pub(crate) fn record_replay_result(
    root: impl AsRef<Path>,
    plan: &ReplayPlan,
    result: ReplayAttemptResult,
) -> MathverseResult<ProofAttempt> {
    let replay_attempt = replay_attempt_from_result(plan, result);
    record_replay_attempt(root, &plan.original.attempt_id, replay_attempt)
}

/// Current Unix timestamp in nanoseconds.
pub(crate) fn now_unix_ns() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos()
        .min(u128::from(u64::MAX)) as u64
}

/// Parse a relative duration for attempt queries and return nanoseconds.
///
/// Accepted units are `ns`, `us`, `ms`, `s`, `m`, `h`, `d`, and `w`.
pub(crate) fn parse_since_duration_ns(value: &str) -> MathverseResult<u64> {
    let value = value.trim();
    if value.is_empty() {
        return Err(MathverseError::Kernel(
            "attempt query --since duration must not be empty".to_owned(),
        ));
    }

    let digits_len = value
        .as_bytes()
        .iter()
        .take_while(|byte| byte.is_ascii_digit())
        .count();
    if digits_len == 0 {
        return Err(MathverseError::Kernel(format!(
            "invalid attempt query duration `{value}`: expected an integer followed by a unit"
        )));
    }

    let amount: u64 = value[..digits_len].parse().map_err(|err| {
        MathverseError::Kernel(format!(
            "invalid attempt query duration `{value}`: could not parse integer amount: {err}"
        ))
    })?;
    let unit = value[digits_len..].trim().to_ascii_lowercase();
    let multiplier = match unit.as_str() {
        "ns" | "nanosecond" | "nanoseconds" => 1,
        "us" | "microsecond" | "microseconds" => 1_000,
        "ms" | "millisecond" | "milliseconds" => 1_000_000,
        "s" | "sec" | "secs" | "second" | "seconds" => NS_PER_SECOND,
        "m" | "min" | "mins" | "minute" | "minutes" => 60 * NS_PER_SECOND,
        "h" | "hr" | "hrs" | "hour" | "hours" => 60 * 60 * NS_PER_SECOND,
        "d" | "day" | "days" => SECONDS_PER_DAY * NS_PER_SECOND,
        "w" | "week" | "weeks" => 7 * SECONDS_PER_DAY * NS_PER_SECOND,
        "" => {
            return Err(MathverseError::Kernel(format!(
                "invalid attempt query duration `{value}`: missing unit"
            )))
        }
        other => {
            return Err(MathverseError::Kernel(format!(
                "invalid attempt query duration unit `{other}` in `{value}`"
            )))
        }
    };

    amount.checked_mul(multiplier).ok_or_else(|| {
        MathverseError::Kernel(format!(
            "attempt query duration `{value}` overflows u64 nanoseconds"
        ))
    })
}

/// Convert a relative duration string into an inclusive `created_at` lower bound.
pub fn since_duration_lower_bound_ns(now_ns: u64, value: &str) -> MathverseResult<u64> {
    Ok(now_ns.saturating_sub(parse_since_duration_ns(value)?))
}

/// Validate replay-binding fields required to reproduce an accepted proof attempt.
///
/// Accepted attempts must carry a command binding, an environment fingerprint, and a
/// content-addressed solver/proof artifact. Callers can require authority policy metadata
/// and can choose whether non-accepted attempts are skipped or fail closed.
pub fn validate_replay_binding(
    attempt: &ProofAttempt,
    options: ReplayBindingValidationOptions,
) -> MathverseResult<()> {
    match attempt.status {
        AttemptStatus::Accepted => {}
        AttemptStatus::Rejected { .. } | AttemptStatus::Timeout { .. } => {
            if options.allow_non_accepted {
                return Ok(());
            }
            return Err(MathverseError::Kernel(format!(
                "attempt `{}` is not accepted; replay binding validation requires an accepted attempt",
                attempt.attempt_id
            )));
        }
    }

    validate_env_fingerprint(&attempt.env)?;
    validate_command_binding(attempt)?;

    let solver_artifact = attempt.solver_artifact.as_ref().ok_or_else(|| {
        MathverseError::Kernel(format!(
            "accepted attempt `{}` is missing solver/proof artifact reference",
            attempt.attempt_id
        ))
    })?;
    validate_content_addressed_artifact("solver_artifact", solver_artifact)?;

    if options.require_policy_metadata {
        validate_policy_metadata(attempt)?;
    }

    Ok(())
}

fn record_optional_replay_result(
    root: &Path,
    plan: ReplayPlan,
    result: Option<ReplayAttemptResult>,
) -> MathverseResult<ReplayAttemptReport> {
    let recorded_replay = match result {
        Some(result) => Some(record_replay_result(root, &plan, result)?),
        None => None,
    };
    Ok(ReplayAttemptReport {
        plan,
        recorded_replay,
    })
}

fn validate_env_fingerprint(env: &EnvFingerprint) -> MathverseResult<()> {
    let required = [
        ("env.lean_toolchain", env.lean_toolchain.as_str()),
        ("env.clean_commit", env.clean_commit.as_str()),
        ("env.host_arch", env.host_arch.as_str()),
        ("env.host_os", env.host_os.as_str()),
    ];
    for (field, value) in required {
        if value.trim().is_empty() {
            return Err(MathverseError::Kernel(format!(
                "accepted attempt replay binding is missing {field}"
            )));
        }
    }
    Ok(())
}

fn validate_command_binding(attempt: &ProofAttempt) -> MathverseResult<()> {
    if let Some(command_digest) = attempt
        .producer
        .as_ref()
        .and_then(|producer| producer.command_digest.as_ref())
    {
        validate_blake3_hash_field("producer command_digest", command_digest)?;
        return Ok(());
    }

    if let Some(artifact) = &attempt.command_evidence {
        if is_command_evidence_artifact(artifact) {
            validate_content_addressed_artifact("command evidence artifact", artifact)?;
            return Ok(());
        }
        return Err(MathverseError::Kernel(format!(
            "accepted attempt `{}` command evidence artifact kind must identify command evidence",
            attempt.attempt_id
        )));
    }

    Err(MathverseError::Kernel(format!(
        "accepted attempt `{}` is missing producer command digest or command evidence artifact",
        attempt.attempt_id
    )))
}

fn is_command_evidence_artifact(artifact: &ArtifactRef) -> bool {
    artifact.kind.as_deref().is_some_and(|kind| {
        let kind = kind.to_ascii_lowercase();
        kind.contains("command") && (kind.contains("transcript") || kind.contains("evidence"))
    })
}

fn validate_content_addressed_artifact(field: &str, artifact: &ArtifactRef) -> MathverseResult<()> {
    validate_blake3_hash_field(field, &artifact.blake3)?;
    if artifact.byte_len == 0 {
        return Err(MathverseError::Kernel(format!(
            "accepted attempt {field} must have a non-zero byte_len"
        )));
    }
    Ok(())
}

fn validate_policy_metadata(attempt: &ProofAttempt) -> MathverseResult<()> {
    let gate = attempt
        .authority_gate
        .as_deref()
        .map(str::trim)
        .filter(|gate| !gate.is_empty())
        .ok_or_else(|| {
            MathverseError::Kernel(format!(
                "accepted attempt `{}` is missing authority policy metadata",
                attempt.attempt_id
            ))
        })?;
    if attempt.authority_gate.as_deref() != Some(gate) {
        return Err(MathverseError::Kernel(format!(
            "accepted attempt `{}` authority policy metadata must not contain leading or trailing whitespace",
            attempt.attempt_id
        )));
    }
    if attempt.trust_level.is_none() {
        return Err(MathverseError::Kernel(format!(
            "accepted attempt `{}` is missing trust level policy metadata",
            attempt.attempt_id
        )));
    }
    Ok(())
}

fn validate_authority_attempt(attempt: &ProofAttempt) -> MathverseResult<()> {
    let gate = attempt
        .authority_gate
        .as_ref()
        .ok_or_else(|| {
            MathverseError::Kernel(
                "authority gate attempt requires a non-empty gate name".to_owned(),
            )
        })?
        .trim();
    if gate.is_empty() {
        return Err(MathverseError::Kernel(
            "authority gate attempt requires a non-empty gate name".to_owned(),
        ));
    }
    if attempt.authority_gate.as_deref() != Some(gate) {
        return Err(MathverseError::Kernel(
            "authority gate attempt gate name must not contain leading or trailing whitespace"
                .to_owned(),
        ));
    }

    validate_blake3_hash_field("goal_hash", &attempt.goal_hash)?;
    validate_blake3_hash_field("trust_audit_hash", &attempt.trust_audit_hash)?;
    for artifact in attempt.artifact_refs() {
        validate_blake3_hash_field("artifact blake3", &artifact.blake3)?;
    }
    Ok(())
}

fn validate_blake3_hash_field(field: &str, value: &str) -> MathverseResult<()> {
    if value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Ok(());
    }

    Err(MathverseError::Kernel(format!(
        "authority gate attempt {field} must be a 64-character BLAKE3 hex digest"
    )))
}

fn attempt_log_path(root: &Path, created_at_ns: u64) -> PathBuf {
    root.join(ATTEMPT_LOG_DIR)
        .join(ATTEMPTS_DIR)
        .join(log_filename_for_ns(created_at_ns))
}

fn attempt_log_lock_file(attempts_dir: &Path) -> MathverseResult<File> {
    Ok(OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(attempts_dir.join(ATTEMPT_LOG_LOCK))?)
}

fn trust_level_report_key(level: TrustLevel) -> &'static str {
    match level {
        TrustLevel::KernelVerified => "KernelVerified",
        TrustLevel::AxiomDependent => "AxiomDependent",
        TrustLevel::CertificateReplayed => "CertificateReplayed",
        TrustLevel::PartiallyAxiomatized => "PartiallyAxiomatized",
        TrustLevel::TrustedOracle => "TrustedOracle",
    }
}

fn log_filename_for_ns(created_at_ns: u64) -> String {
    let seconds = created_at_ns / NS_PER_SECOND;
    let days = (seconds / SECONDS_PER_DAY) as i64;
    let (year, month, day) = civil_from_days(days);
    format!("{year:04}-{month:02}-{day:02}.jsonl")
}

fn civil_from_days(days_since_unix_epoch: i64) -> (i32, u32, u32) {
    let z = days_since_unix_epoch + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let day_of_era = z - era * 146_097;
    let year_of_era =
        (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let year = year_of_era + era * 400;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_prime = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_prime + 2) / 5 + 1;
    let month = month_prime + if month_prime < 10 { 3 } else { -9 };
    let year = year + if month <= 2 { 1 } else { 0 };
    (year as i32, month as u32, day as u32)
}

fn format_uuid(bytes: &[u8; 16]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(36);
    for (index, byte) in bytes.iter().enumerate() {
        if matches!(index, 4 | 6 | 8 | 10) {
            out.push('-');
        }
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_env() -> EnvFingerprint {
        EnvFingerprint {
            lean_toolchain: "leanprover/lean4:v4.18.0".to_owned(),
            clean_commit: "0123456789abcdef0123456789abcdef01234567".to_owned(),
            ay_revision: None,
            llvm2_revision: None,
            host_arch: "test-arch".to_owned(),
            host_os: "test-os".to_owned(),
            solver_binaries: Vec::new(),
        }
    }

    fn hash(label: &str) -> String {
        blake3::hash(label.as_bytes()).to_hex().to_string()
    }

    fn producer(provider: &str, name: &str) -> AttemptProducer {
        AttemptProducer {
            producer_kind: ProducerKind::Model,
            provider: provider.to_owned(),
            name: name.to_owned(),
            version: Some("v1".to_owned()),
            command_digest: Some(hash(&format!("{provider}/{name}/command"))),
        }
    }

    fn context(task_id: &str, patch_artifact: Option<ArtifactRef>) -> AttemptContext {
        AttemptContext {
            external_run_id: Some(format!("run-{task_id}")),
            external_task_id: Some(task_id.to_owned()),
            prompt_digest: Some(hash(&format!("{task_id}/prompt"))),
            patch_artifact,
        }
    }

    fn replay_bound_authority_artifacts(root: &Path) -> (ArtifactRef, ArtifactRef) {
        let solver_artifact = put_artifact(
            root,
            b"authority solver report",
            Some("solver/lrat"),
            Some("authority.lrat"),
        )
        .expect("put solver artifact");
        let command_evidence = put_artifact(
            root,
            b"$ clean authority gate\naccepted\n",
            Some("command/transcript"),
            Some("authority-command.txt"),
        )
        .expect("put command evidence");
        (solver_artifact, command_evidence)
    }

    #[test]
    fn authority_gate_attempt_copies_generic_producer_context_metadata() {
        let temp = tempfile::tempdir().expect("tempdir");
        let patch_artifact = put_artifact(
            temp.path(),
            b"diff --git a/proof.clean b/proof.clean\n",
            Some("patch/unified-diff"),
            Some("proof.patch"),
        )
        .expect("put patch artifact");
        let (solver_artifact, command_evidence) = replay_bound_authority_artifacts(temp.path());

        let result = AuthorityGateAttempt {
            solver_artifact: Some(solver_artifact.clone()),
            command_evidence: Some(command_evidence.clone()),
            trust_level: Some(TrustLevel::KernelVerified),
            producer: Some(producer("provider-a", "attempt-producer-a")),
            context: Some(context("task-1", Some(patch_artifact.clone()))),
            ..AuthorityGateAttempt::new(
                "trust_audit",
                hash("goal"),
                AttemptStatus::Accepted,
                hash("audit"),
                test_env(),
            )
        };

        let attempt =
            record_authority_gate_attempt(temp.path(), result).expect("record authority attempt");

        assert_eq!(
            attempt
                .producer
                .as_ref()
                .map(|producer| producer.name.as_str()),
            Some("attempt-producer-a")
        );
        assert_eq!(
            attempt
                .context
                .as_ref()
                .and_then(|context| context.external_task_id.as_deref()),
            Some("task-1")
        );
        assert_eq!(
            attempt.artifact_refs(),
            vec![&solver_artifact, &command_evidence, &patch_artifact]
        );

        let decoded: ProofAttempt =
            serde_json::from_str(&serde_json::to_string(&attempt).expect("encode attempt"))
                .expect("decode attempt");
        assert_eq!(decoded.producer, attempt.producer);
        assert_eq!(decoded.context, attempt.context);
        assert_eq!(decoded.command_evidence, attempt.command_evidence);
    }

    #[test]
    fn authority_append_rejects_malformed_essential_fields() {
        let temp = tempfile::tempdir().expect("tempdir");

        let mut missing_gate = ProofAttempt::new(
            hash("goal"),
            AttemptStatus::Accepted,
            hash("audit"),
            test_env(),
        );
        let err = append_authority_attempt_to(temp.path(), &missing_gate)
            .expect_err("missing authority gate should fail");
        assert!(err.to_string().contains("non-empty gate name"));

        missing_gate.authority_gate = Some(" trust_audit ".to_owned());
        let err = append_authority_attempt_to(temp.path(), &missing_gate)
            .expect_err("whitespace-padded authority gate should fail");
        assert!(err.to_string().contains("leading or trailing whitespace"));

        let malformed_goal = AuthorityGateAttempt::new(
            "trust_audit",
            "not-a-blake3-hash".to_owned(),
            AttemptStatus::Accepted,
            hash("audit"),
            test_env(),
        );
        let err = record_authority_gate_attempt(temp.path(), malformed_goal)
            .expect_err("malformed goal hash should fail");
        assert!(err.to_string().contains("goal_hash"));

        let malformed_audit = AuthorityGateAttempt::new(
            "trust_audit",
            hash("goal"),
            AttemptStatus::Accepted,
            String::new(),
            test_env(),
        );
        let err = record_authority_gate_attempt(temp.path(), malformed_audit)
            .expect_err("empty audit hash should fail");
        assert!(err.to_string().contains("trust_audit_hash"));

        let mut malformed_artifact = AuthorityGateAttempt::new(
            "trust_audit",
            hash("goal"),
            AttemptStatus::Accepted,
            hash("audit"),
            test_env(),
        );
        malformed_artifact.solver_artifact = Some(ArtifactRef {
            blake3: "bad-artifact-hash".to_owned(),
            byte_len: 42,
            kind: Some("solver/drat".to_owned()),
            logical_name: Some("attempt.drat".to_owned()),
        });
        let err = record_authority_gate_attempt(temp.path(), malformed_artifact)
            .expect_err("malformed artifact hash should fail");
        assert!(err.to_string().contains("artifact blake3"));
    }

    #[test]
    fn authority_append_enforces_replay_binding_for_accepted_attempts() {
        let temp = tempfile::tempdir().expect("tempdir");
        let mut accepted = ProofAttempt::new(
            hash("goal"),
            AttemptStatus::Accepted,
            hash("audit"),
            test_env(),
        );
        accepted.authority_gate = Some("trust_audit".to_owned());
        accepted.trust_level = Some(TrustLevel::KernelVerified);

        let err = append_authority_attempt_to(temp.path(), &accepted)
            .expect_err("accepted authority attempt missing command binding should fail");
        assert!(err.to_string().contains("command digest"));

        let (solver_artifact, command_evidence) = replay_bound_authority_artifacts(temp.path());
        accepted.solver_artifact = Some(solver_artifact);
        accepted.command_evidence = Some(command_evidence);

        append_authority_attempt_to(temp.path(), &accepted)
            .expect("accepted authority attempt with command evidence should append");

        let attempts: Vec<_> = iter_from(temp.path(), AttemptFilter::default())
            .expect("iter attempts")
            .collect();
        assert_eq!(attempts, vec![accepted]);
    }

    #[test]
    fn authority_append_rejects_zero_byte_command_evidence() {
        let temp = tempfile::tempdir().expect("tempdir");
        let solver_artifact = put_artifact(
            temp.path(),
            b"authority solver report",
            Some("solver/lrat"),
            Some("authority.lrat"),
        )
        .expect("put solver artifact");
        let mut accepted = ProofAttempt::new(
            hash("goal"),
            AttemptStatus::Accepted,
            hash("audit"),
            test_env(),
        );
        accepted.authority_gate = Some("trust_audit".to_owned());
        accepted.trust_level = Some(TrustLevel::KernelVerified);
        accepted.solver_artifact = Some(solver_artifact);
        accepted.command_evidence = Some(ArtifactRef {
            blake3: hash("empty-command-evidence"),
            byte_len: 0,
            kind: Some("command/transcript".to_owned()),
            logical_name: Some("authority-command.txt".to_owned()),
        });

        let err = append_authority_attempt_to(temp.path(), &accepted)
            .expect_err("zero-byte command evidence should fail");
        assert!(err.to_string().contains("non-zero byte_len"));
    }

    #[test]
    fn raw_append_preserves_incomplete_diagnostic_attempts() {
        let temp = tempfile::tempdir().expect("tempdir");
        let mut attempt = ProofAttempt::new(
            String::new(),
            AttemptStatus::Accepted,
            "diagnostic-only".to_owned(),
            test_env(),
        );
        attempt.created_at = 1_700_000_000_000_000_000;

        append_to(temp.path(), &attempt).expect("raw append should remain permissive");

        let attempts: Vec<_> = iter_from(temp.path(), AttemptFilter::default())
            .expect("iter raw attempts")
            .collect();
        assert_eq!(attempts, vec![attempt]);
    }

    #[test]
    fn replay_attempt_from_result_copies_generic_producer_context_metadata() {
        let mut original = ProofAttempt::new(
            hash("goal"),
            AttemptStatus::Rejected {
                reason: "original failure".to_owned(),
            },
            hash("original-audit"),
            test_env(),
        );
        original.proof_state_before = Some(StateId::from("state-before-original"));
        original.authority_gate = Some("trust_audit".to_owned());

        let plan = ReplayPlan {
            original,
            live_env: test_env(),
            env_matches: true,
            mismatch_explanation: None,
        };
        let patch_artifact = ArtifactRef {
            blake3: hash("patch"),
            byte_len: 12,
            kind: Some("patch/unified-diff".to_owned()),
            logical_name: Some("candidate.patch".to_owned()),
        };
        let mut result = ReplayAttemptResult::new(AttemptStatus::Accepted, hash("replay-audit"));
        result.producer = Some(producer("provider-b", "attempt-producer-b"));
        result.context = Some(context("task-2", Some(patch_artifact.clone())));

        let replay = replay_attempt_from_result(&plan, result);

        assert_eq!(replay.authority_gate.as_deref(), Some("trust_audit"));
        assert_eq!(
            replay.proof_state_before.as_ref().map(StateId::as_str),
            Some("state-before-original")
        );
        assert_eq!(
            replay
                .producer
                .as_ref()
                .map(|producer| producer.provider.as_str()),
            Some("provider-b")
        );
        assert_eq!(
            replay
                .context
                .as_ref()
                .and_then(|context| context.external_task_id.as_deref()),
            Some("task-2")
        );
        assert_eq!(replay.artifact_refs(), vec![&patch_artifact]);
    }

    #[test]
    fn attempt_filter_and_summary_support_generic_producer_context_metadata() {
        let temp = tempfile::tempdir().expect("tempdir");

        let mut accepted = ProofAttempt::new(
            hash("goal-a"),
            AttemptStatus::Accepted,
            hash("audit-a"),
            test_env(),
        );
        accepted.created_at = 1_700_000_000_000_000_000;
        accepted.producer = Some(producer("provider-a", "producer-a"));
        accepted.context = Some(context("task-a", None));

        let mut rejected = ProofAttempt::new(
            hash("goal-b"),
            AttemptStatus::Rejected {
                reason: "type mismatch".to_owned(),
            },
            hash("audit-b"),
            test_env(),
        );
        rejected.created_at = 1_700_000_000_001_000_000;
        rejected.producer = Some(producer("provider-a", "producer-b"));
        rejected.context = Some(context("task-b", None));

        let mut timeout = ProofAttempt::new(
            hash("goal-c"),
            AttemptStatus::Timeout { after_ms: 5_000 },
            hash("audit-c"),
            test_env(),
        );
        timeout.created_at = 1_700_000_000_002_000_000;
        timeout.producer = Some(AttemptProducer {
            producer_kind: ProducerKind::Solver,
            provider: "provider-c".to_owned(),
            name: "producer-c".to_owned(),
            version: None,
            command_digest: None,
        });
        timeout.context = Some(context("task-a", None));

        append_to(temp.path(), &accepted).expect("append accepted");
        append_to(temp.path(), &rejected).expect("append rejected");
        append_to(temp.path(), &timeout).expect("append timeout");

        let by_provider: Vec<_> = iter_from(
            temp.path(),
            AttemptFilter {
                producer_provider: Some("provider-a".to_owned()),
                ..AttemptFilter::default()
            },
        )
        .expect("filter by provider")
        .collect();
        assert_eq!(by_provider, vec![accepted.clone(), rejected.clone()]);

        let by_producer: Vec<_> = iter_from(
            temp.path(),
            AttemptFilter {
                producer: Some("producer-c".to_owned()),
                producer_kind: Some(ProducerKind::Solver),
                ..AttemptFilter::default()
            },
        )
        .expect("filter by producer")
        .collect();
        assert_eq!(by_producer, vec![timeout.clone()]);

        let by_task_and_status: Vec<_> = iter_from(
            temp.path(),
            AttemptFilter {
                external_task_id: Some("task-a".to_owned()),
                status: Some(AttemptStatusFilter::Timeout),
                ..AttemptFilter::default()
            },
        )
        .expect("filter by task and status")
        .collect();
        assert_eq!(by_task_and_status, vec![timeout]);

        let report =
            query_attempts_limited(temp.path(), AttemptFilter::default(), Some(1)).expect("query");
        assert_eq!(report.total, 3);
        assert_eq!(report.returned, 1);
        assert_eq!(report.summary.by_producer.get("producer-a"), Some(&1));
        assert_eq!(report.summary.by_producer.get("producer-b"), Some(&1));
        assert_eq!(
            report.summary.by_producer_provider.get("provider-a"),
            Some(&2)
        );
        assert_eq!(report.summary.by_producer_kind.get("model"), Some(&2));
        assert_eq!(report.summary.by_producer_kind.get("solver"), Some(&1));
        assert_eq!(report.summary.by_external_task_id.get("task-a"), Some(&2));
        assert_eq!(report.summary.by_external_task_id.get("task-b"), Some(&1));
        assert_eq!(report.summary.without_producer, 0);
        assert_eq!(report.summary.without_external_task_id, 0);
    }

    #[test]
    fn append_writes_cake_directory_not_legacy_mathverse() {
        let temp = tempfile::tempdir().expect("tempdir");
        let mut attempt = ProofAttempt::new(
            hash("goal-cake"),
            AttemptStatus::Accepted,
            hash("audit-cake"),
            test_env(),
        );
        attempt.created_at = 1_700_000_000_000_000_000;

        append_to(temp.path(), &attempt).expect("append attempt");

        assert!(
            temp.path().join(".cake").join("attempts").is_dir(),
            "new attempts must be written under .cake/attempts"
        );
        assert!(
            !temp.path().join(".mathverse").exists(),
            "writes must not create the legacy .mathverse directory"
        );
    }

    #[test]
    fn iter_reads_legacy_mathverse_attempts_and_merges_with_cake() {
        let temp = tempfile::tempdir().expect("tempdir");

        let mut legacy = ProofAttempt::new(
            hash("goal-legacy"),
            AttemptStatus::Accepted,
            hash("audit-legacy"),
            test_env(),
        );
        legacy.created_at = 1_700_000_000_000_000_000;
        let legacy_dir = temp.path().join(".mathverse").join("attempts");
        fs::create_dir_all(&legacy_dir).expect("create legacy attempts dir");
        fs::write(
            legacy_dir.join(log_filename_for_ns(legacy.created_at)),
            serde_json::to_string(&legacy).expect("encode legacy attempt") + "\n",
        )
        .expect("write legacy attempt log");

        let mut current = ProofAttempt::new(
            hash("goal-current"),
            AttemptStatus::Accepted,
            hash("audit-current"),
            test_env(),
        );
        current.created_at = 1_700_000_100_000_000_000;
        append_to(temp.path(), &current).expect("append current attempt");

        let attempts: Vec<_> = iter_from(temp.path(), AttemptFilter::default())
            .expect("iter merged attempt logs")
            .collect();
        assert_eq!(
            attempts,
            vec![legacy.clone(), current],
            "legacy .mathverse attempts must be read before .cake attempts"
        );

        let found = find_attempt(temp.path(), &legacy.attempt_id)
            .expect("find legacy attempt")
            .expect("legacy attempt should be found by id");
        assert_eq!(found, legacy);
    }

    #[test]
    fn artifact_path_falls_back_to_legacy_mathverse_store() {
        let temp = tempfile::tempdir().expect("tempdir");
        let bytes = b"legacy artifact body";
        let digest = blake3::hash(bytes).to_hex().to_string();
        let legacy_dir = temp.path().join(".mathverse").join("artifacts");
        fs::create_dir_all(&legacy_dir).expect("create legacy artifacts dir");
        fs::write(legacy_dir.join(&digest), bytes).expect("write legacy artifact");

        let artifact = ArtifactRef {
            blake3: digest.clone(),
            byte_len: bytes.len() as u64,
            kind: Some("solver/lrat".to_owned()),
            logical_name: None,
        };
        assert_eq!(
            artifact_path(temp.path(), &artifact),
            legacy_dir.join(&digest),
            "artifact_path must fall back to the legacy .mathverse store"
        );
        assert_eq!(
            read_artifact(temp.path(), &artifact).expect("read legacy artifact"),
            bytes.to_vec()
        );

        // A current-store artifact with the same root resolves to .cake.
        let current = put_artifact(temp.path(), b"current artifact body", None, None)
            .expect("put current artifact");
        assert_eq!(
            artifact_path(temp.path(), &current),
            temp.path()
                .join(".cake")
                .join("artifacts")
                .join(&current.blake3)
        );
    }
}
