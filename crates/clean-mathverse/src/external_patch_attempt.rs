// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generic recording for externally produced patch attempts.
//!
//! This module is intentionally library-only. Product surfaces such as
//! `mathbot bakeoff` can call it after their own authority gates have accepted
//! or rejected an external patch attempt.

use std::collections::BTreeMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::attempt_log::{
    append_to, iter_from, put_artifact, read_artifact, validate_replay_binding, ArtifactRef,
    AttemptBudget, AttemptContext, AttemptFilter, AttemptProducer, AttemptStatus,
    AttemptStatusFilter, Blake3Hash, EnvFingerprint, ProofAttempt, ReplayBindingValidationOptions,
};
use crate::env_fingerprint::{capture_git_dirty_state, GitDirtyState};
use crate::error::{MathverseError, MathverseResult};
use crate::types::TrustLevel;

/// Default authority-gate label for generic external patch attempts.
pub const EXTERNAL_PATCH_AUTHORITY_GATE: &str = "external_patch";

/// Artifact kind used for accepted external patch contents.
pub const EXTERNAL_PATCH_ARTIFACT_KIND: &str = "external_patch/patch";

/// Artifact kind used for the JSON envelope holding optional attempt context.
pub const EXTERNAL_PATCH_CONTEXT_ARTIFACT_KIND: &str = "external_patch/context+json";

const DIRTY_ROOT_POLICY_KEY: &str = "external_patch.dirty_root.policy";
const DIRTY_ROOT_REASON_KEY: &str = "external_patch.dirty_root.reason";
const DIRTY_ROOT_IS_GIT_WORKTREE_KEY: &str = "external_patch.dirty_root.is_git_worktree";
const DIRTY_ROOT_ENTRY_COUNT_KEY: &str = "external_patch.dirty_root.entry_count";
const DIRTY_ROOT_ENTRIES_SHA256_KEY: &str = "external_patch.dirty_root.entries_sha256";
const TRUST_AUDIT_GATE: &str = "trust_audit";
const STATEMENT_PRESERVATION_GATE: &str = "statement_preservation";
const FALSE_CONTROLS_GATE: &str = "false_controls";
const TRUST_LEDGER_GATE: &str = "trust_ledger";

/// Optional metadata and hash evidence that does not have first-class fields in
/// [`ProofAttempt`].
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternalPatchMetadata {
    /// Caller-defined context fields, kept stringly typed for stable JSON.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub context: BTreeMap<String, String>,
    /// Additional gate hashes, keyed by stable gate name.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub gate_hashes: BTreeMap<String, Blake3Hash>,
    /// Additional audit hashes, keyed by stable audit/report name.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub audit_hashes: BTreeMap<String, Blake3Hash>,
}

impl ExternalPatchMetadata {
    fn is_empty(&self) -> bool {
        self.context.is_empty() && self.gate_hashes.is_empty() && self.audit_hashes.is_empty()
    }
}

/// Patch, prompt, or response artifact supplied either as bytes to store or as
/// an already stored attempt-log artifact reference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternalPatchArtifact<'a> {
    /// Bytes that should be written under `.cake/artifacts`.
    Bytes {
        /// Artifact bytes.
        bytes: &'a [u8],
        /// Producer-defined artifact kind.
        kind: Option<&'a str>,
        /// Optional logical filename.
        logical_name: Option<&'a str>,
    },
    /// Existing content-addressed artifact reference.
    Existing(ArtifactRef),
}

impl<'a> ExternalPatchArtifact<'a> {
    /// Build a patch-content artifact with the generic patch kind.
    pub fn patch_bytes(bytes: &'a [u8], logical_name: Option<&'a str>) -> Self {
        Self::Bytes {
            bytes,
            kind: Some(EXTERNAL_PATCH_ARTIFACT_KIND),
            logical_name,
        }
    }
}

/// Caller-supplied data for one external patch attempt record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternalPatchAttemptInput<'a> {
    /// BLAKE3 hash of the target goal, issue, theorem, or normalized objective.
    pub goal_hash: Blake3Hash,
    /// Final external patch gate status.
    pub status: AttemptStatus,
    /// BLAKE3 hash of the primary gate/audit report.
    pub trust_audit_hash: Blake3Hash,
    /// Reproducible execution fingerprint.
    pub env: EnvFingerprint,
    /// Patch artifact or bytes. Required when `status` is accepted.
    pub patch: Option<ExternalPatchArtifact<'a>>,
    /// Optional prompt artifact or bytes.
    pub prompt: Option<ExternalPatchArtifact<'a>>,
    /// Optional model/service response artifact or bytes.
    pub model_response: Option<ExternalPatchArtifact<'a>>,
    /// Authority-gate name. Defaults to [`EXTERNAL_PATCH_AUTHORITY_GATE`].
    pub authority_gate: Option<String>,
    /// Stable failure-mode classification for rejected/timeout attempts.
    pub failure_mode: Option<String>,
    /// Trust level assigned by the accepted audit path, when known.
    pub trust_level: Option<TrustLevel>,
    /// Wall-clock duration in milliseconds.
    pub wall_time_ms: u64,
    /// Optional resource accounting and attempt-budget metadata.
    pub budget: Option<AttemptBudget>,
    /// Generic producer metadata.
    pub producer: Option<AttemptProducer>,
    /// Generic external context metadata. `patch_artifact` is filled from
    /// `patch` when bytes are supplied here.
    pub context: AttemptContext,
    /// Optional supplemental hash evidence that does not have first-class
    /// attempt fields.
    pub metadata: ExternalPatchMetadata,
    /// Explicit reason allowing an accepted attempt to be recorded from a dirty
    /// git worktree. `None` is fail-closed for accepted attempts.
    pub allow_dirty_root_reason: Option<String>,
}

impl<'a> ExternalPatchAttemptInput<'a> {
    /// Build an external patch attempt input with no optional artifacts.
    pub fn new(
        goal_hash: Blake3Hash,
        status: AttemptStatus,
        trust_audit_hash: Blake3Hash,
        env: EnvFingerprint,
    ) -> Self {
        Self {
            goal_hash,
            status,
            trust_audit_hash,
            env,
            patch: None,
            prompt: None,
            model_response: None,
            authority_gate: None,
            failure_mode: None,
            trust_level: None,
            wall_time_ms: 0,
            budget: None,
            producer: None,
            context: AttemptContext::default(),
            metadata: ExternalPatchMetadata::default(),
            allow_dirty_root_reason: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct ExternalPatchContextArtifact {
    schema_version: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    prompt: Option<ArtifactRef>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    model_response: Option<ArtifactRef>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    authority_gate_attempts: BTreeMap<String, ExternalPatchAuthorityGateEvidence>,
    #[serde(default, skip_serializing_if = "ExternalPatchMetadata::is_empty")]
    metadata: ExternalPatchMetadata,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct ExternalPatchAuthorityGateEvidence {
    attempt_id: String,
    authority_gate: String,
    status: String,
    goal_hash: Blake3Hash,
    trust_audit_hash: Blake3Hash,
    report_artifact_hash: Blake3Hash,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ValidatedAuthorityGateAttempt {
    evidence: ExternalPatchAuthorityGateEvidence,
    attempt: ProofAttempt,
}

/// Record an externally produced patch attempt in the generic attempt log.
///
/// Accepted attempts fail closed when no patch artifact/content is supplied or
/// the target root is a dirty git worktree without an explicit override reason.
/// Existing artifact references are validated before the log entry is appended.
pub fn record_external_patch_attempt(
    target_root: impl AsRef<Path>,
    input: ExternalPatchAttemptInput<'_>,
) -> MathverseResult<ProofAttempt> {
    let root = target_root.as_ref();
    if matches!(input.status, AttemptStatus::Accepted)
        && input.patch.is_none()
        && input.context.patch_artifact.is_none()
    {
        return Err(MathverseError::Kernel(
            "accepted external patch attempt requires a patch artifact".to_owned(),
        ));
    }

    let mut metadata = input.metadata;
    enforce_accepted_dirty_root_policy(
        root,
        &input.status,
        input.allow_dirty_root_reason.as_deref(),
        &mut metadata,
    )?;

    let mut attempt_context = input.context;
    let patch_artifact = match input.patch.as_ref() {
        Some(artifact) => {
            let stored = store_or_validate_artifact(root, artifact)?;
            if let Some(existing) = &attempt_context.patch_artifact {
                if existing != &stored {
                    return Err(MathverseError::Kernel(
                        "external patch attempt supplied conflicting patch artifacts".to_owned(),
                    ));
                }
            }
            Some(stored)
        }
        None => attempt_context
            .patch_artifact
            .as_ref()
            .map(|reference| {
                read_artifact(root, reference)?;
                Ok::<ArtifactRef, MathverseError>(reference.clone())
            })
            .transpose()?,
    };
    attempt_context.patch_artifact = patch_artifact;

    let prompt_artifact = input
        .prompt
        .as_ref()
        .map(|artifact| store_or_validate_artifact(root, artifact))
        .transpose()?;
    let model_response_artifact = input
        .model_response
        .as_ref()
        .map(|artifact| store_or_validate_artifact(root, artifact))
        .transpose()?;
    let authority_gate_attempts = enforce_accepted_replayable_authority_artifacts(
        root,
        &input.status,
        &input.goal_hash,
        &input.trust_audit_hash,
        &attempt_context,
        model_response_artifact.as_ref(),
        &metadata,
    )?;

    let context_artifact = build_context_artifact(
        root,
        prompt_artifact,
        model_response_artifact,
        authority_gate_attempts,
        metadata,
    )?;

    let gate = input
        .authority_gate
        .as_deref()
        .unwrap_or(EXTERNAL_PATCH_AUTHORITY_GATE)
        .trim();
    if gate.is_empty() {
        return Err(MathverseError::Kernel(
            "external patch attempt requires a non-empty authority gate name".to_owned(),
        ));
    }

    let mut attempt = ProofAttempt::new(
        input.goal_hash,
        input.status,
        input.trust_audit_hash,
        input.env,
    );
    attempt.model_response = context_artifact;
    attempt.authority_gate = Some(gate.to_owned());
    attempt.failure_mode = input.failure_mode;
    attempt.trust_level = input.trust_level;
    attempt.wall_time_ms = input.wall_time_ms;
    attempt.budget = input.budget;
    attempt.producer = input.producer;
    if !attempt_context_is_empty(&attempt_context) {
        attempt.context = Some(attempt_context);
    }

    append_to(root, &attempt)?;
    Ok(attempt)
}

fn enforce_accepted_replayable_authority_artifacts(
    root: &Path,
    status: &AttemptStatus,
    external_goal_hash: &str,
    trust_audit_hash: &str,
    context: &AttemptContext,
    model_response: Option<&ArtifactRef>,
    metadata: &ExternalPatchMetadata,
) -> MathverseResult<BTreeMap<String, ExternalPatchAuthorityGateEvidence>> {
    if !matches!(status, AttemptStatus::Accepted) {
        return Ok(BTreeMap::new());
    }

    if context.patch_artifact.is_none() {
        return Err(MathverseError::Kernel(
            "accepted external patch attempt requires a patch artifact".to_owned(),
        ));
    }

    let has_prompt_digest = match context.prompt_digest.as_deref().map(str::trim) {
        Some(digest) if !digest.is_empty() => {
            if !is_blake3_hex(digest) {
                return Err(MathverseError::Kernel(
                    "accepted external patch attempt requires prompt digest to be a BLAKE3 hash"
                        .to_owned(),
                ));
            }
            true
        }
        _ => false,
    };
    if !has_prompt_digest && model_response.is_none() {
        return Err(MathverseError::Kernel(
            "accepted external patch attempt requires a prompt digest or model response artifact"
                .to_owned(),
        ));
    }

    validate_trust_audit_metadata_hash(metadata, trust_audit_hash)?;
    let mut evidence = BTreeMap::new();
    let trust_audit_evidence =
        validate_replayable_authority_gate_attempt(root, TRUST_AUDIT_GATE, trust_audit_hash)?;
    enforce_authority_gate_context(
        TRUST_AUDIT_GATE,
        &trust_audit_evidence.attempt,
        external_goal_hash,
        context,
    )?;
    evidence.insert(TRUST_AUDIT_GATE.to_owned(), trust_audit_evidence.evidence);
    let statement_preservation_hash = required_gate_hash(metadata, STATEMENT_PRESERVATION_GATE)?;
    let statement_preservation_evidence = validate_replayable_authority_gate_attempt(
        root,
        STATEMENT_PRESERVATION_GATE,
        statement_preservation_hash,
    )?;
    enforce_authority_gate_context(
        STATEMENT_PRESERVATION_GATE,
        &statement_preservation_evidence.attempt,
        external_goal_hash,
        context,
    )?;
    evidence.insert(
        STATEMENT_PRESERVATION_GATE.to_owned(),
        statement_preservation_evidence.evidence,
    );
    let false_controls_hash = required_gate_hash(metadata, FALSE_CONTROLS_GATE)?;
    let false_controls_evidence =
        validate_replayable_authority_gate_attempt(root, FALSE_CONTROLS_GATE, false_controls_hash)?;
    enforce_authority_gate_context(
        FALSE_CONTROLS_GATE,
        &false_controls_evidence.attempt,
        external_goal_hash,
        context,
    )?;
    evidence.insert(
        FALSE_CONTROLS_GATE.to_owned(),
        false_controls_evidence.evidence,
    );
    if let Some(trust_ledger_hash) = metadata.gate_hashes.get(TRUST_LEDGER_GATE) {
        let trust_ledger_evidence =
            validate_replayable_authority_gate_attempt(root, TRUST_LEDGER_GATE, trust_ledger_hash)?;
        enforce_authority_gate_context(
            TRUST_LEDGER_GATE,
            &trust_ledger_evidence.attempt,
            external_goal_hash,
            context,
        )?;
        evidence.insert(TRUST_LEDGER_GATE.to_owned(), trust_ledger_evidence.evidence);
    }
    Ok(evidence)
}

fn validate_trust_audit_metadata_hash(
    metadata: &ExternalPatchMetadata,
    trust_audit_hash: &str,
) -> MathverseResult<()> {
    let Some(metadata_hash) = metadata.audit_hashes.get(TRUST_AUDIT_GATE) else {
        return Ok(());
    };
    if metadata_hash == trust_audit_hash {
        return Ok(());
    }
    Err(MathverseError::Kernel(format!(
        "accepted external patch attempt trust_audit metadata hash `{metadata_hash}` does not match primary trust_audit_hash `{trust_audit_hash}`"
    )))
}

fn required_gate_hash<'a>(
    metadata: &'a ExternalPatchMetadata,
    gate: &str,
) -> MathverseResult<&'a str> {
    metadata
        .gate_hashes
        .get(gate)
        .map(String::as_str)
        .ok_or_else(|| {
            MathverseError::Kernel(format!(
                "accepted external patch attempt requires replayable {gate} evidence"
            ))
        })
}

fn validate_replayable_authority_gate_attempt(
    root: &Path,
    gate: &str,
    hash: &str,
) -> MathverseResult<ValidatedAuthorityGateAttempt> {
    let hash = hash.trim();
    if !is_blake3_hex(hash) {
        return Err(MathverseError::Kernel(format!(
            "accepted external patch attempt requires {gate} evidence to be a BLAKE3 artifact hash"
        )));
    }

    let attempts: Vec<_> = iter_from(
        root,
        AttemptFilter {
            status: Some(AttemptStatusFilter::Accepted),
            authority_gate: Some(gate.to_owned()),
            ..AttemptFilter::default()
        },
    )?
    .collect();

    let mut candidate_error = None;
    for attempt in attempts {
        if attempt.trust_audit_hash != hash {
            continue;
        }
        match validate_replayable_authority_gate_candidate(root, gate, hash, &attempt) {
            Ok(evidence) => return Ok(evidence),
            Err(err) => candidate_error = Some(err.to_string()),
        }
    }

    if let Some(err) = candidate_error {
        return Err(MathverseError::Kernel(format!(
            "accepted external patch attempt requires replayable {gate} authority-gate attempt `{hash}`: {err}"
        )));
    }

    Err(MathverseError::Kernel(format!(
        "accepted external patch attempt requires accepted {gate} authority-gate attempt with trust audit artifact `{hash}`"
    )))
}

fn validate_replayable_authority_gate_candidate(
    root: &Path,
    gate: &str,
    expected_hash: &str,
    attempt: &ProofAttempt,
) -> MathverseResult<ValidatedAuthorityGateAttempt> {
    if !matches!(attempt.status, AttemptStatus::Accepted) {
        return Err(MathverseError::Kernel(format!(
            "{gate} authority-gate attempt `{}` is not accepted",
            attempt.attempt_id
        )));
    }
    if attempt.authority_gate.as_deref() != Some(gate) {
        return Err(MathverseError::Kernel(format!(
            "{gate} authority-gate attempt `{}` recorded gate {:?}",
            attempt.attempt_id, attempt.authority_gate
        )));
    }
    if attempt.trust_audit_hash != expected_hash {
        return Err(MathverseError::Kernel(format!(
            "{gate} authority-gate attempt `{}` trust_audit_hash `{}` does not match expected `{expected_hash}`",
            attempt.attempt_id, attempt.trust_audit_hash
        )));
    }
    validate_replay_binding(
        attempt,
        ReplayBindingValidationOptions {
            require_policy_metadata: true,
            ..ReplayBindingValidationOptions::default()
        },
    )?;

    let report_artifact = attempt.solver_artifact.as_ref().ok_or_else(|| {
        MathverseError::Kernel(format!(
            "{gate} authority-gate attempt `{}` has no replayable report artifact",
            attempt.attempt_id
        ))
    })?;
    if report_artifact.blake3 != expected_hash {
        return Err(MathverseError::Kernel(format!(
            "{gate} authority-gate attempt `{}` report artifact hash `{}` does not match trust_audit_hash `{expected_hash}`",
            attempt.attempt_id, report_artifact.blake3
        )));
    }
    read_artifact(root, report_artifact)?;

    for artifact in attempt.artifact_refs() {
        read_artifact(root, artifact)?;
    }

    let evidence = ExternalPatchAuthorityGateEvidence {
        attempt_id: attempt.attempt_id.to_string(),
        authority_gate: gate.to_owned(),
        status: "accepted".to_owned(),
        goal_hash: attempt.goal_hash.clone(),
        trust_audit_hash: attempt.trust_audit_hash.clone(),
        report_artifact_hash: report_artifact.blake3.clone(),
    };
    Ok(ValidatedAuthorityGateAttempt {
        evidence,
        attempt: attempt.clone(),
    })
}

fn enforce_authority_gate_context(
    gate: &str,
    gate_attempt: &ProofAttempt,
    external_goal_hash: &str,
    external_context: &AttemptContext,
) -> MathverseResult<()> {
    let gate_context = gate_attempt.context.as_ref();

    if gate_attempt.goal_hash != external_goal_hash {
        return Err(authority_gate_context_error(
            gate,
            format!(
                "goal_hash `{}` does not match external patch goal_hash `{external_goal_hash}`",
                gate_attempt.goal_hash
            ),
        ));
    }

    let external_patch = external_context.patch_artifact.as_ref().ok_or_else(|| {
        authority_gate_context_error(
            gate,
            "external patch context has no patch_artifact anchor".to_owned(),
        )
    })?;
    let gate_patch = gate_context
        .and_then(|context| context.patch_artifact.as_ref())
        .ok_or_else(|| {
            authority_gate_context_error(
                gate,
                "authority-gate attempt has no patch_artifact anchor".to_owned(),
            )
        })?;
    if !patch_artifact_matches(external_patch, gate_patch) {
        return Err(authority_gate_context_error(
            gate,
            format!(
                "patch artifact `{}` does not match external patch artifact `{}`",
                gate_patch.blake3, external_patch.blake3
            ),
        ));
    }

    if let Some(external_task) = external_context
        .external_task_id
        .as_deref()
        .and_then(non_empty_opt)
    {
        let gate_task = gate_context
            .and_then(|context| context.external_task_id.as_deref())
            .and_then(non_empty_opt)
            .ok_or_else(|| {
                authority_gate_context_error(
                    gate,
                    format!(
                        "authority-gate attempt has no external_task_id for patch external_task_id `{external_task}`"
                    ),
                )
            })?;
        if external_task != gate_task {
            return Err(authority_gate_context_error(gate, format!(
                "external_task_id `{gate_task}` does not match patch external_task_id `{external_task}`"
            )));
        }
    }

    if let (Some(external_prompt), Some(gate_prompt)) = (
        external_context
            .prompt_digest
            .as_deref()
            .and_then(non_empty_opt),
        gate_context
            .and_then(|context| context.prompt_digest.as_deref())
            .and_then(non_empty_opt),
    ) {
        if external_prompt != gate_prompt {
            return Err(authority_gate_context_error(gate, format!(
                "prompt_digest `{gate_prompt}` does not match patch prompt_digest `{external_prompt}`"
            )));
        }
    }

    Ok(())
}

fn patch_artifact_matches(left: &ArtifactRef, right: &ArtifactRef) -> bool {
    left.blake3 == right.blake3 && left.byte_len == right.byte_len
}

fn non_empty_opt(value: &str) -> Option<&str> {
    let trimmed = value.trim();
    (!trimmed.is_empty()).then_some(trimmed)
}

fn authority_gate_context_error(gate: &str, detail: String) -> MathverseError {
    MathverseError::Kernel(format!(
        "accepted external patch attempt requires {gate} evidence tied to the same goal/task/artifact/prompt context as the patch: {detail}"
    ))
}

fn is_blake3_hex(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn enforce_accepted_dirty_root_policy(
    root: &Path,
    status: &AttemptStatus,
    allow_reason: Option<&str>,
    metadata: &mut ExternalPatchMetadata,
) -> MathverseResult<()> {
    let allow_reason = match allow_reason {
        Some(reason) => {
            let trimmed = reason.trim();
            if trimmed.is_empty() {
                return Err(MathverseError::Kernel(
                    "dirty-root override reason must not be empty".to_owned(),
                ));
            }
            Some(trimmed)
        }
        None => None,
    };

    if !matches!(status, AttemptStatus::Accepted) {
        return Ok(());
    }

    let dirty_state = capture_git_dirty_state(root)?;
    if dirty_state.git_status_clean != Some(false) {
        return Ok(());
    }

    let Some(reason) = allow_reason else {
        let digest = dirty_state
            .dirty_entries_sha256
            .as_deref()
            .unwrap_or("unavailable");
        return Err(MathverseError::Kernel(format!(
            "accepted external patch attempt refused because target root `{}` is a dirty git worktree (dirty_entries={}, dirty_entries_sha256={digest}); provide an explicit dirty-root override reason to record anyway",
            root.display(),
            dirty_state.dirty_entry_count
        )));
    };

    record_dirty_root_override_metadata(metadata, &dirty_state, reason)
}

fn record_dirty_root_override_metadata(
    metadata: &mut ExternalPatchMetadata,
    dirty_state: &GitDirtyState,
    reason: &str,
) -> MathverseResult<()> {
    insert_context_metadata(metadata, DIRTY_ROOT_POLICY_KEY, "allowed")?;
    insert_context_metadata(metadata, DIRTY_ROOT_REASON_KEY, reason)?;
    insert_context_metadata(
        metadata,
        DIRTY_ROOT_IS_GIT_WORKTREE_KEY,
        dirty_state.is_git_worktree.to_string(),
    )?;
    insert_context_metadata(
        metadata,
        DIRTY_ROOT_ENTRY_COUNT_KEY,
        dirty_state.dirty_entry_count.to_string(),
    )?;
    if let Some(digest) = &dirty_state.dirty_entries_sha256 {
        insert_context_metadata(metadata, DIRTY_ROOT_ENTRIES_SHA256_KEY, digest)?;
    }
    Ok(())
}

fn insert_context_metadata(
    metadata: &mut ExternalPatchMetadata,
    key: &str,
    value: impl Into<String>,
) -> MathverseResult<()> {
    let value = value.into();
    if let Some(existing) = metadata.context.get(key) {
        if existing == &value {
            return Ok(());
        }
        return Err(MathverseError::Kernel(format!(
            "external patch metadata key `{key}` conflicts with dirty-root policy metadata"
        )));
    }
    metadata.context.insert(key.to_owned(), value);
    Ok(())
}

fn attempt_context_is_empty(context: &AttemptContext) -> bool {
    context.external_run_id.is_none()
        && context.external_task_id.is_none()
        && context.prompt_digest.is_none()
        && context.patch_artifact.is_none()
}

fn store_or_validate_artifact(
    root: &Path,
    artifact: &ExternalPatchArtifact<'_>,
) -> MathverseResult<ArtifactRef> {
    match artifact {
        ExternalPatchArtifact::Bytes {
            bytes,
            kind,
            logical_name,
        } => put_artifact(root, bytes, *kind, *logical_name),
        ExternalPatchArtifact::Existing(reference) => {
            read_artifact(root, reference)?;
            Ok(reference.clone())
        }
    }
}

fn build_context_artifact(
    root: &Path,
    prompt: Option<ArtifactRef>,
    model_response: Option<ArtifactRef>,
    authority_gate_attempts: BTreeMap<String, ExternalPatchAuthorityGateEvidence>,
    metadata: ExternalPatchMetadata,
) -> MathverseResult<Option<ArtifactRef>> {
    if prompt.is_none()
        && model_response.is_none()
        && authority_gate_attempts.is_empty()
        && metadata.is_empty()
    {
        return Ok(None);
    }

    let context = ExternalPatchContextArtifact {
        schema_version: 1,
        prompt,
        model_response,
        authority_gate_attempts,
        metadata,
    };
    let bytes = serde_json::to_vec(&context)?;
    put_artifact(
        root,
        &bytes,
        Some(EXTERNAL_PATCH_CONTEXT_ARTIFACT_KIND),
        Some("external-patch-attempt-context.json"),
    )
    .map(Some)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::attempt_log::{
        iter_from, put_artifact, read_artifact, record_authority_gate_attempt, AttemptFilter,
        AuthorityGateAttempt, ProducerKind,
    };
    use std::process::Command;

    fn test_env() -> EnvFingerprint {
        EnvFingerprint {
            lean_toolchain: "leanprover/lean4:v4.18.0".to_owned(),
            clean_commit: "0123456789abcdef0123456789abcdef01234567".to_owned(),
            ay_revision: Some("tag:v0.10.1".to_owned()),
            llvm2_revision: None,
            host_arch: "test-arch".to_owned(),
            host_os: "test-os".to_owned(),
            solver_binaries: Vec::new(),
        }
    }

    fn hash(label: &str) -> String {
        blake3::hash(label.as_bytes()).to_hex().to_string()
    }

    fn producer() -> AttemptProducer {
        AttemptProducer {
            producer_kind: ProducerKind::Model,
            provider: "mathbot".to_owned(),
            name: "manual-patch".to_owned(),
            version: Some("slot-2-test".to_owned()),
            command_digest: Some(hash("manual-patch-command")),
        }
    }

    fn accepted_authority_evidence(
        root: &Path,
    ) -> (
        Blake3Hash,
        ExternalPatchMetadata,
        BTreeMap<String, ProofAttempt>,
    ) {
        let patch = default_patch_artifact(root);
        accepted_authority_evidence_for_context(
            root,
            hash("goal"),
            AttemptContext {
                prompt_digest: Some(hash("prompt")),
                patch_artifact: Some(patch),
                ..AttemptContext::default()
            },
        )
    }

    fn accepted_authority_evidence_for_context(
        root: &Path,
        goal_hash: Blake3Hash,
        context: AttemptContext,
    ) -> (
        Blake3Hash,
        ExternalPatchMetadata,
        BTreeMap<String, ProofAttempt>,
    ) {
        let trust_audit = accepted_gate_attempt_with_goal_and_context(
            root,
            TRUST_AUDIT_GATE,
            goal_hash.clone(),
            b"{\"gate\":\"trust_audit\",\"accepted\":true}",
            "external_patch/test_trust_audit",
            "trust-audit.json",
            context.clone(),
        );
        let statement_preservation = accepted_gate_attempt_with_goal_and_context(
            root,
            STATEMENT_PRESERVATION_GATE,
            goal_hash.clone(),
            b"{\"gate\":\"statement_preservation\",\"accepted\":true}",
            "external_patch/test_statement_preservation",
            "statement-preservation.json",
            context.clone(),
        );
        let false_controls = accepted_gate_attempt_with_goal_and_context(
            root,
            FALSE_CONTROLS_GATE,
            goal_hash,
            b"{\"gate\":\"false_controls\",\"accepted\":true}",
            "external_patch/test_false_controls",
            "false-controls.json",
            context,
        );

        let mut metadata = ExternalPatchMetadata::default();
        metadata.gate_hashes.insert(
            STATEMENT_PRESERVATION_GATE.to_owned(),
            statement_preservation.trust_audit_hash.clone(),
        );
        metadata.gate_hashes.insert(
            FALSE_CONTROLS_GATE.to_owned(),
            false_controls.trust_audit_hash.clone(),
        );
        metadata.audit_hashes.insert(
            TRUST_AUDIT_GATE.to_owned(),
            trust_audit.trust_audit_hash.clone(),
        );
        let trust_audit_hash = trust_audit.trust_audit_hash.clone();

        let attempts = BTreeMap::from([
            (TRUST_AUDIT_GATE.to_owned(), trust_audit),
            (
                STATEMENT_PRESERVATION_GATE.to_owned(),
                statement_preservation,
            ),
            (FALSE_CONTROLS_GATE.to_owned(), false_controls),
        ]);
        (trust_audit_hash, metadata, attempts)
    }

    fn append_raw_authority_gate_attempt(
        root: &Path,
        result: AuthorityGateAttempt,
    ) -> ProofAttempt {
        let AuthorityGateAttempt {
            gate,
            goal_hash,
            status,
            trust_audit_hash,
            env,
            wall_time_ms,
            solver_artifact,
            proof_state_before,
            proof_state_after,
            model_response,
            command_evidence,
            failure_mode,
            trust_level,
            budget,
            producer,
            context,
        } = result;
        let mut attempt = ProofAttempt::new(goal_hash, status, trust_audit_hash, env);
        attempt.wall_time_ms = wall_time_ms;
        attempt.authority_gate = Some(gate.trim().to_owned());
        attempt.solver_artifact = solver_artifact;
        attempt.proof_state_before = proof_state_before;
        attempt.proof_state_after = proof_state_after;
        attempt.model_response = model_response;
        attempt.command_evidence = command_evidence;
        attempt.failure_mode = failure_mode;
        attempt.trust_level = trust_level;
        attempt.budget = budget;
        attempt.producer = producer;
        attempt.context = context;
        append_to(root, &attempt).expect("raw append malformed authority gate attempt");
        attempt
    }

    fn accepted_gate_attempt(
        root: &Path,
        gate: &str,
        bytes: &[u8],
        kind: &str,
        logical_name: &str,
    ) -> ProofAttempt {
        accepted_gate_attempt_with_goal_and_context(
            root,
            gate,
            hash("goal"),
            bytes,
            kind,
            logical_name,
            AttemptContext {
                prompt_digest: Some(hash("prompt")),
                patch_artifact: Some(default_patch_artifact(root)),
                ..AttemptContext::default()
            },
        )
    }

    fn accepted_gate_attempt_with_goal(
        root: &Path,
        gate: &str,
        goal_hash: Blake3Hash,
        bytes: &[u8],
        kind: &str,
        logical_name: &str,
    ) -> ProofAttempt {
        accepted_gate_attempt_with_goal_and_context(
            root,
            gate,
            goal_hash,
            bytes,
            kind,
            logical_name,
            AttemptContext {
                prompt_digest: Some(hash("prompt")),
                patch_artifact: Some(default_patch_artifact(root)),
                ..AttemptContext::default()
            },
        )
    }

    fn accepted_gate_attempt_with_goal_and_context(
        root: &Path,
        gate: &str,
        goal_hash: Blake3Hash,
        bytes: &[u8],
        kind: &str,
        logical_name: &str,
        context: AttemptContext,
    ) -> ProofAttempt {
        let artifact = put_artifact(root, bytes, Some(kind), Some(logical_name))
            .expect("put authority gate artifact");
        let mut result = AuthorityGateAttempt::new(
            gate,
            goal_hash,
            AttemptStatus::Accepted,
            artifact.blake3.clone(),
            test_env(),
        );
        result.solver_artifact = Some(artifact);
        result.trust_level = Some(TrustLevel::KernelVerified);
        result.producer = Some(producer());
        result.context = Some(context);
        record_authority_gate_attempt(root, result).expect("record authority gate attempt")
    }

    fn default_patch_artifact(root: &Path) -> ArtifactRef {
        put_artifact(
            root,
            b"diff --git a/Foo.lean b/Foo.lean\n",
            Some(EXTERNAL_PATCH_ARTIFACT_KIND),
            Some("foo.patch"),
        )
        .expect("put default patch artifact")
    }

    fn external_patch_attempts(root: &Path) -> Vec<ProofAttempt> {
        iter_from(
            root,
            AttemptFilter {
                authority_gate: Some(EXTERNAL_PATCH_AUTHORITY_GATE.to_owned()),
                ..AttemptFilter::default()
            },
        )
        .expect("iter external patch attempts")
        .collect()
    }

    fn git_repo() -> tempfile::TempDir {
        let temp = tempfile::tempdir().expect("temp git repo");
        let output = Command::new("git")
            .arg("-C")
            .arg(temp.path())
            .arg("init")
            .output()
            .expect("run git init");
        assert!(
            output.status.success(),
            "git init failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        temp
    }

    #[test]
    fn accepted_external_patch_records_patch_and_context_artifacts() {
        let temp = tempfile::tempdir().expect("tempdir");
        let external_context = AttemptContext {
            external_run_id: Some("run-123".to_owned()),
            external_task_id: Some("task-123".to_owned()),
            prompt_digest: Some(hash("prompt")),
            patch_artifact: Some(default_patch_artifact(temp.path())),
        };
        let (trust_audit_hash, mut metadata, authority_attempts) =
            accepted_authority_evidence_for_context(temp.path(), hash("goal"), external_context);
        metadata
            .context
            .insert("target".to_owned(), "Nat.add_assoc".to_owned());
        metadata
            .gate_hashes
            .insert("statement_shape".to_owned(), hash("statement-gate"));

        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            prompt: Some(ExternalPatchArtifact::Bytes {
                bytes: b"prove Nat.add_assoc",
                kind: Some("external_patch/prompt"),
                logical_name: Some("prompt.txt"),
            }),
            model_response: Some(ExternalPatchArtifact::Bytes {
                bytes: br#"{"patch":"..."}"#,
                kind: Some("external_patch/model_response"),
                logical_name: Some("response.json"),
            }),
            producer: Some(producer()),
            context: AttemptContext {
                external_run_id: Some("run-123".to_owned()),
                external_task_id: Some("task-123".to_owned()),
                prompt_digest: Some(hash("prompt")),
                patch_artifact: None,
            },
            wall_time_ms: 42,
            trust_level: Some(TrustLevel::KernelVerified),
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit_hash,
                test_env(),
            )
        };

        let attempt =
            record_external_patch_attempt(temp.path(), input).expect("record external patch");
        assert_eq!(
            attempt.authority_gate.as_deref(),
            Some(EXTERNAL_PATCH_AUTHORITY_GATE)
        );
        assert!(matches!(attempt.status, AttemptStatus::Accepted));
        assert_eq!(attempt.wall_time_ms, 42);
        assert_eq!(attempt.trust_level, Some(TrustLevel::KernelVerified));
        assert_eq!(
            attempt
                .producer
                .as_ref()
                .map(|producer| producer.name.as_str()),
            Some("manual-patch")
        );
        assert_eq!(
            attempt
                .context
                .as_ref()
                .and_then(|context| context.external_task_id.as_deref()),
            Some("task-123")
        );

        let patch = attempt
            .context
            .as_ref()
            .and_then(|context| context.patch_artifact.as_ref())
            .expect("patch artifact");
        assert_eq!(patch.kind.as_deref(), Some(EXTERNAL_PATCH_ARTIFACT_KIND));
        assert_eq!(
            read_artifact(temp.path(), patch).expect("read patch"),
            b"diff --git a/Foo.lean b/Foo.lean\n"
        );

        let context = attempt.model_response.as_ref().expect("context artifact");
        assert_eq!(
            context.kind.as_deref(),
            Some(EXTERNAL_PATCH_CONTEXT_ARTIFACT_KIND)
        );
        let context_json: serde_json::Value =
            serde_json::from_slice(&read_artifact(temp.path(), context).expect("read context"))
                .expect("context json");
        assert_eq!(context_json["schema_version"], 1);
        assert_eq!(
            context_json["metadata"]["context"]["target"],
            "Nat.add_assoc"
        );
        assert!(context_json["prompt"]["blake3"].is_string());
        assert!(context_json["model_response"]["blake3"].is_string());
        assert_eq!(
            context_json["authority_gate_attempts"][TRUST_AUDIT_GATE]["attempt_id"],
            authority_attempts[TRUST_AUDIT_GATE].attempt_id.to_string()
        );
        assert_eq!(
            context_json["authority_gate_attempts"][STATEMENT_PRESERVATION_GATE]["status"],
            "accepted"
        );
        assert_eq!(
            context_json["authority_gate_attempts"][FALSE_CONTROLS_GATE]["report_artifact_hash"],
            authority_attempts[FALSE_CONTROLS_GATE].trust_audit_hash
        );

        assert_eq!(external_patch_attempts(temp.path()), vec![attempt]);
    }

    #[test]
    fn accepted_external_patch_rejects_unanchored_statement_preservation_evidence() {
        let temp = tempfile::tempdir().expect("tempdir");
        let trust_audit = accepted_gate_attempt(
            temp.path(),
            TRUST_AUDIT_GATE,
            b"{\"gate\":\"trust_audit\",\"accepted\":true}",
            "external_patch/test_trust_audit",
            "trust-audit.json",
        );
        let statement_report = put_artifact(
            temp.path(),
            b"{\"gate\":\"statement_preservation\",\"accepted\":true}",
            Some("external_patch/test_statement_preservation"),
            Some("statement-preservation.json"),
        )
        .expect("put statement-preservation artifact");
        let mut statement_input = AuthorityGateAttempt::new(
            STATEMENT_PRESERVATION_GATE,
            hash("unrelated-statement-goal"),
            AttemptStatus::Accepted,
            statement_report.blake3.clone(),
            test_env(),
        );
        statement_input.solver_artifact = Some(statement_report);
        statement_input.trust_level = Some(TrustLevel::KernelVerified);
        statement_input.producer = Some(producer());
        let statement_preservation = record_authority_gate_attempt(temp.path(), statement_input)
            .expect("record unanchored statement-preservation attempt");
        let false_controls = accepted_gate_attempt(
            temp.path(),
            FALSE_CONTROLS_GATE,
            b"{\"gate\":\"false_controls\",\"accepted\":true}",
            "external_patch/test_false_controls",
            "false-controls.json",
        );
        let mut metadata = ExternalPatchMetadata::default();
        metadata.audit_hashes.insert(
            TRUST_AUDIT_GATE.to_owned(),
            trust_audit.trust_audit_hash.clone(),
        );
        metadata.gate_hashes.insert(
            STATEMENT_PRESERVATION_GATE.to_owned(),
            statement_preservation.trust_audit_hash,
        );
        metadata.gate_hashes.insert(
            FALSE_CONTROLS_GATE.to_owned(),
            false_controls.trust_audit_hash,
        );

        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                prompt_digest: Some(hash("prompt")),
                ..AttemptContext::default()
            },
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit.trust_audit_hash,
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt must reject unanchored statement preservation evidence");
        assert!(err
            .to_string()
            .contains("same goal/task/artifact/prompt context"));
        assert!(external_patch_attempts(temp.path()).is_empty());
    }

    #[test]
    fn accepted_external_patch_rejects_unanchored_trust_audit_evidence() {
        let temp = tempfile::tempdir().expect("tempdir");
        let trust_report = put_artifact(
            temp.path(),
            b"{\"gate\":\"trust_audit\",\"accepted\":true}",
            Some("external_patch/test_trust_audit"),
            Some("trust-audit.json"),
        )
        .expect("put trust audit artifact");
        let mut trust_input = AuthorityGateAttempt::new(
            TRUST_AUDIT_GATE,
            hash("trust-audit-goal"),
            AttemptStatus::Accepted,
            trust_report.blake3.clone(),
            test_env(),
        );
        trust_input.solver_artifact = Some(trust_report);
        trust_input.trust_level = Some(TrustLevel::KernelVerified);
        trust_input.producer = Some(producer());
        let trust_audit = record_authority_gate_attempt(temp.path(), trust_input)
            .expect("record unanchored trust-audit attempt");
        let statement_preservation = accepted_gate_attempt_with_goal(
            temp.path(),
            STATEMENT_PRESERVATION_GATE,
            hash("goal"),
            b"{\"gate\":\"statement_preservation\",\"accepted\":true}",
            "external_patch/test_statement_preservation",
            "statement-preservation.json",
        );
        let false_controls = accepted_gate_attempt(
            temp.path(),
            FALSE_CONTROLS_GATE,
            b"{\"gate\":\"false_controls\",\"accepted\":true}",
            "external_patch/test_false_controls",
            "false-controls.json",
        );
        let mut metadata = ExternalPatchMetadata::default();
        metadata.audit_hashes.insert(
            TRUST_AUDIT_GATE.to_owned(),
            trust_audit.trust_audit_hash.clone(),
        );
        metadata.gate_hashes.insert(
            STATEMENT_PRESERVATION_GATE.to_owned(),
            statement_preservation.trust_audit_hash,
        );
        metadata.gate_hashes.insert(
            FALSE_CONTROLS_GATE.to_owned(),
            false_controls.trust_audit_hash,
        );

        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                prompt_digest: Some(hash("prompt")),
                ..AttemptContext::default()
            },
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit.trust_audit_hash,
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt must reject unanchored trust audit evidence");
        let message = err.to_string();
        assert!(message.contains("requires trust_audit evidence"));
        assert!(message.contains("same goal/task/artifact/prompt context"));
        assert!(external_patch_attempts(temp.path()).is_empty());
    }

    #[test]
    fn accepted_external_patch_rejects_statement_preservation_task_mismatch() {
        let temp = tempfile::tempdir().expect("tempdir");
        let patch = default_patch_artifact(temp.path());
        let patch_context = AttemptContext {
            external_task_id: Some("task-patch".to_owned()),
            prompt_digest: Some(hash("prompt")),
            patch_artifact: Some(patch.clone()),
            ..AttemptContext::default()
        };
        let trust_audit = accepted_gate_attempt_with_goal_and_context(
            temp.path(),
            TRUST_AUDIT_GATE,
            hash("goal"),
            b"{\"gate\":\"trust_audit\",\"accepted\":true}",
            "external_patch/test_trust_audit",
            "trust-audit.json",
            patch_context.clone(),
        );
        let artifact = put_artifact(
            temp.path(),
            b"{\"gate\":\"statement_preservation\",\"accepted\":true}",
            Some("external_patch/test_statement_preservation"),
            Some("statement-preservation.json"),
        )
        .expect("put statement-preservation artifact");
        let mut statement_attempt = AuthorityGateAttempt::new(
            STATEMENT_PRESERVATION_GATE,
            hash("goal"),
            AttemptStatus::Accepted,
            artifact.blake3.clone(),
            test_env(),
        );
        statement_attempt.solver_artifact = Some(artifact);
        statement_attempt.trust_level = Some(TrustLevel::KernelVerified);
        statement_attempt.producer = Some(producer());
        statement_attempt.context = Some(AttemptContext {
            external_task_id: Some("task-other".to_owned()),
            prompt_digest: Some(hash("prompt")),
            patch_artifact: Some(patch),
            ..AttemptContext::default()
        });
        let statement_preservation = record_authority_gate_attempt(temp.path(), statement_attempt)
            .expect("record statement-preservation attempt");
        let false_controls = accepted_gate_attempt_with_goal_and_context(
            temp.path(),
            FALSE_CONTROLS_GATE,
            hash("goal"),
            b"{\"gate\":\"false_controls\",\"accepted\":true}",
            "external_patch/test_false_controls",
            "false-controls.json",
            patch_context,
        );
        let mut metadata = ExternalPatchMetadata::default();
        metadata.audit_hashes.insert(
            TRUST_AUDIT_GATE.to_owned(),
            trust_audit.trust_audit_hash.clone(),
        );
        metadata.gate_hashes.insert(
            STATEMENT_PRESERVATION_GATE.to_owned(),
            statement_preservation.trust_audit_hash,
        );
        metadata.gate_hashes.insert(
            FALSE_CONTROLS_GATE.to_owned(),
            false_controls.trust_audit_hash,
        );

        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                external_task_id: Some("task-patch".to_owned()),
                prompt_digest: Some(hash("prompt")),
                ..AttemptContext::default()
            },
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit.trust_audit_hash,
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt must reject statement preservation task mismatch");
        let message = err.to_string();
        assert!(message.contains("same goal/task/artifact/prompt context"));
        assert!(message.contains("external_task_id"));
        assert!(external_patch_attempts(temp.path()).is_empty());
    }

    #[test]
    fn accepted_external_patch_fails_closed_without_patch_artifact() {
        let temp = tempfile::tempdir().expect("tempdir");
        let input = ExternalPatchAttemptInput::new(
            hash("goal"),
            AttemptStatus::Accepted,
            hash("audit"),
            test_env(),
        );

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt without patch must fail");
        assert!(err
            .to_string()
            .contains("accepted external patch attempt requires a patch artifact"));

        let attempts: Vec<_> = iter_from(temp.path(), AttemptFilter::default())
            .expect("iter attempts")
            .collect();
        assert!(attempts.is_empty());
    }

    #[test]
    fn accepted_external_patch_fails_closed_on_dirty_git_root() {
        let repo = git_repo();
        std::fs::write(repo.path().join("dirty.txt"), "uncommitted\n").expect("write dirty file");
        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                hash("audit"),
                test_env(),
            )
        };

        let err = record_external_patch_attempt(repo.path(), input)
            .expect_err("dirty accepted attempt must fail");
        let message = err.to_string();
        assert!(message.contains("dirty git worktree"));
        assert!(message.contains("dirty_entries=1"));

        let attempts: Vec<_> = iter_from(repo.path(), AttemptFilter::default())
            .expect("iter attempts")
            .collect();
        assert!(attempts.is_empty());
    }

    #[test]
    fn accepted_external_patch_dirty_root_override_records_reason() {
        let repo = git_repo();
        std::fs::write(repo.path().join("dirty.txt"), "reviewed\n").expect("write dirty file");
        let (trust_audit_hash, metadata, _) = accepted_authority_evidence(repo.path());
        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                prompt_digest: Some(hash("prompt")),
                ..AttemptContext::default()
            },
            metadata,
            allow_dirty_root_reason: Some("reviewed local fixture state".to_owned()),
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit_hash,
                test_env(),
            )
        };

        let attempt = record_external_patch_attempt(repo.path(), input)
            .expect("record dirty accepted attempt with override");
        let context = attempt.model_response.as_ref().expect("context artifact");
        let context_json: serde_json::Value =
            serde_json::from_slice(&read_artifact(repo.path(), context).expect("read context"))
                .expect("context json");

        assert_eq!(
            context_json["metadata"]["context"][DIRTY_ROOT_POLICY_KEY],
            "allowed"
        );
        assert_eq!(
            context_json["metadata"]["context"][DIRTY_ROOT_REASON_KEY],
            "reviewed local fixture state"
        );
        let dirty_entry_count = context_json["metadata"]["context"][DIRTY_ROOT_ENTRY_COUNT_KEY]
            .as_str()
            .expect("dirty entry count string")
            .parse::<usize>()
            .expect("dirty entry count parses");
        assert!(dirty_entry_count >= 1);
        assert!(context_json["metadata"]["context"][DIRTY_ROOT_ENTRIES_SHA256_KEY].is_string());
    }

    #[test]
    fn existing_patch_artifact_reference_is_validated_before_append() {
        let temp = tempfile::tempdir().expect("tempdir");
        let patch = put_artifact(
            temp.path(),
            b"patch bytes",
            Some(EXTERNAL_PATCH_ARTIFACT_KIND),
            Some("external.patch"),
        )
        .expect("put patch");
        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::Existing(patch.clone())),
            failure_mode: Some("authority_gate_rejected".to_owned()),
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Rejected {
                    reason: "statement preservation failed".to_owned(),
                },
                hash("audit"),
                test_env(),
            )
        };

        let attempt = record_external_patch_attempt(temp.path(), input)
            .expect("record rejected external patch");
        assert_eq!(
            attempt
                .context
                .as_ref()
                .and_then(|context| context.patch_artifact.as_ref()),
            Some(&patch)
        );
        assert_eq!(
            attempt.failure_mode.as_deref(),
            Some("authority_gate_rejected")
        );
    }

    #[test]
    fn accepted_existing_context_patch_artifact_is_validated() {
        let temp = tempfile::tempdir().expect("tempdir");
        let patch = put_artifact(
            temp.path(),
            b"patch bytes",
            Some(EXTERNAL_PATCH_ARTIFACT_KIND),
            Some("external.patch"),
        )
        .expect("put patch");
        let context = AttemptContext {
            external_run_id: Some("run-existing".to_owned()),
            external_task_id: Some("task-existing".to_owned()),
            prompt_digest: Some(hash("prompt")),
            patch_artifact: Some(patch.clone()),
        };
        let (trust_audit_hash, metadata, _) =
            accepted_authority_evidence_for_context(temp.path(), hash("goal"), context.clone());
        let input = ExternalPatchAttemptInput {
            context,
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit_hash,
                test_env(),
            )
        };

        let attempt = record_external_patch_attempt(temp.path(), input)
            .expect("record accepted external patch from context artifact");
        assert_eq!(
            attempt
                .context
                .as_ref()
                .and_then(|context| context.patch_artifact.as_ref()),
            Some(&patch)
        );
    }

    #[test]
    fn accepted_external_patch_fails_closed_without_prompt_or_response_artifact() {
        let temp = tempfile::tempdir().expect("tempdir");
        let (trust_audit_hash, metadata, _) = accepted_authority_evidence(temp.path());
        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit_hash,
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt without prompt/response evidence must fail");
        assert!(err
            .to_string()
            .contains("requires a prompt digest or model response artifact"));

        assert!(external_patch_attempts(temp.path()).is_empty());
    }

    #[test]
    fn accepted_external_patch_fails_closed_without_replayable_gate_artifacts() {
        let temp = tempfile::tempdir().expect("tempdir");
        let trust_audit = accepted_gate_attempt(
            temp.path(),
            TRUST_AUDIT_GATE,
            b"{\"gate\":\"trust_audit\",\"accepted\":true}",
            "external_patch/test_trust_audit",
            "trust-audit.json",
        );
        let mut metadata = ExternalPatchMetadata::default();
        metadata.audit_hashes.insert(
            TRUST_AUDIT_GATE.to_owned(),
            trust_audit.trust_audit_hash.clone(),
        );
        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                prompt_digest: Some(hash("prompt")),
                ..AttemptContext::default()
            },
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit.trust_audit_hash,
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt without downstream gate evidence must fail");
        assert!(err
            .to_string()
            .contains("requires replayable statement_preservation evidence"));

        assert!(external_patch_attempts(temp.path()).is_empty());
    }

    #[test]
    fn accepted_external_patch_fails_closed_on_artifact_hashes_without_gate_attempts() {
        let temp = tempfile::tempdir().expect("tempdir");
        let trust_audit = put_artifact(
            temp.path(),
            b"{\"gate\":\"trust_audit\",\"accepted\":true}",
            Some("external_patch/spoofed_trust_audit"),
            Some("trust-audit.json"),
        )
        .expect("put spoofed trust audit artifact");
        let statement_preservation = put_artifact(
            temp.path(),
            b"{\"gate\":\"statement_preservation\",\"accepted\":true}",
            Some("external_patch/spoofed_statement_preservation"),
            Some("statement-preservation.json"),
        )
        .expect("put spoofed statement preservation artifact");
        let false_controls = put_artifact(
            temp.path(),
            b"{\"gate\":\"false_controls\",\"accepted\":true}",
            Some("external_patch/spoofed_false_controls"),
            Some("false-controls.json"),
        )
        .expect("put spoofed false controls artifact");
        let mut metadata = ExternalPatchMetadata::default();
        metadata
            .audit_hashes
            .insert(TRUST_AUDIT_GATE.to_owned(), trust_audit.blake3.clone());
        metadata.gate_hashes.insert(
            STATEMENT_PRESERVATION_GATE.to_owned(),
            statement_preservation.blake3,
        );
        metadata
            .gate_hashes
            .insert(FALSE_CONTROLS_GATE.to_owned(), false_controls.blake3);

        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                prompt_digest: Some(hash("prompt")),
                ..AttemptContext::default()
            },
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit.blake3,
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt must require typed trust audit evidence");
        assert!(err
            .to_string()
            .contains("requires accepted trust_audit authority-gate attempt"));
        assert!(external_patch_attempts(temp.path()).is_empty());
    }

    #[test]
    fn accepted_external_patch_requires_accepted_gate_identity() {
        let temp = tempfile::tempdir().expect("tempdir");
        let trust_audit = put_artifact(
            temp.path(),
            b"{\"gate\":\"trust_audit\",\"accepted\":true}",
            Some("external_patch/test_trust_audit"),
            Some("trust-audit.json"),
        )
        .expect("put trust audit artifact");
        let mut wrong_gate = AuthorityGateAttempt::new(
            "not_trust_audit",
            hash("wrong-gate-goal"),
            AttemptStatus::Accepted,
            trust_audit.blake3.clone(),
            test_env(),
        );
        wrong_gate.solver_artifact = Some(trust_audit.clone());
        append_raw_authority_gate_attempt(temp.path(), wrong_gate);

        let mut rejected_trust_audit = AuthorityGateAttempt::new(
            TRUST_AUDIT_GATE,
            hash("rejected-trust-audit-goal"),
            AttemptStatus::Rejected {
                reason: "audit rejected".to_owned(),
            },
            trust_audit.blake3.clone(),
            test_env(),
        );
        rejected_trust_audit.solver_artifact = Some(trust_audit.clone());
        record_authority_gate_attempt(temp.path(), rejected_trust_audit)
            .expect("record rejected trust audit attempt");

        let statement_preservation = accepted_gate_attempt(
            temp.path(),
            STATEMENT_PRESERVATION_GATE,
            b"{\"gate\":\"statement_preservation\",\"accepted\":true}",
            "external_patch/test_statement_preservation",
            "statement-preservation.json",
        );
        let false_controls = accepted_gate_attempt(
            temp.path(),
            FALSE_CONTROLS_GATE,
            b"{\"gate\":\"false_controls\",\"accepted\":true}",
            "external_patch/test_false_controls",
            "false-controls.json",
        );
        let mut metadata = ExternalPatchMetadata::default();
        metadata
            .audit_hashes
            .insert(TRUST_AUDIT_GATE.to_owned(), trust_audit.blake3.clone());
        metadata.gate_hashes.insert(
            STATEMENT_PRESERVATION_GATE.to_owned(),
            statement_preservation.trust_audit_hash,
        );
        metadata.gate_hashes.insert(
            FALSE_CONTROLS_GATE.to_owned(),
            false_controls.trust_audit_hash,
        );

        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                prompt_digest: Some(hash("prompt")),
                ..AttemptContext::default()
            },
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit.blake3,
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt must require accepted trust_audit gate identity");
        assert!(err
            .to_string()
            .contains("requires accepted trust_audit authority-gate attempt"));
        assert!(external_patch_attempts(temp.path()).is_empty());
    }

    #[test]
    fn accepted_external_patch_rejects_gate_report_artifact_hash_mismatch() {
        let temp = tempfile::tempdir().expect("tempdir");
        let trust_audit = accepted_gate_attempt(
            temp.path(),
            TRUST_AUDIT_GATE,
            b"{\"gate\":\"trust_audit\",\"accepted\":true}",
            "external_patch/test_trust_audit",
            "trust-audit.json",
        );
        let statement_report = put_artifact(
            temp.path(),
            b"{\"gate\":\"statement_preservation\",\"accepted\":true}",
            Some("external_patch/test_statement_preservation"),
            Some("statement-preservation.json"),
        )
        .expect("put statement report artifact");
        let wrong_statement_report = put_artifact(
            temp.path(),
            b"{\"gate\":\"statement_preservation\",\"accepted\":false}",
            Some("external_patch/test_statement_preservation"),
            Some("wrong-statement-preservation.json"),
        )
        .expect("put wrong statement report artifact");
        let mut statement_attempt = AuthorityGateAttempt::new(
            STATEMENT_PRESERVATION_GATE,
            hash("statement-preservation-goal"),
            AttemptStatus::Accepted,
            statement_report.blake3.clone(),
            test_env(),
        );
        statement_attempt.solver_artifact = Some(wrong_statement_report);
        statement_attempt.trust_level = Some(TrustLevel::KernelVerified);
        statement_attempt.producer = Some(producer());
        record_authority_gate_attempt(temp.path(), statement_attempt)
            .expect("record mismatched statement gate attempt");
        let false_controls = accepted_gate_attempt(
            temp.path(),
            FALSE_CONTROLS_GATE,
            b"{\"gate\":\"false_controls\",\"accepted\":true}",
            "external_patch/test_false_controls",
            "false-controls.json",
        );

        let mut metadata = ExternalPatchMetadata::default();
        metadata.audit_hashes.insert(
            TRUST_AUDIT_GATE.to_owned(),
            trust_audit.trust_audit_hash.clone(),
        );
        metadata.gate_hashes.insert(
            STATEMENT_PRESERVATION_GATE.to_owned(),
            statement_report.blake3,
        );
        metadata.gate_hashes.insert(
            FALSE_CONTROLS_GATE.to_owned(),
            false_controls.trust_audit_hash,
        );

        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                prompt_digest: Some(hash("prompt")),
                ..AttemptContext::default()
            },
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit.trust_audit_hash,
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt must reject mismatched gate report artifact");
        let message = err.to_string();
        assert!(message.contains(STATEMENT_PRESERVATION_GATE));
        assert!(message.contains("report artifact hash"));
        assert!(external_patch_attempts(temp.path()).is_empty());
    }

    #[test]
    fn accepted_external_patch_rejects_downstream_gate_missing_command_binding() {
        let temp = tempfile::tempdir().expect("tempdir");
        let context = AttemptContext {
            prompt_digest: Some(hash("prompt")),
            patch_artifact: Some(default_patch_artifact(temp.path())),
            ..AttemptContext::default()
        };
        let trust_audit = accepted_gate_attempt_with_goal_and_context(
            temp.path(),
            TRUST_AUDIT_GATE,
            hash("goal"),
            b"{\"gate\":\"trust_audit\",\"accepted\":true}",
            "external_patch/test_trust_audit",
            "trust-audit.json",
            context.clone(),
        );
        let statement_report = put_artifact(
            temp.path(),
            b"{\"gate\":\"statement_preservation\",\"accepted\":true}",
            Some("external_patch/test_statement_preservation"),
            Some("statement-preservation.json"),
        )
        .expect("put statement-preservation artifact");
        let mut statement_attempt = AuthorityGateAttempt::new(
            STATEMENT_PRESERVATION_GATE,
            hash("goal"),
            AttemptStatus::Accepted,
            statement_report.blake3.clone(),
            test_env(),
        );
        statement_attempt.solver_artifact = Some(statement_report);
        statement_attempt.trust_level = Some(TrustLevel::KernelVerified);
        statement_attempt.context = Some(context.clone());
        let statement_preservation =
            append_raw_authority_gate_attempt(temp.path(), statement_attempt);
        let false_controls = accepted_gate_attempt_with_goal_and_context(
            temp.path(),
            FALSE_CONTROLS_GATE,
            hash("goal"),
            b"{\"gate\":\"false_controls\",\"accepted\":true}",
            "external_patch/test_false_controls",
            "false-controls.json",
            context,
        );
        let mut metadata = ExternalPatchMetadata::default();
        metadata.audit_hashes.insert(
            TRUST_AUDIT_GATE.to_owned(),
            trust_audit.trust_audit_hash.clone(),
        );
        metadata.gate_hashes.insert(
            STATEMENT_PRESERVATION_GATE.to_owned(),
            statement_preservation.trust_audit_hash,
        );
        metadata.gate_hashes.insert(
            FALSE_CONTROLS_GATE.to_owned(),
            false_controls.trust_audit_hash,
        );

        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                prompt_digest: Some(hash("prompt")),
                ..AttemptContext::default()
            },
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit.trust_audit_hash,
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt must reject downstream gate without command binding");
        let message = err.to_string();
        assert!(message.contains(STATEMENT_PRESERVATION_GATE));
        assert!(message.contains("missing producer command digest or command evidence artifact"));
        assert!(external_patch_attempts(temp.path()).is_empty());
    }

    #[test]
    fn accepted_external_patch_rejects_downstream_gate_missing_solver_artifact() {
        let temp = tempfile::tempdir().expect("tempdir");
        let context = AttemptContext {
            prompt_digest: Some(hash("prompt")),
            patch_artifact: Some(default_patch_artifact(temp.path())),
            ..AttemptContext::default()
        };
        let trust_audit = accepted_gate_attempt_with_goal_and_context(
            temp.path(),
            TRUST_AUDIT_GATE,
            hash("goal"),
            b"{\"gate\":\"trust_audit\",\"accepted\":true}",
            "external_patch/test_trust_audit",
            "trust-audit.json",
            context.clone(),
        );
        let statement_preservation = accepted_gate_attempt_with_goal_and_context(
            temp.path(),
            STATEMENT_PRESERVATION_GATE,
            hash("goal"),
            b"{\"gate\":\"statement_preservation\",\"accepted\":true}",
            "external_patch/test_statement_preservation",
            "statement-preservation.json",
            context.clone(),
        );
        let false_report = put_artifact(
            temp.path(),
            b"{\"gate\":\"false_controls\",\"accepted\":true}",
            Some("external_patch/test_false_controls"),
            Some("false-controls.json"),
        )
        .expect("put false-controls artifact");
        let mut false_attempt = AuthorityGateAttempt::new(
            FALSE_CONTROLS_GATE,
            hash("goal"),
            AttemptStatus::Accepted,
            false_report.blake3.clone(),
            test_env(),
        );
        false_attempt.trust_level = Some(TrustLevel::KernelVerified);
        false_attempt.producer = Some(producer());
        false_attempt.context = Some(context);
        let false_controls = append_raw_authority_gate_attempt(temp.path(), false_attempt);
        let mut metadata = ExternalPatchMetadata::default();
        metadata.audit_hashes.insert(
            TRUST_AUDIT_GATE.to_owned(),
            trust_audit.trust_audit_hash.clone(),
        );
        metadata.gate_hashes.insert(
            STATEMENT_PRESERVATION_GATE.to_owned(),
            statement_preservation.trust_audit_hash,
        );
        metadata.gate_hashes.insert(
            FALSE_CONTROLS_GATE.to_owned(),
            false_controls.trust_audit_hash,
        );

        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                prompt_digest: Some(hash("prompt")),
                ..AttemptContext::default()
            },
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit.trust_audit_hash,
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt must reject downstream gate without solver artifact");
        let message = err.to_string();
        assert!(message.contains(FALSE_CONTROLS_GATE));
        assert!(message.contains("missing solver/proof artifact reference"));
        assert!(external_patch_attempts(temp.path()).is_empty());
    }

    #[test]
    fn accepted_external_patch_rejects_downstream_gate_missing_policy_metadata() {
        let temp = tempfile::tempdir().expect("tempdir");
        let context = AttemptContext {
            prompt_digest: Some(hash("prompt")),
            patch_artifact: Some(default_patch_artifact(temp.path())),
            ..AttemptContext::default()
        };
        let trust_audit = accepted_gate_attempt_with_goal_and_context(
            temp.path(),
            TRUST_AUDIT_GATE,
            hash("goal"),
            b"{\"gate\":\"trust_audit\",\"accepted\":true}",
            "external_patch/test_trust_audit",
            "trust-audit.json",
            context.clone(),
        );
        let statement_preservation = accepted_gate_attempt_with_goal_and_context(
            temp.path(),
            STATEMENT_PRESERVATION_GATE,
            hash("goal"),
            b"{\"gate\":\"statement_preservation\",\"accepted\":true}",
            "external_patch/test_statement_preservation",
            "statement-preservation.json",
            context.clone(),
        );
        let false_report = put_artifact(
            temp.path(),
            b"{\"gate\":\"false_controls\",\"accepted\":true}",
            Some("external_patch/test_false_controls"),
            Some("false-controls.json"),
        )
        .expect("put false-controls artifact");
        let mut false_attempt = AuthorityGateAttempt::new(
            FALSE_CONTROLS_GATE,
            hash("goal"),
            AttemptStatus::Accepted,
            false_report.blake3.clone(),
            test_env(),
        );
        false_attempt.solver_artifact = Some(false_report);
        false_attempt.producer = Some(producer());
        false_attempt.context = Some(context);
        let false_controls = append_raw_authority_gate_attempt(temp.path(), false_attempt);
        let mut metadata = ExternalPatchMetadata::default();
        metadata.audit_hashes.insert(
            TRUST_AUDIT_GATE.to_owned(),
            trust_audit.trust_audit_hash.clone(),
        );
        metadata.gate_hashes.insert(
            STATEMENT_PRESERVATION_GATE.to_owned(),
            statement_preservation.trust_audit_hash,
        );
        metadata.gate_hashes.insert(
            FALSE_CONTROLS_GATE.to_owned(),
            false_controls.trust_audit_hash,
        );

        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                prompt_digest: Some(hash("prompt")),
                ..AttemptContext::default()
            },
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit.trust_audit_hash,
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt must reject downstream gate without policy metadata");
        let message = err.to_string();
        assert!(message.contains(FALSE_CONTROLS_GATE));
        assert!(message.contains("missing trust level policy metadata"));
        assert!(external_patch_attempts(temp.path()).is_empty());
    }

    #[test]
    fn accepted_external_patch_fails_closed_on_malformed_prompt_digest() {
        let temp = tempfile::tempdir().expect("tempdir");
        let (trust_audit_hash, metadata, _) = accepted_authority_evidence(temp.path());
        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                prompt_digest: Some("not-a-blake3-digest".to_owned()),
                ..AttemptContext::default()
            },
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                trust_audit_hash,
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt with malformed prompt digest must fail");
        assert!(err
            .to_string()
            .contains("requires prompt digest to be a BLAKE3 hash"));

        assert!(external_patch_attempts(temp.path()).is_empty());
    }

    #[test]
    fn accepted_external_patch_fails_closed_on_missing_trust_audit_artifact() {
        let temp = tempfile::tempdir().expect("tempdir");
        let (_, mut metadata, _) = accepted_authority_evidence(temp.path());
        metadata.audit_hashes.remove(TRUST_AUDIT_GATE);
        let input = ExternalPatchAttemptInput {
            patch: Some(ExternalPatchArtifact::patch_bytes(
                b"diff --git a/Foo.lean b/Foo.lean\n",
                Some("foo.patch"),
            )),
            context: AttemptContext {
                prompt_digest: Some(hash("prompt")),
                ..AttemptContext::default()
            },
            metadata,
            ..ExternalPatchAttemptInput::new(
                hash("goal"),
                AttemptStatus::Accepted,
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_owned(),
                test_env(),
            )
        };

        let err = record_external_patch_attempt(temp.path(), input)
            .expect_err("accepted attempt without trust audit artifact must fail");
        assert!(err
            .to_string()
            .contains("requires accepted trust_audit authority-gate attempt"));

        assert!(external_patch_attempts(temp.path()).is_empty());
    }
}
