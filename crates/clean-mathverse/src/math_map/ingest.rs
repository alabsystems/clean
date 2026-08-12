// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed ingest pipeline for untrusted MathMap patch bundles.
//!
//! # Fail-closed contract
//!
//! Nothing in this module ever returns [`IngestStatus::Accepted`] by default.
//! A [`MathMapIngestReport`] starts life `Blocked`, every pipeline step starts
//! [`StepStatus::NotRun`], and a step only becomes `Passed` when its evidence
//! was supplied AND satisfied the gate. In particular:
//!
//! * an unverifiable, unregistered, or non-cryptographic signature REJECTS at
//!   [`PipelineStep::BundleIntegrity`] (when policy requires it);
//! * a mismatched repo revision or Lake toolchain REJECTS at
//!   [`PipelineStep::EnvironmentPin`];
//! * a failed `git apply --check`, `git apply`, or Lake re-check REJECTS;
//! * a target statement hash that moved, or any blocking statement drift,
//!   REJECTS at [`PipelineStep::DriftStatementPreservation`];
//! * missing pre/post trust-audit evidence, or zero post-patch constants,
//!   REJECTS at [`PipelineStep::TrustAudit`] — absent evidence is never
//!   treated as clean evidence;
//! * a missing false-control rerun report BLOCKS; it never accepts;
//! * a bundle whose target/patch envelope was already ingested REJECTS at
//!   [`PipelineStep::WriteProofAttempt`] as a replay.

use std::collections::BTreeMap;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use serde::{Deserialize, Serialize};

use crate::attempt_log::{self, ArtifactRef, AttemptStatus, ProofAttempt};
use crate::drift::{DriftReport, TheoremStatementComparisonInput};
use crate::env_fingerprint::EnvFingerprint;
use crate::error::MathverseResult;
use crate::false_control_suite::FalseControlReport;
use crate::trust::audit_report::AuditReport;
use crate::types::TrustLevel;

use super::bundle::{sha256_hex, BundleFileSystem, BundleLoadError};
use super::keys::{
    Ed25519SignatureVerifier, ManifestSignatureVerifier, SignatureVerification, TrustedKeyRegistry,
    TrustedKeyRegistryError,
};
use super::manifest::{is_safe_relative_path, BundleManifest, ManifestValidationError};
use super::policy::{MathMapPolicy, PolicyViolation};
use super::trust_audit_gate::evaluate_trust_audit_gate;
use super::{
    ArtifactKind, MATH_MAP_ARTIFACT_KIND, MATH_MAP_BUNDLE_ARTIFACT_FORMAT,
    MATH_MAP_INGEST_SCHEMA_VERSION, MATH_MAP_MODEL_RESPONSE_ARTIFACT_KIND,
};

/// Operator-controlled configuration for one ingest run.
#[derive(Debug, Clone)]
pub struct MathMapIngestConfig {
    /// Ingest policy.
    pub policy: MathMapPolicy,
    /// Trusted signing keys.
    pub trusted_keys: TrustedKeyRegistry,
}

/// Machine-readable outcome of an ingest run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MathMapIngestReport {
    /// Ingest contract version.
    pub schema_version: String,
    /// Artifact kind this pipeline ingests.
    pub artifact_kind: String,
    /// Path the bundle was loaded from.
    pub bundle_path: String,
    /// Deterministic bundle digest, once integrity ran.
    pub bundle_sha256: Option<String>,
    /// Producer job id, once the manifest parsed.
    pub job_id: Option<String>,
    /// Producing service, once the manifest parsed.
    pub service: Option<String>,
    /// Overall status. Starts `Blocked` and is only ever narrowed.
    pub status: IngestStatus,
    /// Per-step results, in pipeline order.
    pub steps: Vec<PipelineStepResult>,
    /// Authority-gate sub-report, when authority inputs were supplied.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub authority_gates: Option<MathMapAuthorityGateReport>,
    /// Signature verification record, when integrity ran.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signature: Option<SignatureVerification>,
    /// Attempt-log record, when the recording ingest path was used.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_attempt: Option<MathMapProofAttemptStub>,
}

/// Overall ingest status.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum IngestStatus {
    /// Every wired gate passed.
    Accepted,
    /// A gate rejected the bundle.
    Rejected {
        /// Step that rejected.
        step: PipelineStep,
        /// Human-readable reason.
        reason: String,
    },
    /// No gate rejected, but required evidence was absent. NOT an acceptance.
    Blocked {
        /// Human-readable reason.
        reason: String,
    },
}

/// Summary of the attempt-log row written for this ingest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MathMapProofAttemptStub {
    /// Attempt id.
    pub attempt_id: String,
    /// Producing service.
    pub service: String,
    /// Producer job id.
    pub job_id: String,
    /// Ingest status at write time.
    pub status: IngestStatus,
    /// Attempt-log status.
    pub attempt_status: AttemptStatus,
    /// Authority gate credited with the outcome.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub authority_gate: Option<String>,
    /// Stable failure-mode classification.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub failure_mode: Option<String>,
    /// Trust level observed by the trust-audit gate.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trust_level: Option<TrustLevel>,
    /// Deterministic bundle digest.
    pub bundle_sha256: String,
    /// Stored model-response artifact, when the bundle carried a prompt tree.
    pub model_response: Option<ArtifactRef>,
    /// Stored bundle artifact.
    pub solver_artifact: Option<ArtifactRef>,
    /// Deterministic audit-envelope digest.
    pub trust_audit_hash: Option<String>,
}

/// Caller-supplied evidence for one ingest run.
#[derive(Debug, Clone, Copy, Default)]
pub struct MathMapIngestInputs<'a> {
    /// Authority-gate evidence (statement preservation, trust audit, false controls).
    pub authority_gates: Option<MathMapAuthorityGateInputs<'a>>,
    /// Local patch/Lake primitives.
    pub local_checks: Option<MathMapLocalCheckInputs<'a>>,
}

impl<'a> MathMapIngestInputs<'a> {
    /// No caller-supplied evidence. Integrity runs; everything else blocks.
    #[must_use]
    pub const fn none() -> Self {
        Self {
            authority_gates: None,
            local_checks: None,
        }
    }

    /// Only authority-gate evidence.
    #[must_use]
    pub const fn with_authority_gates(authority_gates: MathMapAuthorityGateInputs<'a>) -> Self {
        Self {
            authority_gates: Some(authority_gates),
            local_checks: None,
        }
    }

    /// Only local patch/Lake primitives.
    #[must_use]
    pub const fn with_local_checks(local_checks: MathMapLocalCheckInputs<'a>) -> Self {
        Self {
            authority_gates: None,
            local_checks: Some(local_checks),
        }
    }

    /// Both authority-gate evidence and local patch/Lake primitives.
    #[must_use]
    pub const fn with_authority_gates_and_local_checks(
        authority_gates: MathMapAuthorityGateInputs<'a>,
        local_checks: MathMapLocalCheckInputs<'a>,
    ) -> Self {
        Self {
            authority_gates: Some(authority_gates),
            local_checks: Some(local_checks),
        }
    }
}

/// Pre- and post-patch audit reports for the trust-audit gate.
#[derive(Debug, Clone, Copy)]
pub struct MathMapTrustAuditGateInput<'a> {
    /// Pre-patch audit report.
    pub before: &'a AuditReport,
    /// Post-patch audit report.
    pub after: &'a AuditReport,
}

/// Evidence for the three authority gates.
#[derive(Debug, Clone, Copy)]
pub struct MathMapAuthorityGateInputs<'a> {
    /// Observed post-patch statement hash per target theorem.
    pub observed_target_statement_hashes: &'a BTreeMap<String, String>,
    /// Optional per-theorem before/after statement hashes, for diagnostics.
    pub statement_comparison_inputs: &'a [TheoremStatementComparisonInput],
    /// Declaration-surface drift reports.
    pub drift_reports: &'a [DriftReport],
    /// Pre/post trust audit reports. `None` REJECTS the trust-audit gate.
    pub trust_audit: Option<MathMapTrustAuditGateInput<'a>>,
    /// False-control rerun evidence. `None` BLOCKS.
    pub false_control_rerun: Option<MathMapFalseControlRerunInput<'a>>,
}

/// Where a false-control rerun report came from.
#[derive(Debug, Clone, Copy)]
pub enum MathMapFalseControlRerunInput<'a> {
    /// Report handed to this ingest by its caller.
    SuppliedReport(&'a FalseControlReport),
    /// Report generated locally alongside this ingest.
    LocalReport(&'a FalseControlReport),
}

/// Local patch/Lake primitives the caller wants this ingest to drive.
#[derive(Debug, Clone, Copy)]
pub struct MathMapLocalCheckInputs<'a> {
    /// Repository the patches apply to.
    pub clean_repo_path: &'a Path,
    /// Environment-pin runner.
    pub environment_pin: Option<MathMapEnvironmentPinInputs<'a>>,
    /// Mutating patch-apply runner.
    pub patch_apply: Option<MathMapPatchApplyInputs<'a>>,
    /// Non-mutating patch preflight runner. Ignored when `patch_apply` is set.
    pub patch_preflight: Option<MathMapPatchPreflightInputs<'a>>,
    /// Lake re-check runner.
    pub lake_recheck: Option<MathMapLakeRecheckInputs<'a>>,
    /// False-control rerun evidence produced locally.
    pub false_control_rerun: Option<MathMapFalseControlRerunInput<'a>>,
}

/// Environment-pin runner selection.
#[derive(Debug, Clone, Copy)]
pub struct MathMapEnvironmentPinInputs<'a> {
    /// Runner that observes the repo's revision and toolchain.
    pub runner: &'a dyn EnvironmentPinRunner,
}

/// Mutating patch-apply runner selection.
#[derive(Debug, Clone, Copy)]
pub struct MathMapPatchApplyInputs<'a> {
    /// Runner that applies the bundle patches.
    pub runner: &'a dyn PatchApplyRunner,
    /// Whether to commit after a successful apply.
    pub commit: bool,
}

/// Non-mutating patch preflight runner selection.
#[derive(Debug, Clone, Copy)]
pub struct MathMapPatchPreflightInputs<'a> {
    /// Runner that checks whether the bundle patches would apply.
    pub runner: &'a dyn PatchPreflightRunner,
}

/// Lake re-check runner selection.
#[derive(Debug, Clone, Copy)]
pub struct MathMapLakeRecheckInputs<'a> {
    /// Runner that executes the re-check command.
    pub runner: &'a dyn LakeRecheckRunner,
    /// Command to execute.
    pub command: &'a LakeRecheckCommand,
    /// Module label for diagnostics.
    pub module: Option<&'a str>,
}

/// The three authority gates, evaluated together.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MathMapAuthorityGateReport {
    /// Combined status.
    pub status: IngestStatus,
    /// Statement-preservation gate.
    pub statement_preservation: PipelineStepResult,
    /// Trust-audit gate.
    pub trust_audit: PipelineStepResult,
    /// False-control rerun gate.
    pub false_control_rerun: PipelineStepResult,
}

/// One stage of the ingest pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PipelineStep {
    /// Bundle load, manifest schema, policy, signature, patch hashes.
    BundleIntegrity,
    /// Repository revision and Lake toolchain pin.
    EnvironmentPin,
    /// Pre-patch baseline capture.
    PrePatchBaseline,
    /// Patch preflight or apply.
    PatchApply,
    /// Lake re-check of the patched tree.
    LakeRecheck,
    /// Statement-preservation authority gate.
    DriftStatementPreservation,
    /// Trust-audit authority gate.
    TrustAudit,
    /// False-control rerun authority gate.
    FalseControlRerun,
    /// Attempt-log write, including replay protection.
    WriteProofAttempt,
}

/// Per-step outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StepStatus {
    /// The step has not been reached.
    NotRun,
    /// The step ran and its gate accepted.
    Passed,
    /// The step ran and its gate rejected.
    Failed,
    /// The step was not run because required evidence was absent.
    Skipped,
}

/// Result of one pipeline step.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PipelineStepResult {
    /// One-based step number.
    pub number: u8,
    /// Step identity.
    pub step: PipelineStep,
    /// Stable step name.
    pub name: String,
    /// Step outcome.
    pub status: StepStatus,
    /// Failure detail, when the step failed or was blocked.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub failure: Option<IngestFailure>,
    /// Stringly-typed diagnostic details, in deterministic key order.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub details: BTreeMap<String, String>,
}

/// Why a pipeline step rejected or blocked.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum IngestFailure {
    /// Bundle layout, manifest schema, or content hashes failed.
    BundleIntegrityFailed {
        /// Offending field or diagnostic.
        field: String,
    },
    /// The repo did not match the manifest's pin.
    EnvironmentPinFailed {
        /// Diagnostic.
        reason: String,
    },
    /// The pre-patch baseline could not be established.
    BaselineFailed {
        /// Diagnostic.
        reason: String,
    },
    /// A patch failed to apply.
    PatchApplyFailed {
        /// Patch label.
        patch: String,
        /// Conflict diagnostic.
        conflict: String,
    },
    /// The Lake re-check failed.
    LakeRecheckFailed {
        /// Module label.
        module: String,
        /// Error diagnostic.
        error: String,
    },
    /// A target's statement hash moved.
    TargetStatementMismatch {
        /// Target theorem.
        theorem: String,
        /// Manifest-declared hash.
        expected: String,
        /// Observed hash.
        actual: String,
    },
    /// Blocking declaration-surface drift was reported.
    DriftRejected {
        /// Blocking drift descriptions.
        drifts: Vec<String>,
    },
    /// The trust-audit gate rejected.
    TrustAuditRejected {
        /// Rejection reasons.
        reasons: Vec<String>,
    },
    /// This target/patch envelope was already ingested.
    JobIdAlreadyIngested {
        /// Producer job id.
        job_id: String,
    },
    /// Statement-preservation evidence could not be evaluated at all.
    StatementPreservationUnavailable {
        /// Diagnostic.
        reason: String,
    },
    /// A false control stopped rejecting its known-bad input.
    FalseControlRegressed {
        /// Control identifier or set diagnostic.
        control: String,
    },
    /// The manifest violated local policy.
    PolicyRejected {
        /// Diagnostic.
        reason: String,
    },
    /// The manifest signature was rejected.
    SignatureRejected {
        /// Diagnostic.
        reason: String,
    },
    /// The stage has no wired runner in this ingest path.
    StageNotImplemented {
        /// Stage name.
        stage: String,
    },
}

/// Exit status of a subprocess the ingest drove.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MathMapCommandStatus {
    /// Whether the process exited successfully.
    pub success: bool,
    /// Exit code, absent when killed by a signal.
    pub code: Option<i32>,
}

impl MathMapCommandStatus {
    /// A successful exit.
    #[must_use]
    pub const fn success() -> Self {
        Self {
            success: true,
            code: Some(0),
        }
    }

    /// A failed exit with `code`.
    #[must_use]
    pub const fn failure(code: i32) -> Self {
        Self {
            success: false,
            code: Some(code),
        }
    }

    fn from_exit_status(status: std::process::ExitStatus) -> Self {
        Self {
            success: status.success(),
            code: status.code(),
        }
    }

    fn label(&self) -> String {
        match (self.success, self.code) {
            (true, Some(code)) => format!("success({code})"),
            (true, None) => "success".to_owned(),
            (false, Some(code)) => format!("failed({code})"),
            (false, None) => "failed(signal)".to_owned(),
        }
    }
}

/// Captured output of a subprocess the ingest drove.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MathMapCommandOutput {
    /// Exit status.
    pub status: MathMapCommandStatus,
    /// Captured stdout.
    pub stdout: String,
    /// Captured stderr.
    pub stderr: String,
}

impl MathMapCommandOutput {
    /// A successful run with the given streams.
    #[must_use]
    pub fn success(stdout: impl Into<String>, stderr: impl Into<String>) -> Self {
        Self {
            status: MathMapCommandStatus::success(),
            stdout: stdout.into(),
            stderr: stderr.into(),
        }
    }

    /// A failed run with the given exit code and streams.
    #[must_use]
    pub fn failure(code: i32, stdout: impl Into<String>, stderr: impl Into<String>) -> Self {
        Self {
            status: MathMapCommandStatus::failure(code),
            stdout: stdout.into(),
            stderr: stderr.into(),
        }
    }

    fn from_process_output(output: std::process::Output) -> Self {
        Self {
            status: MathMapCommandStatus::from_exit_status(output.status),
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        }
    }
}

/// Failure to run a subprocess at all.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum MathMapCommandError {
    /// Spawn or wait failed.
    #[error("failed to run `{program}` in `{cwd}`: {message}")]
    Io {
        /// Program name.
        program: String,
        /// Working directory.
        cwd: String,
        /// Diagnostic.
        message: String,
    },
    /// Writing the child's stdin failed.
    #[error("failed to write stdin for `{program}` in `{cwd}`: {message}")]
    Stdin {
        /// Program name.
        program: String,
        /// Working directory.
        cwd: String,
        /// Diagnostic.
        message: String,
    },
}

/// The pin the manifest declares.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnvironmentPinRequest {
    /// Revision the patches were produced against.
    pub expected_rev: String,
    /// Lake/Lean toolchain the patches were produced against.
    pub expected_lake_toolchain: String,
}

/// What the local repository actually reports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnvironmentPinObservation {
    /// Observed revision.
    pub rev: String,
    /// Observed Lake/Lean toolchain.
    pub lake_toolchain: String,
}

/// A matched environment pin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnvironmentPinReport {
    /// The manifest's declared pin.
    pub request: EnvironmentPinRequest,
    /// The observed repository state.
    pub observation: EnvironmentPinObservation,
}

/// Why an environment pin was rejected.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum EnvironmentPinError {
    /// The supplied repo path is not a directory.
    #[error("environment pin repo path `{path}` is not a directory")]
    RepoPathNotDirectory {
        /// Supplied path.
        path: String,
    },
    /// The manifest did not declare a revision.
    #[error("manifest is missing target_repo.rev")]
    MissingExpectedRev,
    /// The manifest did not declare a toolchain.
    #[error("manifest is missing target_repo.lake_toolchain")]
    MissingExpectedLakeToolchain,
    /// The observed revision does not match the declared one.
    #[error("repo revision mismatch: expected `{expected}`, actual `{actual}`")]
    RevMismatch {
        /// Declared revision.
        expected: String,
        /// Observed revision.
        actual: String,
    },
    /// The observed toolchain does not match the declared one.
    #[error("Lake toolchain mismatch: expected `{expected}`, actual `{actual}`")]
    LakeToolchainMismatch {
        /// Declared toolchain.
        expected: String,
        /// Observed toolchain.
        actual: String,
    },
    /// The repo has no `lean-toolchain` file.
    #[error("repo is missing lean-toolchain")]
    MissingLeanToolchain,
    /// The `lean-toolchain` file could not be read.
    #[error("failed to read lean-toolchain in `{cwd}`: {message}")]
    ToolchainIo {
        /// Working directory.
        cwd: String,
        /// Diagnostic.
        message: String,
    },
    /// A subprocess could not be run.
    #[error(transparent)]
    Command(#[from] MathMapCommandError),
    /// A subprocess exited non-zero.
    #[error("environment pin command failed: {message}")]
    CommandFailed {
        /// Diagnostic.
        message: String,
        /// Captured output.
        output: MathMapCommandOutput,
    },
}

impl EnvironmentPinError {
    fn to_failure(&self) -> IngestFailure {
        IngestFailure::EnvironmentPinFailed {
            reason: self.to_string(),
        }
    }
}

/// Observes the local repository's revision and Lake toolchain.
pub trait EnvironmentPinRunner: std::fmt::Debug {
    /// Observe the pin state of `clean_repo_path`.
    fn inspect_environment_pin(
        &self,
        clean_repo_path: &Path,
    ) -> Result<EnvironmentPinObservation, EnvironmentPinError>;
}

/// Environment-pin runner backed by `git rev-parse HEAD` plus `lean-toolchain`.
#[derive(Debug, Default, Clone, Copy)]
pub struct GitEnvironmentPinRunner;

impl EnvironmentPinRunner for GitEnvironmentPinRunner {
    fn inspect_environment_pin(
        &self,
        clean_repo_path: &Path,
    ) -> Result<EnvironmentPinObservation, EnvironmentPinError> {
        let rev_output = run_command_capture(clean_repo_path, "git", ["rev-parse", "HEAD"], None)?;
        if !rev_output.status.success {
            return Err(EnvironmentPinError::CommandFailed {
                message: command_failure_message(&rev_output),
                output: rev_output,
            });
        }
        let toolchain_path = clean_repo_path.join("lean-toolchain");
        let lake_toolchain = match fs::read_to_string(&toolchain_path) {
            Ok(text) => text.trim().to_owned(),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
                return Err(EnvironmentPinError::MissingLeanToolchain);
            }
            Err(err) => {
                return Err(EnvironmentPinError::ToolchainIo {
                    cwd: clean_repo_path.display().to_string(),
                    message: err.to_string(),
                });
            }
        };
        Ok(EnvironmentPinObservation {
            rev: rev_output.stdout.trim().to_owned(),
            lake_toolchain,
        })
    }
}

/// The concatenated patch payload to preflight.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PatchPreflightRequest {
    /// Patch paths, in manifest order.
    pub patches: Vec<String>,
    /// Concatenated, newline-terminated patch bytes.
    pub payload: Vec<u8>,
}

impl PatchPreflightRequest {
    /// Comma-joined patch label for diagnostics.
    #[must_use]
    pub fn patch_label(&self) -> String {
        if self.patches.is_empty() {
            "<no patches>".to_owned()
        } else {
            self.patches.join(",")
        }
    }
}

/// A successful patch preflight.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PatchPreflightReport {
    /// Patch paths that were checked.
    pub patches: Vec<String>,
    /// Captured `git apply --check` output.
    pub output: MathMapCommandOutput,
}

/// The concatenated patch payload to apply.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PatchApplyRequest {
    /// Patch paths, in manifest order.
    pub patches: Vec<String>,
    /// Concatenated, newline-terminated patch bytes.
    pub payload: Vec<u8>,
    /// Whether to commit after a successful apply.
    pub commit: bool,
}

impl PatchApplyRequest {
    /// Comma-joined patch label for diagnostics.
    #[must_use]
    pub fn patch_label(&self) -> String {
        if self.patches.is_empty() {
            "<no patches>".to_owned()
        } else {
            self.patches.join(",")
        }
    }
}

/// A successful patch apply.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PatchApplyReport {
    /// Patch paths that were applied.
    pub patches: Vec<String>,
    /// Captured `git apply --check` output.
    pub check_output: MathMapCommandOutput,
    /// Captured `git apply` output.
    pub apply_output: MathMapCommandOutput,
    /// Captured `git commit` output, when a commit was requested.
    pub commit_output: Option<MathMapCommandOutput>,
}

/// Why a patch preflight was rejected.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum PatchPreflightError {
    /// The supplied repo path is not a directory.
    #[error("patch preflight repo path `{path}` is not a directory")]
    RepoPathNotDirectory {
        /// Supplied path.
        path: String,
    },
    /// The manifest declared no patches.
    #[error("manifest contains no patches")]
    EmptyPatchSet,
    /// A manifest patch path was missing or unsafe.
    #[error("manifest patch path `{path}` is missing or unsafe")]
    InvalidPatchPath {
        /// Offending path.
        path: String,
    },
    /// The bundle did not carry a declared patch.
    #[error("bundle is missing patch `{path}`")]
    MissingPatch {
        /// Missing path.
        path: String,
    },
    /// A subprocess could not be run.
    #[error(transparent)]
    Command(#[from] MathMapCommandError),
    /// `git apply --check` rejected the payload.
    #[error("git apply --check rejected `{patch}`: {conflict}")]
    CheckFailed {
        /// Patch label.
        patch: String,
        /// Conflict diagnostic.
        conflict: String,
        /// Captured output.
        output: MathMapCommandOutput,
    },
}

impl PatchPreflightError {
    fn to_failure(&self) -> IngestFailure {
        match self {
            Self::RepoPathNotDirectory { path } => IngestFailure::PatchApplyFailed {
                patch: "<repo>".to_owned(),
                conflict: format!("repo path `{path}` is not a directory"),
            },
            Self::EmptyPatchSet => IngestFailure::PatchApplyFailed {
                patch: "<manifest>".to_owned(),
                conflict: "manifest contains no patches".to_owned(),
            },
            Self::InvalidPatchPath { path } => IngestFailure::PatchApplyFailed {
                patch: path.clone(),
                conflict: "manifest patch path is missing or unsafe".to_owned(),
            },
            Self::MissingPatch { path } => IngestFailure::PatchApplyFailed {
                patch: path.clone(),
                conflict: "bundle is missing patch".to_owned(),
            },
            Self::Command(err) => IngestFailure::PatchApplyFailed {
                patch: "<git apply --check>".to_owned(),
                conflict: err.to_string(),
            },
            Self::CheckFailed {
                patch, conflict, ..
            } => IngestFailure::PatchApplyFailed {
                patch: patch.clone(),
                conflict: conflict.clone(),
            },
        }
    }
}

/// Why a patch apply was rejected.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum PatchApplyError {
    /// The supplied repo path is not a directory.
    #[error("patch apply repo path `{path}` is not a directory")]
    RepoPathNotDirectory {
        /// Supplied path.
        path: String,
    },
    /// The manifest declared no patches.
    #[error("manifest contains no patches")]
    EmptyPatchSet,
    /// A manifest patch path was missing or unsafe.
    #[error("manifest patch path `{path}` is missing or unsafe")]
    InvalidPatchPath {
        /// Offending path.
        path: String,
    },
    /// The bundle did not carry a declared patch.
    #[error("bundle is missing patch `{path}`")]
    MissingPatch {
        /// Missing path.
        path: String,
    },
    /// A subprocess could not be run.
    #[error(transparent)]
    Command(#[from] MathMapCommandError),
    /// `git apply --check` rejected the payload.
    #[error("git apply --check rejected `{patch}`: {conflict}")]
    CheckFailed {
        /// Patch label.
        patch: String,
        /// Conflict diagnostic.
        conflict: String,
        /// Captured output.
        output: MathMapCommandOutput,
    },
    /// `git apply` rejected the payload.
    #[error("git apply rejected `{patch}`: {conflict}")]
    ApplyFailed {
        /// Patch label.
        patch: String,
        /// Conflict diagnostic.
        conflict: String,
        /// Captured output.
        output: MathMapCommandOutput,
    },
    /// `git add` failed.
    #[error("git add rejected `{patch}`: {conflict}")]
    AddFailed {
        /// Patch label.
        patch: String,
        /// Conflict diagnostic.
        conflict: String,
        /// Captured output.
        output: MathMapCommandOutput,
    },
    /// `git commit` failed.
    #[error("git commit rejected `{patch}`: {conflict}")]
    CommitFailed {
        /// Patch label.
        patch: String,
        /// Conflict diagnostic.
        conflict: String,
        /// Captured output.
        output: MathMapCommandOutput,
    },
}

impl PatchApplyError {
    fn to_failure(&self) -> IngestFailure {
        match self {
            Self::RepoPathNotDirectory { path } => IngestFailure::PatchApplyFailed {
                patch: "<repo>".to_owned(),
                conflict: format!("repo path `{path}` is not a directory"),
            },
            Self::EmptyPatchSet => IngestFailure::PatchApplyFailed {
                patch: "<manifest>".to_owned(),
                conflict: "manifest contains no patches".to_owned(),
            },
            Self::InvalidPatchPath { path } => IngestFailure::PatchApplyFailed {
                patch: path.clone(),
                conflict: "manifest patch path is missing or unsafe".to_owned(),
            },
            Self::MissingPatch { path } => IngestFailure::PatchApplyFailed {
                patch: path.clone(),
                conflict: "bundle is missing patch".to_owned(),
            },
            Self::Command(err) => IngestFailure::PatchApplyFailed {
                patch: "<git apply>".to_owned(),
                conflict: err.to_string(),
            },
            Self::CheckFailed {
                patch, conflict, ..
            }
            | Self::ApplyFailed {
                patch, conflict, ..
            }
            | Self::AddFailed {
                patch, conflict, ..
            }
            | Self::CommitFailed {
                patch, conflict, ..
            } => IngestFailure::PatchApplyFailed {
                patch: patch.clone(),
                conflict: conflict.clone(),
            },
        }
    }

    fn output(&self) -> Option<&MathMapCommandOutput> {
        match self {
            Self::CheckFailed { output, .. }
            | Self::ApplyFailed { output, .. }
            | Self::AddFailed { output, .. }
            | Self::CommitFailed { output, .. } => Some(output),
            _ => None,
        }
    }
}

/// Checks whether the bundle patches would apply, without mutating the repo.
pub trait PatchPreflightRunner: std::fmt::Debug {
    /// Run the preflight check.
    fn check_patch_preflight(
        &self,
        clean_repo_path: &Path,
        request: &PatchPreflightRequest,
    ) -> Result<MathMapCommandOutput, MathMapCommandError>;
}

/// Preflight runner backed by `git apply --check`.
#[derive(Debug, Default, Clone, Copy)]
pub struct GitApplyCheckRunner;

impl PatchPreflightRunner for GitApplyCheckRunner {
    fn check_patch_preflight(
        &self,
        clean_repo_path: &Path,
        request: &PatchPreflightRequest,
    ) -> Result<MathMapCommandOutput, MathMapCommandError> {
        run_command_capture(
            clean_repo_path,
            "git",
            ["apply", "--check"],
            Some(&request.payload),
        )
    }
}

/// Applies the bundle patches to the repo.
pub trait PatchApplyRunner: std::fmt::Debug {
    /// Apply the patches, optionally committing.
    fn apply_patch(
        &self,
        clean_repo_path: &Path,
        request: &PatchApplyRequest,
    ) -> Result<PatchApplyReport, PatchApplyError>;
}

/// Apply runner backed by `git apply`, always preceded by `git apply --check`.
#[derive(Debug, Default, Clone, Copy)]
pub struct GitPatchApplyRunner;

impl PatchApplyRunner for GitPatchApplyRunner {
    fn apply_patch(
        &self,
        clean_repo_path: &Path,
        request: &PatchApplyRequest,
    ) -> Result<PatchApplyReport, PatchApplyError> {
        let check_output = run_command_capture(
            clean_repo_path,
            "git",
            ["apply", "--check"],
            Some(&request.payload),
        )?;
        if !check_output.status.success {
            return Err(PatchApplyError::CheckFailed {
                patch: request.patch_label(),
                conflict: command_failure_message(&check_output),
                output: check_output,
            });
        }

        let apply_output =
            run_command_capture(clean_repo_path, "git", ["apply"], Some(&request.payload))?;
        if !apply_output.status.success {
            return Err(PatchApplyError::ApplyFailed {
                patch: request.patch_label(),
                conflict: command_failure_message(&apply_output),
                output: apply_output,
            });
        }

        let commit_output = if request.commit {
            let add_output = run_command_capture(clean_repo_path, "git", ["add", "-A"], None)?;
            if !add_output.status.success {
                return Err(PatchApplyError::AddFailed {
                    patch: request.patch_label(),
                    conflict: command_failure_message(&add_output),
                    output: add_output,
                });
            }
            let commit_output = run_command_capture(
                clean_repo_path,
                "git",
                [
                    "-c",
                    "user.name=MathMap Ingest",
                    "-c",
                    "user.email=math_map-ingest@example.invalid",
                    "commit",
                    "-m",
                    "Apply MathMap patch",
                ],
                None,
            )?;
            if !commit_output.status.success {
                return Err(PatchApplyError::CommitFailed {
                    patch: request.patch_label(),
                    conflict: command_failure_message(&commit_output),
                    output: commit_output,
                });
            }
            Some(commit_output)
        } else {
            None
        };

        Ok(PatchApplyReport {
            patches: request.patches.clone(),
            check_output,
            apply_output,
            commit_output,
        })
    }
}

/// The re-check command to run in the patched repository.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LakeRecheckCommand {
    /// Program to execute.
    pub program: String,
    /// Arguments.
    pub args: Vec<String>,
}

impl LakeRecheckCommand {
    /// Build a re-check command.
    #[must_use]
    pub fn new<I, S>(program: impl Into<String>, args: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            program: program.into(),
            args: args.into_iter().map(Into::into).collect(),
        }
    }

    /// Space-joined command line for diagnostics.
    #[must_use]
    pub fn command_line(&self) -> String {
        std::iter::once(self.program.as_str())
            .chain(self.args.iter().map(String::as_str))
            .collect::<Vec<_>>()
            .join(" ")
    }
}

impl Default for LakeRecheckCommand {
    fn default() -> Self {
        Self::new("lake", ["build"])
    }
}

/// Runs the Lake re-check in the patched repository.
pub trait LakeRecheckRunner: std::fmt::Debug {
    /// Execute the re-check command.
    fn run_lake_recheck(
        &self,
        clean_repo_path: &Path,
        command: &LakeRecheckCommand,
    ) -> Result<MathMapCommandOutput, MathMapCommandError>;
}

/// Lake re-check runner that spawns the command as a subprocess.
#[derive(Debug, Default, Clone, Copy)]
pub struct ProcessLakeRecheckRunner;

impl LakeRecheckRunner for ProcessLakeRecheckRunner {
    fn run_lake_recheck(
        &self,
        clean_repo_path: &Path,
        command: &LakeRecheckCommand,
    ) -> Result<MathMapCommandOutput, MathMapCommandError> {
        run_command_capture(
            clean_repo_path,
            &command.program,
            command.args.iter().map(String::as_str),
            None,
        )
    }
}

/// Why bundle integrity rejected an untrusted bundle.
#[derive(Debug, thiserror::Error)]
pub enum MathMapIngestError {
    /// The bundle could not be loaded.
    #[error(transparent)]
    Bundle(#[from] BundleLoadError),
    /// `manifest.json` was not UTF-8.
    #[error("manifest.json is not valid UTF-8: {0}")]
    ManifestUtf8(#[from] std::str::Utf8Error),
    /// `manifest.json` was not valid JSON, or violated the strict schema.
    #[error("manifest.json is not valid JSON: {0}")]
    ManifestJson(#[from] serde_json::Error),
    /// A mandatory manifest field was missing or empty.
    #[error(transparent)]
    ManifestValidation(#[from] ManifestValidationError),
    /// Local policy rejected the manifest.
    #[error(transparent)]
    Policy(#[from] PolicyViolation),
    /// The signature or trusted-key policy rejected the bundle.
    #[error(transparent)]
    Keys(#[from] TrustedKeyRegistryError),
    /// A required bundle entry was absent.
    #[error("bundle is missing `{0}`")]
    MissingBundleFile(&'static str),
    /// A manifest-declared patch was absent from the bundle.
    #[error("bundle is missing patch `{0}`")]
    MissingPatch(String),
    /// A patch's content hash did not match the manifest.
    #[error("patch `{path}` sha256 mismatch: expected {expected}, actual {actual}")]
    PatchHashMismatch {
        /// Patch path.
        path: String,
        /// Manifest-declared hash.
        expected: String,
        /// Observed hash.
        actual: String,
    },
    /// An optional tree digest did not match the manifest.
    #[error("{field} digest mismatch: expected {expected}, actual {actual}")]
    DigestMismatch {
        /// Manifest field.
        field: &'static str,
        /// Manifest-declared digest.
        expected: String,
        /// Observed digest.
        actual: String,
    },
}

impl Default for MathMapIngestConfig {
    fn default() -> Self {
        Self {
            policy: MathMapPolicy::builtin(),
            trusted_keys: TrustedKeyRegistry::builtin(),
        }
    }
}

/// Ingest a bundle with the built-in policy, keys, and Ed25519 verifier.
pub fn ingest_bundle(path: impl AsRef<Path>) -> MathMapIngestReport {
    ingest_bundle_with_inputs(path, MathMapIngestInputs::none())
}

/// Ingest a bundle with the built-in configuration and caller-supplied evidence.
pub fn ingest_bundle_with_inputs(
    path: impl AsRef<Path>,
    inputs: MathMapIngestInputs<'_>,
) -> MathMapIngestReport {
    let config = MathMapIngestConfig::default();
    ingest_bundle_with_verifier_and_inputs(path, config, &Ed25519SignatureVerifier, inputs)
}

/// Ingest a bundle and record the outcome in the attempt log under `store_root`.
pub fn ingest_bundle_to_attempt_log(
    path: impl AsRef<Path>,
    store_root: impl AsRef<Path>,
) -> MathverseResult<MathMapIngestReport> {
    ingest_bundle_to_attempt_log_with_inputs(path, store_root, MathMapIngestInputs::none())
}

/// Ingest a bundle with caller-supplied evidence and record it in the attempt log.
pub fn ingest_bundle_to_attempt_log_with_inputs(
    path: impl AsRef<Path>,
    store_root: impl AsRef<Path>,
    inputs: MathMapIngestInputs<'_>,
) -> MathverseResult<MathMapIngestReport> {
    let config = MathMapIngestConfig::default();
    ingest_bundle_with_verifier_to_attempt_log_and_inputs(
        path,
        store_root,
        config,
        &Ed25519SignatureVerifier,
        inputs,
    )
}

/// Ingest a bundle with an explicit configuration and signature verifier.
pub fn ingest_bundle_with_verifier(
    path: impl AsRef<Path>,
    config: MathMapIngestConfig,
    verifier: &dyn ManifestSignatureVerifier,
) -> MathMapIngestReport {
    ingest_bundle_with_verifier_and_inputs(path, config, verifier, MathMapIngestInputs::none())
}

/// Ingest a bundle with an explicit configuration, verifier, and evidence.
pub fn ingest_bundle_with_verifier_and_inputs(
    path: impl AsRef<Path>,
    config: MathMapIngestConfig,
    verifier: &dyn ManifestSignatureVerifier,
    inputs: MathMapIngestInputs<'_>,
) -> MathMapIngestReport {
    let path = path.as_ref();
    let mut report = MathMapIngestReport::new(path);
    match run_bundle_integrity(path, &config, verifier) {
        Ok(integrity) => {
            report.record_integrity(&integrity);
            report.block_after_integrity();
            report.apply_inputs(&integrity, inputs);
        }
        Err(err) => {
            let failure = err.to_failure();
            report.fail_step(PipelineStep::BundleIntegrity, failure.clone());
            report.status = IngestStatus::Rejected {
                step: PipelineStep::BundleIntegrity,
                reason: failure_reason(&failure),
            };
        }
    }
    report
}

/// Ingest a bundle with an explicit configuration and verifier, recording it.
pub fn ingest_bundle_with_verifier_to_attempt_log(
    path: impl AsRef<Path>,
    store_root: impl AsRef<Path>,
    config: MathMapIngestConfig,
    verifier: &dyn ManifestSignatureVerifier,
) -> MathverseResult<MathMapIngestReport> {
    ingest_bundle_with_verifier_to_attempt_log_and_inputs(
        path,
        store_root,
        config,
        verifier,
        MathMapIngestInputs::none(),
    )
}

/// Ingest a bundle with full control, recording the outcome in the attempt log.
///
/// Replay protection lives here: a second bundle carrying the same
/// service/target/patch envelope is REJECTED even when its `job_id` differs,
/// and even when the first attempt was itself blocked or rejected.
pub fn ingest_bundle_with_verifier_to_attempt_log_and_inputs(
    path: impl AsRef<Path>,
    store_root: impl AsRef<Path>,
    config: MathMapIngestConfig,
    verifier: &dyn ManifestSignatureVerifier,
    inputs: MathMapIngestInputs<'_>,
) -> MathverseResult<MathMapIngestReport> {
    let path = path.as_ref();
    let store_root = store_root.as_ref();
    let mut report = MathMapIngestReport::new(path);
    match run_bundle_integrity(path, &config, verifier) {
        Ok(integrity) => {
            report.record_integrity(&integrity);
            report.block_after_integrity();
            report.apply_inputs(&integrity, inputs);

            // Replay protection: do not append a second attempt for the same
            // MathMap target/patch envelope, even when the previous attempt
            // was blocked or rejected.
            let goal_hash = deterministic_blake3_hex(&MathMapGoalHashEnvelope {
                schema_version: MATH_MAP_INGEST_SCHEMA_VERSION,
                service: integrity.manifest.service.as_deref(),
                target_repo: &integrity.manifest.target_repo,
                targets: &integrity.manifest.targets,
                patches: &integrity.manifest.patches,
            });

            let duplicate_found = attempt_log::iter_from(
                store_root,
                attempt_log::AttemptFilter {
                    goal_hash: Some(goal_hash),
                    ..attempt_log::AttemptFilter::default()
                },
            )?
            .next()
            .is_some();

            if duplicate_found {
                let job_id = report.job_id.as_deref().unwrap_or("unknown");
                let reason = format!(
                    "MathMap bundle replay detected for job_id `{job_id}`; rejecting duplicate target/patch envelope"
                );
                report.status = IngestStatus::Rejected {
                    step: PipelineStep::WriteProofAttempt,
                    reason,
                };
                report.fail_step(
                    PipelineStep::WriteProofAttempt,
                    IngestFailure::JobIdAlreadyIngested {
                        job_id: job_id.to_owned(),
                    },
                );
            } else {
                let attempt = build_blocked_attempt(store_root, &integrity, &report)?;
                attempt_log::append_to(store_root, &attempt)?;
                report.pass_step(
                    PipelineStep::WriteProofAttempt,
                    proof_attempt_step_details(&attempt, attempt_status_name(&attempt.status)),
                );
                report.proof_attempt = Some(MathMapProofAttemptStub {
                    attempt_id: attempt.attempt_id.to_string(),
                    service: report
                        .service
                        .clone()
                        .unwrap_or_else(|| "unknown".to_owned()),
                    job_id: report
                        .job_id
                        .clone()
                        .unwrap_or_else(|| "unknown".to_owned()),
                    status: report.status.clone(),
                    attempt_status: attempt.status.clone(),
                    authority_gate: attempt.authority_gate.clone(),
                    failure_mode: attempt.failure_mode.clone(),
                    trust_level: attempt.trust_level,
                    bundle_sha256: report.bundle_sha256.clone().unwrap_or_default(),
                    model_response: attempt.model_response,
                    solver_artifact: attempt.solver_artifact,
                    trust_audit_hash: Some(attempt.trust_audit_hash),
                });
            }
        }
        Err(err) => {
            let failure = err.to_failure();
            report.fail_step(PipelineStep::BundleIntegrity, failure.clone());
            report.status = IngestStatus::Rejected {
                step: PipelineStep::BundleIntegrity,
                reason: failure_reason(&failure),
            };
        }
    }
    Ok(report)
}

fn proof_attempt_step_details(
    attempt: &ProofAttempt,
    attempt_status: &str,
) -> BTreeMap<String, String> {
    let mut details = BTreeMap::from([
        ("attempt_id".to_owned(), attempt.attempt_id.to_string()),
        ("attempt_status".to_owned(), attempt_status.to_owned()),
        (
            "trust_audit_hash".to_owned(),
            attempt.trust_audit_hash.clone(),
        ),
    ]);
    if let Some(gate) = &attempt.authority_gate {
        details.insert("authority_gate".to_owned(), gate.clone());
    }
    if let Some(mode) = &attempt.failure_mode {
        details.insert("failure_mode".to_owned(), mode.clone());
    }
    if let Some(level) = attempt.trust_level {
        details.insert("trust_level".to_owned(), trust_level_name(level).to_owned());
    }
    details
}

/// Evaluate the three authority gates over caller-supplied evidence.
///
/// The combined status is `Accepted` only when all three gates passed. If no
/// gate rejected but the false-control rerun did not pass, the result is
/// `Blocked`, never `Accepted`.
#[must_use]
pub fn evaluate_authority_gates(
    manifest: &BundleManifest,
    inputs: MathMapAuthorityGateInputs<'_>,
) -> MathMapAuthorityGateReport {
    let mut statement_preservation = evaluate_statement_preservation_gate(
        manifest,
        inputs.observed_target_statement_hashes,
        inputs.drift_reports,
    );
    attach_statement_comparison_input_details(
        &mut statement_preservation,
        manifest,
        inputs.statement_comparison_inputs,
    );
    let trust_audit = evaluate_trust_audit_pipeline_gate(manifest, inputs.trust_audit);
    let false_control_rerun = evaluate_false_control_rerun_gate(inputs.false_control_rerun);
    let status = first_rejection(&[&statement_preservation, &trust_audit, &false_control_rerun])
        .unwrap_or_else(|| {
            if false_control_rerun.status == StepStatus::Passed {
                IngestStatus::Accepted
            } else {
                IngestStatus::Blocked {
                    reason: "statement-preservation and trust-audit gates passed; missing false-control rerun report".to_owned(),
                }
            }
        });

    MathMapAuthorityGateReport {
        status,
        statement_preservation,
        trust_audit,
        false_control_rerun,
    }
}

/// Attach per-target before/after statement hashes to a gate result.
///
/// Diagnostics only: this never changes the gate verdict. Returns the number of
/// manifest targets that were matched to a comparison input.
pub fn attach_statement_comparison_input_details(
    result: &mut PipelineStepResult,
    manifest: &BundleManifest,
    statement_comparison_inputs: &[TheoremStatementComparisonInput],
) -> usize {
    result.details.insert(
        "statement_comparison_input_count".to_owned(),
        statement_comparison_inputs.len().to_string(),
    );

    let by_qualified_name: BTreeMap<&str, &TheoremStatementComparisonInput> =
        statement_comparison_inputs
            .iter()
            .map(|input| (input.qualified_name.as_str(), input))
            .collect();
    let by_theorem: BTreeMap<&str, &TheoremStatementComparisonInput> = statement_comparison_inputs
        .iter()
        .map(|input| (input.theorem.as_str(), input))
        .collect();

    let mut attached = 0usize;
    for target in &manifest.targets {
        let Some(theorem) = target
            .theorem
            .as_deref()
            .map(str::trim)
            .filter(|theorem| !theorem.is_empty())
        else {
            continue;
        };
        let Some(input) = by_qualified_name
            .get(theorem)
            .copied()
            .or_else(|| by_theorem.get(theorem).copied())
        else {
            continue;
        };

        let prefix = format!("statement_comparison.target.{attached}");
        result
            .details
            .insert(format!("{prefix}.target_theorem"), theorem.to_owned());
        result.details.insert(
            format!("{prefix}.qualified_name"),
            input.qualified_name.clone(),
        );
        result
            .details
            .insert(format!("{prefix}.theorem"), input.theorem.clone());
        result.details.insert(
            format!("{prefix}.before_statement_hash"),
            input
                .before_statement_hash
                .clone()
                .unwrap_or_else(|| "<missing>".to_owned()),
        );
        result.details.insert(
            format!("{prefix}.after_statement_hash"),
            input
                .after_statement_hash
                .clone()
                .unwrap_or_else(|| "<missing>".to_owned()),
        );
        attached += 1;
    }
    result.details.insert(
        "statement_comparison_target_count".to_owned(),
        attached.to_string(),
    );
    attached
}

/// Statement-preservation authority gate.
///
/// Fail-closed: a manifest with no targets, a target whose observed statement
/// hash is absent or different, or ANY blocking drift report all reject. A
/// missing observed hash compares as `<missing observed statement hash>` and
/// therefore never matches a declared hash.
#[must_use]
pub fn evaluate_statement_preservation_gate(
    manifest: &BundleManifest,
    observed_target_statement_hashes: &BTreeMap<String, String>,
    drift_reports: &[DriftReport],
) -> PipelineStepResult {
    let mut result = PipelineStepResult::new(PipelineStep::DriftStatementPreservation);
    result.details = BTreeMap::from([
        (
            "target_count".to_owned(),
            manifest.targets.len().to_string(),
        ),
        (
            "observed_target_statement_hash_count".to_owned(),
            observed_target_statement_hashes.len().to_string(),
        ),
        (
            "drift_report_count".to_owned(),
            drift_reports.len().to_string(),
        ),
    ]);
    if manifest.targets.is_empty() {
        fail_result(
            &mut result,
            IngestFailure::StatementPreservationUnavailable {
                reason: "manifest has no targets to preserve".to_owned(),
            },
        );
        return result;
    }

    for target in &manifest.targets {
        let theorem = target
            .theorem
            .as_deref()
            .map(str::trim)
            .filter(|theorem| !theorem.is_empty())
            .unwrap_or("<missing theorem>");
        let expected = target
            .expected_statement_hash
            .as_deref()
            .map(str::trim)
            .filter(|hash| !hash.is_empty())
            .unwrap_or("<missing expected_statement_hash>");
        let actual = observed_target_statement_hashes
            .get(theorem)
            .map(String::as_str)
            .unwrap_or("<missing observed statement hash>");

        if normalize_digest(expected) != normalize_digest(actual) {
            fail_result(
                &mut result,
                IngestFailure::TargetStatementMismatch {
                    theorem: theorem.to_owned(),
                    expected: expected.to_owned(),
                    actual: actual.to_owned(),
                },
            );
            return result;
        }
    }

    let rejected_drifts: Vec<_> = drift_reports
        .iter()
        .filter_map(rejected_statement_drift)
        .collect();
    if !rejected_drifts.is_empty() {
        fail_result(
            &mut result,
            IngestFailure::DriftRejected {
                drifts: rejected_drifts,
            },
        );
        return result;
    }

    result.status = StepStatus::Passed;
    result
}

/// Trust-audit authority gate.
///
/// Fail-closed: a manifest without a `declared_trust` envelope rejects, missing
/// pre/post audit reports reject, and a post-patch report covering zero
/// constants rejects rather than passing on empty evidence.
#[must_use]
pub fn evaluate_trust_audit_pipeline_gate(
    manifest: &BundleManifest,
    input: Option<MathMapTrustAuditGateInput<'_>>,
) -> PipelineStepResult {
    let mut result = PipelineStepResult::new(PipelineStep::TrustAudit);
    result.details = BTreeMap::from([
        (
            "declared_trust_present".to_owned(),
            manifest.declared_trust.is_some().to_string(),
        ),
        (
            "trust_audit_reports_supplied".to_owned(),
            input.is_some().to_string(),
        ),
    ]);
    let Some(declared_trust) = manifest.declared_trust.as_ref() else {
        fail_result(
            &mut result,
            IngestFailure::TrustAuditRejected {
                reasons: vec!["manifest is missing declared_trust".to_owned()],
            },
        );
        return result;
    };
    let Some(input) = input else {
        fail_result(
            &mut result,
            IngestFailure::TrustAuditRejected {
                reasons: vec!["missing pre/post trust audit reports".to_owned()],
            },
        );
        return result;
    };

    let decision = evaluate_trust_audit_gate(input.before, input.after, declared_trust);
    result.details.extend([
        (
            "post_total_constants".to_owned(),
            input.after.total_constants.to_string(),
        ),
        (
            "added_axioms".to_owned(),
            decision.delta.added_axioms.len().to_string(),
        ),
        (
            "added_opaques".to_owned(),
            decision.delta.added_opaques.len().to_string(),
        ),
        (
            "added_unsafe".to_owned(),
            decision.delta.added_unsafe.len().to_string(),
        ),
        (
            "added_external_solvers".to_owned(),
            decision.delta.added_external_solvers.len().to_string(),
        ),
        (
            "added_critical_findings".to_owned(),
            decision.delta.added_critical_findings.len().to_string(),
        ),
        (
            "recursive_trust_violations".to_owned(),
            input.after.trust_violations.len().to_string(),
        ),
    ]);
    if let Some(level) = worst_reported_trust_level(input.after) {
        result.details.insert(
            "post_worst_trust_level".to_owned(),
            trust_level_name(level).to_owned(),
        );
    }

    if input.after.total_constants == 0 {
        result
            .details
            .insert("authority_gate_status".to_owned(), "rejected".to_owned());
        fail_result(
            &mut result,
            IngestFailure::TrustAuditRejected {
                reasons: vec![
                    "post-patch trust audit has zero constants; refusing empty authority evidence"
                        .to_owned(),
                ],
            },
        );
        return result;
    }

    if !decision.is_accepted() {
        result
            .details
            .insert("authority_gate_status".to_owned(), "rejected".to_owned());
        fail_result(
            &mut result,
            IngestFailure::TrustAuditRejected {
                reasons: decision.rejection_reasons,
            },
        );
        return result;
    }

    result.status = StepStatus::Passed;
    result
        .details
        .insert("authority_gate_status".to_owned(), "accepted".to_owned());
    result
}

/// False-control rerun authority gate.
///
/// Fail-closed: no report means `Skipped` with a blocked reason, which can
/// never produce an overall `Accepted`. An incomplete or duplicated control set
/// rejects, as does any control that did not reject its known-bad input —
/// including controls that are merely pending or errored.
#[must_use]
pub fn evaluate_false_control_rerun_gate(
    input: Option<MathMapFalseControlRerunInput<'_>>,
) -> PipelineStepResult {
    let mut result = PipelineStepResult::new(PipelineStep::FalseControlRerun);

    match input {
        Some(MathMapFalseControlRerunInput::SuppliedReport(report)) => {
            evaluate_false_control_report(
                &mut result,
                report,
                "caller_supplied",
                "supplied_report",
            );
        }
        Some(MathMapFalseControlRerunInput::LocalReport(report)) => {
            evaluate_false_control_report(&mut result, report, "local_generated", "local_report");
        }
        None => {
            result.details.extend([
                (
                    "false_control_report_supplied".to_owned(),
                    "false".to_owned(),
                ),
                (
                    "false_control_report_source".to_owned(),
                    "missing".to_owned(),
                ),
            ]);
            result.status = StepStatus::Skipped;
            result
                .details
                .insert("authority_gate_status".to_owned(), "blocked".to_owned());
            result.details.insert(
                "blocked_reason".to_owned(),
                "missing false-control rerun report".to_owned(),
            );
        }
    }

    result
}

fn evaluate_false_control_report(
    result: &mut PipelineStepResult,
    report: &FalseControlReport,
    report_source: &'static str,
    rerun_mode: &'static str,
) {
    result.details.extend([
        (
            "false_control_report_supplied".to_owned(),
            "true".to_owned(),
        ),
        (
            "false_control_report_source".to_owned(),
            report_source.to_owned(),
        ),
        ("false_control_rerun_mode".to_owned(), rerun_mode.to_owned()),
    ]);

    let summary = report.replay_summary();
    result.details.extend([
        ("total_controls".to_owned(), summary.total.to_string()),
        ("rejected_controls".to_owned(), summary.rejected.to_string()),
        ("pending_controls".to_owned(), summary.pending.to_string()),
        (
            "accepted_bad_input_controls".to_owned(),
            summary.accepted_bad_input.to_string(),
        ),
        (
            "expected_total_controls".to_owned(),
            summary.expected_total.to_string(),
        ),
        (
            "missing_control_ids".to_owned(),
            summary.missing_control_ids.join(","),
        ),
        (
            "duplicate_control_ids".to_owned(),
            summary.duplicate_control_ids.join(","),
        ),
        (
            "probe_error_controls".to_owned(),
            summary.probe_errors.to_string(),
        ),
        ("replay_ready".to_owned(), summary.replay_ready.to_string()),
        (
            "non_rejected_controls".to_owned(),
            summary.non_rejected_control_ids.join(","),
        ),
    ]);

    if !summary.missing_control_ids.is_empty() || !summary.duplicate_control_ids.is_empty() {
        let reason = format!(
            "incomplete_control_set: missing=[{}] duplicate=[{}]",
            summary.missing_control_ids.join(","),
            summary.duplicate_control_ids.join(",")
        );
        fail_result(
            result,
            IngestFailure::FalseControlRegressed {
                control: reason.clone(),
            },
        );
        result
            .details
            .insert("authority_gate_status".to_owned(), "rejected".to_owned());
        result
            .details
            .insert("blocking_control_status".to_owned(), reason);
        return;
    }

    if let Some(control) = report.blocking_controls().first() {
        fail_result(
            result,
            IngestFailure::FalseControlRegressed {
                control: control.id.as_str().to_owned(),
            },
        );
        result
            .details
            .insert("authority_gate_status".to_owned(), "rejected".to_owned());
        result.details.insert(
            "blocking_control_status".to_owned(),
            format!("{:?}", control.status),
        );
        return;
    }

    result.status = StepStatus::Passed;
    result
        .details
        .insert("authority_gate_status".to_owned(), "accepted".to_owned());
}

/// Environment-pin step: the repo MUST match the manifest's declared pin.
#[must_use]
pub fn evaluate_environment_pin(
    clean_repo_path: impl AsRef<Path>,
    manifest: &BundleManifest,
    runner: &dyn EnvironmentPinRunner,
) -> PipelineStepResult {
    let clean_repo_path = clean_repo_path.as_ref();
    let mut result = PipelineStepResult::new(PipelineStep::EnvironmentPin);
    result.details = BTreeMap::from([(
        "repo_path".to_owned(),
        clean_repo_path.display().to_string(),
    )]);

    let request = match build_environment_pin_request(manifest) {
        Ok(request) => request,
        Err(err) => {
            fail_result(&mut result, err.to_failure());
            return result;
        }
    };
    result.details.extend([
        ("expected_rev".to_owned(), request.expected_rev.clone()),
        (
            "expected_lake_toolchain".to_owned(),
            request.expected_lake_toolchain.clone(),
        ),
    ]);

    match validate_environment_pin(clean_repo_path, request, runner) {
        Ok(report) => {
            result.status = StepStatus::Passed;
            result.details.extend([
                ("actual_rev".to_owned(), report.observation.rev),
                (
                    "actual_lake_toolchain".to_owned(),
                    report.observation.lake_toolchain,
                ),
            ]);
        }
        Err(err) => {
            fail_result(&mut result, err.to_failure());
        }
    }

    result
}

/// Extract the manifest's declared environment pin.
///
/// An unpinned manifest is an error, not a wildcard.
pub fn build_environment_pin_request(
    manifest: &BundleManifest,
) -> Result<EnvironmentPinRequest, EnvironmentPinError> {
    let expected_rev = manifest
        .target_repo
        .rev
        .as_deref()
        .map(str::trim)
        .filter(|rev| !rev.is_empty())
        .ok_or(EnvironmentPinError::MissingExpectedRev)?;
    let expected_lake_toolchain = manifest
        .target_repo
        .lake_toolchain
        .as_deref()
        .map(str::trim)
        .filter(|toolchain| !toolchain.is_empty())
        .ok_or(EnvironmentPinError::MissingExpectedLakeToolchain)?;
    Ok(EnvironmentPinRequest {
        expected_rev: expected_rev.to_owned(),
        expected_lake_toolchain: expected_lake_toolchain.to_owned(),
    })
}

/// Check the observed repository state against a declared pin.
///
/// The revision matches on equality or when the observed full revision starts
/// with the declared abbreviated revision; the toolchain must match exactly.
pub fn validate_environment_pin(
    clean_repo_path: impl AsRef<Path>,
    request: EnvironmentPinRequest,
    runner: &dyn EnvironmentPinRunner,
) -> Result<EnvironmentPinReport, EnvironmentPinError> {
    let clean_repo_path = clean_repo_path.as_ref();
    if !clean_repo_path.is_dir() {
        return Err(EnvironmentPinError::RepoPathNotDirectory {
            path: clean_repo_path.display().to_string(),
        });
    }
    let observation = runner.inspect_environment_pin(clean_repo_path)?;
    let actual_rev = observation.rev.trim();
    if actual_rev != request.expected_rev && !actual_rev.starts_with(&request.expected_rev) {
        return Err(EnvironmentPinError::RevMismatch {
            expected: request.expected_rev,
            actual: observation.rev,
        });
    }
    if observation.lake_toolchain.trim() != request.expected_lake_toolchain {
        return Err(EnvironmentPinError::LakeToolchainMismatch {
            expected: request.expected_lake_toolchain,
            actual: observation.lake_toolchain,
        });
    }
    Ok(EnvironmentPinReport {
        request,
        observation,
    })
}

/// Record that no pre-patch baseline could be captured.
///
/// Emits `Skipped` with a `BaselineFailed` reason so the missing baseline is
/// visible in the report rather than silently absent.
#[must_use]
pub fn evaluate_pre_patch_baseline_unavailable(reason: impl Into<String>) -> PipelineStepResult {
    let reason = reason.into();
    let mut result = PipelineStepResult::new(PipelineStep::PrePatchBaseline);
    result.status = StepStatus::Skipped;
    result.failure = Some(IngestFailure::BaselineFailed {
        reason: reason.clone(),
    });
    result
        .details
        .insert("baseline_status".to_owned(), "unavailable".to_owned());
    result.details.insert("blocked_reason".to_owned(), reason);
    result
}

/// Concatenate the manifest-declared patches into one payload.
///
/// Every path is re-checked with [`is_safe_relative_path`] here, independently
/// of manifest validation, so no unsafe path can reach `git apply`.
pub fn build_patch_preflight_request(
    manifest: &BundleManifest,
    bundle: &BundleFileSystem,
) -> Result<PatchPreflightRequest, PatchPreflightError> {
    if manifest.patches.is_empty() {
        return Err(PatchPreflightError::EmptyPatchSet);
    }

    let mut patches = Vec::new();
    let mut payload = Vec::new();
    for patch in &manifest.patches {
        let path = patch
            .path
            .as_deref()
            .map(str::trim)
            .filter(|path| !path.is_empty() && is_safe_relative_path(path))
            .ok_or_else(|| PatchPreflightError::InvalidPatchPath {
                path: patch.path.clone().unwrap_or_else(|| "<missing>".to_owned()),
            })?;
        let bytes = bundle
            .read(path)
            .ok_or_else(|| PatchPreflightError::MissingPatch {
                path: path.to_owned(),
            })?;
        if !payload.is_empty() && !payload.ends_with(b"\n") {
            payload.push(b'\n');
        }
        payload.extend_from_slice(bytes);
        if !payload.ends_with(b"\n") {
            payload.push(b'\n');
        }
        patches.push(path.to_owned());
    }

    Ok(PatchPreflightRequest { patches, payload })
}

/// Build the apply request from the same validated payload as the preflight.
pub fn build_patch_apply_request(
    manifest: &BundleManifest,
    bundle: &BundleFileSystem,
    commit: bool,
) -> Result<PatchApplyRequest, PatchApplyError> {
    match build_patch_preflight_request(manifest, bundle) {
        Ok(request) => Ok(PatchApplyRequest {
            patches: request.patches,
            payload: request.payload,
            commit,
        }),
        Err(PatchPreflightError::RepoPathNotDirectory { path }) => {
            Err(PatchApplyError::RepoPathNotDirectory { path })
        }
        Err(PatchPreflightError::EmptyPatchSet) => Err(PatchApplyError::EmptyPatchSet),
        Err(PatchPreflightError::InvalidPatchPath { path }) => {
            Err(PatchApplyError::InvalidPatchPath { path })
        }
        Err(PatchPreflightError::MissingPatch { path }) => {
            Err(PatchApplyError::MissingPatch { path })
        }
        Err(PatchPreflightError::Command(err)) => Err(PatchApplyError::Command(err)),
        Err(PatchPreflightError::CheckFailed {
            patch,
            conflict,
            output,
        }) => Err(PatchApplyError::CheckFailed {
            patch,
            conflict,
            output,
        }),
    }
}

/// Check whether the bundle patches apply, without mutating the repo.
pub fn preflight_bundle_patches(
    clean_repo_path: impl AsRef<Path>,
    manifest: &BundleManifest,
    bundle: &BundleFileSystem,
    runner: &dyn PatchPreflightRunner,
) -> Result<PatchPreflightReport, PatchPreflightError> {
    let clean_repo_path = clean_repo_path.as_ref();
    if !clean_repo_path.is_dir() {
        return Err(PatchPreflightError::RepoPathNotDirectory {
            path: clean_repo_path.display().to_string(),
        });
    }

    let request = build_patch_preflight_request(manifest, bundle)?;
    let output = runner.check_patch_preflight(clean_repo_path, &request)?;
    if !output.status.success {
        return Err(PatchPreflightError::CheckFailed {
            patch: request.patch_label(),
            conflict: command_failure_message(&output),
            output,
        });
    }

    Ok(PatchPreflightReport {
        patches: request.patches,
        output,
    })
}

/// Patch-apply step in non-mutating preflight mode.
#[must_use]
pub fn evaluate_patch_apply_preflight(
    clean_repo_path: impl AsRef<Path>,
    manifest: &BundleManifest,
    bundle: &BundleFileSystem,
    runner: &dyn PatchPreflightRunner,
) -> PipelineStepResult {
    let clean_repo_path = clean_repo_path.as_ref();
    let mut result = PipelineStepResult::new(PipelineStep::PatchApply);
    result.details = BTreeMap::from([
        (
            "repo_path".to_owned(),
            clean_repo_path.display().to_string(),
        ),
        ("mode".to_owned(), "git_apply_check_preflight".to_owned()),
    ]);

    match preflight_bundle_patches(clean_repo_path, manifest, bundle, runner) {
        Ok(report) => {
            result.status = StepStatus::Passed;
            result
                .details
                .insert("patch_count".to_owned(), report.patches.len().to_string());
            result
                .details
                .insert("patches".to_owned(), report.patches.join(","));
            record_command_output_details(&mut result, &report.output);
        }
        Err(err) => {
            if let PatchPreflightError::CheckFailed { output, .. } = &err {
                record_command_output_details(&mut result, output);
            }
            fail_result(&mut result, err.to_failure());
        }
    }

    result
}

/// Apply the bundle patches to the repository.
pub fn apply_bundle_patches(
    clean_repo_path: impl AsRef<Path>,
    manifest: &BundleManifest,
    bundle: &BundleFileSystem,
    runner: &dyn PatchApplyRunner,
    commit: bool,
) -> Result<PatchApplyReport, PatchApplyError> {
    let clean_repo_path = clean_repo_path.as_ref();
    if !clean_repo_path.is_dir() {
        return Err(PatchApplyError::RepoPathNotDirectory {
            path: clean_repo_path.display().to_string(),
        });
    }

    let request = build_patch_apply_request(manifest, bundle, commit)?;
    runner.apply_patch(clean_repo_path, &request)
}

/// Patch-apply step in mutating mode.
#[must_use]
pub fn evaluate_patch_apply(
    clean_repo_path: impl AsRef<Path>,
    manifest: &BundleManifest,
    bundle: &BundleFileSystem,
    runner: &dyn PatchApplyRunner,
    commit: bool,
) -> PipelineStepResult {
    let clean_repo_path = clean_repo_path.as_ref();
    let mut result = PipelineStepResult::new(PipelineStep::PatchApply);
    result.details = BTreeMap::from([
        (
            "repo_path".to_owned(),
            clean_repo_path.display().to_string(),
        ),
        ("mode".to_owned(), "git_apply_after_check".to_owned()),
        ("commit_requested".to_owned(), commit.to_string()),
    ]);

    match apply_bundle_patches(clean_repo_path, manifest, bundle, runner, commit) {
        Ok(report) => {
            result.status = StepStatus::Passed;
            result
                .details
                .insert("patch_count".to_owned(), report.patches.len().to_string());
            result
                .details
                .insert("patches".to_owned(), report.patches.join(","));
            result.details.insert(
                "check_status".to_owned(),
                report.check_output.status.label(),
            );
            result.details.insert(
                "apply_status".to_owned(),
                report.apply_output.status.label(),
            );
            result.details.insert(
                "committed".to_owned(),
                report.commit_output.is_some().to_string(),
            );
            if let Some(commit_output) = &report.commit_output {
                result
                    .details
                    .insert("commit_status".to_owned(), commit_output.status.label());
                result
                    .details
                    .insert("commit_stdout".to_owned(), commit_output.stdout.clone());
                result
                    .details
                    .insert("commit_stderr".to_owned(), commit_output.stderr.clone());
            }
        }
        Err(err) => {
            if let Some(output) = err.output() {
                record_command_output_details(&mut result, output);
            }
            fail_result(&mut result, err.to_failure());
        }
    }

    result
}

/// Lake re-check step. A non-zero exit or a spawn failure both reject.
#[must_use]
pub fn evaluate_lake_recheck(
    clean_repo_path: impl AsRef<Path>,
    runner: &dyn LakeRecheckRunner,
    command: &LakeRecheckCommand,
    module: Option<&str>,
) -> PipelineStepResult {
    let clean_repo_path = clean_repo_path.as_ref();
    let module = module
        .map(str::trim)
        .filter(|module| !module.is_empty())
        .unwrap_or("<project>");
    let mut result = PipelineStepResult::new(PipelineStep::LakeRecheck);
    result.details = BTreeMap::from([
        (
            "repo_path".to_owned(),
            clean_repo_path.display().to_string(),
        ),
        ("command".to_owned(), command.command_line()),
        ("module".to_owned(), module.to_owned()),
    ]);

    match runner.run_lake_recheck(clean_repo_path, command) {
        Ok(output) => {
            record_command_output_details(&mut result, &output);
            if output.status.success {
                result.status = StepStatus::Passed;
            } else {
                fail_result(
                    &mut result,
                    IngestFailure::LakeRecheckFailed {
                        module: module.to_owned(),
                        error: command_failure_message(&output),
                    },
                );
            }
        }
        Err(err) => {
            result
                .details
                .insert("command_error".to_owned(), err.to_string());
            fail_result(
                &mut result,
                IngestFailure::LakeRecheckFailed {
                    module: module.to_owned(),
                    error: err.to_string(),
                },
            );
        }
    }

    result
}

struct BundleIntegrity {
    bundle_sha256: String,
    bundle: BundleFileSystem,
    manifest: BundleManifest,
    signature: SignatureVerification,
}

fn run_bundle_integrity(
    path: &Path,
    config: &MathMapIngestConfig,
    verifier: &dyn ManifestSignatureVerifier,
) -> Result<BundleIntegrity, MathMapIngestError> {
    let bundle = BundleFileSystem::load(path, config.policy.max_bundle_bytes)?;
    ensure_layout(&bundle)?;

    let manifest_bytes = bundle
        .read("manifest.json")
        .ok_or(MathMapIngestError::MissingBundleFile("manifest.json"))?;

    // Enforce the manifest size limit before parsing or allocating derived data.
    if manifest_bytes.len() > super::keys::MAX_MANIFEST_SIZE {
        return Err(MathMapIngestError::Keys(
            TrustedKeyRegistryError::ManifestTooLarge {
                size: manifest_bytes.len(),
            },
        ));
    }

    // Verify exactly the bytes in manifest.json; do not reserialize before
    // signature checking or digest reporting.
    let manifest_text = std::str::from_utf8(manifest_bytes)?;
    let manifest: BundleManifest = serde_json::from_str(manifest_text)?;
    manifest.validate_mandatory_fields()?;
    config.policy.validate_manifest(&manifest)?;

    let service = manifest
        .service()
        .expect("manifest validation ensures service is present");
    let signature_required = config.policy.require_signature
        || config.policy.require_registered_signature
        || config.policy.require_cryptographic_signature;
    let signature =
        if signature_required {
            let signature_bytes = bundle.read("signatures/manifest.sig").ok_or(
                MathMapIngestError::MissingBundleFile("signatures/manifest.sig"),
            )?;
            let key_id_bytes = bundle.read("signatures/key_id");
            let key_id_owned: String;
            let key_id = if let Some(bytes) = key_id_bytes {
                std::str::from_utf8(bytes)?.trim()
            } else {
                // With more than one active key and no key_id in the bundle we
                // cannot tell which key the producer meant. Guessing would let an
                // attacker steer verification at whichever key they can forge for.
                let active_key_count = config
                    .trusted_keys
                    .keys
                    .iter()
                    .filter(|key| key.service == service && key.is_active_for_signatures())
                    .count();
                if active_key_count > 1 {
                    return Err(MathMapIngestError::Keys(
                        TrustedKeyRegistryError::UnregisteredKeyId {
                            service: service.to_owned(),
                            key_id:
                                "ambiguous (multiple active keys, but no key_id provided in bundle)"
                                    .to_owned(),
                        },
                    ));
                }
                key_id_owned = config
                    .trusted_keys
                    .active_key_for_service_or_error(service)?
                    .key_id
                    .clone();
                &key_id_owned
            };

            let verification = verifier.verify_manifest(
                service,
                key_id,
                manifest_bytes,
                signature_bytes,
                &config.trusted_keys,
            )?;
            if config.policy.require_registered_signature
                && !config.trusted_keys.has_active_key(
                    &verification.service,
                    &verification.key_id,
                    &verification.algorithm,
                )
            {
                return Err(TrustedKeyRegistryError::UnregisteredSignature {
                    service: verification.service,
                    key_id: verification.key_id,
                }
                .into());
            }
            if config.policy.require_cryptographic_signature && !verification.cryptographic {
                return Err(PolicyViolation::NonCryptographicSignature {
                    service: service.to_owned(),
                }
                .into());
            }
            verification
        } else {
            SignatureVerification {
                service: service.to_owned(),
                key_id: "signature-policy-disabled".to_owned(),
                algorithm: "none".to_owned(),
                cryptographic: false,
                verifier: "signature-policy-disabled".to_owned(),
            }
        };

    if config.policy.require_patch_hashes {
        verify_patch_hashes(&bundle, &manifest)?;
    }
    verify_optional_digest(
        &bundle,
        "prompt_digest",
        manifest.prompt_digest.as_deref(),
        "prompt",
    )?;
    verify_optional_digest(
        &bundle,
        "solver_artifacts_digest",
        manifest.solver_artifacts_digest.as_deref(),
        "solver_artifacts",
    )?;

    let patch_texts = manifest
        .patches
        .iter()
        .filter_map(|patch| patch.path.as_deref())
        .filter_map(|path| bundle.read(path))
        .map(String::from_utf8_lossy)
        .collect::<Vec<_>>();
    config
        .policy
        .validate_patch_imports(patch_texts.iter().map(AsRef::as_ref))?;

    Ok(BundleIntegrity {
        bundle_sha256: bundle.source_sha256().to_owned(),
        bundle,
        manifest,
        signature,
    })
}

fn math_map_bundle_logical_name(job_id: &str) -> String {
    format!("math_map-{job_id}.{MATH_MAP_BUNDLE_ARTIFACT_FORMAT}")
}

fn build_blocked_attempt(
    store_root: &Path,
    integrity: &BundleIntegrity,
    report: &MathMapIngestReport,
) -> MathverseResult<ProofAttempt> {
    let goal_hash = deterministic_blake3_hex(&MathMapGoalHashEnvelope {
        schema_version: MATH_MAP_INGEST_SCHEMA_VERSION,
        service: integrity.manifest.service.as_deref(),
        target_repo: &integrity.manifest.target_repo,
        targets: &integrity.manifest.targets,
        patches: &integrity.manifest.patches,
    });
    let trust_audit_hash = deterministic_blake3_hex(&MathMapAuditHashEnvelope {
        schema_version: MATH_MAP_INGEST_SCHEMA_VERSION,
        artifact_kind: MATH_MAP_ARTIFACT_KIND,
        bundle_sha256: &integrity.bundle_sha256,
        job_id: report.job_id.as_deref(),
        service: report.service.as_deref(),
        status: &report.status,
        steps: &report.steps,
        signature: report.signature.as_ref(),
    });
    let reason = match &report.status {
        IngestStatus::Blocked { reason } => format!("math-map ingest blocked: {reason}"),
        IngestStatus::Rejected { reason, .. } => reason.clone(),
        IngestStatus::Accepted => "math-map ingest accepted".to_owned(),
    };
    let env = EnvFingerprint::capture(store_root)?;
    let metadata = attempt_metadata_for_report(report);
    // This ingest path never mints an accepted attempt: the full Lake-backed
    // pipeline is not wired, so the row is always recorded as rejected.
    let mut attempt = ProofAttempt::new(
        goal_hash,
        AttemptStatus::Rejected { reason },
        trust_audit_hash,
        env,
    );
    attempt.authority_gate = metadata.authority_gate;
    attempt.failure_mode = metadata.failure_mode;
    attempt.trust_level = metadata.trust_level;
    attempt.solver_artifact = Some(attempt_log::put_artifact(
        store_root,
        &encode_bundle_artifact(&integrity.bundle),
        Some(ArtifactKind::MathMapLeanPatch.as_str()),
        Some(&math_map_bundle_logical_name(
            integrity
                .manifest
                .job_id()
                .expect("validated MathMap manifest has job_id"),
        )),
    )?);
    attempt.model_response = encode_prefix_artifact(&integrity.bundle, "prompt")
        .map(|bytes| {
            attempt_log::put_artifact(
                store_root,
                &bytes,
                Some(MATH_MAP_MODEL_RESPONSE_ARTIFACT_KIND),
                Some("math_map-prompt.clean-prefix-v1"),
            )
        })
        .transpose()?;
    Ok(attempt)
}

#[derive(Serialize)]
struct MathMapGoalHashEnvelope<'a> {
    schema_version: &'static str,
    service: Option<&'a str>,
    target_repo: &'a super::manifest::TargetRepo,
    targets: &'a [super::manifest::BundleTarget],
    patches: &'a [super::manifest::PatchEntry],
}

#[derive(Serialize)]
struct MathMapAuditHashEnvelope<'a> {
    schema_version: &'static str,
    artifact_kind: &'static str,
    bundle_sha256: &'a str,
    job_id: Option<&'a str>,
    service: Option<&'a str>,
    status: &'a IngestStatus,
    steps: &'a [PipelineStepResult],
    signature: Option<&'a SignatureVerification>,
}

fn deterministic_blake3_hex(value: &impl Serialize) -> String {
    let bytes =
        serde_json::to_vec(value).expect("MathMap audit envelope serialization is infallible");
    blake3::hash(&bytes).to_hex().to_string()
}

fn encode_bundle_artifact(bundle: &BundleFileSystem) -> Vec<u8> {
    encode_files_artifact(
        MATH_MAP_BUNDLE_ARTIFACT_FORMAT,
        "bundle",
        bundle
            .files()
            .iter()
            .map(|(path, bytes)| (path.as_str(), bytes.as_slice())),
    )
}

fn encode_prefix_artifact(bundle: &BundleFileSystem, prefix: &str) -> Option<Vec<u8>> {
    let files = bundle.files_under(prefix);
    if files.is_empty() {
        return None;
    }
    Some(encode_files_artifact(
        "clean-math_map-prefix-v1",
        prefix,
        files,
    ))
}

fn encode_files_artifact<'a>(
    format: &str,
    label: &str,
    files: impl IntoIterator<Item = (&'a str, &'a [u8])>,
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(format.as_bytes());
    out.extend_from_slice(b"\nlabel ");
    out.extend_from_slice(label.as_bytes());
    out.extend_from_slice(b"\n");
    for (path, bytes) in files {
        out.extend_from_slice(b"path ");
        out.extend_from_slice(path.as_bytes());
        out.extend_from_slice(b"\nlen ");
        out.extend_from_slice(bytes.len().to_string().as_bytes());
        out.extend_from_slice(b"\n");
        out.extend_from_slice(bytes);
        out.extend_from_slice(b"\nend\n");
    }
    out
}

const fn attempt_status_name(status: &AttemptStatus) -> &'static str {
    match status {
        AttemptStatus::Accepted => "accepted",
        AttemptStatus::Rejected { .. } => "rejected",
        AttemptStatus::Timeout { .. } => "timeout",
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AttemptMetadata {
    authority_gate: Option<String>,
    failure_mode: Option<String>,
    trust_level: Option<TrustLevel>,
}

fn attempt_metadata_for_report(report: &MathMapIngestReport) -> AttemptMetadata {
    let source_step = match &report.status {
        IngestStatus::Rejected { step, .. } => Some(*step),
        IngestStatus::Blocked { .. } => report
            .steps
            .iter()
            .find(|result| {
                result.step == PipelineStep::FalseControlRerun
                    && (matches!(
                        result.failure,
                        Some(IngestFailure::StageNotImplemented { .. })
                    ) || result
                        .details
                        .get("false_control_report_supplied")
                        .is_some_and(|supplied| supplied == "false"))
            })
            .or_else(|| {
                report.steps.iter().find(|result| {
                    matches!(
                        result.failure,
                        Some(IngestFailure::StageNotImplemented { .. })
                    )
                })
            })
            .map(|result| result.step),
        IngestStatus::Accepted => None,
    };
    let failure_mode = match &report.status {
        IngestStatus::Accepted => None,
        IngestStatus::Rejected { step, .. } => report
            .steps
            .iter()
            .find(|result| result.step == *step)
            .and_then(|result| result.failure.as_ref())
            .map(failure_mode_name)
            .or_else(|| Some("rejected".to_owned())),
        IngestStatus::Blocked { .. } => source_step
            .and_then(|step| {
                let result = report.steps.iter().find(|result| result.step == step)?;
                result.failure.as_ref().map(failure_mode_name).or_else(|| {
                    (result.step == PipelineStep::FalseControlRerun
                        && result
                            .details
                            .get("false_control_report_supplied")
                            .is_some_and(|supplied| supplied == "false"))
                    .then(|| "false_control_rerun_missing".to_owned())
                })
            })
            .or_else(|| Some("blocked".to_owned())),
    };

    AttemptMetadata {
        authority_gate: source_step
            .map(attempt_authority_gate_name)
            .or_else(|| Some("math_map_ingest".to_owned())),
        failure_mode,
        trust_level: trust_level_for_report(report),
    }
}

fn attempt_authority_gate_name(step: PipelineStep) -> String {
    match step {
        PipelineStep::DriftStatementPreservation => "statement_preservation".to_owned(),
        PipelineStep::TrustAudit => "trust_audit".to_owned(),
        step => step.name().to_owned(),
    }
}

fn failure_mode_name(failure: &IngestFailure) -> String {
    match failure {
        IngestFailure::BundleIntegrityFailed { .. } => "bundle_integrity_failed",
        IngestFailure::EnvironmentPinFailed { .. } => "environment_pin_failed",
        IngestFailure::BaselineFailed { .. } => "baseline_failed",
        IngestFailure::PatchApplyFailed { .. } => "patch_apply_failed",
        IngestFailure::LakeRecheckFailed { .. } => "lake_recheck_failed",
        IngestFailure::TargetStatementMismatch { .. } => "target_statement_mismatch",
        IngestFailure::DriftRejected { .. } => "drift_rejected",
        IngestFailure::TrustAuditRejected { .. } => "trust_audit_rejected",
        IngestFailure::JobIdAlreadyIngested { .. } => "job_id_already_ingested",
        IngestFailure::StatementPreservationUnavailable { .. } => {
            "statement_preservation_unavailable"
        }
        IngestFailure::FalseControlRegressed { .. } => "false_control_regressed",
        IngestFailure::PolicyRejected { .. } => "policy_rejected",
        IngestFailure::SignatureRejected { .. } => "signature_rejected",
        IngestFailure::StageNotImplemented { .. } => "stage_not_implemented",
    }
    .to_owned()
}

fn trust_level_for_report(report: &MathMapIngestReport) -> Option<TrustLevel> {
    report
        .steps
        .iter()
        .find(|result| result.step == PipelineStep::TrustAudit)
        .and_then(|result| result.details.get("post_worst_trust_level"))
        .and_then(|level| trust_level_from_name(level))
}

fn worst_reported_trust_level(report: &AuditReport) -> Option<TrustLevel> {
    report
        .by_trust_level
        .iter()
        .filter(|(_, count)| **count > 0)
        .map(|(level, _)| *level)
        .max()
}

const fn trust_level_name(level: TrustLevel) -> &'static str {
    match level {
        TrustLevel::KernelVerified => "KernelVerified",
        TrustLevel::AxiomDependent => "AxiomDependent",
        TrustLevel::CertificateReplayed => "CertificateReplayed",
        TrustLevel::PartiallyAxiomatized => "PartiallyAxiomatized",
        TrustLevel::TrustedOracle => "TrustedOracle",
    }
}

fn trust_level_from_name(level: &str) -> Option<TrustLevel> {
    match level {
        "KernelVerified" => Some(TrustLevel::KernelVerified),
        "AxiomDependent" => Some(TrustLevel::AxiomDependent),
        "CertificateReplayed" => Some(TrustLevel::CertificateReplayed),
        "PartiallyAxiomatized" => Some(TrustLevel::PartiallyAxiomatized),
        "TrustedOracle" => Some(TrustLevel::TrustedOracle),
        _ => None,
    }
}

fn ensure_layout(bundle: &BundleFileSystem) -> Result<(), MathMapIngestError> {
    if !bundle.contains_file("manifest.json") {
        return Err(MathMapIngestError::MissingBundleFile("manifest.json"));
    }
    if !bundle.has_prefix("patch") {
        return Err(MathMapIngestError::MissingBundleFile("patch/"));
    }
    if !bundle.has_prefix("signatures") {
        return Err(MathMapIngestError::MissingBundleFile("signatures/"));
    }
    Ok(())
}

fn verify_patch_hashes(
    bundle: &BundleFileSystem,
    manifest: &BundleManifest,
) -> Result<(), MathMapIngestError> {
    for patch in &manifest.patches {
        let path = patch
            .path
            .as_deref()
            .expect("manifest validation ensures patch path is present");
        let expected = normalize_sha256(
            patch
                .sha256
                .as_deref()
                .expect("manifest validation ensures patch sha256 is present"),
        );
        let bytes = bundle
            .read(path)
            .ok_or_else(|| MathMapIngestError::MissingPatch(path.to_owned()))?;
        let actual = sha256_hex(bytes);
        if expected != actual {
            return Err(MathMapIngestError::PatchHashMismatch {
                path: path.to_owned(),
                expected,
                actual,
            });
        }
    }
    Ok(())
}

fn verify_optional_digest(
    bundle: &BundleFileSystem,
    field: &'static str,
    expected: Option<&str>,
    prefix: &str,
) -> Result<(), MathMapIngestError> {
    let Some(expected) = expected else {
        return Ok(());
    };
    // A declared digest over an absent tree must not silently pass: fall back
    // to the empty-input digest so the comparison fails unless the producer
    // genuinely declared "empty".
    let actual = bundle
        .blake3_digest_for_prefix(prefix)
        .unwrap_or_else(|| format!("blake3:{}", blake3::hash(&[]).to_hex()));
    if normalize_digest(expected) != actual {
        return Err(MathMapIngestError::DigestMismatch {
            field,
            expected: expected.to_owned(),
            actual,
        });
    }
    Ok(())
}

fn normalize_sha256(value: &str) -> String {
    value
        .trim()
        .strip_prefix("sha256:")
        .unwrap_or_else(|| value.trim())
        .to_ascii_lowercase()
}

fn normalize_digest(value: &str) -> String {
    let trimmed = value.trim();
    if trimmed.contains(':') {
        trimmed.to_ascii_lowercase()
    } else {
        format!("blake3:{}", trimmed.to_ascii_lowercase())
    }
}

fn run_command_capture<I, S>(
    cwd: &Path,
    program: &str,
    args: I,
    stdin: Option<&[u8]>,
) -> Result<MathMapCommandOutput, MathMapCommandError>
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let args = args
        .into_iter()
        .map(|arg| arg.as_ref().to_owned())
        .collect::<Vec<_>>();
    let mut command = Command::new(program);
    command.args(&args).current_dir(cwd);

    let output = if let Some(stdin_bytes) = stdin {
        let mut child = command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|err| MathMapCommandError::Io {
                program: program.to_owned(),
                cwd: cwd.display().to_string(),
                message: err.to_string(),
            })?;
        {
            let mut child_stdin = child
                .stdin
                .take()
                .ok_or_else(|| MathMapCommandError::Stdin {
                    program: program.to_owned(),
                    cwd: cwd.display().to_string(),
                    message: "child stdin was not available".to_owned(),
                })?;
            child_stdin
                .write_all(stdin_bytes)
                .map_err(|err| MathMapCommandError::Stdin {
                    program: program.to_owned(),
                    cwd: cwd.display().to_string(),
                    message: err.to_string(),
                })?;
        }
        child
            .wait_with_output()
            .map_err(|err| MathMapCommandError::Io {
                program: program.to_owned(),
                cwd: cwd.display().to_string(),
                message: err.to_string(),
            })?
    } else {
        command
            .stdin(Stdio::null())
            .output()
            .map_err(|err| MathMapCommandError::Io {
                program: program.to_owned(),
                cwd: cwd.display().to_string(),
                message: err.to_string(),
            })?
    };

    Ok(MathMapCommandOutput::from_process_output(output))
}

fn record_command_output_details(result: &mut PipelineStepResult, output: &MathMapCommandOutput) {
    result
        .details
        .insert("status".to_owned(), output.status.label());
    result.details.insert(
        "status_code".to_owned(),
        output
            .status
            .code
            .map(|code| code.to_string())
            .unwrap_or_else(|| "<signal>".to_owned()),
    );
    result
        .details
        .insert("stdout".to_owned(), output.stdout.clone());
    result
        .details
        .insert("stderr".to_owned(), output.stderr.clone());
}

fn command_failure_message(output: &MathMapCommandOutput) -> String {
    let stderr = output.stderr.trim();
    if !stderr.is_empty() {
        return stderr.to_owned();
    }
    let stdout = output.stdout.trim();
    if !stdout.is_empty() {
        return stdout.to_owned();
    }
    format!("command exited with {}", output.status.label())
}

fn fail_result(result: &mut PipelineStepResult, failure: IngestFailure) {
    result.status = StepStatus::Failed;
    result.failure = Some(failure);
}

fn first_rejection(steps: &[&PipelineStepResult]) -> Option<IngestStatus> {
    steps.iter().find_map(|step| {
        step.failure.as_ref().map(|failure| IngestStatus::Rejected {
            step: step.step,
            reason: failure_reason(failure),
        })
    })
}

fn rejected_statement_drift(report: &DriftReport) -> Option<String> {
    match report {
        DriftReport::NameDropped(name) => Some(format!("name dropped: {name}")),
        DriftReport::NameAdded(_) => None,
        DriftReport::StatementChanged { name, kind, .. } => {
            Some(format!("statement changed ({kind:?}): {name}"))
        }
        DriftReport::UniverseChanged { name, .. } => {
            Some(format!("universe signature changed: {name}"))
        }
        DriftReport::ImportsChanged {
            name,
            added,
            removed,
        } => Some(format!(
            "imports changed for {name}: added {}, removed {}",
            names_csv(added),
            names_csv(removed)
        )),
        DriftReport::HypothesesChanged { name, .. } => Some(format!("hypotheses changed: {name}")),
    }
}

fn names_csv(names: &[clean_kernel::Name]) -> String {
    if names.is_empty() {
        return "<none>".to_owned();
    }
    names
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

impl MathMapIngestReport {
    fn new(path: &Path) -> Self {
        Self {
            schema_version: MATH_MAP_INGEST_SCHEMA_VERSION.to_owned(),
            artifact_kind: MATH_MAP_ARTIFACT_KIND.to_owned(),
            bundle_path: path.display().to_string(),
            bundle_sha256: None,
            job_id: None,
            service: None,
            status: IngestStatus::Blocked {
                reason: "pipeline has not run".to_owned(),
            },
            steps: PipelineStep::all()
                .iter()
                .map(|step| PipelineStepResult::new(*step))
                .collect(),
            authority_gates: None,
            signature: None,
            proof_attempt: None,
        }
    }

    fn record_integrity(&mut self, integrity: &BundleIntegrity) {
        self.bundle_sha256 = Some(integrity.bundle_sha256.clone());
        self.job_id = integrity.manifest.job_id().map(ToOwned::to_owned);
        self.service = integrity.manifest.service().map(ToOwned::to_owned);
        self.signature = Some(integrity.signature.clone());
        self.pass_step(
            PipelineStep::BundleIntegrity,
            BTreeMap::from([
                (
                    "patch_count".to_owned(),
                    integrity.manifest.patches.len().to_string(),
                ),
                (
                    "target_count".to_owned(),
                    integrity.manifest.targets.len().to_string(),
                ),
            ]),
        );
    }

    fn pass_step(&mut self, step: PipelineStep, details: BTreeMap<String, String>) {
        if let Some(result) = self.steps.iter_mut().find(|result| result.step == step) {
            result.status = StepStatus::Passed;
            result.failure = None;
            result.details = details;
        }
    }

    fn fail_step(&mut self, step: PipelineStep, failure: IngestFailure) {
        if let Some(result) = self.steps.iter_mut().find(|result| result.step == step) {
            result.status = StepStatus::Failed;
            result.failure = Some(failure);
        }
    }

    fn skip_step(&mut self, step: PipelineStep, failure: IngestFailure) {
        if let Some(result) = self.steps.iter_mut().find(|result| result.step == step) {
            result.status = StepStatus::Skipped;
            result.failure = Some(failure);
        }
    }

    fn replace_step(&mut self, step: PipelineStepResult) {
        if let Some(result) = self
            .steps
            .iter_mut()
            .find(|result| result.step == step.step)
        {
            *result = step;
        }
    }

    fn apply_inputs(&mut self, integrity: &BundleIntegrity, inputs: MathMapIngestInputs<'_>) {
        let local_checks_supplied = inputs.local_checks.is_some();
        let authority_gates_supplied = inputs.authority_gates.is_some();
        let local_false_control_rerun = inputs
            .local_checks
            .and_then(|checks| checks.false_control_rerun);
        if let Some(local_checks) = inputs.local_checks {
            self.apply_local_checks(integrity, local_checks, !authority_gates_supplied);
        }
        if let Some(mut authority_inputs) = inputs.authority_gates {
            if authority_inputs.false_control_rerun.is_none() {
                authority_inputs.false_control_rerun = local_false_control_rerun;
            }
            let authority_gates = evaluate_authority_gates(&integrity.manifest, authority_inputs);
            self.apply_authority_gates(authority_gates);
        }
        if local_checks_supplied {
            self.refresh_status_after_local_inputs(authority_gates_supplied);
        }
    }

    fn apply_local_checks(
        &mut self,
        integrity: &BundleIntegrity,
        local_checks: MathMapLocalCheckInputs<'_>,
        run_false_control_rerun: bool,
    ) {
        if let Some(environment_pin) = local_checks.environment_pin {
            let mut step = evaluate_environment_pin(
                local_checks.clean_repo_path,
                &integrity.manifest,
                environment_pin.runner,
            );
            step.details.insert(
                "input_source".to_owned(),
                "caller_supplied_local_environment_pin".to_owned(),
            );
            let failed = step.status == StepStatus::Failed;
            self.replace_step(step);
            // A failed environment pin stops the sequence: nothing may be
            // applied to a repository that is not at the declared revision.
            if failed {
                return;
            }
        }

        let mut baseline_step = evaluate_pre_patch_baseline_unavailable(
            "pre-patch baseline is unavailable; no baseline runner is wired into local ingest",
        );
        baseline_step
            .details
            .insert("input_source".to_owned(), "local_ingest".to_owned());
        self.replace_step(baseline_step);

        if let Some(patch_apply) = local_checks.patch_apply {
            let mut step = evaluate_patch_apply(
                local_checks.clean_repo_path,
                &integrity.manifest,
                &integrity.bundle,
                patch_apply.runner,
                patch_apply.commit,
            );
            step.details.insert(
                "input_source".to_owned(),
                "caller_supplied_local_patch_apply".to_owned(),
            );
            let failed = step.status == StepStatus::Failed;
            self.replace_step(step);
            if failed {
                return;
            }
        } else if let Some(patch_preflight) = local_checks.patch_preflight {
            let mut step = evaluate_patch_apply_preflight(
                local_checks.clean_repo_path,
                &integrity.manifest,
                &integrity.bundle,
                patch_preflight.runner,
            );
            step.details.insert(
                "input_source".to_owned(),
                "caller_supplied_local_preflight".to_owned(),
            );
            self.replace_step(step);
        }
        if let Some(lake_recheck) = local_checks.lake_recheck {
            let mut step = evaluate_lake_recheck(
                local_checks.clean_repo_path,
                lake_recheck.runner,
                lake_recheck.command,
                lake_recheck.module,
            );
            step.details.insert(
                "input_source".to_owned(),
                "caller_supplied_local_recheck".to_owned(),
            );
            self.replace_step(step);
        }
        if run_false_control_rerun {
            if let Some(false_control_rerun) = local_checks.false_control_rerun {
                let mut step = evaluate_false_control_rerun_gate(Some(false_control_rerun));
                step.details.insert(
                    "input_source".to_owned(),
                    step.details
                        .get("false_control_report_source")
                        .cloned()
                        .unwrap_or_else(|| "local_checks".to_owned()),
                );
                self.replace_step(step);
            }
        }
    }

    fn refresh_status_after_local_inputs(&mut self, authority_gates_supplied: bool) {
        if let Some(failed_step) = self
            .steps
            .iter()
            .find(|step| step.status == StepStatus::Failed && step.failure.is_some())
        {
            let failure = failed_step
                .failure
                .as_ref()
                .expect("checked failure presence");
            self.status = IngestStatus::Rejected {
                step: failed_step.step,
                reason: failure_reason(failure),
            };
            return;
        }

        let false_control_rerun_passed = self.steps.iter().any(|step| {
            step.step == PipelineStep::FalseControlRerun && step.status == StepStatus::Passed
        });
        let reason = if authority_gates_supplied && false_control_rerun_passed {
            "caller-supplied patch/Lake primitives, authority gates, and false-control rerun passed, but the full ingest path still has unwired environment/baseline stages"
        } else if authority_gates_supplied {
            "caller-supplied patch/Lake primitives and authority gates passed, but the full ingest path still has unwired environment/baseline/false-control stages"
        } else {
            "caller-supplied patch/Lake primitives ran, but authority gates and false-control rerun were not run by this ingest path"
        };
        self.status = IngestStatus::Blocked {
            reason: reason.to_owned(),
        };
    }

    fn apply_authority_gates(&mut self, mut authority_gates: MathMapAuthorityGateReport) {
        authority_gates
            .statement_preservation
            .details
            .insert("input_source".to_owned(), "caller_supplied".to_owned());
        authority_gates
            .trust_audit
            .details
            .insert("input_source".to_owned(), "caller_supplied".to_owned());
        let false_control_input_source = authority_gates
            .false_control_rerun
            .details
            .get("false_control_report_source")
            .cloned()
            .unwrap_or_else(|| {
                if authority_gates
                    .false_control_rerun
                    .details
                    .get("false_control_report_supplied")
                    .is_some_and(|supplied| supplied == "true")
                {
                    "caller_supplied".to_owned()
                } else {
                    "missing".to_owned()
                }
            });
        authority_gates
            .false_control_rerun
            .details
            .insert("input_source".to_owned(), false_control_input_source);

        self.replace_step(authority_gates.statement_preservation.clone());
        self.replace_step(authority_gates.trust_audit.clone());
        self.replace_step(authority_gates.false_control_rerun.clone());
        // Accepted authority gates still do not accept the ingest: the
        // environment/baseline/patch/Lake stages were not run here.
        self.status = match &authority_gates.status {
            IngestStatus::Rejected { .. } => authority_gates.status.clone(),
            IngestStatus::Accepted => IngestStatus::Blocked {
                reason: "authority gates and false-control rerun accepted, but Lake-backed pipeline stages were not run by this ingest path".to_owned(),
            },
            IngestStatus::Blocked { reason } => IngestStatus::Blocked {
                reason: format!(
                    "{reason}; environment/baseline/patch/Lake stages were not run by this ingest path"
                ),
            },
        };
        self.authority_gates = Some(authority_gates);
    }

    fn block_after_integrity(&mut self) {
        for step in PipelineStep::after_integrity() {
            self.skip_step(
                *step,
                IngestFailure::StageNotImplemented {
                    stage: step.name().to_owned(),
                },
            );
        }
        let reason =
            "bundle integrity passed; Lake/drift/audit/false-control gates require caller-supplied evidence"
                .to_owned();
        self.status = IngestStatus::Blocked { reason };
    }
}

impl PipelineStepResult {
    fn new(step: PipelineStep) -> Self {
        Self {
            number: step.number(),
            step,
            name: step.name().to_owned(),
            status: StepStatus::NotRun,
            failure: None,
            details: BTreeMap::new(),
        }
    }
}

impl PipelineStep {
    /// Every pipeline step, in execution order.
    #[must_use]
    pub fn all() -> &'static [Self; 9] {
        &[
            Self::BundleIntegrity,
            Self::EnvironmentPin,
            Self::PrePatchBaseline,
            Self::PatchApply,
            Self::LakeRecheck,
            Self::DriftStatementPreservation,
            Self::TrustAudit,
            Self::FalseControlRerun,
            Self::WriteProofAttempt,
        ]
    }

    /// Every step after bundle integrity, in execution order.
    #[must_use]
    pub fn after_integrity() -> &'static [Self; 8] {
        &[
            Self::EnvironmentPin,
            Self::PrePatchBaseline,
            Self::PatchApply,
            Self::LakeRecheck,
            Self::DriftStatementPreservation,
            Self::TrustAudit,
            Self::FalseControlRerun,
            Self::WriteProofAttempt,
        ]
    }

    /// One-based step number.
    #[must_use]
    pub const fn number(self) -> u8 {
        match self {
            Self::BundleIntegrity => 1,
            Self::EnvironmentPin => 2,
            Self::PrePatchBaseline => 3,
            Self::PatchApply => 4,
            Self::LakeRecheck => 5,
            Self::DriftStatementPreservation => 6,
            Self::TrustAudit => 7,
            Self::FalseControlRerun => 8,
            Self::WriteProofAttempt => 9,
        }
    }

    /// Stable step name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::BundleIntegrity => "bundle_integrity",
            Self::EnvironmentPin => "environment_pin",
            Self::PrePatchBaseline => "pre_patch_baseline",
            Self::PatchApply => "patch_apply",
            Self::LakeRecheck => "lake_recheck",
            Self::DriftStatementPreservation => "drift_statement_preservation",
            Self::TrustAudit => "trust_audit",
            Self::FalseControlRerun => "false_control_rerun",
            Self::WriteProofAttempt => "write_proof_attempt",
        }
    }
}

impl MathMapIngestError {
    fn to_failure(&self) -> IngestFailure {
        match self {
            Self::Policy(err) => IngestFailure::PolicyRejected {
                reason: err.to_string(),
            },
            Self::Keys(err) => IngestFailure::SignatureRejected {
                reason: err.to_string(),
            },
            Self::ManifestValidation(
                ManifestValidationError::MissingMandatoryField { field }
                | ManifestValidationError::EmptyMandatoryField { field },
            ) => IngestFailure::BundleIntegrityFailed {
                field: (*field).to_owned(),
            },
            Self::ManifestValidation(err) => IngestFailure::BundleIntegrityFailed {
                field: err.to_string(),
            },
            Self::PatchHashMismatch {
                path,
                expected,
                actual,
            } => IngestFailure::BundleIntegrityFailed {
                field: format!("patches[{path}].sha256 expected {expected} actual {actual}"),
            },
            Self::DigestMismatch {
                field,
                expected,
                actual,
            } => IngestFailure::BundleIntegrityFailed {
                field: format!("{field} expected {expected} actual {actual}"),
            },
            err => IngestFailure::BundleIntegrityFailed {
                field: err.to_string(),
            },
        }
    }
}

fn failure_reason(failure: &IngestFailure) -> String {
    match failure {
        IngestFailure::BundleIntegrityFailed { field } => {
            format!("bundle integrity failed at {field}")
        }
        IngestFailure::PolicyRejected { reason }
        | IngestFailure::SignatureRejected { reason }
        | IngestFailure::EnvironmentPinFailed { reason }
        | IngestFailure::BaselineFailed { reason } => reason.clone(),
        IngestFailure::PatchApplyFailed { patch, conflict } => {
            format!("patch `{patch}` failed to apply: {conflict}")
        }
        IngestFailure::LakeRecheckFailed { module, error } => {
            format!("Lake recheck failed in module `{module}`: {error}")
        }
        IngestFailure::TargetStatementMismatch {
            theorem,
            expected,
            actual,
        } => {
            format!(
                "target `{theorem}` statement hash mismatch: expected {expected}, actual {actual}"
            )
        }
        IngestFailure::DriftRejected { drifts } => format!("drift rejected: {drifts:?}"),
        IngestFailure::TrustAuditRejected { reasons } => {
            format!("trust audit rejected: {reasons:?}")
        }
        IngestFailure::JobIdAlreadyIngested { job_id } => {
            format!("MathMap job_id `{job_id}` has already been ingested")
        }
        IngestFailure::StatementPreservationUnavailable { reason } => reason.clone(),
        IngestFailure::FalseControlRegressed { control } => {
            format!("false control regressed: {control}")
        }
        IngestFailure::StageNotImplemented { stage } => {
            format!("pipeline stage `{stage}` is not implemented")
        }
    }
}
