// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Local ingest of UNTRUSTED MathMap/Harmonic Lean patch bundles.
//!
//! A MathMap bundle is a signed envelope produced by an external service: a
//! `manifest.json`, a `patch/` tree, a `signatures/` tree, and optional
//! `prompt/` and `solver_artifacts/` trees. Nothing in it is trusted. This
//! module implements the fail-closed pipeline that decides whether such a
//! bundle may be applied:
//!
//! | module | responsibility |
//! |---|---|
//! | [`bundle`] | decode the archive/directory safely, bounded and path-checked |
//! | [`manifest`] | strict manifest schema + mandatory-field validation |
//! | [`policy`] | operator-controlled allow/deny/age/size policy |
//! | [`keys`] | trusted-key policy + Ed25519 manifest signature verification |
//! | [`trust_audit_gate`] | declared-trust vs observed audit-delta policy |
//! | [`ingest`] | the pipeline and its authority gates |
//!
//! Every default is a refusal: see the fail-closed contract documented on
//! [`ingest`].

pub mod bundle;
pub mod ingest;
pub mod keys;
pub mod manifest;
pub mod policy;
pub mod trust_audit_gate;

#[cfg(test)]
mod tests;

pub use bundle::{BundleFileSystem, BundleLoadError};
pub use ingest::{
    apply_bundle_patches, build_environment_pin_request, build_patch_apply_request,
    build_patch_preflight_request, evaluate_authority_gates, evaluate_environment_pin,
    evaluate_false_control_rerun_gate, evaluate_lake_recheck, evaluate_patch_apply,
    evaluate_patch_apply_preflight, evaluate_pre_patch_baseline_unavailable,
    evaluate_statement_preservation_gate, evaluate_trust_audit_pipeline_gate, ingest_bundle,
    ingest_bundle_to_attempt_log, ingest_bundle_to_attempt_log_with_inputs,
    ingest_bundle_with_inputs, ingest_bundle_with_verifier, ingest_bundle_with_verifier_and_inputs,
    ingest_bundle_with_verifier_to_attempt_log,
    ingest_bundle_with_verifier_to_attempt_log_and_inputs, preflight_bundle_patches,
    validate_environment_pin, EnvironmentPinError, EnvironmentPinObservation, EnvironmentPinReport,
    EnvironmentPinRequest, EnvironmentPinRunner, GitApplyCheckRunner, GitEnvironmentPinRunner,
    GitPatchApplyRunner, IngestFailure, IngestStatus, LakeRecheckCommand, LakeRecheckRunner,
    MathMapAuthorityGateInputs, MathMapAuthorityGateReport, MathMapCommandError,
    MathMapCommandOutput, MathMapCommandStatus, MathMapEnvironmentPinInputs,
    MathMapFalseControlRerunInput, MathMapIngestConfig, MathMapIngestInputs, MathMapIngestReport,
    MathMapLakeRecheckInputs, MathMapLocalCheckInputs, MathMapPatchApplyInputs,
    MathMapPatchPreflightInputs, MathMapProofAttemptStub, MathMapTrustAuditGateInput,
    PatchApplyError, PatchApplyReport, PatchApplyRequest, PatchApplyRunner, PatchPreflightError,
    PatchPreflightReport, PatchPreflightRequest, PatchPreflightRunner, PipelineStep,
    PipelineStepResult, ProcessLakeRecheckRunner, StepStatus,
};
pub use keys::{
    Ed25519SignatureVerifier, ManifestSignatureVerifier, SignatureVerification, TrustedKey,
    TrustedKeyRegistry, TrustedKeyRegistryError, TrustedKeyRegistryValidationError,
};
pub use manifest::{
    BundleManifest, BundleTarget, DeclaredTrust, ManifestValidationError, PatchEntry, TargetRepo,
};
pub use policy::{MathMapPolicy, PolicyLoadError, PolicyViolation};
pub use trust_audit_gate::{evaluate_trust_audit_gate, TrustAuditGateDecision};

/// Ingest contract version.
pub const MATH_MAP_INGEST_SCHEMA_VERSION: &str = "clean-math_map-ingest-v1";
/// Attempt-log artifact kind for an ingested patch bundle.
pub const MATH_MAP_ARTIFACT_KIND: &str = "math_map_lean_patch";
/// Serialized-bundle artifact format tag.
pub const MATH_MAP_BUNDLE_ARTIFACT_FORMAT: &str = "clean-math_map-bundle-v1";
/// Attempt-log artifact kind for the producer's model response / prompt tree.
pub const MATH_MAP_MODEL_RESPONSE_ARTIFACT_KIND: &str = "math_map_model_response";
/// Replay-adapter identifier for MathMap Lean patches.
pub const MATH_MAP_REPLAY_ADAPTER_ID: &str = "math_map-lean-patch-v1";
/// Source-system label for MathMap-produced evidence.
pub const MATH_MAP_SOURCE_SYSTEM: &str = "math_map";
/// Domain profile MathMap bundles target.
pub const MATH_MAP_DOMAIN_PROFILE: &str = "lean";
/// The policy compiled into the binary.
pub const DEFAULT_POLICY_TOML: &str = include_str!("policy.toml");
/// The trusted-key registry compiled into the binary.
pub const DEFAULT_TRUSTED_KEYS_TOML: &str = include_str!("trusted_keys.toml");

/// Artifact kinds this ingest path produces.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum ArtifactKind {
    /// A MathMap Lean patch bundle.
    MathMapLeanPatch,
}

impl ArtifactKind {
    /// Stable artifact-kind string.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MathMapLeanPatch => MATH_MAP_ARTIFACT_KIND,
        }
    }
}

/// Static description of the MathMap replay adapter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MathMapReplayAdapterDescriptor {
    /// Stable adapter identifier.
    pub adapter_id: &'static str,
    /// Domain profile the adapter targets.
    pub domain_profile: &'static str,
    /// Source system the adapter ingests from.
    pub source_system: &'static str,
    /// Artifact kind the adapter consumes.
    pub artifact_kind: ArtifactKind,
    /// Artifact format tag.
    pub artifact_format: &'static str,
    /// Replay contract version.
    pub replay_contract: &'static str,
}

impl MathMapReplayAdapterDescriptor {
    /// Stable artifact-kind string for this adapter.
    #[must_use]
    pub const fn artifact_kind_name(self) -> &'static str {
        self.artifact_kind.as_str()
    }
}

/// The MathMap Lean patch replay adapter.
pub const MATH_MAP_LEAN_PATCH_REPLAY_ADAPTER: MathMapReplayAdapterDescriptor =
    MathMapReplayAdapterDescriptor {
        adapter_id: MATH_MAP_REPLAY_ADAPTER_ID,
        domain_profile: MATH_MAP_DOMAIN_PROFILE,
        source_system: MATH_MAP_SOURCE_SYSTEM,
        artifact_kind: ArtifactKind::MathMapLeanPatch,
        artifact_format: MATH_MAP_BUNDLE_ARTIFACT_FORMAT,
        replay_contract: MATH_MAP_INGEST_SCHEMA_VERSION,
    };
