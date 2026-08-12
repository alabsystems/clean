// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed behaviour tests for the untrusted MathMap bundle ingest path.

use std::collections::BTreeMap;
use std::fs;
use std::io::Cursor;
use std::path::Path;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use clean_kernel::Name;
use ring::rand::SystemRandom;
use ring::signature::{Ed25519KeyPair, KeyPair};
use serde_json::json;

use crate::attempt_log::{iter_from, AttemptFilter, AttemptStatus};
use crate::drift::{DriftReport, StmtChangeKind, TheoremStatementComparisonInput};
use crate::false_control_suite::{
    FalseControlId, FalseControlReport, FalseControlResult, FalseControlStatus,
};
use crate::trust::audit_report::{
    AuditFinding, AuditFindingCategory, AuditReport, AuditReportBuilder, AuditSeverity,
};
use crate::types::{AxiomProfile, TrustLevel};

use super::bundle::{hex_lower, sha256_hex};
use super::ingest::{
    evaluate_authority_gates, evaluate_environment_pin, evaluate_lake_recheck,
    evaluate_patch_apply, evaluate_patch_apply_preflight, evaluate_pre_patch_baseline_unavailable,
    evaluate_statement_preservation_gate, ingest_bundle_with_verifier,
    ingest_bundle_with_verifier_and_inputs, ingest_bundle_with_verifier_to_attempt_log_and_inputs,
    EnvironmentPinError, EnvironmentPinObservation, EnvironmentPinRunner, GitApplyCheckRunner,
    GitPatchApplyRunner, IngestFailure, IngestStatus, LakeRecheckCommand, LakeRecheckRunner,
    MathMapAuthorityGateInputs, MathMapCommandError, MathMapCommandOutput,
    MathMapEnvironmentPinInputs, MathMapFalseControlRerunInput, MathMapIngestConfig,
    MathMapIngestInputs, MathMapLakeRecheckInputs, MathMapLocalCheckInputs,
    MathMapPatchApplyInputs, MathMapPatchPreflightInputs, MathMapTrustAuditGateInput, PipelineStep,
    PipelineStepResult, StepStatus,
};
use super::keys::{
    manifest_signature_payload, Ed25519SignatureVerifier, ManifestSignatureVerifier,
    SignatureVerification, SkeletonSignatureVerifier, TrustedKey, TrustedKeyRegistry,
    TrustedKeyRegistryError,
};
use super::policy::MathMapPolicy;

/// Verifier engine label recorded by [`Ed25519SignatureVerifier`].
const ED25519_VERIFIER_ID: &str = "ed25519-ring-strict-v1";

fn test_policy() -> MathMapPolicy {
    MathMapPolicy {
        schema_version: "clean-math_map-policy-v1".to_owned(),
        allowed_schema_versions: vec!["1.0.0".to_owned()],
        allowed_services: vec!["math_map".to_owned()],
        allowed_target_kinds: vec!["fill_sorry".to_owned(), "frontier_candidate".to_owned()],
        denied_target_kinds: Vec::new(),
        denied_imports: Vec::new(),
        max_bundle_bytes: 1024 * 1024,
        max_bundle_age_days: Some(30),
        require_signature: true,
        require_registered_signature: true,
        require_cryptographic_signature: false,
        require_patch_hashes: true,
    }
}

fn test_keys() -> TrustedKeyRegistry {
    TrustedKeyRegistry {
        schema_version: "clean-math_map-trusted-keys-v1".to_owned(),
        keys: vec![TrustedKey {
            service: "math_map".to_owned(),
            key_id: "test-key".to_owned(),
            algorithm: "ed25519".to_owned(),
            public_key: "test-public-key".to_owned(),
            status: "trusted".to_owned(),
        }],
    }
}

fn test_config(policy: MathMapPolicy) -> MathMapIngestConfig {
    MathMapIngestConfig {
        policy,
        trusted_keys: test_keys(),
    }
}

fn generate_keypair() -> Ed25519KeyPair {
    let rng = SystemRandom::new();
    let pkcs8 = Ed25519KeyPair::generate_pkcs8(&rng).expect("keypair generates");
    Ed25519KeyPair::from_pkcs8(pkcs8.as_ref()).expect("keypair loads")
}

fn patch_text() -> String {
    "diff --git a/Foo.lean b/Foo.lean\n--- a/Foo.lean\n+++ b/Foo.lean\n@@\n-sorry\n+by simp\n"
        .to_owned()
}

fn applicable_patch_text() -> String {
    "diff --git a/Foo.lean b/Foo.lean\n--- a/Foo.lean\n+++ b/Foo.lean\n@@ -1 +1 @@\n-sorry\n+by simp\n"
        .to_owned()
}

fn manifest_for_patch(patch: &str, kind: &str) -> serde_json::Value {
    json!({
        "schema_version": "1.0.0",
        "job_id": "ar-test-1",
        "service": "math_map",
        "service_version": "1.4.2",
        "issued_at": fresh_issued_at(),
        "target_repo": {
            "rev": "abc123",
            "lake_toolchain": "leanprover/lean4:v4.14.0"
        },
        "targets": [{
            "theorem": "Foo.bar",
            "module": "Foo.lean",
            "kind": kind,
            "expected_statement_hash": "blake3:statement"
        }],
        "declared_trust": {
            "introduces_new_axioms": false,
            "introduces_new_opaques": false,
            "introduces_unsafe": false,
            "external_solvers": [],
            "generated_proof_terms": true
        },
        "patches": [{
            "path": "patch/0001.patch",
            "sha256": sha256_hex(patch.as_bytes())
        }]
    })
}

fn fresh_issued_at() -> String {
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock is after the Unix epoch")
        .as_secs() as i64;
    format_epoch_seconds(now)
}

fn format_epoch_seconds(seconds: i64) -> String {
    let days = seconds.div_euclid(24 * 60 * 60);
    let seconds_of_day = seconds.rem_euclid(24 * 60 * 60);
    let (year, month, day) = civil_from_days(days);
    let hour = seconds_of_day / (60 * 60);
    let minute = seconds_of_day % (60 * 60) / 60;
    let second = seconds_of_day % 60;
    format!("{year:04}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}Z")
}

fn civil_from_days(days: i64) -> (i64, i64, i64) {
    let days = days + 719_468;
    let era = if days >= 0 { days } else { days - 146_096 } / 146_097;
    let day_of_era = days - era * 146_097;
    let year_of_era =
        (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let mut year = year_of_era + era * 400;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_prime = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_prime + 2) / 5 + 1;
    let month = month_prime + if month_prime < 10 { 3 } else { -9 };
    year += i64::from(month <= 2);
    (year, month, day)
}

fn write_bundle(root: &Path, manifest: &serde_json::Value, patch: &str) {
    fs::create_dir_all(root.join("patch")).expect("patch dir");
    fs::create_dir_all(root.join("signatures")).expect("signatures dir");
    fs::write(
        root.join("manifest.json"),
        serde_json::to_vec_pretty(manifest).expect("manifest serializes"),
    )
    .expect("manifest written");
    fs::write(root.join("patch/0001.patch"), patch).expect("patch written");
    fs::write(root.join("signatures/manifest.sig"), b"test-signature").expect("signature written");
}

fn bundle_report(root: &Path, policy: MathMapPolicy) -> super::MathMapIngestReport {
    ingest_bundle_with_verifier(root, test_config(policy), &SkeletonSignatureVerifier)
}

fn report_step(report: &super::MathMapIngestReport, step: PipelineStep) -> &PipelineStepResult {
    report
        .steps
        .iter()
        .find(|result| result.step == step)
        .expect("every pipeline step is present in the report")
}

fn init_git_repo(root: &Path) {
    let status = Command::new("git")
        .arg("init")
        .arg("--quiet")
        .arg(root)
        .status()
        .expect("git is available");
    assert!(status.success(), "git init failed with {status}");
}

fn git_success(root: &Path, args: &[&str]) {
    let status = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(args)
        .status()
        .expect("git is available");
    assert!(status.success(), "git {args:?} failed with {status}");
}

fn git_output(root: &Path, args: &[&str]) -> String {
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(args)
        .output()
        .expect("git is available");
    assert!(
        output.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn git_commit_all(root: &Path, message: &str) {
    git_success(root, &["add", "-A"]);
    git_success(
        root,
        &[
            "-c",
            "user.name=MathMap Test",
            "-c",
            "user.email=math_map-test@example.invalid",
            "commit",
            "--quiet",
            "-m",
            message,
        ],
    );
}

fn false_control_result(
    id: FalseControlId,
    status: FalseControlStatus,
    detail: &str,
) -> FalseControlResult {
    FalseControlResult {
        id,
        label: "test false control",
        status,
        detail: detail.to_owned(),
        todo: None,
    }
}

fn green_false_control_report() -> FalseControlReport {
    FalseControlReport {
        controls: FalseControlId::all()
            .iter()
            .copied()
            .map(|id| {
                false_control_result(id, FalseControlStatus::Rejected, "known-bad input rejected")
            })
            .collect(),
    }
}

fn kernel_verified_audit_report() -> AuditReport {
    let mut builder = AuditReportBuilder::new();
    builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
    builder.build()
}

#[derive(Debug, Clone)]
struct FakeLakeRunner {
    output: Result<MathMapCommandOutput, MathMapCommandError>,
}

impl LakeRecheckRunner for FakeLakeRunner {
    fn run_lake_recheck(
        &self,
        _clean_repo_path: &Path,
        _command: &LakeRecheckCommand,
    ) -> Result<MathMapCommandOutput, MathMapCommandError> {
        self.output.clone()
    }
}

#[derive(Debug, Clone)]
struct FakeEnvironmentPinRunner {
    output: Result<EnvironmentPinObservation, EnvironmentPinError>,
}

impl EnvironmentPinRunner for FakeEnvironmentPinRunner {
    fn inspect_environment_pin(
        &self,
        _clean_repo_path: &Path,
    ) -> Result<EnvironmentPinObservation, EnvironmentPinError> {
        self.output.clone()
    }
}

/// A hostile verifier that reports a key the registry never registered.
#[derive(Debug, Clone, Copy)]
struct UnregisteredSignatureVerifier;

impl ManifestSignatureVerifier for UnregisteredSignatureVerifier {
    fn verify_manifest(
        &self,
        service: &str,
        _key_id: &str,
        _raw_manifest_json: &[u8],
        _signature: &[u8],
        _keys: &TrustedKeyRegistry,
    ) -> Result<SignatureVerification, TrustedKeyRegistryError> {
        Ok(SignatureVerification {
            service: service.to_owned(),
            key_id: "rogue-key".to_owned(),
            algorithm: "ed25519".to_owned(),
            cryptographic: false,
            verifier: "test-unregistered".to_owned(),
        })
    }
}

#[test]
fn test_ingest_rejects_missing_mandatory_manifest_field() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let mut manifest = manifest_for_patch(&patch, "fill_sorry");
    manifest
        .as_object_mut()
        .expect("manifest is a JSON object")
        .remove("service_version");
    write_bundle(temp.path(), &manifest, &patch);

    let report = bundle_report(temp.path(), test_policy());

    assert!(matches!(
        report.status,
        IngestStatus::Rejected {
            step: PipelineStep::BundleIntegrity,
            ..
        }
    ));
    let failure = report.steps[0]
        .failure
        .as_ref()
        .expect("integrity step failed");
    assert_eq!(
        failure,
        &IngestFailure::BundleIntegrityFailed {
            field: "service_version".to_owned()
        }
    );
}

#[test]
fn test_ingest_rejects_patch_hash_mismatch() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let mut manifest = manifest_for_patch(&patch, "fill_sorry");
    manifest["patches"][0]["sha256"] = json!("sha256:deadbeef");
    write_bundle(temp.path(), &manifest, &patch);

    let report = bundle_report(temp.path(), test_policy());

    assert!(matches!(
        report.steps[0].failure,
        Some(IngestFailure::BundleIntegrityFailed { .. })
    ));
    let reason = match report.status {
        IngestStatus::Rejected { reason, .. } => reason,
        status => panic!("expected rejection, got {status:?}"),
    };
    assert!(reason.contains("sha256"), "{reason}");
}

#[test]
fn test_ingest_rejects_missing_issued_at_when_age_policy_is_enabled() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let mut manifest = manifest_for_patch(&patch, "fill_sorry");
    manifest
        .as_object_mut()
        .expect("manifest is a JSON object")
        .remove("issued_at");
    write_bundle(temp.path(), &manifest, &patch);

    let report = bundle_report(temp.path(), test_policy());

    assert_eq!(
        report.steps[0].failure,
        Some(IngestFailure::PolicyRejected {
            reason: "manifest `issued_at` is required".to_owned()
        })
    );
}

#[test]
fn test_ingest_rejects_malformed_issued_at() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let mut manifest = manifest_for_patch(&patch, "fill_sorry");
    manifest["issued_at"] = json!("not-a-timestamp");
    write_bundle(temp.path(), &manifest, &patch);

    let report = bundle_report(temp.path(), test_policy());

    let reason = match report.status {
        IngestStatus::Rejected { reason, .. } => reason,
        status => panic!("expected rejection, got {status:?}"),
    };
    assert!(reason.contains("issued_at"), "{reason}");
    assert!(reason.contains("not-a-timestamp"), "{reason}");
}

#[test]
fn test_ingest_rejects_stale_issued_at() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let mut manifest = manifest_for_patch(&patch, "fill_sorry");
    manifest["issued_at"] = json!("2000-01-01T00:00:00Z");
    write_bundle(temp.path(), &manifest, &patch);

    let report = bundle_report(temp.path(), test_policy());

    let reason = match report.status {
        IngestStatus::Rejected { reason, .. } => reason,
        status => panic!("expected rejection, got {status:?}"),
    };
    assert!(
        reason.contains("older than policy max age of 30 days"),
        "{reason}"
    );
}

#[test]
fn test_ingest_rejects_far_future_issued_at() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let mut manifest = manifest_for_patch(&patch, "fill_sorry");
    manifest["issued_at"] = json!("2099-01-01T00:00:00Z");
    write_bundle(temp.path(), &manifest, &patch);

    let report = bundle_report(temp.path(), test_policy());

    let reason = match report.status {
        IngestStatus::Rejected { reason, .. } => reason,
        status => panic!("expected rejection, got {status:?}"),
    };
    assert!(reason.contains("too far in the future"), "{reason}");
}

#[test]
fn test_ingest_rejects_oversized_bundle_before_manifest_ingest() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(temp.path(), &manifest, &patch);
    let mut policy = test_policy();
    policy.max_bundle_bytes = 64;

    let report = bundle_report(temp.path(), policy);

    let reason = match report.status {
        IngestStatus::Rejected { reason, .. } => reason,
        status => panic!("expected rejection, got {status:?}"),
    };
    assert!(
        reason.contains("bundle exceeded max byte limit of 64 bytes"),
        "{reason}"
    );
}

#[test]
fn test_ingest_registered_signature_policy_requires_manifest_signature_file() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(temp.path(), &manifest, &patch);
    fs::remove_file(temp.path().join("signatures/manifest.sig")).expect("signature removed");
    fs::write(temp.path().join("signatures/placeholder"), b"local").expect("placeholder written");
    let mut policy = test_policy();
    policy.require_signature = false;
    policy.require_registered_signature = true;

    let report = bundle_report(temp.path(), policy);

    assert_eq!(
        report.steps[0].failure,
        Some(IngestFailure::BundleIntegrityFailed {
            field: "bundle is missing `signatures/manifest.sig`".to_owned()
        })
    );
}

#[test]
fn test_ingest_rejects_signature_without_registered_trusted_key() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(temp.path(), &manifest, &patch);
    let mut config = test_config(test_policy());
    config.trusted_keys.keys.clear();

    let report = ingest_bundle_with_verifier(temp.path(), config, &SkeletonSignatureVerifier);

    assert!(matches!(
        report.steps[0].failure,
        Some(IngestFailure::SignatureRejected { .. })
    ));
    let reason = match report.status {
        IngestStatus::Rejected { reason, .. } => reason,
        status => panic!("expected rejection, got {status:?}"),
    };
    assert!(reason.contains("no active trusted key"), "{reason}");
}

#[test]
fn test_ingest_rejects_verifier_result_for_unregistered_key_id() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(temp.path(), &manifest, &patch);

    let report = ingest_bundle_with_verifier(
        temp.path(),
        test_config(test_policy()),
        &UnregisteredSignatureVerifier,
    );

    let reason = match report.status {
        IngestStatus::Rejected { reason, .. } => reason,
        status => panic!("expected rejection, got {status:?}"),
    };
    assert!(reason.contains("rogue-key"), "{reason}");
    assert!(reason.contains("registered trusted key"), "{reason}");
}

#[test]
fn test_ingest_rejects_non_cryptographic_signature_when_policy_requires_one() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(temp.path(), &manifest, &patch);
    let mut policy = test_policy();
    policy.require_cryptographic_signature = true;

    // The skeleton verifier accepts, but reports `cryptographic: false`.
    let report = bundle_report(temp.path(), policy);

    let reason = match report.status {
        IngestStatus::Rejected { reason, .. } => reason,
        status => panic!("expected rejection, got {status:?}"),
    };
    assert!(
        reason.contains("was not cryptographically verified"),
        "{reason}"
    );
}

#[test]
fn test_ingest_rejects_policy_denied_target_kind() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "frontier_candidate");
    write_bundle(temp.path(), &manifest, &patch);
    let mut policy = test_policy();
    policy.denied_target_kinds = vec!["frontier_candidate".to_owned()];

    let report = bundle_report(temp.path(), policy);

    assert!(matches!(
        report.steps[0].failure,
        Some(IngestFailure::PolicyRejected { .. })
    ));
}

#[test]
fn test_ingest_rejects_policy_denied_added_import() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = "diff --git a/Foo.lean b/Foo.lean\n--- a/Foo.lean\n+++ b/Foo.lean\n@@\n+import Mathlib.Tactic.NativeDecide\n theorem Foo.bar : True := by trivial\n";
    let manifest = manifest_for_patch(patch, "fill_sorry");
    write_bundle(temp.path(), &manifest, patch);
    let mut policy = test_policy();
    policy.denied_imports = vec!["Mathlib.Tactic".to_owned()];

    let report = bundle_report(temp.path(), policy);

    assert_eq!(
        report.steps[0].failure,
        Some(IngestFailure::PolicyRejected {
            reason: "import `Mathlib.Tactic.NativeDecide` is denied".to_owned()
        })
    );
}

#[test]
fn test_ingest_accepts_integrity_from_tar_zst_then_blocks_unwired_gates() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    let archive = temp.path().join("math_map-ar-test-1.tar.zst");
    write_tar_zst(
        &archive,
        &[
            (
                "math_map-ar-test-1/manifest.json",
                serde_json::to_vec_pretty(&manifest).expect("manifest serializes"),
            ),
            (
                "math_map-ar-test-1/patch/0001.patch",
                patch.as_bytes().to_vec(),
            ),
            (
                "math_map-ar-test-1/signatures/manifest.sig",
                b"test-signature".to_vec(),
            ),
        ],
    );

    let report = bundle_report(&archive, test_policy());

    assert_eq!(report.steps[0].status, StepStatus::Passed);
    assert!(matches!(report.status, IngestStatus::Blocked { .. }));
    assert_eq!(report.steps.len(), 9);
    assert_eq!(report.steps[1].status, StepStatus::Skipped);
}

#[test]
fn test_ingest_with_ed25519_cryptographic_signature_passes_integrity() {
    let temp = tempfile::tempdir().expect("tempdir");
    let keypair = generate_keypair();

    let patch = patch_text();
    let manifest_json = manifest_for_patch(&patch, "fill_sorry");
    let raw_manifest_json = serde_json::to_vec_pretty(&manifest_json).expect("manifest serializes");

    let key_id = "test-key";
    let payload = manifest_signature_payload("math_map", key_id, &raw_manifest_json);
    let signature = keypair.sign(&payload);

    fs::create_dir_all(temp.path().join("patch")).expect("patch dir");
    fs::create_dir_all(temp.path().join("signatures")).expect("signatures dir");
    fs::write(temp.path().join("manifest.json"), &raw_manifest_json).expect("manifest written");
    fs::write(temp.path().join("patch/0001.patch"), &patch).expect("patch written");
    fs::write(
        temp.path().join("signatures/manifest.sig"),
        signature.as_ref(),
    )
    .expect("signature written");
    fs::write(temp.path().join("signatures/key_id"), key_id).expect("key id written");

    let mut policy = test_policy();
    policy.require_cryptographic_signature = true;
    let mut config = test_config(policy);
    config.trusted_keys.keys = vec![TrustedKey {
        service: "math_map".to_owned(),
        key_id: key_id.to_owned(),
        algorithm: "ed25519".to_owned(),
        public_key: hex_lower(keypair.public_key().as_ref()),
        status: "trusted".to_owned(),
    }];

    let report = ingest_bundle_with_verifier(temp.path(), config, &Ed25519SignatureVerifier);

    assert_eq!(
        report_step(&report, PipelineStep::BundleIntegrity).status,
        StepStatus::Passed
    );
    let sig = report
        .signature
        .as_ref()
        .expect("integrity records a signature");
    assert!(sig.cryptographic);
    assert_eq!(sig.verifier, ED25519_VERIFIER_ID);
}

#[test]
fn test_ingest_rejects_ed25519_signature_over_tampered_manifest() {
    let temp = tempfile::tempdir().expect("tempdir");
    let keypair = generate_keypair();

    let patch = patch_text();
    let manifest_json = manifest_for_patch(&patch, "fill_sorry");
    let raw_manifest_json = serde_json::to_vec_pretty(&manifest_json).expect("manifest serializes");

    let key_id = "test-key";
    let payload = manifest_signature_payload("math_map", key_id, &raw_manifest_json);
    let signature = keypair.sign(&payload);

    // Write a DIFFERENT manifest than the one that was signed.
    let mut tampered = manifest_json;
    tampered["targets"][0]["expected_statement_hash"] = json!("blake3:attacker");
    let tampered_bytes = serde_json::to_vec_pretty(&tampered).expect("manifest serializes");

    fs::create_dir_all(temp.path().join("patch")).expect("patch dir");
    fs::create_dir_all(temp.path().join("signatures")).expect("signatures dir");
    fs::write(temp.path().join("manifest.json"), &tampered_bytes).expect("manifest written");
    fs::write(temp.path().join("patch/0001.patch"), &patch).expect("patch written");
    fs::write(
        temp.path().join("signatures/manifest.sig"),
        signature.as_ref(),
    )
    .expect("signature written");
    fs::write(temp.path().join("signatures/key_id"), key_id).expect("key id written");

    let mut policy = test_policy();
    policy.require_cryptographic_signature = true;
    let mut config = test_config(policy);
    config.trusted_keys.keys = vec![TrustedKey {
        service: "math_map".to_owned(),
        key_id: key_id.to_owned(),
        algorithm: "ed25519".to_owned(),
        public_key: hex_lower(keypair.public_key().as_ref()),
        status: "trusted".to_owned(),
    }];

    let report = ingest_bundle_with_verifier(temp.path(), config, &Ed25519SignatureVerifier);

    assert!(matches!(
        report_step(&report, PipelineStep::BundleIntegrity).failure,
        Some(IngestFailure::SignatureRejected { .. })
    ));
    assert!(matches!(
        report.status,
        IngestStatus::Rejected {
            step: PipelineStep::BundleIntegrity,
            ..
        }
    ));
}

#[test]
fn test_ingest_rejects_manifest_with_duplicate_json_keys() {
    let temp = tempfile::tempdir().expect("tempdir");

    // Build a manifest with a duplicate key by hand, bypassing serialization.
    let raw_manifest_json = br#"{
        "schema_version": "1.0.0",
        "schema_version": "1.0.0",
        "job_id": "test-job",
        "service": "math_map",
        "service_version": "1.0.0"
    }"#;

    fs::create_dir_all(temp.path().join("patch")).expect("patch dir");
    fs::create_dir_all(temp.path().join("signatures")).expect("signatures dir");
    fs::write(temp.path().join("manifest.json"), raw_manifest_json).expect("manifest written");
    fs::write(temp.path().join("patch/dummy"), "").expect("patch written");
    fs::write(temp.path().join("signatures/dummy"), "").expect("signature written");

    let config = test_config(test_policy());
    let report = ingest_bundle_with_verifier(temp.path(), config, &Ed25519SignatureVerifier);

    assert_eq!(
        report_step(&report, PipelineStep::BundleIntegrity).status,
        StepStatus::Failed
    );
    let Some(IngestFailure::BundleIntegrityFailed { field }) =
        &report_step(&report, PipelineStep::BundleIntegrity).failure
    else {
        panic!("expected BundleIntegrityFailed failure");
    };
    assert!(
        field.contains("duplicate field `schema_version`"),
        "actual error: {field}"
    );
}

#[test]
fn test_ingest_with_explicit_key_id_passes() {
    let temp = tempfile::tempdir().expect("tempdir");
    let keypair = generate_keypair();
    let service = "math_map";
    let key_id = "trusted-key-1";

    let patch = patch_text();
    let manifest_json = manifest_for_patch(&patch, "fill_sorry");
    let raw_manifest_json = serde_json::to_vec_pretty(&manifest_json).expect("manifest serializes");

    let mut payload = Vec::new();
    payload.extend_from_slice(super::keys::MATH_MAP_MANIFEST_DOMAIN_SEPARATOR);
    payload.extend_from_slice(service.as_bytes());
    payload.push(0);
    payload.extend_from_slice(key_id.as_bytes());
    payload.push(0);
    payload.extend_from_slice(&raw_manifest_json);
    let signature = keypair.sign(&payload);

    fs::create_dir_all(temp.path().join("patch")).expect("patch dir");
    fs::create_dir_all(temp.path().join("signatures")).expect("signatures dir");
    fs::write(temp.path().join("manifest.json"), &raw_manifest_json).expect("manifest written");
    fs::write(temp.path().join("patch/0001.patch"), &patch).expect("patch written");
    fs::write(
        temp.path().join("signatures/manifest.sig"),
        signature.as_ref(),
    )
    .expect("signature written");
    fs::write(temp.path().join("signatures/key_id"), key_id).expect("key id written");

    let mut config = test_config(test_policy());
    config.trusted_keys.keys = vec![TrustedKey {
        service: service.to_owned(),
        key_id: key_id.to_owned(),
        algorithm: "ed25519".to_owned(),
        public_key: hex_lower(keypair.public_key().as_ref()),
        status: "trusted".to_owned(),
    }];

    let report = ingest_bundle_with_verifier(temp.path(), config, &Ed25519SignatureVerifier);

    assert_eq!(
        report_step(&report, PipelineStep::BundleIntegrity).status,
        StepStatus::Passed
    );
    assert_eq!(
        report
            .signature
            .as_ref()
            .expect("integrity records a signature")
            .key_id,
        key_id
    );
}

#[test]
fn test_ingest_with_ambiguous_keys_and_no_key_id_fails() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest_json = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(temp.path(), &manifest_json, &patch);

    let mut config = test_config(test_policy());
    config.policy.require_cryptographic_signature = true;
    config.trusted_keys.keys = vec![
        TrustedKey {
            service: "math_map".to_owned(),
            key_id: "key-1".to_owned(),
            algorithm: "ed25519".to_owned(),
            public_key: "00".repeat(32),
            status: "trusted".to_owned(),
        },
        TrustedKey {
            service: "math_map".to_owned(),
            key_id: "key-2".to_owned(),
            algorithm: "ed25519".to_owned(),
            public_key: "01".repeat(32),
            status: "trusted".to_owned(),
        },
    ];

    let report = ingest_bundle_with_verifier(temp.path(), config, &Ed25519SignatureVerifier);

    assert_eq!(
        report_step(&report, PipelineStep::BundleIntegrity).status,
        StepStatus::Failed
    );
    let Some(IngestFailure::SignatureRejected { reason }) =
        &report_step(&report, PipelineStep::BundleIntegrity).failure
    else {
        panic!("expected SignatureRejected failure due to ambiguity");
    };
    assert!(reason.contains("ambiguous"), "{reason}");
}

#[test]
fn test_ingest_with_goal_hash_replay_protection_works() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(temp.path(), &manifest, &patch);
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:changed".to_owned())]);
    let before = AuditReportBuilder::new().build();
    let after = {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        builder.build()
    };

    let report = ingest_bundle_with_verifier_and_inputs(
        temp.path(),
        test_config(test_policy()),
        &SkeletonSignatureVerifier,
        MathMapIngestInputs::with_authority_gates(MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: None,
        }),
    );

    assert_eq!(
        report_step(&report, PipelineStep::BundleIntegrity).status,
        StepStatus::Passed
    );
    assert_eq!(
        report_step(&report, PipelineStep::LakeRecheck).status,
        StepStatus::Skipped
    );
    assert!(matches!(
        report_step(&report, PipelineStep::LakeRecheck)
            .failure
            .as_ref(),
        Some(IngestFailure::StageNotImplemented { .. })
    ));
    let statement = report_step(&report, PipelineStep::DriftStatementPreservation);
    assert_eq!(statement.status, StepStatus::Failed);
    assert_eq!(
        statement.details.get("input_source").map(String::as_str),
        Some("caller_supplied")
    );
    assert_eq!(
        statement
            .details
            .get("observed_target_statement_hash_count")
            .map(String::as_str),
        Some("1")
    );
    assert!(matches!(
        statement.failure.as_ref(),
        Some(IngestFailure::TargetStatementMismatch { .. })
    ));
    assert_eq!(
        report_step(&report, PipelineStep::TrustAudit).status,
        StepStatus::Passed
    );
    assert!(matches!(
        &report.status,
        IngestStatus::Rejected {
            step: PipelineStep::DriftStatementPreservation,
            ..
        }
    ));
    assert_eq!(
        report
            .authority_gates
            .as_ref()
            .expect("authority gates were supplied")
            .statement_preservation
            .status,
        StepStatus::Failed
    );
    assert!(
        report.proof_attempt.is_none(),
        "non-recording ingest must not fabricate a proof attempt"
    );
}

#[test]
fn test_ingest_with_authority_inputs_passes_in_memory_gates_but_blocks_unwired_pipeline() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(temp.path(), &manifest, &patch);
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let before = kernel_verified_audit_report();
    let after = kernel_verified_audit_report();

    let report = ingest_bundle_with_verifier_and_inputs(
        temp.path(),
        test_config(test_policy()),
        &SkeletonSignatureVerifier,
        MathMapIngestInputs::with_authority_gates(MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: None,
        }),
    );

    assert_eq!(
        report_step(&report, PipelineStep::DriftStatementPreservation).status,
        StepStatus::Passed
    );
    assert_eq!(
        report_step(&report, PipelineStep::TrustAudit).status,
        StepStatus::Passed
    );
    assert_eq!(
        report_step(&report, PipelineStep::EnvironmentPin).status,
        StepStatus::Skipped
    );
    assert_eq!(
        report_step(&report, PipelineStep::PrePatchBaseline).status,
        StepStatus::Skipped
    );
    assert_eq!(
        report_step(&report, PipelineStep::PatchApply).status,
        StepStatus::Skipped
    );
    assert_eq!(
        report_step(&report, PipelineStep::LakeRecheck).status,
        StepStatus::Skipped
    );
    assert_eq!(
        report_step(&report, PipelineStep::FalseControlRerun).status,
        StepStatus::Skipped
    );
    let reason = match &report.status {
        IngestStatus::Blocked { reason } => reason,
        status => panic!("expected blocked ingest, got {status:?}"),
    };
    assert!(
        reason.contains("environment/baseline/patch/Lake"),
        "{reason}"
    );
    assert!(matches!(
        &report
            .authority_gates
            .as_ref()
            .expect("authority gates were supplied")
            .status,
        IngestStatus::Blocked { .. }
    ));
    assert!(
        report.proof_attempt.is_none(),
        "non-recording ingest must not fabricate a proof attempt"
    );
}

#[test]
fn test_patch_preflight_accepts_applicable_bundle_patch_without_mutating_repo() {
    let bundle_dir = tempfile::tempdir().expect("tempdir");
    let repo = tempfile::tempdir().expect("tempdir");
    init_git_repo(repo.path());
    fs::write(repo.path().join("Foo.lean"), "sorry\n").expect("source written");
    let patch = applicable_patch_text();
    let manifest_json = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(bundle_dir.path(), &manifest_json, &patch);
    let bundle =
        super::BundleFileSystem::load(bundle_dir.path(), 1024 * 1024).expect("bundle loads");
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_json).expect("manifest parses");

    let step =
        evaluate_patch_apply_preflight(repo.path(), &manifest, &bundle, &GitApplyCheckRunner);

    assert_eq!(step.step, PipelineStep::PatchApply);
    assert_eq!(step.status, StepStatus::Passed);
    assert_eq!(step.failure, None);
    assert_eq!(
        step.details.get("patches").map(String::as_str),
        Some("patch/0001.patch")
    );
    assert_eq!(
        fs::read_to_string(repo.path().join("Foo.lean")).expect("source readable"),
        "sorry\n"
    );
}

#[test]
fn test_patch_preflight_rejects_conflicting_patch_without_mutating_repo() {
    let bundle_dir = tempfile::tempdir().expect("tempdir");
    let repo = tempfile::tempdir().expect("tempdir");
    init_git_repo(repo.path());
    fs::write(repo.path().join("Foo.lean"), "by trivial\n").expect("source written");
    let patch = applicable_patch_text();
    let manifest_json = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(bundle_dir.path(), &manifest_json, &patch);
    let bundle =
        super::BundleFileSystem::load(bundle_dir.path(), 1024 * 1024).expect("bundle loads");
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_json).expect("manifest parses");

    let step =
        evaluate_patch_apply_preflight(repo.path(), &manifest, &bundle, &GitApplyCheckRunner);

    assert_eq!(step.step, PipelineStep::PatchApply);
    assert_eq!(step.status, StepStatus::Failed);
    assert!(matches!(
        step.failure,
        Some(IngestFailure::PatchApplyFailed { .. })
    ));
    assert_eq!(
        fs::read_to_string(repo.path().join("Foo.lean")).expect("source readable"),
        "by trivial\n"
    );
    assert_ne!(
        step.details.get("status").map(String::as_str),
        Some("success(0)")
    );
}

#[test]
fn test_environment_pin_evaluator_maps_revision_mismatch_to_failure() {
    let repo = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let runner = FakeEnvironmentPinRunner {
        output: Ok(EnvironmentPinObservation {
            rev: "def456".to_owned(),
            lake_toolchain: "leanprover/lean4:v4.14.0".to_owned(),
        }),
    };

    let step = evaluate_environment_pin(repo.path(), &manifest, &runner);

    assert_eq!(step.step, PipelineStep::EnvironmentPin);
    assert_eq!(step.status, StepStatus::Failed);
    assert!(matches!(
        step.failure,
        Some(IngestFailure::EnvironmentPinFailed { .. })
    ));
}

#[test]
fn test_environment_pin_evaluator_maps_toolchain_mismatch_to_failure() {
    let repo = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let runner = FakeEnvironmentPinRunner {
        output: Ok(EnvironmentPinObservation {
            rev: "abc123456789".to_owned(),
            lake_toolchain: "leanprover/lean4:v4.99.0".to_owned(),
        }),
    };

    let step = evaluate_environment_pin(repo.path(), &manifest, &runner);

    assert_eq!(step.status, StepStatus::Failed);
    let Some(IngestFailure::EnvironmentPinFailed { reason }) = step.failure else {
        panic!("expected EnvironmentPinFailed");
    };
    assert!(reason.contains("Lake toolchain mismatch"), "{reason}");
}

#[test]
fn test_environment_pin_evaluator_accepts_matching_manifest_pins() {
    let repo = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let runner = FakeEnvironmentPinRunner {
        output: Ok(EnvironmentPinObservation {
            rev: "abc123456789".to_owned(),
            lake_toolchain: "leanprover/lean4:v4.14.0".to_owned(),
        }),
    };

    let step = evaluate_environment_pin(repo.path(), &manifest, &runner);

    assert_eq!(step.step, PipelineStep::EnvironmentPin);
    assert_eq!(step.status, StepStatus::Passed);
    assert_eq!(step.failure, None);
    assert_eq!(
        step.details.get("actual_rev").map(String::as_str),
        Some("abc123456789")
    );
}

#[test]
fn test_pre_patch_baseline_unavailable_reports_blocked_baseline_step() {
    let step = evaluate_pre_patch_baseline_unavailable("baseline runner missing");

    assert_eq!(step.step, PipelineStep::PrePatchBaseline);
    assert_eq!(step.status, StepStatus::Skipped);
    assert_eq!(
        step.failure,
        Some(IngestFailure::BaselineFailed {
            reason: "baseline runner missing".to_owned()
        })
    );
    assert_eq!(
        step.details.get("baseline_status").map(String::as_str),
        Some("unavailable")
    );
}

#[test]
fn test_patch_apply_rejects_conflicting_patch_without_mutating_repo() {
    let bundle_dir = tempfile::tempdir().expect("tempdir");
    let repo = tempfile::tempdir().expect("tempdir");
    init_git_repo(repo.path());
    fs::write(repo.path().join("Foo.lean"), "by trivial\n").expect("source written");
    let patch = applicable_patch_text();
    let manifest_json = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(bundle_dir.path(), &manifest_json, &patch);
    let bundle =
        super::BundleFileSystem::load(bundle_dir.path(), 1024 * 1024).expect("bundle loads");
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_json).expect("manifest parses");

    let step = evaluate_patch_apply(repo.path(), &manifest, &bundle, &GitPatchApplyRunner, false);

    assert_eq!(step.step, PipelineStep::PatchApply);
    assert_eq!(step.status, StepStatus::Failed);
    assert!(matches!(
        step.failure,
        Some(IngestFailure::PatchApplyFailed { .. })
    ));
    assert_eq!(
        fs::read_to_string(repo.path().join("Foo.lean")).expect("source readable"),
        "by trivial\n"
    );
}

#[test]
fn test_patch_apply_mutates_and_commits_on_success_when_requested() {
    let bundle_dir = tempfile::tempdir().expect("tempdir");
    let repo = tempfile::tempdir().expect("tempdir");
    init_git_repo(repo.path());
    fs::write(repo.path().join("Foo.lean"), "sorry\n").expect("source written");
    git_commit_all(repo.path(), "initial");
    let patch = applicable_patch_text();
    let manifest_json = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(bundle_dir.path(), &manifest_json, &patch);
    let bundle =
        super::BundleFileSystem::load(bundle_dir.path(), 1024 * 1024).expect("bundle loads");
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_json).expect("manifest parses");

    let step = evaluate_patch_apply(repo.path(), &manifest, &bundle, &GitPatchApplyRunner, true);

    assert_eq!(step.step, PipelineStep::PatchApply);
    assert_eq!(step.status, StepStatus::Passed);
    assert_eq!(step.failure, None);
    assert_eq!(
        fs::read_to_string(repo.path().join("Foo.lean")).expect("source readable"),
        "by simp\n"
    );
    assert_eq!(
        step.details.get("committed").map(String::as_str),
        Some("true")
    );
    assert_eq!(
        git_output(repo.path(), &["rev-list", "--count", "HEAD"]).trim(),
        "2"
    );
}

#[test]
fn test_lake_recheck_evaluator_records_success_output() {
    let repo = tempfile::tempdir().expect("tempdir");
    let command = LakeRecheckCommand::new("fake-lake", ["build"]);
    let runner = FakeLakeRunner {
        output: Ok(MathMapCommandOutput::success("build ok\n", "")),
    };

    let step = evaluate_lake_recheck(repo.path(), &runner, &command, Some("Foo.lean"));

    assert_eq!(step.step, PipelineStep::LakeRecheck);
    assert_eq!(step.status, StepStatus::Passed);
    assert_eq!(step.failure, None);
    assert_eq!(
        step.details.get("stdout").map(String::as_str),
        Some("build ok\n")
    );
    assert_eq!(
        step.details.get("status").map(String::as_str),
        Some("success(0)")
    );
}

#[test]
fn test_lake_recheck_evaluator_maps_nonzero_status_to_pipeline_failure() {
    let repo = tempfile::tempdir().expect("tempdir");
    let command = LakeRecheckCommand::new("fake-lake", ["build"]);
    let runner = FakeLakeRunner {
        output: Ok(MathMapCommandOutput::failure(
            1,
            "",
            "Foo.lean:1:1: error: tactic failed\n",
        )),
    };

    let step = evaluate_lake_recheck(repo.path(), &runner, &command, Some("Foo.lean"));

    assert_eq!(step.step, PipelineStep::LakeRecheck);
    assert_eq!(step.status, StepStatus::Failed);
    assert_eq!(
        step.failure,
        Some(IngestFailure::LakeRecheckFailed {
            module: "Foo.lean".to_owned(),
            error: "Foo.lean:1:1: error: tactic failed".to_owned(),
        })
    );
    assert_eq!(
        step.details.get("stderr").map(String::as_str),
        Some("Foo.lean:1:1: error: tactic failed\n")
    );
}

#[test]
fn test_lake_recheck_evaluator_maps_spawn_failure_to_pipeline_failure() {
    let repo = tempfile::tempdir().expect("tempdir");
    let command = LakeRecheckCommand::new("fake-lake", ["build"]);
    let runner = FakeLakeRunner {
        output: Err(MathMapCommandError::Io {
            program: "fake-lake".to_owned(),
            cwd: repo.path().display().to_string(),
            message: "no such file or directory".to_owned(),
        }),
    };

    let step = evaluate_lake_recheck(repo.path(), &runner, &command, Some("Foo.lean"));

    assert_eq!(step.status, StepStatus::Failed);
    assert!(matches!(
        step.failure,
        Some(IngestFailure::LakeRecheckFailed { .. })
    ));
}

#[test]
fn test_ingest_with_local_patch_and_lake_inputs_updates_steps_but_stays_blocked() {
    let bundle_dir = tempfile::tempdir().expect("tempdir");
    let repo = tempfile::tempdir().expect("tempdir");
    init_git_repo(repo.path());
    fs::write(repo.path().join("Foo.lean"), "sorry\n").expect("source written");
    let patch = applicable_patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(bundle_dir.path(), &manifest, &patch);
    let git_runner = GitApplyCheckRunner;
    let lake_command = LakeRecheckCommand::new("fake-lake", ["build"]);
    let lake_runner = FakeLakeRunner {
        output: Ok(MathMapCommandOutput::success("checked\n", "")),
    };

    let report = ingest_bundle_with_verifier_and_inputs(
        bundle_dir.path(),
        test_config(test_policy()),
        &SkeletonSignatureVerifier,
        MathMapIngestInputs::with_local_checks(MathMapLocalCheckInputs {
            clean_repo_path: repo.path(),
            environment_pin: None,
            patch_apply: None,
            patch_preflight: Some(MathMapPatchPreflightInputs {
                runner: &git_runner,
            }),
            lake_recheck: Some(MathMapLakeRecheckInputs {
                runner: &lake_runner,
                command: &lake_command,
                module: Some("Foo.lean"),
            }),
            false_control_rerun: None,
        }),
    );

    assert_eq!(
        report_step(&report, PipelineStep::PatchApply).status,
        StepStatus::Passed
    );
    assert_eq!(
        report_step(&report, PipelineStep::LakeRecheck).status,
        StepStatus::Passed
    );
    assert_eq!(
        report_step(&report, PipelineStep::DriftStatementPreservation).status,
        StepStatus::Skipped
    );
    assert!(matches!(report.status, IngestStatus::Blocked { .. }));
    assert_eq!(
        fs::read_to_string(repo.path().join("Foo.lean")).expect("source readable"),
        "sorry\n"
    );
}

#[test]
fn test_ingest_local_sequence_stops_before_patch_when_environment_pin_fails() {
    let bundle_dir = tempfile::tempdir().expect("tempdir");
    let repo = tempfile::tempdir().expect("tempdir");
    init_git_repo(repo.path());
    fs::write(repo.path().join("Foo.lean"), "sorry\n").expect("source written");
    let patch = applicable_patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(bundle_dir.path(), &manifest, &patch);
    let env_runner = FakeEnvironmentPinRunner {
        output: Ok(EnvironmentPinObservation {
            rev: "def456".to_owned(),
            lake_toolchain: "leanprover/lean4:v4.14.0".to_owned(),
        }),
    };
    let patch_runner = GitPatchApplyRunner;

    let report = ingest_bundle_with_verifier_and_inputs(
        bundle_dir.path(),
        test_config(test_policy()),
        &SkeletonSignatureVerifier,
        MathMapIngestInputs::with_local_checks(MathMapLocalCheckInputs {
            clean_repo_path: repo.path(),
            environment_pin: Some(MathMapEnvironmentPinInputs {
                runner: &env_runner,
            }),
            patch_apply: Some(MathMapPatchApplyInputs {
                runner: &patch_runner,
                commit: false,
            }),
            patch_preflight: None,
            lake_recheck: None,
            false_control_rerun: None,
        }),
    );

    assert!(matches!(
        report_step(&report, PipelineStep::EnvironmentPin).failure,
        Some(IngestFailure::EnvironmentPinFailed { .. })
    ));
    assert_eq!(
        report_step(&report, PipelineStep::PatchApply).status,
        StepStatus::Skipped
    );
    assert_eq!(
        fs::read_to_string(repo.path().join("Foo.lean")).expect("source readable"),
        "sorry\n"
    );
    assert!(matches!(
        report.status,
        IngestStatus::Rejected {
            step: PipelineStep::EnvironmentPin,
            ..
        }
    ));
}

#[test]
fn test_ingest_local_sequence_maps_patch_apply_failure_after_environment_pin_passes() {
    let bundle_dir = tempfile::tempdir().expect("tempdir");
    let repo = tempfile::tempdir().expect("tempdir");
    init_git_repo(repo.path());
    fs::write(repo.path().join("Foo.lean"), "by trivial\n").expect("source written");
    let patch = applicable_patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(bundle_dir.path(), &manifest, &patch);
    let env_runner = FakeEnvironmentPinRunner {
        output: Ok(EnvironmentPinObservation {
            rev: "abc123456789".to_owned(),
            lake_toolchain: "leanprover/lean4:v4.14.0".to_owned(),
        }),
    };
    let patch_runner = GitPatchApplyRunner;

    let report = ingest_bundle_with_verifier_and_inputs(
        bundle_dir.path(),
        test_config(test_policy()),
        &SkeletonSignatureVerifier,
        MathMapIngestInputs::with_local_checks(MathMapLocalCheckInputs {
            clean_repo_path: repo.path(),
            environment_pin: Some(MathMapEnvironmentPinInputs {
                runner: &env_runner,
            }),
            patch_apply: Some(MathMapPatchApplyInputs {
                runner: &patch_runner,
                commit: false,
            }),
            patch_preflight: None,
            lake_recheck: None,
            false_control_rerun: None,
        }),
    );

    assert_eq!(
        report_step(&report, PipelineStep::EnvironmentPin).status,
        StepStatus::Passed
    );
    assert!(matches!(
        report_step(&report, PipelineStep::PatchApply).failure,
        Some(IngestFailure::PatchApplyFailed { .. })
    ));
    assert_eq!(
        fs::read_to_string(repo.path().join("Foo.lean")).expect("source readable"),
        "by trivial\n"
    );
    assert!(matches!(
        report.status,
        IngestStatus::Rejected {
            step: PipelineStep::PatchApply,
            ..
        }
    ));
}

#[test]
fn test_ingest_local_false_control_rerun_feeds_authority_gate() {
    let bundle_dir = tempfile::tempdir().expect("tempdir");
    let repo = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(bundle_dir.path(), &manifest, &patch);
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let before = kernel_verified_audit_report();
    let after = kernel_verified_audit_report();
    let false_controls = green_false_control_report();

    let report = ingest_bundle_with_verifier_and_inputs(
        bundle_dir.path(),
        test_config(test_policy()),
        &SkeletonSignatureVerifier,
        MathMapIngestInputs::with_authority_gates_and_local_checks(
            MathMapAuthorityGateInputs {
                observed_target_statement_hashes: &observed,
                statement_comparison_inputs: &[],
                drift_reports: &[],
                trust_audit: Some(MathMapTrustAuditGateInput {
                    before: &before,
                    after: &after,
                }),
                false_control_rerun: None,
            },
            MathMapLocalCheckInputs {
                clean_repo_path: repo.path(),
                environment_pin: None,
                patch_apply: None,
                patch_preflight: None,
                lake_recheck: None,
                false_control_rerun: Some(MathMapFalseControlRerunInput::LocalReport(
                    &false_controls,
                )),
            },
        ),
    );

    let false_control = report_step(&report, PipelineStep::FalseControlRerun);
    assert_eq!(false_control.status, StepStatus::Passed);
    assert_eq!(
        false_control
            .details
            .get("input_source")
            .map(String::as_str),
        Some("local_generated")
    );
    assert_eq!(
        false_control
            .details
            .get("false_control_report_source")
            .map(String::as_str),
        Some("local_generated")
    );
    assert!(matches!(report.status, IngestStatus::Blocked { .. }));
    let authority_gates = report
        .authority_gates
        .as_ref()
        .expect("authority gates were supplied");
    assert_eq!(
        authority_gates.false_control_rerun.status,
        StepStatus::Passed
    );
    assert_eq!(authority_gates.status, IngestStatus::Accepted);
}

#[test]
fn test_statement_preservation_rejects_target_hash_mismatch() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:changed".to_owned())]);

    let step = evaluate_statement_preservation_gate(&manifest, &observed, &[]);

    assert_eq!(step.step, PipelineStep::DriftStatementPreservation);
    assert_eq!(step.status, StepStatus::Failed);
    assert_eq!(
        step.failure,
        Some(IngestFailure::TargetStatementMismatch {
            theorem: "Foo.bar".to_owned(),
            expected: "blake3:statement".to_owned(),
            actual: "blake3:changed".to_owned(),
        })
    );
}

#[test]
fn test_statement_preservation_rejects_missing_observed_hash() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");

    // No observed hash at all must never be read as "unchanged".
    let step = evaluate_statement_preservation_gate(&manifest, &BTreeMap::new(), &[]);

    assert_eq!(step.status, StepStatus::Failed);
    let Some(IngestFailure::TargetStatementMismatch { actual, .. }) = step.failure else {
        panic!("expected TargetStatementMismatch");
    };
    assert_eq!(actual, "<missing observed statement hash>");
}

#[test]
fn test_statement_preservation_mismatch_details_include_statement_comparison_input() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:changed".to_owned())]);
    let comparison_inputs = vec![TheoremStatementComparisonInput {
        theorem: "bar".to_owned(),
        qualified_name: "Foo.bar".to_owned(),
        before_statement_hash: Some("blake3:statement".to_owned()),
        after_statement_hash: Some("blake3:changed".to_owned()),
    }];

    let report = evaluate_authority_gates(
        &manifest,
        MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &comparison_inputs,
            drift_reports: &[],
            trust_audit: None,
            false_control_rerun: None,
        },
    );
    let details = &report.statement_preservation.details;

    assert_eq!(report.statement_preservation.status, StepStatus::Failed);
    assert_eq!(
        details
            .get("statement_comparison_input_count")
            .map(String::as_str),
        Some("1")
    );
    assert_eq!(
        details
            .get("statement_comparison_target_count")
            .map(String::as_str),
        Some("1")
    );
    assert_eq!(
        details
            .get("statement_comparison.target.0.qualified_name")
            .map(String::as_str),
        Some("Foo.bar")
    );
    assert_eq!(
        details
            .get("statement_comparison.target.0.before_statement_hash")
            .map(String::as_str),
        Some("blake3:statement")
    );
    assert_eq!(
        details
            .get("statement_comparison.target.0.after_statement_hash")
            .map(String::as_str),
        Some("blake3:changed")
    );
}

#[test]
fn test_statement_preservation_rejects_empty_target_set() {
    let patch = patch_text();
    let mut manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    manifest.targets.clear();

    let step = evaluate_statement_preservation_gate(&manifest, &BTreeMap::new(), &[]);

    assert_eq!(step.step, PipelineStep::DriftStatementPreservation);
    assert_eq!(step.status, StepStatus::Failed);
    assert_eq!(
        step.failure,
        Some(IngestFailure::StatementPreservationUnavailable {
            reason: "manifest has no targets to preserve".to_owned(),
        })
    );
}

#[test]
fn test_statement_preservation_accepts_matching_targets_and_added_names() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "statement".to_owned())]);
    let drift = vec![DriftReport::NameAdded(Name::from_string("Foo.new_helper"))];

    let step = evaluate_statement_preservation_gate(&manifest, &observed, &drift);

    assert_eq!(step.status, StepStatus::Passed);
    assert_eq!(step.failure, None);
}

#[test]
fn test_statement_preservation_pass_details_include_statement_comparison_input() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let comparison_inputs = vec![TheoremStatementComparisonInput {
        theorem: "bar".to_owned(),
        qualified_name: "Foo.bar".to_owned(),
        before_statement_hash: Some("blake3:statement".to_owned()),
        after_statement_hash: Some("blake3:statement".to_owned()),
    }];

    let report = evaluate_authority_gates(
        &manifest,
        MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &comparison_inputs,
            drift_reports: &[],
            trust_audit: None,
            false_control_rerun: None,
        },
    );
    let details = &report.statement_preservation.details;

    assert_eq!(report.statement_preservation.status, StepStatus::Passed);
    assert_eq!(
        details
            .get("statement_comparison.target.0.qualified_name")
            .map(String::as_str),
        Some("Foo.bar")
    );
    assert_eq!(
        details
            .get("statement_comparison.target.0.before_statement_hash")
            .map(String::as_str),
        Some("blake3:statement")
    );
    assert_eq!(
        details
            .get("statement_comparison.target.0.after_statement_hash")
            .map(String::as_str),
        Some("blake3:statement")
    );
}

#[test]
fn test_statement_preservation_rejects_public_statement_drift() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let drift = vec![DriftReport::StatementChanged {
        name: Name::from_string("Foo.old_public"),
        before: [0; 32],
        after: [1; 32],
        kind: StmtChangeKind::Incomparable,
    }];

    let step = evaluate_statement_preservation_gate(&manifest, &observed, &drift);

    assert_eq!(step.status, StepStatus::Failed);
    assert!(matches!(
        step.failure,
        Some(IngestFailure::DriftRejected { .. })
    ));
}

#[test]
fn test_statement_preservation_rejects_dropped_name_drift() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let drift = vec![DriftReport::NameDropped(Name::from_string("Foo.helper"))];

    let step = evaluate_statement_preservation_gate(&manifest, &observed, &drift);

    assert_eq!(step.status, StepStatus::Failed);
    let Some(IngestFailure::DriftRejected { drifts }) = step.failure else {
        panic!("expected DriftRejected");
    };
    assert_eq!(drifts, vec!["name dropped: Foo.helper".to_owned()]);
}

#[test]
fn test_authority_gates_fail_closed_without_trust_audit_reports() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);

    let report = evaluate_authority_gates(
        &manifest,
        MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: None,
            false_control_rerun: None,
        },
    );

    assert_eq!(report.statement_preservation.status, StepStatus::Passed);
    assert_eq!(report.trust_audit.status, StepStatus::Failed);
    assert!(matches!(
        report.status,
        IngestStatus::Rejected {
            step: PipelineStep::TrustAudit,
            ..
        }
    ));
}

#[test]
fn test_authority_gates_reject_manifest_without_declared_trust() {
    let patch = patch_text();
    let mut manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    manifest.declared_trust = None;
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let before = kernel_verified_audit_report();
    let after = kernel_verified_audit_report();

    let report = evaluate_authority_gates(
        &manifest,
        MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: None,
        },
    );

    assert_eq!(report.trust_audit.status, StepStatus::Failed);
    assert!(matches!(
        report.status,
        IngestStatus::Rejected {
            step: PipelineStep::TrustAudit,
            ..
        }
    ));
}

#[test]
fn test_authority_gates_wire_trust_audit_rejection() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
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

    let report = evaluate_authority_gates(
        &manifest,
        MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: None,
        },
    );

    assert_eq!(report.statement_preservation.status, StepStatus::Passed);
    assert_eq!(report.trust_audit.status, StepStatus::Failed);
    assert!(matches!(
        report.trust_audit.failure,
        Some(IngestFailure::TrustAuditRejected { .. })
    ));
    assert!(matches!(
        report.status,
        IngestStatus::Rejected {
            step: PipelineStep::TrustAudit,
            ..
        }
    ));
}

#[test]
fn test_authority_gates_reject_empty_trust_audit_evidence() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let before = AuditReportBuilder::new().build();
    let after = AuditReportBuilder::new().build();
    let false_controls = green_false_control_report();

    let report = evaluate_authority_gates(
        &manifest,
        MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: Some(MathMapFalseControlRerunInput::SuppliedReport(
                &false_controls,
            )),
        },
    );

    assert_eq!(report.statement_preservation.status, StepStatus::Passed);
    assert_eq!(report.trust_audit.status, StepStatus::Failed);
    assert!(matches!(
        report.trust_audit.failure,
        Some(IngestFailure::TrustAuditRejected { .. })
    ));
    assert_eq!(
        report
            .trust_audit
            .details
            .get("post_total_constants")
            .map(String::as_str),
        Some("0")
    );
    assert!(matches!(
        report.status,
        IngestStatus::Rejected {
            step: PipelineStep::TrustAudit,
            ..
        }
    ));
}

#[test]
fn test_authority_gates_accept_when_false_control_rerun_is_green() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let before = kernel_verified_audit_report();
    let after = kernel_verified_audit_report();
    let false_controls = green_false_control_report();

    let report = evaluate_authority_gates(
        &manifest,
        MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: Some(MathMapFalseControlRerunInput::SuppliedReport(
                &false_controls,
            )),
        },
    );

    assert_eq!(report.statement_preservation.status, StepStatus::Passed);
    assert_eq!(report.trust_audit.status, StepStatus::Passed);
    assert_eq!(report.false_control_rerun.status, StepStatus::Passed);
    assert_eq!(
        report
            .false_control_rerun
            .details
            .get("replay_ready")
            .map(String::as_str),
        Some("true")
    );
    assert_eq!(report.status, IngestStatus::Accepted);
}

#[test]
fn test_authority_gates_reject_incomplete_false_control_rerun_report() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let before = kernel_verified_audit_report();
    let after = kernel_verified_audit_report();
    let false_controls = FalseControlReport {
        controls: vec![false_control_result(
            FalseControlId::InvalidFarkasMultiplier,
            FalseControlStatus::Rejected,
            "known-bad input rejected",
        )],
    };

    let report = evaluate_authority_gates(
        &manifest,
        MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: Some(MathMapFalseControlRerunInput::SuppliedReport(
                &false_controls,
            )),
        },
    );

    assert_eq!(report.statement_preservation.status, StepStatus::Passed);
    assert_eq!(report.trust_audit.status, StepStatus::Passed);
    assert_eq!(report.false_control_rerun.status, StepStatus::Failed);
    assert_eq!(
        report
            .false_control_rerun
            .details
            .get("replay_ready")
            .map(String::as_str),
        Some("false")
    );
    assert_eq!(
        report
            .false_control_rerun
            .details
            .get("missing_control_ids")
            .map(String::as_str),
        Some(
            "broken_branch_cover,changed_llvm2_denotation,direct_false_proof,invalid_qbf_strategy"
        )
    );
    assert!(matches!(
        report.status,
        IngestStatus::Rejected {
            step: PipelineStep::FalseControlRerun,
            ..
        }
    ));
}

#[test]
fn test_authority_gates_accept_when_false_control_rerun_is_locally_generated() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let before = kernel_verified_audit_report();
    let after = kernel_verified_audit_report();
    let false_controls = green_false_control_report();

    let report = evaluate_authority_gates(
        &manifest,
        MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: Some(MathMapFalseControlRerunInput::LocalReport(&false_controls)),
        },
    );

    assert_eq!(report.statement_preservation.status, StepStatus::Passed);
    assert_eq!(report.trust_audit.status, StepStatus::Passed);
    assert_eq!(report.false_control_rerun.status, StepStatus::Passed);
    assert_eq!(
        report
            .false_control_rerun
            .details
            .get("false_control_report_source")
            .map(String::as_str),
        Some("local_generated")
    );
    assert_eq!(
        report
            .false_control_rerun
            .details
            .get("false_control_rerun_mode")
            .map(String::as_str),
        Some("local_report")
    );
    assert_eq!(
        report
            .false_control_rerun
            .details
            .get("total_controls")
            .map(String::as_str),
        Some("5")
    );
    assert_eq!(report.status, IngestStatus::Accepted);
}

#[test]
fn test_authority_gates_reject_when_false_control_rerun_is_not_green() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let before = kernel_verified_audit_report();
    let after = kernel_verified_audit_report();
    let false_controls = FalseControlReport {
        controls: FalseControlId::all()
            .iter()
            .copied()
            .map(|id| {
                let status = if id == FalseControlId::ChangedLlvm2Denotation {
                    FalseControlStatus::AcceptedBadInput
                } else {
                    FalseControlStatus::Rejected
                };
                false_control_result(id, status, "known-bad input replayed")
            })
            .collect(),
    };

    let report = evaluate_authority_gates(
        &manifest,
        MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: Some(MathMapFalseControlRerunInput::SuppliedReport(
                &false_controls,
            )),
        },
    );

    assert_eq!(report.statement_preservation.status, StepStatus::Passed);
    assert_eq!(report.trust_audit.status, StepStatus::Passed);
    assert_eq!(report.false_control_rerun.status, StepStatus::Failed);
    assert_eq!(
        report.false_control_rerun.failure,
        Some(IngestFailure::FalseControlRegressed {
            control: "changed_llvm2_denotation".to_owned(),
        })
    );
    assert!(matches!(
        report.status,
        IngestStatus::Rejected {
            step: PipelineStep::FalseControlRerun,
            ..
        }
    ));
}

#[test]
fn test_authority_gates_reject_pending_false_control() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let before = kernel_verified_audit_report();
    let after = kernel_verified_audit_report();
    let false_controls = FalseControlReport {
        controls: FalseControlId::all()
            .iter()
            .copied()
            .map(|id| {
                let status = if id == FalseControlId::DirectFalseProof {
                    FalseControlStatus::PendingBackend
                } else {
                    FalseControlStatus::Rejected
                };
                false_control_result(id, status, "control status")
            })
            .collect(),
    };

    let report = evaluate_authority_gates(
        &manifest,
        MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: Some(MathMapFalseControlRerunInput::SuppliedReport(
                &false_controls,
            )),
        },
    );

    // A control that never ran is not evidence of rejection.
    assert_eq!(report.false_control_rerun.status, StepStatus::Failed);
    assert!(matches!(
        report.status,
        IngestStatus::Rejected {
            step: PipelineStep::FalseControlRerun,
            ..
        }
    ));
}

#[test]
fn test_attempt_log_records_trust_audit_rejection_metadata() {
    let bundle_dir = tempfile::tempdir().expect("tempdir");
    let store = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(bundle_dir.path(), &manifest, &patch);
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let before = AuditReportBuilder::new().build();
    let after = {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::TrustedOracle, "SMT", AxiomProfile::SMT_ORACLE);
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Warning,
            AuditFindingCategory::AxiomDeclaration,
            "Axiom declaration: Foo.bad",
            vec![],
            None,
        ));
        builder.build()
    };

    let report = ingest_bundle_with_verifier_to_attempt_log_and_inputs(
        bundle_dir.path(),
        store.path(),
        test_config(test_policy()),
        &SkeletonSignatureVerifier,
        MathMapIngestInputs::with_authority_gates(MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: None,
        }),
    )
    .expect("ingest records an attempt");
    let attempts: Vec<_> = iter_from(store.path(), AttemptFilter::default())
        .expect("attempt log is readable")
        .collect();

    assert_eq!(attempts.len(), 1);
    let attempt = &attempts[0];
    assert!(matches!(&attempt.status, AttemptStatus::Rejected { .. }));
    assert_eq!(attempt.authority_gate.as_deref(), Some("trust_audit"));
    assert_eq!(
        attempt.failure_mode.as_deref(),
        Some("trust_audit_rejected")
    );
    assert_eq!(attempt.trust_level, Some(TrustLevel::TrustedOracle));
    let stub = report
        .proof_attempt
        .as_ref()
        .expect("recording ingest writes a stub");
    assert_eq!(stub.authority_gate.as_deref(), Some("trust_audit"));
    assert_eq!(stub.failure_mode.as_deref(), Some("trust_audit_rejected"));
    assert_eq!(stub.trust_level, Some(TrustLevel::TrustedOracle));
    let write_step = report_step(&report, PipelineStep::WriteProofAttempt);
    assert_eq!(
        write_step.details.get("authority_gate").map(String::as_str),
        Some("trust_audit")
    );
    assert_eq!(
        write_step.details.get("failure_mode").map(String::as_str),
        Some("trust_audit_rejected")
    );
    assert_eq!(
        write_step.details.get("trust_level").map(String::as_str),
        Some("TrustedOracle")
    );
}

#[test]
fn test_attempt_log_rejects_duplicate_math_map_job_id_replay() {
    let bundle_dir = tempfile::tempdir().expect("tempdir");
    let store = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(bundle_dir.path(), &manifest, &patch);

    let first = ingest_bundle_with_verifier_to_attempt_log_and_inputs(
        bundle_dir.path(),
        store.path(),
        test_config(test_policy()),
        &SkeletonSignatureVerifier,
        MathMapIngestInputs::none(),
    )
    .expect("first ingest records an attempt");
    assert!(first.proof_attempt.is_some());

    let replay = ingest_bundle_with_verifier_to_attempt_log_and_inputs(
        bundle_dir.path(),
        store.path(),
        test_config(test_policy()),
        &SkeletonSignatureVerifier,
        MathMapIngestInputs::none(),
    )
    .expect("replay ingest returns a report");

    assert!(matches!(
        replay.status,
        IngestStatus::Rejected {
            step: PipelineStep::WriteProofAttempt,
            ..
        }
    ));
    let write_step = report_step(&replay, PipelineStep::WriteProofAttempt);
    assert_eq!(write_step.status, StepStatus::Failed);
    assert_eq!(
        write_step.failure,
        Some(IngestFailure::JobIdAlreadyIngested {
            job_id: "ar-test-1".to_owned(),
        })
    );
    assert!(replay.proof_attempt.is_none());

    let attempts: Vec<_> = iter_from(store.path(), AttemptFilter::default())
        .expect("attempt log is readable")
        .collect();
    assert_eq!(attempts.len(), 1);
}

#[test]
fn test_attempt_log_rejects_replay_when_job_id_changes_but_patch_envelope_matches() {
    let first_bundle = tempfile::tempdir().expect("tempdir");
    let second_bundle = tempfile::tempdir().expect("tempdir");
    let store = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(first_bundle.path(), &manifest, &patch);

    let mut replay_manifest = manifest.clone();
    replay_manifest["job_id"] = json!("ar-test-2");
    write_bundle(second_bundle.path(), &replay_manifest, &patch);

    ingest_bundle_with_verifier_to_attempt_log_and_inputs(
        first_bundle.path(),
        store.path(),
        test_config(test_policy()),
        &SkeletonSignatureVerifier,
        MathMapIngestInputs::none(),
    )
    .expect("first ingest records an attempt");

    let replay = ingest_bundle_with_verifier_to_attempt_log_and_inputs(
        second_bundle.path(),
        store.path(),
        test_config(test_policy()),
        &SkeletonSignatureVerifier,
        MathMapIngestInputs::none(),
    )
    .expect("replay ingest returns a report");

    let write_step = report_step(&replay, PipelineStep::WriteProofAttempt);
    assert_eq!(write_step.status, StepStatus::Failed);
    assert_eq!(
        write_step.failure,
        Some(IngestFailure::JobIdAlreadyIngested {
            job_id: "ar-test-2".to_owned(),
        })
    );

    let attempts: Vec<_> = iter_from(store.path(), AttemptFilter::default())
        .expect("attempt log is readable")
        .collect();
    assert_eq!(attempts.len(), 1);
}

#[test]
fn test_attempt_log_records_unwired_false_control_metadata_fail_closed() {
    let bundle_dir = tempfile::tempdir().expect("tempdir");
    let store = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    write_bundle(bundle_dir.path(), &manifest, &patch);
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let before = AuditReportBuilder::new().build();
    let after = {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        builder.build()
    };

    let report = ingest_bundle_with_verifier_to_attempt_log_and_inputs(
        bundle_dir.path(),
        store.path(),
        test_config(test_policy()),
        &SkeletonSignatureVerifier,
        MathMapIngestInputs::with_authority_gates(MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: None,
        }),
    )
    .expect("ingest records an attempt");
    let attempts: Vec<_> = iter_from(store.path(), AttemptFilter::default())
        .expect("attempt log is readable")
        .collect();

    assert!(matches!(report.status, IngestStatus::Blocked { .. }));
    let false_control_step = report_step(&report, PipelineStep::FalseControlRerun);
    assert_eq!(false_control_step.status, StepStatus::Skipped);
    assert_eq!(false_control_step.failure, None);
    assert_eq!(
        false_control_step
            .details
            .get("false_control_report_supplied")
            .map(String::as_str),
        Some("false")
    );
    assert_eq!(
        false_control_step
            .details
            .get("blocked_reason")
            .map(String::as_str),
        Some("missing false-control rerun report")
    );
    assert_eq!(attempts.len(), 1);
    let attempt = &attempts[0];
    assert!(matches!(&attempt.status, AttemptStatus::Rejected { .. }));
    assert_eq!(
        attempt.authority_gate.as_deref(),
        Some("false_control_rerun")
    );
    assert_eq!(
        attempt.failure_mode.as_deref(),
        Some("false_control_rerun_missing")
    );
    assert_eq!(attempt.trust_level, Some(TrustLevel::KernelVerified));
}

#[test]
fn test_authority_gates_block_after_passing_when_false_control_rerun_is_missing() {
    let patch = patch_text();
    let manifest: super::BundleManifest =
        serde_json::from_value(manifest_for_patch(&patch, "fill_sorry")).expect("manifest parses");
    let observed = BTreeMap::from([("Foo.bar".to_owned(), "blake3:statement".to_owned())]);
    let before = kernel_verified_audit_report();
    let after = kernel_verified_audit_report();

    let report = evaluate_authority_gates(
        &manifest,
        MathMapAuthorityGateInputs {
            observed_target_statement_hashes: &observed,
            statement_comparison_inputs: &[],
            drift_reports: &[],
            trust_audit: Some(MathMapTrustAuditGateInput {
                before: &before,
                after: &after,
            }),
            false_control_rerun: None,
        },
    );

    assert_eq!(report.statement_preservation.status, StepStatus::Passed);
    assert_eq!(report.trust_audit.status, StepStatus::Passed);
    assert_eq!(report.false_control_rerun.status, StepStatus::Skipped);
    assert_eq!(
        report
            .false_control_rerun
            .details
            .get("false_control_report_supplied")
            .map(String::as_str),
        Some("false")
    );
    assert!(matches!(report.status, IngestStatus::Blocked { .. }));
}

#[test]
fn test_bundle_rejects_path_traversal_entry_in_archive() {
    let temp = tempfile::tempdir().expect("tempdir");
    let patch = patch_text();
    let manifest = manifest_for_patch(&patch, "fill_sorry");
    let archive = temp.path().join("hostile.tar");
    let mut tar = Vec::new();
    append_tar_entry(
        &mut tar,
        "manifest.json",
        &serde_json::to_vec_pretty(&manifest).expect("manifest serializes"),
    );
    append_tar_entry(&mut tar, "../escape.txt", b"owned");
    tar.extend_from_slice(&[0u8; 1024]);
    fs::write(&archive, tar).expect("archive written");

    let err = super::BundleFileSystem::load(&archive, 1024 * 1024)
        .expect_err("a traversal entry must be rejected");

    assert!(
        matches!(err, super::BundleLoadError::UnsafePath(_)),
        "{err}"
    );
}

fn write_tar_zst(path: &Path, entries: &[(&str, Vec<u8>)]) {
    let mut tar = Vec::new();
    for (name, bytes) in entries {
        append_tar_entry(&mut tar, name, bytes);
    }
    tar.extend_from_slice(&[0u8; 1024]);
    let compressed = zstd::stream::encode_all(Cursor::new(tar), 0).expect("zstd encodes");
    fs::write(path, compressed).expect("archive written");
}

fn append_tar_entry(tar: &mut Vec<u8>, name: &str, bytes: &[u8]) {
    let mut header = [0u8; 512];
    header[0..name.len()].copy_from_slice(name.as_bytes());
    write_octal(&mut header[100..108], 0o644);
    write_octal(&mut header[108..116], 0);
    write_octal(&mut header[116..124], 0);
    write_octal(&mut header[124..136], bytes.len() as u64);
    write_octal(&mut header[136..148], 0);
    for byte in &mut header[148..156] {
        *byte = b' ';
    }
    header[156] = b'0';
    header[257..263].copy_from_slice(b"ustar\0");
    header[263..265].copy_from_slice(b"00");
    let checksum = header.iter().map(|byte| u64::from(*byte)).sum::<u64>();
    write_octal(&mut header[148..156], checksum);
    tar.extend_from_slice(&header);
    tar.extend_from_slice(bytes);
    let padding = (512 - (bytes.len() % 512)) % 512;
    tar.extend(std::iter::repeat_n(0, padding));
}

fn write_octal(slot: &mut [u8], value: u64) {
    let text = format!("{value:0width$o}", width = slot.len() - 1);
    slot[..text.len()].copy_from_slice(text.as_bytes());
    slot[slot.len() - 1] = 0;
}
