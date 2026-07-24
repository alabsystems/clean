// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for [`super`] (the re-auditor). Split out of `reauditor.rs` to keep
//! that file within the 500-line rigor budget; included as a child module via
//! `#[path]` so `super::*` still resolves to the re-auditor's internals.

use super::*;
use clean_kernel::{BinderInfo, Expr, Name};

use crate::graduate::{
    graduate, EvidenceClass, GraduationBaseline, GraduationRequest, OnDuplicate,
};
use crate::trust_sign::ed25519_ring::{Ed25519LocalBackend, Ed25519Verifier};
use crate::trust_sign::signed_verdict::SignedVerdictKind;

const FOUND_THM: &str = "Reaudit.imp_self";

fn bd() -> BinderInfo {
    BinderInfo::Default
}

/// `∀ (p : Prop), p → p`.
fn imp_self_type() -> Expr {
    Expr::pi(
        bd(),
        Expr::prop(),
        Expr::pi(bd(), Expr::bvar(0), Expr::bvar(1)),
    )
}

/// `fun (p : Prop) (h : p) => h`.
fn imp_self_value() -> Expr {
    Expr::lam(
        bd(),
        Expr::prop(),
        Expr::lam(bd(), Expr::bvar(0), Expr::bvar(0)),
    )
}

fn req() -> GraduationRequest {
    GraduationRequest {
        project_name: "reaudit-test".to_string(),
        manifest_kind: "clean-math-project-v1".to_string(),
        manifest_digest: "blake3:fixture".to_string(),
        certificate_schema: Some("clean-math-certificate-v1".to_string()),
        certificate_cross_checks: Vec::new(),
        mathverse_release: "fixture".to_string(),
        on_duplicate: OnDuplicate::Reject,
        attempt_id: Some("reaudit-0001".to_string()),
        replay_archive_sha256: Some(format!("sha256:{}", "0".repeat(64))),
        engine: Some("reaudit-test".to_string()),
        seed: Some("0".to_string()),
        evidence_class: EvidenceClass::HarnessTranscribed,
        residual_risk: "fixture".to_string(),
        clean_commit: Some("fixture-commit".to_string()),
        shard_filename: None,
        decided_at_epoch_s: Some(0),
        env_provenance: None,
        score_identity: false,
        score_defeq: false,
    }
}

/// Graduate the single foundational theorem into `out_dir`, returning the
/// `.mathverse` shard path. This is a GENUINE green: the shard is produced
/// by the real intake gate (kernel re-check + digest binding).
fn graduate_foundational(out_dir: &Path) -> PathBuf {
    let mut env = clean_kernel::Environment::new();
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(FOUND_THM),
        level_params: vec![],
        type_: imp_self_type(),
        value: imp_self_value(),
    })
    .expect("foundational theorem kernel-checks");
    let record = graduate(
        &env,
        &[Name::from_string(FOUND_THM)],
        &req(),
        &GraduationBaseline::empty(),
        out_dir,
    )
    .expect("graduation runs");
    assert!(
        record.result.accepted.iter().any(|n| n == FOUND_THM),
        "the foundational theorem must be accepted (genuine green)"
    );
    out_dir.join(&record.result.shard_filename)
}

#[test]
fn test_reaudit_genuine_green_signs_valid_kernel_verified_verdict() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let shard_path = graduate_foundational(tmp.path());

    let (backend, _secret) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
    let report = reaudit_shard(&shard_path, &backend, "live-commit", "2026-06-24T00:00:00Z")
        .expect("re-audit runs on a genuine green");

    assert_eq!(report.examined, 1, "one value-bearing theorem in the shard");
    assert_eq!(report.reverified, 1, "the genuine green re-earns");
    let v = &report.verdicts[0];
    assert_eq!(v.name, FOUND_THM);
    assert!(v.outcome.is_kernel_verified());
    assert_eq!(v.signed.verdict, SignedVerdictKind::KernelVerified);
    assert!(v.signed.foundational);
    assert!(v.signed.axiom_closure.is_empty());
    assert!(v.signed.expr_canonical_digest.starts_with("blake3:"));
    assert!(v.signed.proof_canonical_digest.starts_with("blake3:"));

    // The signed KernelVerified verdict verifies against the public key.
    let verifier = Ed25519Verifier::new("ed25519-local:test", backend.public_key_bytes());
    v.signed
        .verify_with(&verifier)
        .expect("genuine green signed verdict verifies");
}

#[test]
fn test_reaudit_tampered_verdict_fails_signature_verification() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let shard_path = graduate_foundational(tmp.path());

    let (backend, _secret) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
    let report = reaudit_shard(&shard_path, &backend, "live-commit", "2026-06-24T00:00:00Z")
        .expect("re-audit runs");
    let mut signed = report.verdicts[0].signed.clone();

    // Tamper with the proof digest AFTER signing — a consumer recomputing
    // from the shard would see the mismatch; here the signature catches it.
    signed.proof_canonical_digest = "blake3:tampered".to_string();
    let verifier = Ed25519Verifier::new("ed25519-local:test", backend.public_key_bytes());
    let err = signed
        .verify_with(&verifier)
        .expect_err("a tampered signed verdict must fail verification");
    assert!(matches!(err, SigningError::Verify(_)));
}

#[test]
fn test_reaudit_tampered_shard_fails_closed_no_green() {
    // A shard whose bytes were rewritten after graduation breaks the
    // digest binding; the cake gate (and thus the re-auditor) fails closed.
    let tmp = tempfile::tempdir().expect("tempdir");
    let shard_path = graduate_foundational(tmp.path());

    let mut bytes = std::fs::read(&shard_path).expect("read shard");
    let mid = bytes.len() / 2;
    bytes[mid] ^= 0xFF;
    std::fs::write(&shard_path, &bytes).expect("write tampered shard");

    let (backend, _secret) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
    let err = reaudit_shard(&shard_path, &backend, "live-commit", "2026-06-24T00:00:00Z")
        .expect_err("tampered shard must fail the re-auditor, never green");
    // Tamper is caught fail-closed either by the shard's internal blake3
    // footer (`ShardRead`) or, if it survives that, by the cake gate's
    // record digest binding (`CakeGate`). Both are hard errors — no verdict
    // is signed for a tampered shard.
    assert!(
        matches!(
            err,
            ReauditError::ShardRead { .. } | ReauditError::CakeGate { .. }
        ),
        "tamper must surface as a fail-closed error (footer or gate digest), not a green: {err}"
    );
}

#[test]
fn test_could_not_reverify_is_never_signed_as_kernel_verified() {
    // Drive `sign_outcome` directly with a could-not-reverify outcome and a
    // None attestation (the reconstruct/recheck-failure path). The signed
    // record MUST be Rejected, never KernelVerified — the structural fence.
    let (backend, _secret) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
    let v = sign_outcome(
        "Reaudit.broken",
        None,
        ReauditOutcome::CouldNotReverify("reconstruct failed: synthetic".to_string()),
        &backend,
        "live-commit",
        "2026-06-24T00:00:00Z",
    )
    .expect("could-not-reverify still produces a (Rejected) signed record");
    assert!(!v.outcome.is_kernel_verified());
    assert_eq!(
        v.signed.verdict,
        SignedVerdictKind::Rejected,
        "a non-replaying decl is NEVER signed as KernelVerified"
    );
    assert!(!v.signed.foundational);
    // It still verifies as a Rejected record (provenance of the rejection).
    let verifier = Ed25519Verifier::new("ed25519-local:test", backend.public_key_bytes());
    v.signed
        .verify_with(&verifier)
        .expect("the Rejected verdict's signature is authentic");
}

#[test]
fn test_axiom_dependent_outcome_signs_as_rejected_and_revokes() {
    // An axiom-dependent attestation classifies as AxiomDependent and signs
    // as Rejected; the revocation list records it now-axiom-dependent.
    let (backend, _secret) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
    let att = KernelAttestation {
        name: "Reaudit.uses_axiom".to_string(),
        statement_digest: "blake3:aaaa".to_string(),
        proof_digest: "blake3:bbbb".to_string(),
        foundational: false,
        domain_axioms: vec!["Real.completeness".to_string()],
        clean_version: env!("CARGO_PKG_VERSION").to_string(),
        clean_commit: "live-commit".to_string(),
    };
    let v = sign_outcome(
        "Reaudit.uses_axiom",
        Some(att),
        ReauditOutcome::AxiomDependent,
        &backend,
        "live-commit",
        "2026-06-24T00:00:00Z",
    )
    .expect("axiom-dependent signs as Rejected");
    assert_eq!(v.signed.verdict, SignedVerdictKind::Rejected);

    let mut report = ReauditReport {
        verdicts: vec![v],
        examined: 1,
        reverified: 0,
    };
    report.examined = 1;
    let mut list = RevocationList::new("2026-06-25T00:00:00Z".to_string());
    let appended = report.append_revocations(&mut list, "2026-06-25T00:00:00Z", "live-commit");
    assert_eq!(appended, 1, "the axiom-dependent claim is revoked");
    assert_eq!(
        list.revocations[0].reason,
        RevocationReason::NowAxiomDependent
    );
    assert!(list.is_revoked("blake3:aaaa"));
}
