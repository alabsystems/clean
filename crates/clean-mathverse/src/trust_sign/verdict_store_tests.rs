// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for [`super`] (the verdict store). Split out of `verdict_store.rs` to
//! keep that file within the 500-line rigor budget; included as a child module
//! via `#[path]` so `super::*` resolves to the store's items.

use super::*;
use crate::trust_sign::attestation::KernelAttestation;
use crate::trust_sign::ed25519_ring::Ed25519LocalBackend;
use crate::trust_sign::revocation::{RevocationEntry, RevocationReason};

fn att(name: &str, digest: &str, foundational: bool) -> KernelAttestation {
    KernelAttestation {
        name: name.to_string(),
        statement_digest: digest.to_string(),
        proof_digest: format!("{digest}-proof"),
        foundational,
        domain_axioms: if foundational {
            vec![]
        } else {
            vec!["Real.completeness".to_string()]
        },
        clean_version: "1.2.0".to_string(),
        clean_commit: "test-commit".to_string(),
    }
}

/// Write a signed verdict file for `att` into `<dir>/verdicts/`.
fn write_verdict(dir: &Path, att: &KernelAttestation, backend: &Ed25519LocalBackend) {
    let verdicts = dir.join("verdicts");
    std::fs::create_dir_all(&verdicts).expect("verdicts dir");
    let mut signed = SignedVerdict::from_attestation(att, "2026-06-24T00:00:00Z".to_string());
    signed.sign_with(backend).expect("sign");
    let json = serde_json::to_vec_pretty(&signed).expect("serialize");
    let safe = att.name.replace('.', "_");
    std::fs::write(verdicts.join(format!("{safe}.json")), json).expect("write");
}

/// Write a signed revocation list at `<dir>/revocation-list.json` revoking
/// the single `digest` (named `name`).
fn revoke_digest(
    dir: &Path,
    digest: &str,
    name: &str,
    reason: RevocationReason,
    backend: &Ed25519LocalBackend,
) {
    let mut list = RevocationList::new("2026-06-25T00:00:00Z".to_string());
    list.revoke(RevocationEntry {
        expr_canonical_digest: digest.to_string(),
        name: name.to_string(),
        revoked_at: "2026-06-25T00:00:00Z".to_string(),
        reason,
        detail: "test revocation".to_string(),
        clean_commit_at_revocation: "c0ffee".to_string(),
    });
    list.sign_with(backend).expect("sign list");
    std::fs::write(
        dir.join("revocation-list.json"),
        serde_json::to_vec_pretty(&list).expect("serialize list"),
    )
    .expect("write list");
}

#[test]
fn test_empty_store_reports_not_reaudited() {
    let store = VerdictStore::empty();
    assert!(!store.is_loaded());
    assert!(store.get("Anything").is_none());
    let audit = store.audit_json();
    assert_eq!(audit["reaudited"].as_bool(), Some(false));
    assert!(store.verdict_json("Anything").is_none());
}

#[test]
fn test_load_serves_signed_verdict_by_name() {
    let tmp = tempfile::tempdir().expect("tmp");
    let (backend, _secret) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
    write_verdict(
        tmp.path(),
        &att("Proj.lemma", "blake3:aaaa", true),
        &backend,
    );

    let store = VerdictStore::load(tmp.path()).expect("load");
    assert!(store.is_loaded());
    assert_eq!(store.examined(), 1);

    let stored = store.get("Proj.lemma").expect("present");
    assert!(stored.is_live_kernel_verified());
    assert_eq!(
        stored.effective_verdict(),
        SignedVerdictKind::KernelVerified
    );

    let payload = store.verdict_json("Proj.lemma").expect("payload");
    assert_eq!(payload["verdict"].as_str(), Some("KernelVerified"));
    assert_eq!(payload["revoked"].as_bool(), Some(false));
    assert_eq!(
        payload["expr_canonical_digest"].as_str(),
        Some("blake3:aaaa")
    );
    assert!(
        payload["trust_note"]
            .as_str()
            .unwrap_or("")
            .contains("attests PROVENANCE"),
        "verdict payload carries the honesty note"
    );
    // The verbatim signed record is present for offline re-verification.
    assert_eq!(
        payload["signed_record"]["schema"].as_str(),
        Some(super::super::signed_verdict::SIGNED_VERDICT_SCHEMA)
    );
}

#[test]
fn test_revoked_claim_badge_is_stripped() {
    let tmp = tempfile::tempdir().expect("tmp");
    let (backend, _secret) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
    let attestation = att("Proj.demoted", "blake3:dddd", true);
    write_verdict(tmp.path(), &attestation, &backend);

    // Write a revocation list that revokes this digest.
    revoke_digest(
        tmp.path(),
        "blake3:dddd",
        "Proj.demoted",
        RevocationReason::NowAxiomDependent,
        &backend,
    );

    let store = VerdictStore::load(tmp.path()).expect("load");
    let stored = store.get("Proj.demoted").expect("present");
    assert!(stored.revoked, "claim is revoked");
    assert!(
        !stored.is_live_kernel_verified(),
        "a revoked claim is not a live KernelVerified"
    );
    assert_eq!(stored.effective_verdict(), SignedVerdictKind::Revoked);

    let payload = store.verdict_json("Proj.demoted").expect("payload");
    assert_eq!(
        payload["verdict"].as_str(),
        Some("Revoked"),
        "the served badge is Revoked even though the signed kind was KernelVerified"
    );
    assert_eq!(payload["revoked"].as_bool(), Some(true));
}

#[test]
fn test_audit_summary_counts() {
    let tmp = tempfile::tempdir().expect("tmp");
    let (backend, _secret) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
    write_verdict(tmp.path(), &att("Proj.a", "blake3:a", true), &backend);
    write_verdict(tmp.path(), &att("Proj.b", "blake3:b", true), &backend);
    // A non-foundational one signs as Rejected.
    write_verdict(tmp.path(), &att("Proj.c", "blake3:c", false), &backend);

    // Revoke Proj.b.
    revoke_digest(
        tmp.path(),
        "blake3:b",
        "Proj.b",
        RevocationReason::NoLongerVerifies,
        &backend,
    );

    let store = VerdictStore::load(tmp.path()).expect("load");
    let audit = store.audit_json();
    assert_eq!(audit["reaudited"].as_bool(), Some(true));
    assert_eq!(audit["examined"].as_u64(), Some(3));
    assert_eq!(
        audit["signed_kernel_verified"].as_u64(),
        Some(1),
        "Proj.a is the only live KernelVerified (Proj.b revoked, Proj.c rejected)"
    );
    assert_eq!(audit["rejected"].as_u64(), Some(1));
    assert_eq!(audit["revoked"].as_u64(), Some(1));
    assert_eq!(audit["revocation_list"]["entries"].as_u64(), Some(1));
}

#[test]
fn test_malformed_verdict_file_is_skipped() {
    let tmp = tempfile::tempdir().expect("tmp");
    let verdicts = tmp.path().join("verdicts");
    std::fs::create_dir_all(&verdicts).expect("dir");
    // A KernelVerified record with a non-empty closure violates the
    // structural invariants → must be dropped, not served.
    let bad = serde_json::json!({
        "schema": super::super::signed_verdict::SIGNED_VERDICT_SCHEMA,
        "name": "Forged.lemma",
        "expr_canonical_digest": "blake3:forged",
        "proof_canonical_digest": "blake3:forged-proof",
        "verdict": "KernelVerified",
        "axiom_closure": ["Sneaky.axiom"],
        "foundational": true,
        "verifier": { "clean_version": "1.2.0", "clean_commit": "x", "tcb_axioms": 3 },
        "verified_at": "2026-06-24T00:00:00Z",
        "key_id": "k",
        "sig_alg": "ed25519",
        "signature": "00"
    });
    std::fs::write(
        verdicts.join("forged.json"),
        serde_json::to_vec_pretty(&bad).expect("ser"),
    )
    .expect("write");
    // Also a flat-out non-JSON file.
    std::fs::write(verdicts.join("garbage.json"), b"not json").expect("write");

    let store = VerdictStore::load(tmp.path()).expect("load");
    assert_eq!(
        store.examined(),
        0,
        "a structurally-invalid KernelVerified and a non-JSON file are both skipped"
    );
    assert!(store.get("Forged.lemma").is_none());
}
