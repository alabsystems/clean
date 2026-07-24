// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `mathverse-revocation-list-v1` schema.
//!
//! The re-auditor periodically re-earns every signed `KernelVerified` claim via
//! `shard_verify::cake_gate::verify_cake_shard` under the CURRENT kernel
//! commit. A claim that no longer re-earns is **revoked** — appended to a
//! signed, append-only, monotone revocation list keyed by
//! `expr_canonical_digest`.
//!
//! Consumer trust is `signed ∧ ¬revoked` (and, if they choose, their own
//! re-check). The whole list is signed so a consumer cannot be tricked into
//! ignoring a revocation that exists — provided they hold the current list.

use serde::{Deserialize, Serialize};

use super::backend::{SigningBackend, SigningError, VerifyingBackend};

/// The pinned revocation-list schema identifier.
pub const REVOCATION_LIST_SCHEMA: &str = "mathverse-revocation-list-v1";

/// Why a previously-`KernelVerified` claim was revoked.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum RevocationReason {
    /// The kernel re-check now fails outright (`KernelRejected`/`Unclassifiable`).
    NoLongerVerifies,
    /// Re-check succeeds but the closure is no longer foundational-only.
    NowAxiomDependent,
    /// The shard ⇄ record binding broke, or a recomputed digest disagreed.
    TamperDetected,
    /// A sharper/corrected claim replaced it (administrative).
    Superseded,
}

/// One revocation entry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RevocationEntry {
    /// The revoked claim's identity (de Bruijn statement digest).
    pub expr_canonical_digest: String,
    pub name: String,
    /// RFC-3339 UTC timestamp.
    pub revoked_at: String,
    pub reason: RevocationReason,
    /// Human-readable detail (e.g. the cake-gate violation text).
    pub detail: String,
    /// The kernel commit under which the claim failed to re-earn.
    pub clean_commit_at_revocation: String,
}

/// The signed revocation list.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RevocationList {
    pub schema: String,
    pub issued_at: String,
    pub key_id: String,
    pub sig_alg: String,
    /// Append-only, monotone: a digest, once revoked, stays revoked.
    pub revocations: Vec<RevocationEntry>,
    /// Hex of the signature over the list with `signature` cleared.
    pub signature: String,
}

impl RevocationList {
    /// A fresh, empty, unsigned list.
    #[must_use]
    pub fn new(issued_at: String) -> Self {
        Self {
            schema: REVOCATION_LIST_SCHEMA.to_string(),
            issued_at,
            key_id: String::new(),
            sig_alg: String::new(),
            revocations: Vec::new(),
            signature: String::new(),
        }
    }

    /// `true` iff `digest` appears in the list (claim is revoked).
    #[must_use]
    pub fn is_revoked(&self, digest: &str) -> bool {
        self.revocations
            .iter()
            .any(|e| e.expr_canonical_digest == digest)
    }

    /// Append a revocation, preserving monotonicity: a digest already present
    /// is NOT re-added (the earliest revocation stands). Returns `true` if a
    /// new entry was appended.
    pub fn revoke(&mut self, entry: RevocationEntry) -> bool {
        if self.is_revoked(&entry.expr_canonical_digest) {
            return false;
        }
        self.revocations.push(entry);
        true
    }

    /// Canonical bytes that get signed: the list with `signature` cleared,
    /// serialized deterministically (serde preserves struct field order).
    pub fn canonical_bytes(&self) -> Result<Vec<u8>, SigningError> {
        let mut canonical = self.clone();
        canonical.signature = String::new();
        serde_json::to_vec(&canonical)
            .map_err(|e| SigningError::Sign(format!("canonical serialization: {e}")))
    }

    /// Sign the list in place.
    pub fn sign_with(&mut self, backend: &dyn SigningBackend) -> Result<(), SigningError> {
        self.key_id = backend.key_id().to_string();
        self.sig_alg = backend.sig_alg().to_string();
        let bytes = self.canonical_bytes()?;
        let sig = backend.sign(&bytes)?;
        self.signature = hex_encode(&sig);
        Ok(())
    }

    /// Verify the list's signature. `Ok(())` means authentic; any error means
    /// **do not trust this list** (and a consumer should fail closed — treat
    /// the unverified list as if it might be hiding revocations).
    pub fn verify_with(&self, backend: &dyn VerifyingBackend) -> Result<(), SigningError> {
        if self.schema != REVOCATION_LIST_SCHEMA {
            return Err(SigningError::Verify(format!(
                "unexpected revocation-list schema `{}`",
                self.schema
            )));
        }
        if self.sig_alg != backend.sig_alg() {
            return Err(SigningError::AlgorithmMismatch {
                record: self.sig_alg.clone(),
                backend: backend.sig_alg().to_string(),
            });
        }
        let bytes = self.canonical_bytes()?;
        let sig = hex_decode(&self.signature)
            .ok_or_else(|| SigningError::Verify("signature is not valid hex".to_string()))?;
        backend.verify(&bytes, &sig)
    }
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode(s: &str) -> Option<Vec<u8>> {
    if !s.len().is_multiple_of(2) {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trust_sign::ed25519_ring::{Ed25519LocalBackend, Ed25519Verifier};

    fn entry(digest: &str) -> RevocationEntry {
        RevocationEntry {
            expr_canonical_digest: digest.to_string(),
            name: "Test.demoted".to_string(),
            revoked_at: "2026-06-25T00:00:00Z".to_string(),
            reason: RevocationReason::NowAxiomDependent,
            detail: "cake gate: depends on Real.completeness".to_string(),
            clean_commit_at_revocation: "c0ffee".to_string(),
        }
    }

    #[test]
    fn test_revoke_is_monotone() {
        let mut list = RevocationList::new("2026-06-25T00:00:00Z".to_string());
        assert!(list.revoke(entry("blake3:aaaa")));
        assert!(
            !list.revoke(entry("blake3:aaaa")),
            "duplicate revocation is a no-op"
        );
        assert_eq!(list.revocations.len(), 1);
        assert!(list.is_revoked("blake3:aaaa"));
        assert!(!list.is_revoked("blake3:bbbb"));
    }

    #[test]
    fn test_revocation_list_round_trip_verifies() {
        let (backend, _) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
        let mut list = RevocationList::new("2026-06-25T00:00:00Z".to_string());
        list.revoke(entry("blake3:aaaa"));
        list.sign_with(&backend).expect("signs");
        let verifier = Ed25519Verifier::new("ed25519-local:test", backend.public_key_bytes());
        list.verify_with(&verifier)
            .expect("authentic list verifies");
    }

    #[test]
    fn test_tampered_revocation_list_fails_closed() {
        let (backend, _) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
        let mut list = RevocationList::new("2026-06-25T00:00:00Z".to_string());
        list.revoke(entry("blake3:aaaa"));
        list.sign_with(&backend).expect("signs");
        // Drop the revocation after signing → an attacker trying to hide it.
        list.revocations.clear();
        let verifier = Ed25519Verifier::new("ed25519-local:test", backend.public_key_bytes());
        let err = list
            .verify_with(&verifier)
            .expect_err("a list with a dropped revocation must fail verification");
        assert!(matches!(err, SigningError::Verify(_)));
    }
}
