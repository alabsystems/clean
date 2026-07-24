// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `mathverse-signed-verdict-v1` schema and its soundness invariants.
//!
//! A [`SignedVerdict`] attests **provenance**: a named verifier, at a pinned
//! `clean_version`/`clean_commit` with `tcb_axioms == 3`, re-ran its kernel
//! over a content-addressed declaration and observed a verdict. The signature
//! covers every field except `signature` itself (the canonical verdict bytes).
//!
//! Soundness fences enforced here (not just documented):
//! * a `KernelVerified` verdict REQUIRES `foundational == true` AND an empty
//!   `axiom_closure` — the signer refuses otherwise;
//! * `tcb_axioms` is pinned at [`PINNED_TCB_AXIOMS`];
//! * a verifier re-checks these invariants BEFORE checking the signature, so a
//!   malformed-but-correctly-signed record is still rejected.

use serde::{Deserialize, Serialize};

use super::attestation::KernelAttestation;
use super::backend::{SigningBackend, SigningError, VerifyingBackend};

/// The pinned signed-verdict schema identifier.
pub const SIGNED_VERDICT_SCHEMA: &str = "mathverse-signed-verdict-v1";

/// The pinned TCB axiom count: the three canonical Lean foundational axioms
/// (`propext`, `Quot.sound`, `Classical.choice`). See
/// `docs/SOUNDNESS_CERTIFICATE.md`.
pub const PINNED_TCB_AXIOMS: u32 = 3;

/// The kernel-re-check verdict carried by a signed record.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SignedVerdictKind {
    /// The kernel re-checked the declaration WITH its proof value and the
    /// transitive axiom closure is foundational-only.
    KernelVerified,
    /// The candidate did not earn a kernel verdict (closure non-foundational,
    /// or the kernel rejected it).
    Rejected,
    /// A previously-`KernelVerified` claim the re-auditor demoted (it no longer
    /// re-earns under the current kernel). Never produced by the signer at
    /// mint time; only by the re-auditor via the revocation list.
    Revoked,
}

/// The verifier identity pinned into a signed verdict.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerifierInfo {
    pub clean_version: String,
    pub clean_commit: String,
    /// Pinned at [`PINNED_TCB_AXIOMS`]; a different value is rejected.
    pub tcb_axioms: u32,
}

/// A signed provenance attestation for one kernel-re-verified declaration.
///
/// The struct field order IS the canonical byte order (serde preserves it);
/// see [`Self::canonical_bytes`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SignedVerdict {
    pub schema: String,
    pub name: String,
    /// de Bruijn (FlatExpr) digest of the declaration TYPE — the claim identity.
    pub expr_canonical_digest: String,
    /// de Bruijn digest of the declaration VALUE — the specific proof term.
    pub proof_canonical_digest: String,
    pub verdict: SignedVerdictKind,
    /// Transitive NON-foundational axioms, sorted. Empty iff `foundational`.
    pub axiom_closure: Vec<String>,
    pub foundational: bool,
    pub verifier: VerifierInfo,
    /// RFC-3339 UTC timestamp string.
    pub verified_at: String,
    pub key_id: String,
    pub sig_alg: String,
    /// Hex of the signature over the canonical bytes ([`Self::canonical_bytes`]).
    /// Empty while computing the bytes to sign.
    pub signature: String,
}

/// Why a signed verdict is structurally invalid (independent of the
/// signature). Checked BEFORE the signature so a correctly-signed but
/// ill-formed record is still rejected (fail-closed).
#[derive(Clone, Debug, thiserror::Error)]
#[non_exhaustive]
pub enum VerdictInvariantError {
    #[error("unexpected schema `{0}`, expected `{SIGNED_VERDICT_SCHEMA}`")]
    Schema(String),
    #[error(
        "KernelVerified verdict must be foundational with an empty axiom closure \
         (foundational={foundational}, closure_len={closure_len})"
    )]
    KernelVerifiedNotFoundational {
        foundational: bool,
        closure_len: usize,
    },
    #[error("foundational=true requires an empty axiom closure (closure_len={0})")]
    FoundationalWithClosure(usize),
    #[error("tcb_axioms must be {PINNED_TCB_AXIOMS}, got {0}")]
    TcbAxioms(u32),
}

impl SignedVerdict {
    /// Build an UNSIGNED verdict from a kernel attestation. The verdict kind is
    /// derived from the attestation's foundational flag — the signer cannot
    /// upgrade a non-foundational attestation to `KernelVerified`.
    #[must_use]
    pub fn from_attestation(att: &KernelAttestation, verified_at: String) -> Self {
        let (verdict, foundational) = if att.foundational {
            (SignedVerdictKind::KernelVerified, true)
        } else {
            (SignedVerdictKind::Rejected, false)
        };
        Self {
            schema: SIGNED_VERDICT_SCHEMA.to_string(),
            name: att.name.clone(),
            expr_canonical_digest: att.statement_digest.clone(),
            proof_canonical_digest: att.proof_digest.clone(),
            verdict,
            axiom_closure: att.domain_axioms.clone(),
            foundational,
            verifier: VerifierInfo {
                clean_version: att.clean_version.clone(),
                clean_commit: att.clean_commit.clone(),
                tcb_axioms: PINNED_TCB_AXIOMS,
            },
            verified_at,
            key_id: String::new(),
            sig_alg: String::new(),
            signature: String::new(),
        }
    }

    /// Re-check the structural soundness invariants. Run by the signer before
    /// signing AND by every verifier before trusting.
    pub fn check_invariants(&self) -> Result<(), VerdictInvariantError> {
        if self.schema != SIGNED_VERDICT_SCHEMA {
            return Err(VerdictInvariantError::Schema(self.schema.clone()));
        }
        if self.verifier.tcb_axioms != PINNED_TCB_AXIOMS {
            return Err(VerdictInvariantError::TcbAxioms(self.verifier.tcb_axioms));
        }
        if self.verdict == SignedVerdictKind::KernelVerified
            && (!self.foundational || !self.axiom_closure.is_empty())
        {
            return Err(VerdictInvariantError::KernelVerifiedNotFoundational {
                foundational: self.foundational,
                closure_len: self.axiom_closure.len(),
            });
        }
        if self.foundational && !self.axiom_closure.is_empty() {
            return Err(VerdictInvariantError::FoundationalWithClosure(
                self.axiom_closure.len(),
            ));
        }
        Ok(())
    }

    /// The canonical bytes that get signed: this record with `signature`
    /// cleared, serialized deterministically (serde preserves struct field
    /// order — the same scheme `GraduationRecord::binding_digest` uses).
    pub fn canonical_bytes(&self) -> Result<Vec<u8>, SigningError> {
        let mut canonical = self.clone();
        canonical.signature = String::new();
        serde_json::to_vec(&canonical)
            .map_err(|e| SigningError::Sign(format!("canonical serialization: {e}")))
    }

    /// Sign this verdict in place with `backend`. Refuses to sign if the
    /// structural invariants do not hold (so a `KernelVerified` over a
    /// non-foundational closure can never be signed).
    pub fn sign_with(&mut self, backend: &dyn SigningBackend) -> Result<(), SigningError> {
        self.check_invariants()
            .map_err(|e| SigningError::Sign(format!("refusing to sign invalid verdict: {e}")))?;
        self.key_id = backend.key_id().to_string();
        self.sig_alg = backend.sig_alg().to_string();
        let bytes = self.canonical_bytes()?;
        let sig = backend.sign(&bytes)?;
        self.signature = hex_encode(&sig);
        Ok(())
    }

    /// Verify this verdict's signature with `backend` after re-checking the
    /// structural invariants. `Ok(())` means both the invariants hold AND the
    /// signature is authentic; any error means **do not trust**.
    pub fn verify_with(&self, backend: &dyn VerifyingBackend) -> Result<(), SigningError> {
        self.check_invariants()
            .map_err(|e| SigningError::Verify(format!("invalid verdict: {e}")))?;
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

/// Lowercase hex encode.
fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Decode lowercase/uppercase hex; `None` on any malformed input.
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
    use crate::trust_sign::hmac_dev::HmacDevBackend;

    fn foundational_att() -> KernelAttestation {
        KernelAttestation {
            name: "Test.lemma".to_string(),
            statement_digest: "blake3:aaaa".to_string(),
            proof_digest: "blake3:bbbb".to_string(),
            foundational: true,
            domain_axioms: vec![],
            clean_version: "1.2.0".to_string(),
            clean_commit: "deadbeef".to_string(),
        }
    }

    fn axiom_dependent_att() -> KernelAttestation {
        KernelAttestation {
            name: "Test.uses_axiom".to_string(),
            statement_digest: "blake3:cccc".to_string(),
            proof_digest: "blake3:dddd".to_string(),
            foundational: false,
            domain_axioms: vec!["Real.completeness".to_string()],
            clean_version: "1.2.0".to_string(),
            clean_commit: "deadbeef".to_string(),
        }
    }

    #[test]
    fn test_foundational_attestation_signs_as_kernel_verified() {
        let (backend, _) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
        let mut verdict = SignedVerdict::from_attestation(
            &foundational_att(),
            "2026-06-24T00:00:00Z".to_string(),
        );
        assert_eq!(verdict.verdict, SignedVerdictKind::KernelVerified);
        verdict
            .sign_with(&backend)
            .expect("foundational verdict signs");
        let verifier = Ed25519Verifier::new("ed25519-local:test", backend.public_key_bytes());
        verdict
            .verify_with(&verifier)
            .expect("authentic verdict verifies");
    }

    #[test]
    fn test_non_foundational_attestation_signs_as_rejected_not_verified() {
        let att = axiom_dependent_att();
        let verdict = SignedVerdict::from_attestation(&att, "2026-06-24T00:00:00Z".to_string());
        // The signer cannot upgrade a non-foundational attestation.
        assert_eq!(verdict.verdict, SignedVerdictKind::Rejected);
        assert!(!verdict.foundational);
        assert_eq!(verdict.axiom_closure, vec!["Real.completeness".to_string()]);
    }

    #[test]
    fn test_kernel_verified_with_nonempty_closure_refuses_to_sign() {
        // Hand-forge an inconsistent record: KernelVerified but with a domain
        // axiom in the closure. The signer MUST refuse it.
        let (backend, _) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
        let mut forged = SignedVerdict::from_attestation(
            &foundational_att(),
            "2026-06-24T00:00:00Z".to_string(),
        );
        forged.axiom_closure = vec!["Sneaky.axiom".to_string()];
        let err = forged
            .sign_with(&backend)
            .expect_err("a KernelVerified verdict with a non-empty closure must not sign");
        assert!(matches!(err, SigningError::Sign(_)));
    }

    #[test]
    fn test_kernel_verified_not_foundational_invariant_rejected() {
        let mut forged = SignedVerdict::from_attestation(&foundational_att(), "t".to_string());
        forged.foundational = false; // KernelVerified but not foundational.
        assert!(matches!(
            forged.check_invariants(),
            Err(VerdictInvariantError::KernelVerifiedNotFoundational { .. })
        ));
    }

    #[test]
    fn test_wrong_tcb_axioms_rejected() {
        let mut forged = SignedVerdict::from_attestation(&foundational_att(), "t".to_string());
        forged.verifier.tcb_axioms = 9;
        assert!(matches!(
            forged.check_invariants(),
            Err(VerdictInvariantError::TcbAxioms(9))
        ));
    }

    #[test]
    fn test_tampered_signed_verdict_fails_verification() {
        let (backend, _) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
        let mut verdict = SignedVerdict::from_attestation(
            &foundational_att(),
            "2026-06-24T00:00:00Z".to_string(),
        );
        verdict.sign_with(&backend).expect("signs");
        // Tamper with the digest AFTER signing.
        verdict.expr_canonical_digest = "blake3:tampered".to_string();
        let verifier = Ed25519Verifier::new("ed25519-local:test", backend.public_key_bytes());
        let err = verdict
            .verify_with(&verifier)
            .expect_err("tampered record must fail signature verification");
        assert!(matches!(err, SigningError::Verify(_)));
    }

    #[test]
    fn test_canonical_bytes_are_deterministic() {
        let v = SignedVerdict::from_attestation(&foundational_att(), "t".to_string());
        assert_eq!(
            v.canonical_bytes().expect("a"),
            v.canonical_bytes().expect("b"),
            "canonical bytes must be reproducible"
        );
    }

    #[test]
    fn test_hmac_dev_backend_signs_but_is_not_asymmetric() {
        let backend = HmacDevBackend::new("hmac-dev:test", b"secret".to_vec());
        let mut verdict = SignedVerdict::from_attestation(&foundational_att(), "t".to_string());
        verdict.sign_with(&backend).expect("hmac signs");
        assert_eq!(verdict.sig_alg, "hmac-sha256");
        verdict.verify_with(&backend).expect("hmac verifies");
        assert!(
            !SigningBackend::is_asymmetric(&backend),
            "HMAC must declare itself non-asymmetric so consumers can refuse it"
        );
    }

    #[test]
    fn test_algorithm_mismatch_rejected() {
        let (signer, _) = Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair");
        let mut verdict = SignedVerdict::from_attestation(&foundational_att(), "t".to_string());
        verdict.sign_with(&signer).expect("signs ed25519");
        // Verify with an HMAC backend → algorithm mismatch, fail closed.
        let hmac = HmacDevBackend::new("hmac-dev:test", b"secret".to_vec());
        let err = verdict
            .verify_with(&hmac)
            .expect_err("ed25519 record verified with hmac backend must fail");
        assert!(matches!(err, SigningError::AlgorithmMismatch { .. }));
    }
}
