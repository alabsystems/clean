// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Signing/verifying backend traits for the Phase-2 trust layer.
//!
//! A [`SigningBackend`] attests **provenance**: "this key saw these canonical
//! verdict bytes". It says nothing about the *truth* of the verdict — that is
//! independently re-derivable by re-running the kernel over the
//! content-addressed digest (the de Bruijn criterion). See
//! [`crate::trust_sign`] for the trust semantics.
//!
//! The signature is always computed over the canonical verdict bytes
//! ([`crate::trust_sign::signed_verdict::SignedVerdict::canonical_bytes`]).

/// Why a sign or verify call failed. Fail-closed: a verify error means
/// "do not trust", never "trust anyway".
#[derive(Clone, Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SigningError {
    /// The backend could not load or parse its key material.
    #[error("signing key error: {0}")]
    Key(String),

    /// The underlying signing primitive failed (should be rare; treated as a
    /// hard error, never a silent unsigned pass).
    #[error("signature operation failed: {0}")]
    Sign(String),

    /// Verification rejected the signature for the given bytes. The trust
    /// decision is "untrusted".
    #[error("signature verification failed: {0}")]
    Verify(String),

    /// The record's `sig_alg` does not match the backend's algorithm.
    #[error("algorithm mismatch: record uses `{record}`, backend provides `{backend}`")]
    AlgorithmMismatch { record: String, backend: String },
}

/// A provenance-signing backend. The signature is over the canonical verdict
/// bytes; it attests "this key saw these bytes", nothing about truth.
pub trait SigningBackend: Send + Sync {
    /// Stable identifier of the signing key (e.g. `"ed25519-local:2026-06"`,
    /// `"gcp-kms:projects/…/cryptoKeyVersions/3"`). Embedded in the record so a
    /// verifier can select the matching public key.
    fn key_id(&self) -> &str;

    /// The `sig_alg` label written into the record (e.g. `"ed25519"`,
    /// `"hmac-sha256"`). A verifier selects its backend by this label and
    /// refuses an algorithm it does not recognise.
    fn sig_alg(&self) -> &str;

    /// `true` for a public-key signature a third party can verify WITHOUT the
    /// secret. `false` for a keyed-hash (HMAC) fallback, verifiable only by a
    /// key holder. A consumer that requires non-repudiation refuses `false`.
    fn is_asymmetric(&self) -> bool;

    /// Sign the canonical verdict bytes. Returns the detached signature bytes
    /// (the caller hex-encodes for the record).
    fn sign(&self, canonical_bytes: &[u8]) -> Result<Vec<u8>, SigningError>;
}

/// The verification side: consumers, and the re-auditor when it re-signs.
pub trait VerifyingBackend: Send + Sync {
    /// Identifier of the key this backend verifies against.
    fn key_id(&self) -> &str;

    /// Algorithm label this backend understands (must match the record's
    /// `sig_alg`).
    fn sig_alg(&self) -> &str;

    /// `true` for asymmetric (public-key) verification.
    fn is_asymmetric(&self) -> bool;

    /// Verify `signature` over `canonical_bytes`. `Ok(())` means the signature
    /// is authentic; any error means **do not trust**.
    fn verify(&self, canonical_bytes: &[u8], signature: &[u8]) -> Result<(), SigningError>;
}
