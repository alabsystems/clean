// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real Ed25519 signing/verification over `ring 0.17` (already in the lock).
//!
//! This is NOT a stub: it is genuine public-key cryptography. The secret key
//! lives in a PKCS#8 v2 document on disk (never in git); the public key is
//! published with the Core so any consumer verifies offline.
//!
//! TODO-for-the-vendored-crate: if a future lane lands `ed25519-dalek` (or a
//! `signature`-trait crate) in `Cargo.lock` as a direct dependency, the engine
//! below MAY be swapped behind the [`SigningBackend`] trait without touching
//! callers or the schema. The `ring` backend is fully functional today.

use ring::rand::SystemRandom;
use ring::signature::{Ed25519KeyPair, KeyPair, UnparsedPublicKey, ED25519};

use super::backend::{SigningBackend, SigningError, VerifyingBackend};

/// The `sig_alg` label for Ed25519.
pub const SIG_ALG_ED25519: &str = "ed25519";

/// An Ed25519 signing backend backed by a PKCS#8 keypair.
pub struct Ed25519LocalBackend {
    key_id: String,
    key_pair: Ed25519KeyPair,
}

impl Ed25519LocalBackend {
    /// Generate a fresh dev keypair, returning the backend plus the PKCS#8
    /// document bytes the caller must persist OUTSIDE git (the secret).
    pub fn generate(key_id: impl Into<String>) -> Result<(Self, Vec<u8>), SigningError> {
        let rng = SystemRandom::new();
        let pkcs8 = Ed25519KeyPair::generate_pkcs8(&rng)
            .map_err(|e| SigningError::Key(format!("generate_pkcs8: {e}")))?;
        let key_pair = Ed25519KeyPair::from_pkcs8(pkcs8.as_ref())
            .map_err(|e| SigningError::Key(format!("from_pkcs8: {e}")))?;
        Ok((
            Self {
                key_id: key_id.into(),
                key_pair,
            },
            pkcs8.as_ref().to_vec(),
        ))
    }

    /// Load a backend from previously-persisted PKCS#8 secret bytes.
    pub fn from_pkcs8(key_id: impl Into<String>, pkcs8: &[u8]) -> Result<Self, SigningError> {
        let key_pair = Ed25519KeyPair::from_pkcs8(pkcs8)
            .map_err(|e| SigningError::Key(format!("from_pkcs8: {e}")))?;
        Ok(Self {
            key_id: key_id.into(),
            key_pair,
        })
    }

    /// The raw public-key bytes (32 bytes), to publish with the Core.
    #[must_use]
    pub fn public_key_bytes(&self) -> Vec<u8> {
        self.key_pair.public_key().as_ref().to_vec()
    }
}

impl SigningBackend for Ed25519LocalBackend {
    fn key_id(&self) -> &str {
        &self.key_id
    }

    fn sig_alg(&self) -> &str {
        SIG_ALG_ED25519
    }

    fn is_asymmetric(&self) -> bool {
        true
    }

    fn sign(&self, canonical_bytes: &[u8]) -> Result<Vec<u8>, SigningError> {
        Ok(self.key_pair.sign(canonical_bytes).as_ref().to_vec())
    }
}

/// The public-key verifier counterpart: holds only the public key, so a
/// consumer can verify without the secret.
pub struct Ed25519Verifier {
    key_id: String,
    public_key: Vec<u8>,
}

impl Ed25519Verifier {
    /// Build a verifier from a `key_id` and the raw 32-byte public key.
    pub fn new(key_id: impl Into<String>, public_key: Vec<u8>) -> Self {
        Self {
            key_id: key_id.into(),
            public_key,
        }
    }
}

impl VerifyingBackend for Ed25519Verifier {
    fn key_id(&self) -> &str {
        &self.key_id
    }

    fn sig_alg(&self) -> &str {
        SIG_ALG_ED25519
    }

    fn is_asymmetric(&self) -> bool {
        true
    }

    fn verify(&self, canonical_bytes: &[u8], signature: &[u8]) -> Result<(), SigningError> {
        UnparsedPublicKey::new(&ED25519, &self.public_key)
            .verify(canonical_bytes, signature)
            .map_err(|e| SigningError::Verify(format!("ed25519: {e}")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ed25519_round_trip_verifies() {
        let (backend, _secret) =
            Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair generates");
        let msg = b"canonical verdict bytes";
        let sig = backend.sign(msg).expect("sign succeeds");
        let verifier = Ed25519Verifier::new("ed25519-local:test", backend.public_key_bytes());
        verifier
            .verify(msg, &sig)
            .expect("authentic signature verifies");
        assert!(backend.is_asymmetric());
        assert_eq!(backend.sig_alg(), "ed25519");
    }

    #[test]
    fn test_ed25519_tampered_bytes_fail_closed() {
        let (backend, _secret) =
            Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair generates");
        let sig = backend.sign(b"original bytes").expect("sign succeeds");
        let verifier = Ed25519Verifier::new("ed25519-local:test", backend.public_key_bytes());
        let err = verifier
            .verify(b"tampered bytes", &sig)
            .expect_err("a different message must fail verification");
        assert!(matches!(err, SigningError::Verify(_)));
    }

    #[test]
    fn test_ed25519_persisted_secret_reloads() {
        let (backend, secret) =
            Ed25519LocalBackend::generate("ed25519-local:test").expect("keypair generates");
        let reloaded =
            Ed25519LocalBackend::from_pkcs8("ed25519-local:test", &secret).expect("reload");
        // Both keypairs share the same public key.
        assert_eq!(backend.public_key_bytes(), reloaded.public_key_bytes());
        let sig = reloaded.sign(b"msg").expect("reloaded key signs");
        Ed25519Verifier::new("ed25519-local:test", backend.public_key_bytes())
            .verify(b"msg", &sig)
            .expect("signature from reloaded key verifies against original public key");
    }
}
