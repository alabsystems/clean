// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HMAC-SHA256 keyed-hash fallback — DEV/TEST ONLY.
//!
//! This is the dependency-free fallback for environments where even `ring` is
//! unavailable. It is a KEYED HASH, **not** a public-key signature: it is
//! verifiable only by a holder of the same secret key, so it provides
//! key-holder provenance but NOT non-repudiation. [`Self::is_asymmetric`]
//! returns `false` so a consumer policy can refuse to treat an HMAC tag as a
//! public-key attestation.
//!
//! HMAC-SHA256 is hand-rolled over `sha2` (the `hmac` crate is not in the lock).
//! This is real, correct HMAC (RFC 2104), NOT fake crypto — it just is not a
//! signature. Never published as a `KernelVerified` trust attestation.

use sha2::{Digest, Sha256};

use super::backend::{SigningBackend, SigningError, VerifyingBackend};

/// The `sig_alg` label for the HMAC dev fallback.
pub const SIG_ALG_HMAC_SHA256: &str = "hmac-sha256";

const BLOCK_SIZE: usize = 64; // SHA-256 block size in bytes.

/// Compute HMAC-SHA256(key, msg) per RFC 2104.
fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {
    // Keys longer than the block size are first hashed.
    let mut block = [0u8; BLOCK_SIZE];
    if key.len() > BLOCK_SIZE {
        let hashed = Sha256::digest(key);
        block[..hashed.len()].copy_from_slice(&hashed);
    } else {
        block[..key.len()].copy_from_slice(key);
    }

    let mut ipad = [0x36u8; BLOCK_SIZE];
    let mut opad = [0x5cu8; BLOCK_SIZE];
    for i in 0..BLOCK_SIZE {
        ipad[i] ^= block[i];
        opad[i] ^= block[i];
    }

    let mut inner = Sha256::new();
    inner.update(ipad);
    inner.update(msg);
    let inner_digest = inner.finalize();

    let mut outer = Sha256::new();
    outer.update(opad);
    outer.update(inner_digest);
    outer.finalize().into()
}

/// Constant-time-ish equality over fixed-size tags (avoids early-exit timing
/// leakage on the tag comparison).
fn tags_equal(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

/// An HMAC-SHA256 keyed-hash backend. DEV/TEST ONLY — `is_asymmetric == false`.
pub struct HmacDevBackend {
    key_id: String,
    secret: Vec<u8>,
}

impl HmacDevBackend {
    /// Build a dev backend from a `key_id` and a shared secret.
    pub fn new(key_id: impl Into<String>, secret: Vec<u8>) -> Self {
        Self {
            key_id: key_id.into(),
            secret,
        }
    }
}

impl SigningBackend for HmacDevBackend {
    fn key_id(&self) -> &str {
        &self.key_id
    }

    fn sig_alg(&self) -> &str {
        SIG_ALG_HMAC_SHA256
    }

    fn is_asymmetric(&self) -> bool {
        false
    }

    fn sign(&self, canonical_bytes: &[u8]) -> Result<Vec<u8>, SigningError> {
        Ok(hmac_sha256(&self.secret, canonical_bytes).to_vec())
    }
}

impl VerifyingBackend for HmacDevBackend {
    fn key_id(&self) -> &str {
        &self.key_id
    }

    fn sig_alg(&self) -> &str {
        SIG_ALG_HMAC_SHA256
    }

    fn is_asymmetric(&self) -> bool {
        false
    }

    fn verify(&self, canonical_bytes: &[u8], signature: &[u8]) -> Result<(), SigningError> {
        let expected = hmac_sha256(&self.secret, canonical_bytes);
        if tags_equal(&expected, signature) {
            Ok(())
        } else {
            Err(SigningError::Verify("hmac-sha256 tag mismatch".to_string()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// RFC 4231 Test Case 2: key = "Jefe", data = "what do ya want for
    /// nothing?" → known HMAC-SHA256 digest. Pins our hand-rolled HMAC against
    /// the standard test vector.
    #[test]
    fn test_hmac_sha256_rfc4231_vector_2() {
        let tag = hmac_sha256(b"Jefe", b"what do ya want for nothing?");
        let hex: String = tag.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(
            hex,
            "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
        );
    }

    #[test]
    fn test_hmac_dev_round_trip_verifies() {
        let backend = HmacDevBackend::new("hmac-dev:test", b"shared-secret".to_vec());
        let sig = backend.sign(b"canonical bytes").expect("sign");
        backend.verify(b"canonical bytes", &sig).expect("verify");
        assert!(
            !SigningBackend::is_asymmetric(&backend),
            "HMAC is not a public-key signature"
        );
        assert_eq!(SigningBackend::sig_alg(&backend), "hmac-sha256");
    }

    #[test]
    fn test_hmac_dev_tampered_bytes_fail_closed() {
        let backend = HmacDevBackend::new("hmac-dev:test", b"shared-secret".to_vec());
        let sig = backend.sign(b"original").expect("sign");
        let err = backend
            .verify(b"tampered", &sig)
            .expect_err("tampered message must fail");
        assert!(matches!(err, SigningError::Verify(_)));
    }
}
