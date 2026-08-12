// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minimal PEM/DER/SPKI parsing for the GCP KMS verifier.
//!
//! `gcloud kms keys versions get-public-key` returns the public key as a
//! SubjectPublicKeyInfo (SPKI) in PEM. `ring` wants the *inner* public key in a
//! key-type-specific shape, so we decode the PEM and walk just enough DER to
//! reach (and shape) the `subjectPublicKey` BIT STRING. No external ASN.1 crate
//! is in `Cargo.lock`; this hand-rolled reader does only what SPKI needs, with
//! full bounds checks. Split out of `gcp_kms.rs` to keep that file ≤500 lines.

use base64::Engine as _;

use super::backend::SigningError;
use super::gcp_kms::GcpKmsKeyType;

/// Decode a single PEM block with the given label into its DER bytes.
pub(super) fn pem_to_der(pem: &str, label: &str) -> Result<Vec<u8>, SigningError> {
    let begin = format!("-----BEGIN {label}-----");
    let end = format!("-----END {label}-----");
    let start = pem
        .find(&begin)
        .ok_or_else(|| SigningError::Key(format!("PEM missing `{begin}`")))?
        + begin.len();
    let rest = &pem[start..];
    let stop = rest
        .find(&end)
        .ok_or_else(|| SigningError::Key(format!("PEM missing `{end}`")))?;
    let body: String = rest[..stop]
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    base64::engine::general_purpose::STANDARD
        .decode(body.as_bytes())
        .map_err(|e| SigningError::Key(format!("PEM base64 decode: {e}")))
}

/// Extract the `ring`-shaped public key from a SubjectPublicKeyInfo (SPKI) DER.
///
/// SPKI is `SEQUENCE { algorithm AlgorithmIdentifier, subjectPublicKey BIT
/// STRING }`. We parse just enough to reach the BIT STRING, then shape its
/// contents per `key_type`:
/// * Ed25519 — the BIT STRING contents ARE the raw 32-byte key.
/// * ECDSA P-256 — the BIT STRING contents ARE the uncompressed SEC1 point.
/// * RSA — the BIT STRING contents are the PKCS#1 `RSAPublicKey` DER `ring`
///   wants.
pub(super) fn spki_to_ring_public_key(
    der: &[u8],
    key_type: GcpKmsKeyType,
) -> Result<Vec<u8>, SigningError> {
    let bit_string = spki_subject_public_key(der)?;
    // ECDSA P-256: ring wants the 65-byte uncompressed point (0x04||X||Y).
    if key_type == GcpKmsKeyType::EcdsaP256Sha256 && bit_string.first() != Some(&0x04) {
        return Err(SigningError::Key(
            "ECDSA SPKI public key is not an uncompressed SEC1 point".to_string(),
        ));
    }
    Ok(bit_string)
}

/// Parse a DER SPKI and return the contents of its `subjectPublicKey` BIT STRING
/// (the leading "unused bits" octet stripped).
fn spki_subject_public_key(der: &[u8]) -> Result<Vec<u8>, SigningError> {
    let mut r = DerReader::new(der);
    let mut seq = r.read_tagged(0x30)?; // outer SEQUENCE
    seq.read_tagged(0x30)?; // algorithm AlgorithmIdentifier (skipped)
    let bit_string = seq.read_tagged(0x03)?; // subjectPublicKey BIT STRING
    let (unused_bits, contents) = bit_string
        .remaining()
        .split_first()
        .ok_or_else(|| SigningError::Key("SPKI BIT STRING is empty".to_string()))?;
    if *unused_bits != 0 {
        return Err(SigningError::Key(format!(
            "SPKI BIT STRING has {unused_bits} unused bits (expected 0)"
        )));
    }
    Ok(contents.to_vec())
}

/// A minimal DER reader: just enough to walk SPKI (SEQUENCE / BIT STRING) with
/// bounds checks. No external dependency.
struct DerReader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> DerReader<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    /// Read a TLV with the expected tag byte, returning a reader over its value.
    fn read_tagged(&mut self, expected_tag: u8) -> Result<DerReader<'a>, SigningError> {
        let tag = *self
            .buf
            .get(self.pos)
            .ok_or_else(|| SigningError::Key("DER truncated at tag".to_string()))?;
        if tag != expected_tag {
            return Err(SigningError::Key(format!(
                "DER tag 0x{tag:02x} != expected 0x{expected_tag:02x}"
            )));
        }
        self.pos += 1;
        let len = self.read_len()?;
        let start = self.pos;
        let end = start
            .checked_add(len)
            .filter(|&e| e <= self.buf.len())
            .ok_or_else(|| SigningError::Key("DER length exceeds buffer".to_string()))?;
        self.pos = end;
        Ok(DerReader {
            buf: &self.buf[start..end],
            pos: 0,
        })
    }

    /// Read a DER definite length (short or long form).
    fn read_len(&mut self) -> Result<usize, SigningError> {
        let first = *self
            .buf
            .get(self.pos)
            .ok_or_else(|| SigningError::Key("DER truncated at length".to_string()))?;
        self.pos += 1;
        if first & 0x80 == 0 {
            return Ok(first as usize);
        }
        let n = (first & 0x7f) as usize;
        if n == 0 || n > size_of::<usize>() {
            return Err(SigningError::Key(format!(
                "DER unsupported length-of-length {n}"
            )));
        }
        let mut len = 0usize;
        for _ in 0..n {
            let b = *self
                .buf
                .get(self.pos)
                .ok_or_else(|| SigningError::Key("DER truncated in long length".to_string()))?;
            self.pos += 1;
            len = (len << 8) | (b as usize);
        }
        Ok(len)
    }

    /// The not-yet-consumed bytes of this reader.
    fn remaining(&self) -> &'a [u8] {
        &self.buf[self.pos..]
    }
}
