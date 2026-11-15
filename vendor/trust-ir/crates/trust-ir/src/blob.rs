// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Content-addressed weight blobs (PKG-U13e, wire v70,
//! `docs/SPEC_RATIFICATIONS.md` §27).
//!
//! A weight is an INPUT to the compiled code, never a constant baked into it.
//! A [`crate::Constant::TensorBlob`] names a tensor by the SHA-256 of its
//! element bytes, and the module's blob table ([`crate::Module::blobs`])
//! holds each digest once with its bytes. A function body's identity
//! ([`crate::Module::function_body_digest`]) reads the digest the constant
//! spells, never the bytes: the table is a module table, outside the body's
//! preimage, so replacing a weight's bytes moves no body digest, and a body
//! that names other bytes names another digest.
//!
//! The digest is FIPS 180-4 SHA-256 of the raw bytes, with no domain prefix,
//! so an external content-addressed store (OCI, safetensors tooling) can key
//! the same bytes by the same digest. The table's canonical order is strictly
//! ascending digest; every decoder refuses another order and a digest listed
//! twice, and `validate_module` refuses a row whose bytes do not hash to its
//! digest (`InvalidBlobTable`) and a constant whose digest names no row
//! (`MissingBlob`).

use sha2::{Digest, Sha256};

/// The SHA-256 of a blob's bytes: its key in the module blob table.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BlobDigest(pub [u8; 32]);

impl BlobDigest {
    /// The digest of `bytes` (FIPS 180-4 SHA-256, no domain prefix).
    pub fn of(bytes: &[u8]) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(bytes);
        Self(hasher.finalize().into())
    }

    /// The 64 lower-case hexadecimal digits of the digest.
    pub fn to_hex(&self) -> String {
        let mut out = String::with_capacity(64);
        for byte in self.0 {
            out.push(hex_digit(byte >> 4));
            out.push(hex_digit(byte & 0x0f));
        }
        out
    }

    /// The digest spelled by exactly 64 hexadecimal digits (either case), or
    /// `None`.
    pub fn from_hex(text: &str) -> Option<Self> {
        let bytes = text.as_bytes();
        if bytes.len() != 64 {
            return None;
        }
        let mut out = [0u8; 32];
        let (pairs, _) = bytes.as_chunks::<2>();
        for (slot, [high, low]) in out.iter_mut().zip(pairs) {
            let (Some(high), Some(low)) = (hex_value(*high), hex_value(*low)) else {
                return None;
            };
            *slot = (high << 4) | low;
        }
        Some(Self(out))
    }
}

fn hex_digit(nibble: u8) -> char {
    char::from(b"0123456789abcdef"[usize::from(nibble & 0x0f)])
}

fn hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

impl core::fmt::Display for BlobDigest {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(&self.to_hex())
    }
}

impl core::fmt::Debug for BlobDigest {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "BlobDigest({})", self.to_hex())
    }
}

/// One row of the module blob table: a digest and the bytes it names.
///
/// [`Blob::new`] computes the digest, so a row it builds always matches. A
/// decoded row is taken as written: whether its bytes hash to its digest is
/// `validate_module`'s question (`InvalidBlobTable`), and both engines ask
/// it again where a constant reads the row.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Blob {
    /// The SHA-256 of `data`, as recorded.
    pub digest: BlobDigest,
    /// The blob's bytes.
    pub data: Vec<u8>,
}

impl Blob {
    /// A row naming `data` by its own digest.
    pub fn new(data: Vec<u8>) -> Self {
        Self {
            digest: BlobDigest::of(&data),
            data,
        }
    }

    /// Whether `data` hashes to `digest`.
    pub fn digest_matches(&self) -> bool {
        BlobDigest::of(&self.data) == self.digest
    }
}

/// Why a blob table is not in its one canonical order, or `None` when every
/// digest is strictly greater than the one before it (so each digest is listed
/// once). The rule every decoder and `validate_module` share.
pub fn blob_table_order_refusal(blobs: &[Blob]) -> Option<String> {
    blobs.windows(2).find_map(|pair| {
        let (previous, next) = (&pair[0].digest, &pair[1].digest);
        if next == previous {
            Some(format!("the blob table lists digest {next} twice"))
        } else if next < previous {
            Some(format!(
                "the blob table is out of canonical order: digest {next} follows {previous} \
                 (rows are strictly ascending by digest)"
            ))
        } else {
            None
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digest_is_plain_sha256_of_the_bytes() {
        assert_eq!(
            BlobDigest::of(b"").to_hex(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            BlobDigest::of(b"abc").to_hex(),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn hex_round_trips_and_refuses_malformed_spellings() {
        let digest = BlobDigest::of(b"weights");
        assert_eq!(BlobDigest::from_hex(&digest.to_hex()), Some(digest));
        assert_eq!(
            BlobDigest::from_hex(&digest.to_hex().to_uppercase()),
            Some(digest)
        );
        assert_eq!(BlobDigest::from_hex(&digest.to_hex()[1..]), None);
        assert_eq!(BlobDigest::from_hex(&format!("{}0", digest.to_hex())), None);
        let mut bad = digest.to_hex();
        bad.replace_range(0..1, "g");
        assert_eq!(BlobDigest::from_hex(&bad), None);
    }

    #[test]
    fn table_order_refusal_names_duplicates_and_disorder() {
        let a = Blob::new(vec![1]);
        let b = Blob::new(vec![2]);
        let (low, high) = if a.digest < b.digest { (a, b) } else { (b, a) };
        assert_eq!(blob_table_order_refusal(&[]), None);
        assert_eq!(blob_table_order_refusal(&[low.clone(), high.clone()]), None);
        assert!(
            blob_table_order_refusal(&[high.clone(), low.clone()])
                .is_some_and(|reason| reason.contains("out of canonical order"))
        );
        assert!(
            blob_table_order_refusal(&[low.clone(), low.clone()])
                .is_some_and(|reason| reason.contains("twice"))
        );
        assert!(low.digest_matches());
        let tampered = Blob {
            digest: low.digest,
            data: vec![9],
        };
        assert!(!tampered.digest_matches());
    }
}
