// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `CertifiedPayload` → trust-ir `ProofEvidence::CleanCic` converter.
//!
//! The cross-repo study found this converter MISSING: `ProofEvidence::CleanCic`
//! existed in trust-ir but was never produced. This module produces the
//! handoff payload.
//!
//! # Why a shim, not a `trust-ir` path dep (honest scope note)
//!
//! `trust-ir` is a separate workspace and is intentionally kept out of clean's
//! default build graph (see the trust ecosystem decoupling). [`CleanCicPayload`]
//! is the **shared shim**: byte-for-byte the `ProofEvidence::CleanCic` handoff
//! `{ term: Vec<u8>, context: Vec<u8>, lineage: ProofDigest }`. A trust-ir-side
//! adapter maps it 1:1 into `trust_ir::proof::ProofEvidence::CleanCic`
//! (`term`/`context` verbatim; `lineage.algorithm` ∈ {`TAG_STABLE_V1` →
//! `TrustIrStableV1`, `TAG_SHA256` → `Sha256`}, `lineage.bytes` verbatim).

use super::certified_proof::CertifiedPayload;

/// The lineage digest carried alongside a Clean CIC certificate.
///
/// Mirrors `trust_ir::proof::ProofDigest`: a 1-byte algorithm tag followed by a
/// 32-byte digest. `TAG_STABLE_V1` matches trust-ir's `TrustIrStableV1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CleanCicLineage {
    /// Algorithm tag (`Self::TAG_STABLE_V1` or `Self::TAG_SHA256`).
    pub algorithm: u8,
    /// 32-byte digest binding the certificate to the obligation it certifies.
    pub bytes: [u8; 32],
}

impl CleanCicLineage {
    /// trust-ir `ProofDigestAlgorithm::TrustIrStableV1` tag.
    pub const TAG_STABLE_V1: u8 = 1;
    /// trust-ir `ProofDigestAlgorithm::Sha256` tag.
    pub const TAG_SHA256: u8 = 0;

    /// Deterministic stable digest of `data` (a non-cryptographic, stable-across-
    /// runs structural checksum — the same role trust-ir's `TrustIrStableV1`
    /// plays). FNV-1a over a domain-separated byte stream.
    #[must_use]
    pub fn stable(domain: &str, data: &[u8]) -> Self {
        let mut bytes = [0u8; 32];
        // Eight independent FNV-1a lanes, each salted by lane index + domain, so
        // the 32-byte output is well-mixed and deterministic.
        for (lane, chunk) in bytes.chunks_mut(8).enumerate() {
            let mut h: u64 = 0xcbf2_9ce4_8422_2325 ^ (lane as u64).wrapping_mul(0x100_0000_01b3);
            for &b in domain.as_bytes() {
                h ^= u64::from(b);
                h = h.wrapping_mul(0x100_0000_01b3);
            }
            for &b in data {
                h ^= u64::from(b);
                h = h.wrapping_mul(0x100_0000_01b3);
            }
            chunk.copy_from_slice(&h.to_le_bytes());
        }
        Self {
            algorithm: Self::TAG_STABLE_V1,
            bytes,
        }
    }
}

/// Byte-for-byte the `trust_ir::proof::ProofEvidence::CleanCic` payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CleanCicPayload {
    /// `bincode`-serialized kernel proof term (`CertifiedPayload::term_bytes`).
    pub term: Vec<u8>,
    /// `bincode`-serialized reduced context (`CertifiedPayload::context_bytes`).
    pub context: Vec<u8>,
    /// Lineage digest binding the certificate to its obligation.
    pub lineage: CleanCicLineage,
}

/// Convert a kernel-CHECKED [`CertifiedPayload`] into the trust-ir
/// `ProofEvidence::CleanCic` handoff payload.
///
/// `lineage` binds the certificate to the obligation it certifies; pass the
/// obligation's stable digest (e.g. [`CleanCicLineage::stable`] over the negated
/// goal). The payload's `term`/`context` are exactly the certified bytes — a CIC
/// kernel re-checks them; nothing is trusted.
#[must_use]
pub fn to_clean_cic(payload: &CertifiedPayload, lineage: CleanCicLineage) -> CleanCicPayload {
    CleanCicPayload {
        term: payload.term_bytes.clone(),
        context: payload.context_bytes.clone(),
        lineage,
    }
}

// Gated with the BV bit-blast lane: this test module imports
// `ay_proof::bv_blast_export` and `theory_lemma_bv::reconstruct_bv_bitblast`.
// The `clean_cic` production code above does not depend on that lane.
#[cfg(all(test, feature = "ay-bv-blast"))]
#[path = "tests_clean_cic.rs"]
mod tests_clean_cic;
