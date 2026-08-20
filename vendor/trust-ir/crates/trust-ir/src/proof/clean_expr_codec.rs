// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Canonical, resource-bounded legacy-bincode carrier for Clean kernel terms.
//!
//! Existing TrustIR/Clean TV and contract payloads use bincode 1.x's historical
//! helper-function wire format: little-endian fixed-width integers. This module
//! preserves those bytes while replacing the legacy decoder's unlimited and
//! trailing-byte-accepting behavior with one exact whole-slice contract.

use bincode::Options;
use clean_kernel::{DecodeResourceLimits, Expr};

/// Maximum encoded size of one Clean kernel proof/comparand expression (64 MiB).
pub const CLEAN_EXPR_V1_MAX_BYTES: usize = 64 * 1024 * 1024;
/// Maximum aggregate Expr/Level/Name nodes decoded from one carrier.
pub const CLEAN_EXPR_V1_MAX_NODES: usize = 2_000_000;
/// Maximum recursive Expr/Level/Name depth decoded from one carrier.
pub const CLEAN_EXPR_V1_MAX_DEPTH: usize = 4_096;

fn codec(limit: usize) -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .reject_trailing_bytes()
        .with_limit(limit as u64)
}

/// Encode one kernel expression in the existing bincode-1-compatible wire
/// format, rejecting values whose encoded carrier exceeds the hard limit.
pub fn encode_clean_expr_v1(expr: &Expr) -> Result<Vec<u8>, String> {
    let bytes = codec(CLEAN_EXPR_V1_MAX_BYTES)
        .serialize(expr)
        .map_err(|error| format!("encode Clean Expr v1: {error}"))?;
    if bytes.len() > CLEAN_EXPR_V1_MAX_BYTES {
        return Err(format!(
            "Clean Expr v1 carrier is {} bytes, exceeds limit {}",
            bytes.len(),
            CLEAN_EXPR_V1_MAX_BYTES
        ));
    }
    Ok(bytes)
}

/// Decode one untrusted kernel expression with exact whole-slice, byte, node,
/// depth, and canonical-reencoding checks.
pub fn decode_clean_expr_v1(bytes: &[u8]) -> Result<Expr, String> {
    decode_with_limits(
        bytes,
        CLEAN_EXPR_V1_MAX_BYTES,
        CLEAN_EXPR_V1_MAX_NODES,
        CLEAN_EXPR_V1_MAX_DEPTH,
    )
}

fn decode_with_limits(
    bytes: &[u8],
    max_bytes: usize,
    max_nodes: usize,
    max_depth: usize,
) -> Result<Expr, String> {
    if bytes.len() > max_bytes {
        return Err(format!(
            "Clean Expr v1 carrier is {} bytes, exceeds limit {max_bytes}",
            bytes.len()
        ));
    }
    let expr = clean_kernel::with_decode_resource_limits(
        DecodeResourceLimits {
            max_nodes,
            max_depth,
        },
        || codec(max_bytes).deserialize::<Expr>(bytes),
    )
    .map_err(|error| format!("decode Clean Expr v1: {error}"))?;

    // `reject_trailing_bytes` establishes whole-slice consumption. Re-encoding
    // additionally pins one canonical spelling and catches future serde codecs
    // that accept alternate structural representations.
    let canonical = codec(max_bytes)
        .serialize(&expr)
        .map_err(|error| format!("re-encode Clean Expr v1: {error}"))?;
    if canonical != bytes {
        return Err(format!(
            "non-canonical Clean Expr v1 carrier: supplied {} bytes, canonical encoding is {} bytes",
            bytes.len(),
            canonical.len()
        ));
    }
    Ok(expr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encoding_is_byte_compatible_with_legacy_bincode_helpers() {
        let expr = Expr::app(Expr::const_str("f"), Expr::nat_lit(7));
        assert_eq!(
            encode_clean_expr_v1(&expr).unwrap(),
            bincode::serialize(&expr).unwrap(),
            "hardening must not change the existing bincode-1 wire bytes"
        );
    }

    #[test]
    fn exact_decode_rejects_suffix_and_byte_overrun() {
        let bytes = encode_clean_expr_v1(&Expr::const_str("Bool.true")).unwrap();
        let mut suffixed = bytes.clone();
        suffixed.push(0);
        assert!(decode_clean_expr_v1(&suffixed).is_err());
        assert!(
            decode_with_limits(&bytes, bytes.len().saturating_sub(1), 100, 100).is_err(),
            "an encoded term over the configured byte cap must reject"
        );
    }

    #[test]
    fn exact_decode_rejects_excessive_recursive_depth() {
        let mut expr = Expr::nat_lit(0);
        for _ in 0..16 {
            expr = Expr::app(Expr::const_str("f"), expr);
        }
        let bytes = encode_clean_expr_v1(&expr).unwrap();
        let error = decode_with_limits(&bytes, bytes.len(), 10_000, 8)
            .expect_err("deep expression must fail inside the scoped decoder");
        assert!(error.contains("depth"), "unexpected error: {error}");
    }
}
