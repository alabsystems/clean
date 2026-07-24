// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase-2 `POST /ingest`: accept a solver-attempt record (+ optional proof
//! blob), validate it, append it to telemetry / the proof cache, and best-effort
//! reindex.
//!
//! See `designs/2026-06-24-solver-results-cache-service.md` §10.2/§10.3.
//!
//! # Soundness / honesty (load-bearing)
//!
//! Ingest is the cache's *write* path and it NEVER mints a `verified` badge:
//!
//! - A submitted record is **provenance**. Appending it to `attempts.jsonl`
//!   asserts only "a solver claimed this", never "this is correct".
//! - A submitted **proof blob** is stored *untrusted*: it must decode to a
//!   structurally well-formed kernel term (the kernel's `bincode` `Deserialize`
//!   validates `BVar` range etc.), but it is NOT type-checked here. The consumer
//!   re-runs it through the kernel (`recheck_and_classify`) — the obligation
//!   digest is a soundness *bucket*, the kernel is the *arbiter*. A blob that
//!   does not decode is rejected (`400`); it is never stored as garbage.
//! - A proof blob may only accompany a `Proved` result. A raw `Unsat`/`Timeout`
//!   verdict is telemetry; attaching a "proof" to it is rejected.

use clean_kernel::Expr;
use serde::Deserialize;

use super::record::{AttemptResult, SolverAttemptRecord, SCHEMA_ID};
use super::serve::{ApiResponse, ServeState, TRUST_NOTE};
use super::{index, service, store, telemetry, SolverCacheError};

/// The ingest request envelope: one attempt record plus an optional proof blob.
///
/// The proof blob is `bincode(Expr)` bytes (the kernel-term serialization, the
/// same codec the Phase-0 store uses) rendered as lowercase hex, so the envelope
/// stays plain JSON without a base64 dependency.
#[derive(Debug, Deserialize)]
pub(crate) struct IngestEnvelope {
    /// The `solver-attempt-record-v1` row.
    pub(crate) record: SolverAttemptRecord,
    /// Optional `bincode(Expr)` proof term, lowercase hex. Only valid alongside a
    /// `Proved` result.
    #[serde(default)]
    pub(crate) proof_term_hex: Option<String>,
}

/// Handle `POST /ingest`.
pub(crate) fn handle_ingest(state: &ServeState, body: &[u8]) -> ApiResponse {
    let Some(cfg) = state.ingest.as_ref() else {
        return ApiResponse::with(
            503,
            serde_json::json!({
                "error": "ingest not enabled (set $CLEAN_SOLVER_INGEST)",
                "status": 503,
                "trust_note": TRUST_NOTE,
            }),
        );
    };

    let envelope: IngestEnvelope = match serde_json::from_slice(body) {
        Ok(e) => e,
        Err(e) => return ApiResponse::error(400, &format!("malformed ingest envelope: {e}")),
    };
    let record = envelope.record;

    // ── Validation (fail-closed; nothing is appended on a reject) ──────────
    if record.schema != SCHEMA_ID {
        return ApiResponse::error(
            400,
            &format!(
                "record.schema must be `{SCHEMA_ID}`, got `{}`",
                record.schema
            ),
        );
    }
    if index::digest_key(&record.obligation_digest).is_none() {
        return ApiResponse::error(
            400,
            "record.obligation_digest must be a blake3:<64hex> string",
        );
    }
    let is_proved = record.result == AttemptResult::Proved;
    let proof_hex = envelope.proof_term_hex.filter(|s| !s.is_empty());
    if proof_hex.is_some() && !is_proved {
        return ApiResponse::error(
            400,
            "a proof_term_hex may only accompany a Proved result; a raw verdict is telemetry",
        );
    }

    // Decode (but do not yet store) any proof blob, so a malformed blob rejects
    // the whole request before we durably append the record.
    let proof_term: Option<Expr> = match &proof_hex {
        Some(hex) => match decode_proof_hex(hex) {
            Ok(term) => Some(term),
            Err(e) => {
                return ApiResponse::error(
                    400,
                    &format!("proof_term_hex is not a decodable kernel term: {e}"),
                )
            }
        },
        None => None,
    };

    // ── Durable append (telemetry) ─────────────────────────────────────────
    if let Err(e) = telemetry::append_to(&cfg.telemetry_dir, &record) {
        return ApiResponse::error(500, &format!("append telemetry record: {e}"));
    }

    // ── Optional proof-cache store (untrusted; consumer re-checks) ──────────
    let mut stored_proof = false;
    if let (Some(term), Some(cache_dir)) = (&proof_term, &cfg.cache_dir) {
        let meta = store::CacheMeta::new(record.solver.name.clone(), record.strategy.clone());
        match store::put_in(cache_dir, &record.obligation_digest, term, meta) {
            Ok(()) => stored_proof = true,
            Err(e) => {
                // The record is already durably appended; report the store
                // failure but the ingest still succeeded as telemetry.
                return ApiResponse::with(
                    202,
                    accepted_json(
                        &record,
                        false,
                        "proof store failed; recorded as telemetry only",
                        Some(&e),
                    ),
                );
            }
        }
    }

    // ── Best-effort reindex ────────────────────────────────────────────────
    let reindex = cfg.reindex_path.as_ref().map(|out| {
        let dirs: Vec<std::path::PathBuf> = if state.data_dirs.is_empty() {
            vec![cfg.telemetry_dir.clone()]
        } else {
            state.data_dirs.clone()
        };
        match service::build_index(&dirs, out) {
            Ok(s) => serde_json::json!({ "ok": true, "entries": s.entries, "corpus_pin": s.corpus_digest }),
            Err(e) => serde_json::json!({ "ok": false, "error": e.to_string() }),
        }
    });

    let grade = grade_for(is_proved, stored_proof);
    ApiResponse::with(
        202,
        serde_json::json!({
            "accepted": true,
            "verified": false,
            "obligation_digest": record.obligation_digest,
            "verdict_grade": grade,
            "proof_stored": stored_proof,
            "re_checkable": stored_proof,
            "reindex": reindex,
            "note": "ACCEPTED as provenance. This service NEVER mints a 'verified' badge. A stored \
                     proof term is re-checkable by the consumer through the kernel; a raw verdict \
                     is a hint.",
            "trust_note": TRUST_NOTE,
        }),
    )
}

/// Classify what was accepted (never a trust claim — see module docs).
fn grade_for(is_proved: bool, stored_proof: bool) -> &'static str {
    match (is_proved, stored_proof) {
        (true, true) => "proof-bearing-provenance (re-checkable)",
        (true, false) => "validated-no-certificate (not re-checkable here)",
        (false, _) => "advisory-telemetry",
    }
}

/// Build the `202` body for a partial accept (record stored, proof not).
fn accepted_json(
    record: &SolverAttemptRecord,
    stored_proof: bool,
    note: &str,
    err: Option<&SolverCacheError>,
) -> serde_json::Value {
    serde_json::json!({
        "accepted": true,
        "verified": false,
        "obligation_digest": record.obligation_digest,
        "proof_stored": stored_proof,
        "re_checkable": stored_proof,
        "warning": err.map(ToString::to_string),
        "note": note,
        "trust_note": TRUST_NOTE,
    })
}

/// Encode a kernel proof term to the ingest `proof_term_hex` form.
///
/// Tools / tests use this to build an ingest envelope whose blob round-trips
/// through [`decode_proof_hex`] (the same `bincode` codec the store uses).
///
/// # Errors
/// Propagates a `bincode` serialization failure.
pub fn encode_proof_hex(term: &Expr) -> Result<String, SolverCacheError> {
    Ok(to_hex(&store::encode_proof_term(term)?))
}

/// Decode the ingest `proof_term_hex` blob into a kernel term.
fn decode_proof_hex(hex: &str) -> Result<Expr, SolverCacheError> {
    let bytes = from_hex(hex)?;
    store::decode_proof_term(&bytes)
}

/// Lowercase-hex encode bytes.
fn to_hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// Decode a lowercase/uppercase hex string into bytes (even length, hex only).
fn from_hex(hex: &str) -> Result<Vec<u8>, SolverCacheError> {
    let hex = hex.trim();
    if !hex.len().is_multiple_of(2) {
        return Err(SolverCacheError::Serialize(
            "hex proof blob has odd length".to_string(),
        ));
    }
    let mut out = Vec::with_capacity(hex.len() / 2);
    let bytes = hex.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let hi = hex_nibble(bytes[i])?;
        let lo = hex_nibble(bytes[i + 1])?;
        out.push((hi << 4) | lo);
        i += 2;
    }
    Ok(out)
}

/// Map one ASCII hex digit to its nibble value.
fn hex_nibble(c: u8) -> Result<u8, SolverCacheError> {
    match c {
        b'0'..=b'9' => Ok(c - b'0'),
        b'a'..=b'f' => Ok(c - b'a' + 10),
        b'A'..=b'F' => Ok(c - b'A' + 10),
        _ => Err(SolverCacheError::Serialize(format!(
            "invalid hex digit: {:?}",
            c as char
        ))),
    }
}
