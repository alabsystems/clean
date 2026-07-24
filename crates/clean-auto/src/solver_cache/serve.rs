// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase-2 solver-cache SERVICE: a transport-agnostic query/ingest surface over
//! the `VCIDX01` index + the `solver-attempt-record-v1` telemetry stream.
//!
//! See `designs/2026-06-24-solver-results-cache-service.md` §10. This module is
//! the *pure* dispatch layer: [`dispatch`] maps `(method, path, query, body)` to
//! an [`ApiResponse`] (a status + JSON value) with **no HTTP / `tokio`
//! dependency**, so it is exercised directly by `clean-cli`'s integration tests.
//! The `solver_serve` binary (`src/bin/solver_serve`) is a thin raw-`tokio`
//! HTTP/1.1 shell — mirroring `mathverse_serve` — that calls [`dispatch`].
//!
//! # Soundness / honesty (the through-line)
//!
//! The service is a **distribution front-end, not a trust authority** (design
//! §10.3). A cached solving result is *provenance*, never a verdict:
//!
//! - A **proof-bearing** result ships a re-checkable proof term; the consumer
//!   MUST re-run it through the kernel (`recheck_and_classify`). The solver stays
//!   out of the TCB exactly as in Phase 0.
//! - A **raw** unsat/timeout/unknown verdict is telemetry / a hint, never a
//!   verification.
//! - [`crate::solver_cache::ingest`] NEVER mints a `verified` badge — a submitted
//!   proof must be kernel-re-checkable by the consumer.
//!
//! Every `/stats` and `/lookup` response restates this via [`TRUST_NOTE`] +
//! [`soundness_model_json`], mirroring `mathverse_serve`'s per-response
//! `trust_note`.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use serde_json::json;
use thiserror::Error;

use super::analysis::{AnalysisError, WeakBy};
use super::dataset::{self, ExportFilter};
use super::index::{self, ObligationSummary, SolverIndex, SummaryAccumulator};
use super::record::SolverAttemptRecord;
use super::{service, store};

/// Service identity surfaced in the banner / health response.
pub const SERVICE_NAME: &str = "solver_serve";

/// The honest, per-response trust note (mirrors `mathverse_serve`'s).
pub const TRUST_NOTE: &str = "This service is a DISTRIBUTION FRONT-END, not a trust authority. A \
cached solving result is PROVENANCE, not a verdict: a proof-bearing result ships a re-checkable \
proof term that the consumer MUST re-run through the kernel; a raw unsat/timeout verdict is \
TELEMETRY / a hint, never a verification. Ingest never mints a 'verified' badge.";

/// Default `/export-dataset` row cap (the inline HTTP body is bounded; the file
/// exporter `clean solver export-dataset` has no cap).
const DEFAULT_EXPORT_LIMIT: usize = 256;
/// Hard upper bound on `/export-dataset?limit=`.
const MAX_EXPORT_LIMIT: usize = 4096;
/// Default `/weak?top=`.
const DEFAULT_WEAK_TOP: usize = 20;

/// Errors building the serving state (e.g. a corrupt pre-built index).
#[derive(Debug, Error)]
pub enum ServeApiError {
    /// Loading the configured `VCIDX01` index failed (fail-closed).
    #[error("load VCIDX01 index: {0}")]
    Index(String),
    /// No data directory was configured (nothing to serve).
    #[error(
        "no telemetry/cache directory configured: set $CLEAN_SOLVER_TELEMETRY_DIR \
             and/or $CLEAN_SOLVER_CACHE_DIR"
    )]
    NoDataDir,
}

/// Ingest target: where `POST /ingest` durably appends (design §10.2).
#[derive(Clone, Debug)]
pub(crate) struct IngestConfig {
    /// Telemetry directory the attempt record is appended to (`attempts.jsonl`).
    pub(crate) telemetry_dir: PathBuf,
    /// Optional cache directory a proof-bearing blob is stored under.
    pub(crate) cache_dir: Option<PathBuf>,
    /// Optional `VCIDX01` path rebuilt after each accepted ingest (best-effort).
    pub(crate) reindex_path: Option<PathBuf>,
}

/// Resolved, transport-agnostic serving state.
pub struct ServeState {
    /// Directories scanned for telemetry + cache membership (read endpoints).
    pub(crate) data_dirs: Vec<PathBuf>,
    /// Optional pre-built `VCIDX01` for µs `/lookup` (read-only deployments).
    pub(crate) index: Option<SolverIndex>,
    /// Ingest config; `None` disables `POST /ingest`.
    pub(crate) ingest: Option<IngestConfig>,
    /// PAR-2 timeout budget (ms) the reports assume.
    pub(crate) budget_ms: u64,
}

impl ServeState {
    /// Build serving state.
    ///
    /// `index_path`, when `Some`, is loaded fail-closed (a tamper/structure
    /// failure is returned as [`ServeApiError::Index`]). When `ingest_telemetry_dir`
    /// is `Some`, `POST /ingest` is enabled; otherwise it answers `503`.
    ///
    /// # Errors
    /// [`ServeApiError::NoDataDir`] if no data directory is given, or
    /// [`ServeApiError::Index`] if the index fails to load.
    pub fn new(
        data_dirs: Vec<PathBuf>,
        index_path: Option<PathBuf>,
        ingest_telemetry_dir: Option<PathBuf>,
        ingest_cache_dir: Option<PathBuf>,
        reindex_path: Option<PathBuf>,
        budget_ms: u64,
    ) -> Result<Self, ServeApiError> {
        if data_dirs.is_empty() && ingest_telemetry_dir.is_none() {
            return Err(ServeApiError::NoDataDir);
        }
        let index = match index_path {
            Some(p) => {
                Some(SolverIndex::load(&p).map_err(|e| ServeApiError::Index(e.to_string()))?)
            }
            None => None,
        };
        let ingest = ingest_telemetry_dir.map(|telemetry_dir| IngestConfig {
            telemetry_dir,
            cache_dir: ingest_cache_dir,
            reindex_path,
        });
        Ok(Self {
            data_dirs,
            index,
            ingest,
            budget_ms,
        })
    }

    /// Whether `POST /ingest` is enabled.
    #[must_use]
    pub fn ingest_enabled(&self) -> bool {
        self.ingest.is_some()
    }

    /// Number of configured data directories.
    #[must_use]
    pub fn data_dir_count(&self) -> usize {
        self.data_dirs.len()
    }

    /// The loaded index's corpus-pin digest, if an index is loaded.
    #[must_use]
    pub fn corpus_pin(&self) -> Option<String> {
        self.index.as_ref().map(SolverIndex::corpus_digest_str)
    }

    /// The PAR-2 budget (ms) the reports assume.
    #[must_use]
    pub fn budget_ms(&self) -> u64 {
        self.budget_ms
    }
}

/// A transport-agnostic response: an HTTP status plus a JSON body.
#[derive(Clone, Debug)]
pub struct ApiResponse {
    /// HTTP status code.
    pub status: u16,
    /// JSON response body.
    pub body: serde_json::Value,
}

impl ApiResponse {
    /// A `200 OK` JSON response.
    pub(crate) fn ok(body: serde_json::Value) -> Self {
        Self { status: 200, body }
    }

    /// A JSON response with an explicit status.
    pub(crate) fn with(status: u16, body: serde_json::Value) -> Self {
        Self { status, body }
    }

    /// A JSON error envelope (always carries the trust note).
    pub(crate) fn error(status: u16, message: &str) -> Self {
        Self::with(
            status,
            json!({ "error": message, "status": status, "trust_note": TRUST_NOTE }),
        )
    }
}

/// The honest soundness-model block embedded in `/stats`, `/` and `/lookup`.
fn soundness_model_json() -> serde_json::Value {
    json!({
        "role": "distribution front-end, NOT a trust authority",
        "cached_proof": "PROVENANCE: a proof-bearing result ships a re-checkable proof term; the \
                         consumer MUST re-run it through the kernel (recheck_and_classify). The \
                         solver stays out of the TCB.",
        "raw_verdict": "a bare unsat/timeout/unknown verdict is TELEMETRY / a hint, never a \
                        verification (design §2.4).",
        "ingest": "ingest never mints a 'verified' badge; a submitted proof must be \
                   kernel-re-checkable by the consumer. The obligation digest is a soundness \
                   BUCKET; the kernel is the ARBITER.",
        "index": "VCIDX01 keys the FULL 256-bit obligation digest (no prefix truncation) — the \
                  result-cache safe direction inverts vs the novelty gate (design §2.5).",
    })
}

/// Route a parsed request to its handler.
///
/// `method` is the HTTP verb, `path` the decoded path, `query` the parsed query
/// map, and `body` the request body (empty for GET; the ingest envelope for
/// `POST /ingest`). The result is a status + JSON value the transport renders.
#[must_use]
pub fn dispatch(
    state: &ServeState,
    method: &str,
    path: &str,
    query: &HashMap<String, String>,
    body: &[u8],
) -> ApiResponse {
    if path == "/ingest" {
        return match method {
            "POST" => super::ingest::handle_ingest(state, body),
            _ => ApiResponse::error(405, "POST a solver-attempt-record envelope to /ingest"),
        };
    }

    if method != "GET" {
        return ApiResponse::error(405, "only GET is supported (except POST /ingest)");
    }

    match path {
        "/healthz" => ApiResponse::ok(json!({ "status": "ok", "service": SERVICE_NAME })),
        "/" => ApiResponse::ok(banner_json(state)),
        "/stats" => handle_stats(state),
        "/weak" => handle_weak(state, query),
        "/vbs-gap" => handle_vbs_gap(state, query),
        "/export-dataset" => handle_export(state, query),
        other => match other.strip_prefix("/lookup/") {
            Some(digest) => handle_lookup(state, digest),
            None => ApiResponse::error(404, "no such endpoint"),
        },
    }
}

/// Read every attempt row under the configured data directories.
fn read_rows(state: &ServeState) -> Result<Vec<SolverAttemptRecord>, AnalysisError> {
    let refs: Vec<&Path> = state.data_dirs.iter().map(PathBuf::as_path).collect();
    super::analysis::read_attempts_from_dirs(&refs)
}

/// `GET /stats` — the full aggregate report + honest trust posture.
fn handle_stats(state: &ServeState) -> ApiResponse {
    match service::stats(&state.data_dirs, state.budget_ms) {
        Ok(report) => ApiResponse::ok(json!({
            "service": SERVICE_NAME,
            "report": report,
            "corpus_pin": state.corpus_pin(),
            "ingest_enabled": state.ingest_enabled(),
            "soundness_model": soundness_model_json(),
            "trust_note": TRUST_NOTE,
        })),
        Err(e) => ApiResponse::error(500, &format!("stats: {e}")),
    }
}

/// `GET /weak?by=&top=&budget_ms=` — the worst-class regression worklist.
fn handle_weak(state: &ServeState, query: &HashMap<String, String>) -> ApiResponse {
    let by = match query.get("by").map(String::as_str) {
        None | Some("theory") => WeakBy::Theory,
        Some("solver") => WeakBy::Solver,
        Some("theory-solver") => WeakBy::TheorySolver,
        Some(other) => {
            return ApiResponse::error(
                400,
                &format!("unknown by=`{other}` (theory|solver|theory-solver)"),
            )
        }
    };
    let top = query
        .get("top")
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(DEFAULT_WEAK_TOP);
    let budget = budget_from(query, state.budget_ms);
    match service::weak(&state.data_dirs, by, budget, top) {
        Ok(classes) => ApiResponse::ok(json!({
            "by": query.get("by").map(String::as_str).unwrap_or("theory"),
            "budget_ms": budget,
            "classes": classes,
            "trust_note": TRUST_NOTE,
        })),
        Err(e) => ApiResponse::error(500, &format!("weak: {e}")),
    }
}

/// `GET /vbs-gap?budget_ms=` — the headroom a learned selector could capture.
fn handle_vbs_gap(state: &ServeState, query: &HashMap<String, String>) -> ApiResponse {
    let budget = budget_from(query, state.budget_ms);
    match service::vbs_gap(&state.data_dirs, budget) {
        Ok(gap) => ApiResponse::ok(json!({
            "budget_ms": budget,
            "vbs_gap": gap,
            "note": "the Phase-3 learned-selector gate: a small gap means a per-instance \
                     strategy selector is not worth building (design §6).",
            "trust_note": TRUST_NOTE,
        })),
        Err(e) => ApiResponse::error(500, &format!("vbs-gap: {e}")),
    }
}

/// `GET /export-dataset?engine=&theory=&limit=` — a bounded inline NN dataset.
fn handle_export(state: &ServeState, query: &HashMap<String, String>) -> ApiResponse {
    let filter = ExportFilter {
        engine: query.get("engine").filter(|s| !s.is_empty()).cloned(),
        theory: query.get("theory").filter(|s| !s.is_empty()).cloned(),
    };
    let limit = query
        .get("limit")
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(DEFAULT_EXPORT_LIMIT)
        .min(MAX_EXPORT_LIMIT);
    let records = match read_rows(state) {
        Ok(r) => r,
        Err(e) => return ApiResponse::error(500, &format!("export-dataset: {e}")),
    };
    let all = dataset::rows(&records, &filter, state.budget_ms);
    let total = all.len();
    let truncated = total > limit;
    let rows: Vec<serde_json::Value> = all
        .iter()
        .take(limit)
        .map(|r| serde_json::to_value(r).unwrap_or(serde_json::Value::Null))
        .collect();
    ApiResponse::ok(json!({
        "schema": "solver-attempt-dataset-v1",
        "count": rows.len(),
        "total_available": total,
        "truncated": truncated,
        "budget_ms": state.budget_ms,
        "rows": rows,
        "labels_note": "labels are Clean-engine-specific and non-transferable; oracle rows carry \
                        engine_cost_is_cpu=false; siblings share obligation_digest (design §6.3).",
        "trust_note": TRUST_NOTE,
    }))
}

/// `GET /lookup/{obligation_digest}` — per-obligation provenance summary.
///
/// Uses the pre-built `VCIDX01` for a µs lookup when one is loaded *and* ingest
/// is disabled (a read-only deployment); otherwise it aggregates live from the
/// telemetry stream so a freshly-ingested record is reflected immediately.
fn handle_lookup(state: &ServeState, digest: &str) -> ApiResponse {
    if index::digest_key(digest).is_none() {
        return ApiResponse::error(400, "obligation_digest must be a blake3:<64hex> string");
    }
    let summary = match (&state.index, state.ingest_enabled()) {
        (Some(idx), false) => idx.lookup(digest),
        _ => live_summary(state, digest),
    };
    match summary {
        Some(s) => ApiResponse::ok(lookup_json(digest, &s, state.index.is_some())),
        None => ApiResponse::ok(json!({
            "obligation_digest": digest,
            "found": false,
            "note": "no recorded attempt for this obligation (a clean miss, not an error)",
            "trust_note": TRUST_NOTE,
        })),
    }
}

/// Render a found `/lookup` summary with its re-checkability semantics.
fn lookup_json(digest: &str, s: &ObligationSummary, indexed: bool) -> serde_json::Value {
    let verdict_kind = if s.cached {
        "proof-bearing-provenance"
    } else {
        "telemetry-only"
    };
    json!({
        "obligation_digest": digest,
        "found": true,
        "summary": {
            "cached": s.cached,
            "attempts": s.attempts,
            "solved": s.solved,
            "best_wall_ms": s.best_wall_ms,
        },
        "re_checkable": s.cached,
        "verdict_kind": verdict_kind,
        "served_from": if indexed { "vcidx01-or-live" } else { "live-aggregate" },
        "recheck_note": "If re_checkable, a proof term is cached under this digest: fetch it and \
                         re-run it through the kernel (recheck_and_classify) — the service asserts \
                         nothing on its own authority. Otherwise the attempts are telemetry/hints.",
        "soundness_model": soundness_model_json(),
        "trust_note": TRUST_NOTE,
    })
}

/// Live single-digest summary: fold the telemetry stream + cache membership into
/// one [`ObligationSummary`] (the same shape `VCIDX01` serves).
fn live_summary(state: &ServeState, digest: &str) -> Option<ObligationSummary> {
    let records = read_rows(state).ok()?;
    let mut acc = SummaryAccumulator::default();
    let mut seen = false;
    for r in &records {
        if r.obligation_digest == digest {
            seen = true;
            acc.add_attempt(r.success, r.wall_ms);
        }
    }
    let cached = state
        .data_dirs
        .iter()
        .flat_map(|d| store::cached_digests(d))
        .any(|d| d.as_str() == digest);
    if cached {
        acc.mark_cached();
    }
    (seen || cached).then(|| acc.finish())
}

/// Parse a `budget_ms` query override, falling back to the configured default.
fn budget_from(query: &HashMap<String, String>, default: u64) -> u64 {
    query
        .get("budget_ms")
        .and_then(|s| s.parse::<u64>().ok())
        .filter(|b| *b > 0)
        .unwrap_or(default)
}

/// The `/` service banner: endpoint list + the trust posture.
fn banner_json(state: &ServeState) -> serde_json::Value {
    json!({
        "service": SERVICE_NAME,
        "role": "Phase-2 distribution + ingest front-end for the solver-results cache \
                 (the software-verification analogue of mathverse_serve, over SOLVED OBLIGATIONS \
                 rather than verified MATH).",
        "data_dirs": state.data_dir_count(),
        "corpus_pin": state.corpus_pin(),
        "ingest_enabled": state.ingest_enabled(),
        "endpoints": [
            "GET  /healthz",
            "GET  /stats",
            "GET  /weak?by=theory|solver|theory-solver&top=&budget_ms=",
            "GET  /vbs-gap?budget_ms=",
            "GET  /lookup/{obligation_digest}",
            "GET  /export-dataset?engine=&theory=&limit=",
            "POST /ingest    (append a solver-attempt-record + optional proof blob)",
        ],
        "soundness_model": soundness_model_json(),
        "trust_note": TRUST_NOTE,
    })
}
