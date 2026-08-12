// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Request routing for `mathverse_serve`.
//!
//! Maps the read-only endpoint surface onto [`clean_mathverse::serve_api`] and
//! the Phase-2 verdict store ([`clean_mathverse::trust_sign::VerdictStore`]):
//!
//! - `GET  /healthz`          -> `200 ok` (Cloud Run health probe)
//! - `GET  /stats`            -> corpus stats + honest trust ladder note
//! - `GET  /search?q=&type=&axiom=&domain=&limit=` -> matching declarations
//! - `GET  /type?like=&limit=` -> type-directed (discrimination-tree) search
//! - `GET  /equivalent/{name}` -> structural-equivalence (rewrite-canonical .mvix) lookup
//! - `GET  /theorem/{name}`   -> one declaration (trust, axioms, digest, deps)
//! - `GET  /rdeps/{name}`     -> reverse deps (users / blast radius), impact-ranked
//!   (alias `GET /uses/{name}`; `?transitive=&depth=&limit=`)
//! - `GET  /shards`           -> shard inventory + sizes
//! - `GET  /manifest`         -> release manifest (blake3 per shard) for re-verify
//! - `GET  /download/{shard}` -> stream bytes, or 302 to `$MATHVERSE_DOWNLOAD_BASE`
//! - `GET  /verdict/{name}`   -> the SIGNED provenance record (Phase 2), or 404
//! - `GET  /audit`            -> re-audit summary (examined / signed / revoked)
//! - `POST /submit`           -> Phase-2.1: validate + STAGE a candidate (pending)
//! - `GET  /submit/{id}`      -> Phase-2.1: submission status + signed verdict
//!
//! `POST /submit` holds NO signing key and NEVER mints. It validates
//! well-formedness and stages the candidate to `$MATHVERSE_SUBMIT_QUEUE`; the
//! privileged offline `mathverse_publisher` re-verifies in a fresh kernel and
//! signs only a foundational re-check (the authoritative gate).
//!
//! The Phase-2 endpoints serve STORED, signed provenance produced offline by
//! `mathverse_reauditor`. The signature attests provenance; the de Bruijn
//! `expr_canonical_digest` is the independently re-verifiable truth. This
//! service never mints, upgrades, or re-audits a verdict at request time.

use clean_mathverse::serve_api::{CoreHandle, SearchParams};
use clean_mathverse::trust_sign::{
    StageError, SubmissionError, SubmissionQueue, VerdictStore, SUBMISSION_TRUST_NOTE,
};

use super::config::{DownloadMode, ServeConfig};
use super::http::{Request, Response};

/// Shared, read-only application state: the loaded Core, the signed-verdict
/// store, and the config.
pub(crate) struct AppState {
    pub(crate) core: CoreHandle,
    /// Phase-2 signed verdicts + revocation list loaded from the re-auditor's
    /// output directory (empty when `$MATHVERSE_VERDICTS_DIR` is unset).
    pub(crate) verdicts: VerdictStore,
    /// Phase-2.1 submission queue (when `$MATHVERSE_SUBMIT_QUEUE` is set). The
    /// front-end ONLY stages to it and reads status from it — it holds NO
    /// signing key and never mints a verdict. `None` disables `/submit`.
    pub(crate) submit_queue: Option<SubmissionQueue>,
    pub(crate) config: ServeConfig,
}

/// Route a parsed request to its handler.
pub(crate) fn dispatch(state: &AppState, req: &Request) -> Response {
    let path = req.path.as_str();

    // `POST /submit` stages a candidate (Phase 2.1). `GET /submit/{id}` reads a
    // submission's status. Both go through the queue front-end, which holds no
    // signing key.
    if path == "/submit" {
        if req.method == "POST" {
            return handle_submit(state, req);
        }
        return Response::error(
            405,
            "POST a candidate declaration to /submit; GET /submit/{id} for status",
        );
    }
    if let Some(id) = path.strip_prefix("/submit/") {
        if req.method != "GET" {
            return Response::error(405, "GET /submit/{id} for submission status");
        }
        return handle_submit_status(state, id);
    }

    if req.method != "GET" {
        return Response::error(405, "only GET is supported by this read-only service");
    }

    if path == "/healthz" {
        return Response::text(200, "ok");
    }
    if path == "/stats" {
        return Response::json(&state.core.stats_json());
    }
    if path == "/search" {
        return handle_search(state, req);
    }
    if path == "/type" {
        return handle_type_search(state, req);
    }
    if path == "/shards" {
        return Response::json(&state.core.shards_json());
    }
    if path == "/manifest" {
        // The release manifest (blake3 per shard) so a server-download client
        // can fetch it and re-verify the corpus it pulls.
        return Response::json(&state.core.release_manifest_json());
    }
    if path == "/audit" {
        return Response::json(&state.verdicts.audit_json());
    }
    if let Some(name) = path.strip_prefix("/verdict/") {
        return handle_verdict(state, name);
    }
    if let Some(name) = path.strip_prefix("/theorem/") {
        return handle_theorem(state, name);
    }
    // Structural-equivalence lookup: "is this theorem already proven, differently
    // stated?" — the .mvix semantic-table probe.
    if let Some(name) = path.strip_prefix("/equivalent/") {
        return handle_equivalent(state, name);
    }
    // Reverse-dependency search: `/rdeps/{name}` and its `/uses/{name}` alias.
    if let Some(name) = path
        .strip_prefix("/rdeps/")
        .or_else(|| path.strip_prefix("/uses/"))
    {
        return handle_rdeps(state, req, name);
    }
    if let Some(shard) = path.strip_prefix("/download/") {
        return handle_download(state, shard);
    }
    if path == "/" {
        return Response::json(&index_json());
    }

    Response::error(404, "no such endpoint")
}

/// `GET /search` — name/type/axiom/domain filters with a bounded result count.
fn handle_search(state: &AppState, req: &Request) -> Response {
    let limit = req
        .query
        .get("limit")
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(SearchParams::DEFAULT_LIMIT)
        .min(SearchParams::MAX_LIMIT);

    let params = SearchParams {
        q: req.query.get("q").cloned().unwrap_or_default(),
        type_query: req.query.get("type").filter(|s| !s.is_empty()).cloned(),
        axiom: req.query.get("axiom").filter(|s| !s.is_empty()).cloned(),
        domain: req.query.get("domain").filter(|s| !s.is_empty()).cloned(),
        limit,
    };
    Response::json(&state.core.search_json(&params))
}

/// `GET /theorem/{name}` — one declaration, or 404.
fn handle_theorem(state: &AppState, name: &str) -> Response {
    if name.is_empty() {
        return Response::error(400, "missing theorem name");
    }
    match state.core.theorem_json(name) {
        Some(value) => Response::json(&value),
        None => Response::error(404, "no such declaration in the loaded Core"),
    }
}

/// `GET /type?like={name}&limit=` — type-directed (discrimination-tree) search:
/// declarations whose type structurally matches the reference declaration
/// `{like}`'s type. A 404 distinguishes an unknown reference declaration.
fn handle_type_search(state: &AppState, req: &Request) -> Response {
    let Some(like) = req.query.get("like").filter(|s| !s.is_empty()) else {
        return Response::error(
            400,
            "missing `like` reference declaration (GET /type?like=Nat.add_comm)",
        );
    };
    let limit = req
        .query
        .get("limit")
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(SearchParams::DEFAULT_LIMIT)
        .min(SearchParams::MAX_LIMIT);
    match state.core.type_search_json(like, limit) {
        Some(value) => Response::json(&value),
        None => Response::error(404, "no such reference declaration in the loaded Core"),
    }
}

/// `GET /equivalent/{name}` — structural-equivalence lookup: the corpus-wide
/// canonical representative of `{name}`'s statement, equal up to commutative
/// rewrite (the "already proven, differently stated?" probe over the loaded
/// `baseline.mvix` semantic table). A 404 distinguishes an unknown declaration
/// or one whose type cannot be reconstructed.
fn handle_equivalent(state: &AppState, name: &str) -> Response {
    if name.is_empty() {
        return Response::error(400, "missing declaration name");
    }
    match state.core.equivalent_json(name) {
        Some(value) => Response::json(&value),
        None => Response::error(
            404,
            "no such declaration in the loaded Core, or its type is not reconstructable",
        ),
    }
}

/// `GET /rdeps/{name}` (alias `/uses/{name}`) — reverse-dependency search:
/// the declarations in the loaded Core that depend on `{name}`. Query params:
/// `transitive` (`1`/`true` to follow past direct users), `depth` (BFS bound),
/// and `limit` (max hits, capped at [`SearchParams::MAX_LIMIT`]). A 404
/// distinguishes an unknown declaration from a known one with no users.
fn handle_rdeps(state: &AppState, req: &Request, name: &str) -> Response {
    if name.is_empty() {
        return Response::error(400, "missing declaration name");
    }
    let transitive = req
        .query
        .get("transitive")
        .map(|v| v.as_str() == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false);
    let depth = req
        .query
        .get("depth")
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(if transitive { usize::MAX } else { 1 });
    let limit = req
        .query
        .get("limit")
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(SearchParams::DEFAULT_LIMIT)
        .min(SearchParams::MAX_LIMIT);
    // A `depth > 1` request implies a transitive walk even without the flag.
    let transitive = transitive || depth > 1;
    match state.core.rdeps_json(name, transitive, depth, limit) {
        Some(value) => Response::json(&value),
        None => Response::error(404, "no such declaration in the loaded Core"),
    }
}

/// `GET /verdict/{name}` — the signed provenance record for a re-audited
/// declaration, or a 404 distinguishing "no verdict directory loaded" from
/// "this declaration was not re-audited". The payload restates the honesty
/// contract: the signature is provenance; the digest is the re-verifiable truth.
fn handle_verdict(state: &AppState, name: &str) -> Response {
    if name.is_empty() {
        return Response::error(400, "missing declaration name");
    }
    if let Some(value) = state.verdicts.verdict_json(name) {
        return Response::json(&value);
    }
    // A miss: be honest about *why* there is no signed verdict.
    let detail = if state.verdicts.is_loaded() {
        "no signed verdict for this declaration (not re-audited). The de Bruijn \
         expr_canonical_digest from /theorem remains independently re-verifiable."
    } else {
        "re-audit data not loaded (set $MATHVERSE_VERDICTS_DIR to the reauditor \
         output). This service serves stored provenance, not a live re-audit."
    };
    Response::error(404, detail)
}

/// `POST /submit` — Phase-2.1 live submission front-end.
///
/// VALIDATES well-formedness (parse + size limit + value-bearing shape), STAGES
/// the candidate to the queue with a generated `submission_id` (status=pending),
/// and returns `{submission_id, status: "pending", note}`. The front-end holds
/// NO signing key and NEVER re-verifies-and-mints at request time — the
/// authoritative gate is the privileged offline `mathverse_publisher`, which
/// re-runs the kernel in a FRESH environment and signs only a foundational
/// re-check. A malformed body is rejected here (400); it is never staged.
fn handle_submit(state: &AppState, req: &Request) -> Response {
    let Some(queue) = state.submit_queue.as_ref() else {
        return Response::json_with_status(
            503,
            &serde_json::json!({
                "error": "submissions not enabled (set $MATHVERSE_SUBMIT_QUEUE)",
                "status": 503,
                "note": SUBMISSION_TRUST_NOTE,
            }),
        );
    };

    let now = now_rfc3339_utc();
    match queue.stage(&req.body, &now) {
        Ok(record) => Response::json_with_status(
            202,
            &serde_json::json!({
                "submission_id": record.submission_id,
                "status": "pending",
                "submitted_at": record.submitted_at,
                "note": SUBMISSION_TRUST_NOTE,
            }),
        ),
        Err(StageError::Invalid(e)) => {
            // A well-formedness rejection at the door (cheap syntactic pre-check).
            let status = match &e {
                SubmissionError::TooLarge { .. } => 413,
                _ => 400,
            };
            Response::json_with_status(
                status,
                &serde_json::json!({
                    "error": e.to_string(),
                    "status": status,
                    "note": SUBMISSION_TRUST_NOTE,
                }),
            )
        }
        Err(StageError::Write(reason)) => Response::json_with_status(
            500,
            &serde_json::json!({ "error": format!("could not stage submission: {reason}"), "status": 500 }),
        ),
        // `StageError` is `#[non_exhaustive]`: treat any future variant as a
        // server-side staging failure (fail-closed, never a silent accept).
        Err(other) => Response::json_with_status(
            500,
            &serde_json::json!({ "error": format!("could not stage submission: {other}"), "status": 500 }),
        ),
    }
}

/// `GET /submit/{id}` — the lifecycle status of a staged submission
/// (`pending` | `KernelVerified` | `Rejected`), with the signed verdict once the
/// publisher has decided. A 404 distinguishes "submissions not enabled" from
/// "no such submission id".
fn handle_submit_status(state: &AppState, id: &str) -> Response {
    let Some(queue) = state.submit_queue.as_ref() else {
        return Response::error(404, "submissions not enabled (set $MATHVERSE_SUBMIT_QUEUE)");
    };
    if id.is_empty() {
        return Response::error(400, "missing submission id");
    }
    match queue.load(id) {
        Some(record) => Response::json(&record.status_json()),
        None => Response::error(404, "no such submission id"),
    }
}

/// A coarse RFC-3339-ish UTC timestamp from the wall clock. Mirrors the
/// re-auditor binary's stamp: the schema only requires a deterministic UTC
/// string, not calendar precision.
fn now_rfc3339_utc() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    format!("1970-01-01T00:00:00Z+{secs}s")
}

/// `GET /download/{shard}` — stream local bytes, or 302 to the download base.
fn handle_download(state: &AppState, shard: &str) -> Response {
    if shard.is_empty() {
        return Response::error(400, "missing shard name");
    }
    match &state.config.download_mode {
        DownloadMode::Redirect { base } => match state.core.shard_rel_path(shard) {
            Some(rel) => Response::redirect(format!("{base}/{rel}")),
            None => Response::error(404, "no such shard"),
        },
        DownloadMode::StreamLocal => match state.core.resolve_shard_path(shard) {
            Some(path) => Response::file(path),
            None => Response::error(404, "no such shard"),
        },
    }
}

/// Service banner served at `/` — lists endpoints and restates the trust posture.
fn index_json() -> serde_json::Value {
    serde_json::json!({
        "service": "mathverse_serve",
        "role": "read-only distribution front-end for the verified Mathverse Core, \
                 plus Phase-2 signed-verdict provenance",
        "trust_posture": "NOT a trust authority. Serves STORED labels, content digests, and \
                          signed PROVENANCE so consumers re-verify independently (de Bruijn). \
                          A signature attests which verifier saw which kernel result over which \
                          digest; it is never the root of trust.",
        "endpoints": [
            "GET  /healthz",
            "GET  /stats",
            "GET  /search?q=&type=&axiom=&domain=&limit=",
            "GET  /type?like={name}&limit=   (type-directed discrimination-tree search)",
            "GET  /equivalent/{name}   (structural-equivalence: corpus-wide canonical representative up to commutative rewrite)",
            "GET  /theorem/{name}",
            "GET  /rdeps/{name}?transitive=&depth=&limit=   (reverse deps / users, impact-ranked; alias /uses/{name})",
            "GET  /shards",
            "GET  /manifest",
            "GET  /download/{shard}",
            "GET  /verdict/{name}   (Phase 2: signed provenance record, or 404)",
            "GET  /audit            (Phase 2: re-audit summary)",
            "POST /submit           (Phase 2.1: validate + stage a candidate, status=pending)",
            "GET  /submit/{id}      (Phase 2.1: submission status + signed verdict)",
        ],
        "submit_note": SUBMISSION_TRUST_NOTE,
    })
}
