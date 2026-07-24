// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse_serve` — the Phase-1 Mathverse Cloud Run distribution front-end.
//!
//! A read-only async HTTP/1.1 service that browses, searches, and streams the
//! verified Core. It is a DISTRIBUTION front-end, NOT a trust authority: it
//! serves the STORED import/trust labels plus the per-declaration
//! `expr_canonical_digest` so a consumer re-verifies independently (de Bruijn).
//! It never mints or alters a verdict — minting verdicts is Phase 2.
//!
//! Phase 2.1 adds a LIVE submission front-end: `POST /submit` validates +
//! stages a candidate declaration to a queue (status=pending) and
//! `GET /submit/{id}` reports its status. The front-end holds NO signing key
//! and never mints — the privileged offline `mathverse_publisher` re-verifies
//! each queued submission in a FRESH kernel and signs only a foundational
//! re-check.
//!
//! Configuration (all via environment):
//!   - `$PORT`                   TCP port (Cloud Run injects it; default 8080)
//!   - `$MATHVERSE_CORE_DIR`     verified Core (manifest + base/ shards + .mvix)
//!   - `$MATHVERSE_DOWNLOAD_BASE`  optional: 302-redirect downloads to this host
//!     (e.g. a GCS signed-URL base) instead of streaming local bytes.
//!   - `$MATHVERSE_VERDICTS_DIR`   optional: signed verdicts for /verdict + /audit
//!   - `$MATHVERSE_SUBMIT_QUEUE`   optional: enables POST /submit + GET /submit/{id}

mod config;
mod http;
mod routes;

use std::rc::Rc;

use anyhow::{Context, Result};
use clean_mathverse::serve_api::CoreHandle;
use clean_mathverse::trust_sign::{SubmissionQueue, VerdictStore};

use config::ServeConfig;
use routes::AppState;

fn main() -> Result<()> {
    let config = ServeConfig::from_env()?;

    eprintln!(
        "Loading Mathverse Core from {} ...",
        config.core_dir.display()
    );
    let core = CoreHandle::load(&config.core_dir)
        .with_context(|| format!("failed to load Core at {}", config.core_dir.display()))?;
    eprintln!(
        "Loaded {} declarations. Trust labels are STORED import verdicts, not a \
         re-verification by this service.",
        core.constant_count()
    );

    // Phase-2: load the offline re-auditor's signed verdicts + revocation list,
    // if a verdict directory is configured. The service serves this stored
    // PROVENANCE; it never re-audits at request time. Absent the directory, the
    // verdict store is empty and `/verdict` / `/audit` report "not re-audited".
    let verdicts = match &config.verdicts_dir {
        Some(dir) => {
            eprintln!("Loading signed verdicts from {} ...", dir.display());
            let store = VerdictStore::load(dir)
                .with_context(|| format!("failed to load verdict store at {}", dir.display()))?;
            eprintln!(
                "Loaded {} signed verdict(s). Signatures attest PROVENANCE, not correctness — \
                 the de Bruijn digest stays the independently re-verifiable truth.",
                store.examined()
            );
            store
        }
        None => {
            eprintln!(
                "No $MATHVERSE_VERDICTS_DIR set: /verdict and /audit will report \
                 \"not re-audited\"."
            );
            VerdictStore::empty()
        }
    };

    // Phase-2.1: open the submission queue if configured. The front-end ONLY
    // stages candidates to it and reads their status — it holds NO signing key
    // and never mints. The privileged offline `mathverse_publisher` is the
    // authoritative re-verify-and-sign gate.
    let submit_queue = match &config.submit_queue_dir {
        Some(dir) => {
            let queue = SubmissionQueue::open(dir)
                .with_context(|| format!("failed to open submission queue at {}", dir.display()))?;
            eprintln!(
                "Submission queue at {}: POST /submit stages candidates (status=pending). \
                 This front-end holds NO signing key — the offline mathverse_publisher \
                 re-verifies and mints.",
                dir.display()
            );
            Some(queue)
        }
        None => {
            eprintln!(
                "No $MATHVERSE_SUBMIT_QUEUE set: POST /submit will report \
                 \"submissions not enabled\"."
            );
            None
        }
    };

    let port = config.port;
    let state = Rc::new(AppState {
        core,
        verdicts,
        submit_queue,
        config,
    });

    // A current-thread runtime: the loaded library is `!Sync` (thread-local
    // BM25 index), so the front-end serves connections sequentially on one
    // thread. Cloud Run scales out by instance count, and every request is a
    // cheap in-memory lookup or a streamed file.
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .context("failed to build tokio runtime")?;

    let local = tokio::task::LocalSet::new();
    local.block_on(&runtime, http::serve(state, port))
}
