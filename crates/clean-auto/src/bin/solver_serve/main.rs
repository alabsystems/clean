// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `solver_serve` — the Phase-2 solver-results-cache distribution + ingest
//! front-end.
//!
//! An async HTTP/1.1 service over the `VCIDX01` index + the
//! `solver-attempt-record-v1` telemetry stream. It is a DISTRIBUTION front-end,
//! NOT a trust authority (design §10.3): it serves the telemetry, the content
//! digests, and (where present) the re-checkable proof terms so a consumer
//! re-verifies independently through the kernel. It never asserts a result is
//! correct on its own authority, and `POST /ingest` never mints a `verified`
//! badge.
//!
//! This is the software-verification analogue of `mathverse_serve` (which serves
//! verified MATH); it serves SOLVED OBLIGATIONS. The transport-agnostic dispatch
//! + ingest logic lives in the library (`clean_auto::solver_cache_service`); this
//! binary is the thin raw-`tokio` HTTP shell, mirroring `mathverse_serve`.
//!
//! Configuration (all via environment):
//!   - `$PORT`                          TCP port (Cloud Run injects it; default 8080)
//!   - `$CLEAN_SOLVER_TELEMETRY_DIR`    telemetry dir (`attempts.jsonl`)
//!   - `$CLEAN_SOLVER_CACHE_DIR`        content-addressed proof-cache dir
//!   - `$CLEAN_SOLVER_INDEX`            optional pre-built `VCIDX01` (µs `/lookup`)
//!   - `$CLEAN_SOLVER_INGEST`           set non-empty to enable `POST /ingest`
//!   - `$CLEAN_SOLVER_BUDGET_MS`        PAR-2 timeout budget (default 5000)

#[cfg(not(target_arch = "wasm32"))]
mod config;
#[cfg(not(target_arch = "wasm32"))]
mod http;
#[cfg(not(target_arch = "wasm32"))]
mod routes;

#[cfg(not(target_arch = "wasm32"))]
use std::rc::Rc;

#[cfg(not(target_arch = "wasm32"))]
use anyhow::{Context, Result};
#[cfg(not(target_arch = "wasm32"))]
use clean_auto::solver_cache_service::ServeState;

#[cfg(not(target_arch = "wasm32"))]
use config::ServeConfig;
#[cfg(not(target_arch = "wasm32"))]
use routes::AppState;

/// What `-h`/`--help` prints. The service takes no arguments; every knob is an
/// environment variable `ServeConfig::from_env` reads.
#[cfg(not(target_arch = "wasm32"))]
const USAGE: &str = "\
usage: solver_serve   (no arguments; configured entirely by environment)
  PORT                        TCP port to bind (default 8080)
  CLEAN_SOLVER_TELEMETRY_DIR  telemetry dir (attempts.jsonl) — this and/or the cache dir is
                              required
  CLEAN_SOLVER_CACHE_DIR      content-addressed proof-cache dir
  CLEAN_SOLVER_INDEX          optional pre-built VCIDX01 index for /lookup
  CLEAN_SOLVER_INGEST         set non-empty to enable POST /ingest (needs the telemetry dir)
  CLEAN_SOLVER_BUDGET_MS      PAR-2 timeout budget in ms (default 5000; 0 or non-numeric
                              falls back to the default)
";

// wasm32 has no sockets and no tokio runtime; the service is native-only.
#[cfg(target_arch = "wasm32")]
fn main() {
    eprintln!("solver_serve is unavailable on wasm");
}

#[cfg(not(target_arch = "wasm32"))]
fn main() -> Result<()> {
    if let Some(arg) = std::env::args().nth(1) {
        if arg == "-h" || arg == "--help" {
            print!("{USAGE}");
            return Ok(());
        }
        eprint!("solver_serve: unexpected argument {arg:?}\n{USAGE}");
        std::process::exit(2);
    }
    let config = ServeConfig::from_env()?;

    eprintln!(
        "Loading solver-cache service over {} data dir(s){} ...",
        config.data_dirs.len(),
        config
            .index_path
            .as_ref()
            .map(|p| format!(" + VCIDX01 index {}", p.display()))
            .unwrap_or_default()
    );

    let state = ServeState::new(
        config.data_dirs.clone(),
        config.index_path.clone(),
        config.ingest_telemetry_dir.clone(),
        config.ingest_cache_dir.clone(),
        config.reindex_path.clone(),
        config.budget_ms,
    )
    .context("failed to build solver-cache serving state")?;

    eprintln!(
        "Ready. Trust posture: DISTRIBUTION front-end, NOT a trust authority. A cached result is \
         PROVENANCE — a proof-bearing hit ships a re-checkable proof term the consumer re-runs \
         through the kernel; a raw verdict is telemetry. Ingest {} and NEVER mints 'verified'.",
        if state.ingest_enabled() {
            "ENABLED"
        } else {
            "disabled"
        }
    );

    let port = config.port;
    let app = Rc::new(AppState { state, config });

    // A current-thread runtime: each request is a cheap in-memory aggregation or
    // an append; Cloud Run scales out by instance count. `state` is therefore an
    // `Rc`, not an `Arc` (mirrors `mathverse_serve`).
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .context("failed to build tokio runtime")?;

    let local = tokio::task::LocalSet::new();
    local.block_on(&runtime, http::serve(app, port))
}
