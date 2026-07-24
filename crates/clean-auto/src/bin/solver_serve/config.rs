// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Environment-driven configuration for `solver_serve`.
//!
//! Cloud Run injects `$PORT`; the operator points the service at the Phase-0/1
//! producer artifacts via the SAME env vars the producer + `clean solver` CLI
//! use (`$CLEAN_SOLVER_TELEMETRY_DIR`, `$CLEAN_SOLVER_CACHE_DIR`), optionally a
//! pre-built `VCIDX01` (`$CLEAN_SOLVER_INDEX`), and enables ingest with
//! `$CLEAN_SOLVER_INGEST`.

use std::path::PathBuf;

use anyhow::{bail, Context, Result};
use clean_auto::solver_cache_service as svc;

/// The PAR-2 timeout-budget env var (ms).
const BUDGET_ENV: &str = "CLEAN_SOLVER_BUDGET_MS";
/// Pre-built `VCIDX01` index path env var.
const INDEX_ENV: &str = "CLEAN_SOLVER_INDEX";
/// Ingest-enable flag env var (non-empty ⇒ `POST /ingest` enabled).
const INGEST_ENV: &str = "CLEAN_SOLVER_INGEST";

/// Fully resolved service configuration.
#[derive(Clone, Debug)]
pub(crate) struct ServeConfig {
    /// TCP port to bind (`$PORT`; default 8080).
    pub(crate) port: u16,
    /// Telemetry + cache directories scanned by the read endpoints.
    pub(crate) data_dirs: Vec<PathBuf>,
    /// Optional pre-built `VCIDX01` for µs `/lookup`.
    pub(crate) index_path: Option<PathBuf>,
    /// Telemetry dir `POST /ingest` appends to (`None` ⇒ ingest disabled).
    pub(crate) ingest_telemetry_dir: Option<PathBuf>,
    /// Cache dir `POST /ingest` stores proof blobs under.
    pub(crate) ingest_cache_dir: Option<PathBuf>,
    /// `VCIDX01` rebuilt after each accepted ingest (best-effort).
    pub(crate) reindex_path: Option<PathBuf>,
    /// PAR-2 timeout budget (ms) the reports assume.
    pub(crate) budget_ms: u64,
}

impl ServeConfig {
    /// Default port when `$PORT` is unset (Cloud Run's documented default).
    const DEFAULT_PORT: u16 = 8080;
    /// Default PAR-2 budget when `$CLEAN_SOLVER_BUDGET_MS` is unset.
    const DEFAULT_BUDGET_MS: u64 = 5000;

    /// Read configuration from the process environment.
    ///
    /// # Errors
    /// Fails when no data directory is configured, when `$PORT` is set but not a
    /// valid `u16`, or when ingest is requested without a telemetry directory.
    pub(crate) fn from_env() -> Result<Self> {
        let port = match std::env::var("PORT") {
            Ok(s) if !s.is_empty() => s
                .parse::<u16>()
                .with_context(|| format!("$PORT is not a valid TCP port: {s:?}"))?,
            _ => Self::DEFAULT_PORT,
        };

        let telemetry_dir = non_empty_env(svc::telemetry_dir_env());
        let cache_dir = non_empty_env(svc::cache_dir_env());
        let mut data_dirs = Vec::new();
        if let Some(d) = &telemetry_dir {
            data_dirs.push(d.clone());
        }
        if let Some(d) = &cache_dir {
            data_dirs.push(d.clone());
        }
        if data_dirs.is_empty() {
            bail!(
                "set ${} and/or ${} to the Phase-0 producer artifact dirs before starting \
                 the service",
                svc::telemetry_dir_env(),
                svc::cache_dir_env()
            );
        }

        let index_path = non_empty_env(INDEX_ENV);

        let ingest_on = std::env::var_os(INGEST_ENV).is_some_and(|v| !v.is_empty());
        let (ingest_telemetry_dir, ingest_cache_dir, reindex_path) = if ingest_on {
            let dir = telemetry_dir.clone().with_context(|| {
                format!(
                    "ingest requires ${} (somewhere to append the accepted record)",
                    svc::telemetry_dir_env()
                )
            })?;
            (Some(dir), cache_dir.clone(), index_path.clone())
        } else {
            (None, None, None)
        };

        let budget_ms = std::env::var(BUDGET_ENV)
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .filter(|b| *b > 0)
            .unwrap_or(Self::DEFAULT_BUDGET_MS);

        Ok(Self {
            port,
            data_dirs,
            index_path,
            ingest_telemetry_dir,
            ingest_cache_dir,
            reindex_path,
            budget_ms,
        })
    }
}

/// Read an environment variable, returning `Some(PathBuf)` only when set + non-empty.
fn non_empty_env(name: &str) -> Option<PathBuf> {
    std::env::var_os(name)
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
}
