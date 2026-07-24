// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Environment-driven configuration for the Mathverse Cloud Run service.
//!
//! Cloud Run injects `$PORT`; the operator points `$MATHVERSE_CORE_DIR` at the
//! verified Core (a `LibraryLoader` layout) and may set
//! `$MATHVERSE_DOWNLOAD_BASE` to redirect shard downloads to GCS signed URLs.

use std::path::PathBuf;

use anyhow::{Context, Result};

/// How `/download/{shard}` serves shard bytes.
#[derive(Clone, Debug)]
pub(crate) enum DownloadMode {
    /// Stream the `.mathverse` bytes directly from the local Core directory.
    StreamLocal,
    /// 302-redirect to `{base}/{shard-rel-path}` (e.g. a GCS signed-URL host).
    Redirect { base: String },
}

/// Fully resolved service configuration.
#[derive(Clone, Debug)]
pub(crate) struct ServeConfig {
    /// TCP port to bind (Cloud Run injects `$PORT`; default 8080).
    pub(crate) port: u16,
    /// Core directory: manifest + base/delta shards (+ optional baseline.mvix).
    pub(crate) core_dir: PathBuf,
    /// Shard download strategy.
    pub(crate) download_mode: DownloadMode,
    /// Optional Phase-2 re-auditor output directory (signed verdicts +
    /// revocation list). When set, `/verdict/{name}` and `/audit` serve the
    /// stored signed PROVENANCE; when unset, they honestly report "not
    /// re-audited". This service never re-audits at request time — it serves
    /// what the offline `mathverse_reauditor` signed.
    pub(crate) verdicts_dir: Option<PathBuf>,
    /// Optional Phase-2.1 submission queue directory. When set, `POST /submit`
    /// validates + stages a candidate declaration (status=pending) and
    /// `GET /submit/{id}` reports its status. The front-end holds NO signing key
    /// and NEVER mints — the privileged offline `mathverse_publisher` is the
    /// authoritative gate that re-verifies + signs. When unset, `/submit`
    /// reports "submissions not enabled".
    pub(crate) submit_queue_dir: Option<PathBuf>,
}

impl ServeConfig {
    /// Default port when `$PORT` is unset (matches Cloud Run's documented
    /// default contract).
    pub(crate) const DEFAULT_PORT: u16 = 8080;

    /// Read configuration from the process environment.
    ///
    /// # Errors
    /// Fails when `$MATHVERSE_CORE_DIR` is unset/empty or `$PORT` is set but
    /// not a valid u16.
    pub(crate) fn from_env() -> Result<Self> {
        let port = match std::env::var("PORT") {
            Ok(s) if !s.is_empty() => s
                .parse::<u16>()
                .with_context(|| format!("$PORT is not a valid TCP port: {s:?}"))?,
            _ => Self::DEFAULT_PORT,
        };

        let core_dir = std::env::var("MATHVERSE_CORE_DIR")
            .ok()
            .filter(|s| !s.is_empty())
            .map(PathBuf::from)
            .context(
                "$MATHVERSE_CORE_DIR must point at the verified Core directory \
                 (manifest.json + base/ shards). Set it before starting the service.",
            )?;

        let download_mode = match std::env::var("MATHVERSE_DOWNLOAD_BASE") {
            Ok(base) if !base.is_empty() => DownloadMode::Redirect {
                base: base.trim_end_matches('/').to_string(),
            },
            _ => DownloadMode::StreamLocal,
        };

        let verdicts_dir = std::env::var("MATHVERSE_VERDICTS_DIR")
            .ok()
            .filter(|s| !s.is_empty())
            .map(PathBuf::from);

        let submit_queue_dir = std::env::var("MATHVERSE_SUBMIT_QUEUE")
            .ok()
            .filter(|s| !s.is_empty())
            .map(PathBuf::from);

        Ok(Self {
            port,
            core_dir,
            download_mode,
            verdicts_dir,
            submit_queue_dir,
        })
    }
}
