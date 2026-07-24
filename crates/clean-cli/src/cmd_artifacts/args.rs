// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clap argument surface for `clean artifacts <verb>`.

use std::path::PathBuf;

use clap::{Args, Subcommand};
use clean_mathverse::release::DEFAULT_CLEAN_RELEASE_REPO;

/// Verbs under `clean artifacts`.
///
/// Marked `#[non_exhaustive]` so §5.6 follow-ups (`push`, `pin`, registry
/// abstraction) can add variants without breaking downstream tooling.
#[derive(Debug, Clone, Subcommand)]
#[non_exhaustive]
pub(crate) enum ArtifactsCommands {
    /// List releases of a repository, or the assets of one release tag.
    List(ArtifactsListArgs),
    /// Download release assets with mandatory blake3 manifest verification.
    Get(ArtifactsGetArgs),
    /// Verify a directory of artifacts against a blake3 manifest.
    Verify(ArtifactsVerifyArgs),
    /// Extract an archive and verify the extracted tree against its manifest.
    Extract(ArtifactsExtractArgs),
}

/// Arguments accepted by `clean artifacts list`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ArtifactsListArgs {
    /// GitHub repository (owner/name) to query.
    #[arg(long, default_value = DEFAULT_CLEAN_RELEASE_REPO)]
    pub repo: String,
    /// Maximum number of releases to list.
    #[arg(long, value_name = "N", default_value_t = 30)]
    pub limit: usize,
    /// Show the assets of this single release tag instead of the release index.
    #[arg(long, value_name = "TAG")]
    pub tag: Option<String>,
    /// Emit JSON instead of the human-readable table.
    #[arg(long)]
    pub json: bool,
}

/// Arguments accepted by `clean artifacts get`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ArtifactsGetArgs {
    /// Release tag to download from (e.g. `mathverse-v1.2.0`).
    pub tag: String,
    /// GitHub repository (owner/name) to download from.
    #[arg(long, default_value = DEFAULT_CLEAN_RELEASE_REPO)]
    pub repo: String,
    /// Glob restricting which assets to download (e.g. `*.tar.zst`).
    /// A `*manifest.json` asset is always fetched in addition when present.
    #[arg(long, value_name = "GLOB")]
    pub pattern: Option<String>,
    /// Directory the verified assets are published into.
    #[arg(long, value_name = "DIR", default_value = ".")]
    pub out: PathBuf,
    /// Proceed when downloaded files are not covered by a manifest
    /// (loud warning; positive checksum mismatches still always fail).
    #[arg(long)]
    pub allow_unverified: bool,
    /// Emit a JSON report instead of human-readable output.
    #[arg(long)]
    pub json: bool,
    /// Rejected: `clean artifacts` never skips verification (fail-closed).
    #[arg(long, hide = true)]
    pub skip_verify: bool,
}

/// Arguments accepted by `clean artifacts verify`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ArtifactsVerifyArgs {
    /// Directory containing the artifacts to verify.
    pub dir: PathBuf,
    /// Manifest file to verify against (default: the first `*manifest.json`
    /// found directly inside DIR).
    #[arg(long, value_name = "FILE")]
    pub manifest: Option<PathBuf>,
    /// Emit a JSON report instead of human-readable rows.
    #[arg(long)]
    pub json: bool,
}

/// Arguments accepted by `clean artifacts extract`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ArtifactsExtractArgs {
    /// Archive to extract (`.tar.zst`, `.tar.gz`, or `.tgz`).
    pub archive: PathBuf,
    /// Directory the verified extracted tree is published into.
    #[arg(long, value_name = "DIR")]
    pub out: PathBuf,
    /// Number of leading path components to strip during extraction.
    #[arg(long, value_name = "N", default_value_t = 1)]
    pub strip_components: u32,
    /// Proceed when the extracted tree carries no `*manifest.json`
    /// (loud warning; manifest mismatches still always fail).
    #[arg(long)]
    pub allow_unverified: bool,
    /// Emit a JSON report instead of human-readable output.
    #[arg(long)]
    pub json: bool,
    /// Rejected: `clean artifacts` never skips verification (fail-closed).
    #[arg(long, hide = true)]
    pub skip_verify: bool,
}
