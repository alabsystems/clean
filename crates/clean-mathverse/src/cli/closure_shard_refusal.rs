// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Why the load-time content binding left a fail-closed v3 closure shard
//! UNVERIFIED: one variant per gate of
//! [`super::closure_shard_binding`], in the order the gates run. The loader
//! prints `kv lazy-closure: <Display>` and serves nothing from the shard (each
//! of its names falls back to eager); the tests match the variant, so a test
//! can say WHICH gate refused a tamper instead of only that something did.
//!
//! This is a `#[path]`-included submodule of `closure_load`.

use std::path::PathBuf;

/// The first load-time gate that refused a fail-closed v3 closure shard.
#[derive(Debug, thiserror::Error)]
pub(crate) enum ClosureShardRefusal {
    /// The shard carries the fail-closed marker but records no declaring
    /// module, so there is no `.olean` to bind it to.
    #[error(
        "a fail-closed v3 shard records no declaring module name — it can never bind; \
         UNVERIFIED (=> eager)."
    )]
    NoModuleName,
    /// No `.olean` for the shard's declaring module on the closure search paths.
    #[error(
        "shard for `{module}` has no resolvable .olean on the closure search paths — left \
         UNVERIFIED (=> eager for its names)."
    )]
    OleanUnresolved { module: String },
    /// The source `.olean` (or a companion) could not be read for hashing.
    #[error("hashing `{}` failed: {error} — UNVERIFIED.", .path.display())]
    OleanUnreadable {
        path: PathBuf,
        #[source]
        error: std::io::Error,
    },
    /// THE SOURCE-OLEAN BINDING: the blake3 or length recomputed from the
    /// on-disk `.olean` and its companions differs from the one the shard
    /// header records, so the shard is stale or swapped relative to the bytes
    /// eager would import.
    #[error(
        "source-olean MISMATCH for module `{module}` (shard is stale/swapped vs on-disk \
         .olean) — UNVERIFIED (=> eager)."
    )]
    SourceOleanMismatch { module: String },
    /// The subset check could not parse the source `.olean` to list the names
    /// it declares.
    #[error("parsing `{}` for the subset check failed: {error} — UNVERIFIED.", .path.display())]
    OleanUnparseable {
        path: PathBuf,
        #[source]
        error: crate::error::MathverseError,
    },
    /// The subset check: the shard serves a name its `.olean` does not declare
    /// (foreign-constant laundering).
    #[error(
        "shard `{module}` serves name `{name}` NOT declared by its olean — UNVERIFIED \
         (foreign-constant laundering refused)."
    )]
    ForeignName { module: String, name: String },
    /// The arena binding: a served constant has no stamped recon digest.
    #[error(
        "shard `{module}` served constant #{index} has NO recon_digest — UNVERIFIED (=> eager)."
    )]
    MissingReconDigest { module: String, index: usize },
    /// The arena binding: a served constant reconstructs to a recon digest
    /// other than the stamped one.
    #[error(
        "shard `{module}` constant #{index} arena reconstructs to a recon_digest != the stamped \
         one (corrupted/stale/swapped arena) — UNVERIFIED (=> eager)."
    )]
    ArenaMismatch { module: String, index: usize },
    /// The arena binding: a served constant failed to materialize.
    #[error(
        "shard `{module}` constant #{index} failed to materialize at load time — UNVERIFIED \
         (=> eager)."
    )]
    ArenaUnmaterializable { module: String, index: usize },
    /// The Lean-world gate (docs/DECISIONS.md R81): the source `.olean` is not
    /// of the world the caller reads.
    #[error("shard for `{module}`: {error} — UNVERIFIED (=> eager).")]
    LeanWorld {
        module: String,
        #[source]
        error: clean_olean::ImportError,
    },
}
