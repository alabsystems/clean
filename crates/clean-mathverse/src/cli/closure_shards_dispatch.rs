// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean mathverse build-closure-shards` — first-class builder for the v3
//! fail-closed closure shard cache, plus the auto-discovery resolver that lets
//! `stamp-verified --closure-root` serve those shards lazily with NO env vars.
//!
//! The shard BUILDER itself ([`crate::cli::closure_load::build_closure_shards_for_target`])
//! already writes v3 fail-closed shards (source-olean digest + per-constant
//! recon_digest, validated at load time). Before this module it was reachable
//! ONLY through a gated test. This file exposes it as a clap subcommand and adds
//! the co-located cache discovery used by the lazy serving path.
//!
//! SOUNDNESS: this is pure ergonomics. The shard builder, the v3 load-time
//! binding, and the eager hard-fallback are unchanged. Auto-discovery only
//! decides WHICH directory the lazy loader is pointed at; a missing, empty,
//! foreign, stale, or corrupt cache always degrades to the trusted eager
//! `.olean` closure (the load-time digest/arena gate + coverage gate are the
//! backstop — see [`crate::cli::closure_load`] and
//! [`crate::cli::stamp_verified_dispatch`]).

use std::io::Write;
use std::path::{Path, PathBuf};

use crate::cli::closure_load::build_closure_shards_for_target;
use crate::cli::{BuildClosureShardsArgs, MathverseCliError};

/// The co-located default closure-shard cache directory name.
///
/// Auto-discovery looks for (and `--build-closure-cache` writes into) a
/// `.clean-closure-shards/` directory SIBLING to the `stamp-verified --out-dir`
/// (i.e. `<out_dir>/../.clean-closure-shards`). Co-locating the cache with the
/// run's output keeps it discoverable and self-documenting, and lets a repeated
/// re-import against the same out-dir reuse it with no flags.
pub(crate) const CLOSURE_CACHE_DIRNAME: &str = ".clean-closure-shards";

/// Derive the default co-located closure-shard cache directory for an
/// `--out-dir`. Chosen as a sibling of `out_dir` so it is not nested inside the
/// stamped-shard output (which gets scanned for `*.mathverse`) yet stays
/// physically adjacent to the run that produced it.
///
/// Falls back to placing the cache INSIDE `out_dir` only when `out_dir` has no
/// parent (e.g. a bare relative name with no directory component) — the closure
/// cache uses a distinct extension-free dir name so it is never mistaken for a
/// stamped shard.
#[must_use]
pub(crate) fn default_closure_cache_dir(out_dir: &Path) -> PathBuf {
    match out_dir.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent.join(CLOSURE_CACHE_DIRNAME),
        _ => out_dir.join(CLOSURE_CACHE_DIRNAME),
    }
}

/// True iff `dir` exists, is a directory, and contains at least one
/// `*.mathverse` shard. An empty or non-existent dir is NOT a usable cache —
/// the caller must then fall back to eager (the hard invariant).
#[must_use]
pub(crate) fn cache_dir_is_populated(dir: &Path) -> bool {
    let Ok(read) = std::fs::read_dir(dir) else {
        return false;
    };
    read.filter_map(Result::ok)
        .any(|e| e.path().extension().is_some_and(|ext| ext == "mathverse"))
}

/// `clean mathverse build-closure-shards` entry point.
///
/// Thin wrapper over [`build_closure_shards_for_target`]: builds the v3
/// fail-closed `.mathverse` closure shards for `target`'s transitive import
/// closure (the target itself excluded) into `--out`. `--closure-elide` is
/// accepted for parity with `stamp-verified` and recorded in the human-readable
/// summary, but the BUILT shards are policy-independent: elision is a LOAD-TIME
/// memory cap applied when the lazy loader installs the closure, not a property
/// of the on-disk bytes (which are always kernel-faithful full-value shards).
pub(crate) fn cmd_build_closure_shards(
    args: BuildClosureShardsArgs,
) -> Result<(), MathverseCliError> {
    let (converted, skipped) =
        build_closure_shards_for_target(&args.target, &args.closure_root, &args.out)?;

    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    writeln!(
        out,
        "build-closure-shards: target=`{}` root=`{}` -> {} ({} converted, {} skipped, elide={:?})",
        args.target.display(),
        args.closure_root.display(),
        args.out.display(),
        converted,
        skipped,
        args.closure_elide,
    )?;
    if converted == 0 {
        // Best-effort builder: zero shards usually means a wrong target/root
        // (no resolvable imports). Surface a hint but do NOT fail — an empty
        // cache simply forces the trusted eager fallback when later served.
        writeln!(
            out,
            "build-closure-shards: WARNING — 0 modules converted; check that \
             --target imports modules resolvable under --closure-root \
             (an empty cache will fall back to the eager .olean closure)"
        )?;
    }
    Ok(())
}

#[cfg(test)]
#[path = "closure_shards_dispatch_tests.rs"]
mod tests;
