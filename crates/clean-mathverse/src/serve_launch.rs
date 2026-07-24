// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Turnkey launcher for the Mathverse distribution server
//! (`clean mathverse serve`).
//!
//! The `mathverse_serve` binary is configured entirely by environment
//! variables (`$MATHVERSE_CORE_DIR`, `$PORT`, `$MATHVERSE_DOWNLOAD_BASE`, …) and
//! has no Core discovery, no baseline-index bootstrap, and no human-facing
//! "here is your URL" summary. This module supplies exactly that turnkey layer
//! while REUSING the existing server verbatim: it locates a Core, ensures the
//! `baseline.mvix` novelty index exists (building it from the shards when
//! missing), summarizes the corpus, and builds the `mathverse_serve` invocation
//! (binary path + environment). The command layer
//! ([`crate::mathverse_bin_cmds::commands`]) prints the summary + URL and spawns
//! the resulting [`std::process::Command`].
//!
//! This module is print-free and process-spawn-free so it stays unit-testable;
//! the orchestration policy (what to print, whether a benign baseline-build
//! failure is fatal) lives in the command layer.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::error::{MathverseError, MathverseResult};
use crate::release::BASELINE_INDEX_FILENAME;

/// Environment variable naming an explicit `mathverse_serve` binary path.
pub const SERVE_BIN_ENV: &str = "MATHVERSE_SERVE_BIN";

/// Knobs for the turnkey `serve` launcher: the Core to serve, the bind port,
/// and an optional shard-download redirect base.
#[derive(Clone, Debug)]
pub struct ServeLaunchConfig {
    /// Explicit Core directory (`--core`); `None` triggers discovery.
    pub core: Option<PathBuf>,
    /// TCP port to bind (`--port`).
    pub port: u16,
    /// Optional `$MATHVERSE_DOWNLOAD_BASE` redirect host (`--download-base`).
    pub download_base: Option<String>,
}

impl Default for ServeLaunchConfig {
    fn default() -> Self {
        Self {
            core: None,
            port: 8080,
            download_base: None,
        }
    }
}

/// A cheap corpus summary read from the manifest (no full library load).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreSummary {
    /// Number of shards (base + delta) in the manifest.
    pub shard_count: usize,
    /// Total declaration count across all shards.
    pub total_constants: u64,
}

/// Whether a directory looks like a servable Core (has a manifest the server
/// can load).
#[must_use]
pub fn is_core_dir(dir: &Path) -> bool {
    dir.join("manifest.json").is_file()
        || dir
            .join(crate::manifest::RELEASE_MANIFEST_FILENAME)
            .is_file()
}

/// Resolve the Core directory: explicit `--core`, then `$MATHVERSE_CORE_DIR`,
/// `$MATHVERSE_LIBRARY_PATH`, `./data/mathverse-library`, and
/// `$HOME/.mathverse/library`.
///
/// # Errors
/// Returns a [`MathverseError`] naming every searched location and pointing at
/// `clean mathverse download` when no candidate holds a manifest.
pub fn resolve_core_dir(explicit: Option<&Path>) -> MathverseResult<PathBuf> {
    let mut searched: Vec<String> = Vec::new();
    for candidate in core_candidates(explicit) {
        searched.push(candidate.display().to_string());
        if is_core_dir(&candidate) {
            return Ok(candidate);
        }
    }
    Err(MathverseError::Io(std::io::Error::new(
        std::io::ErrorKind::NotFound,
        format!(
            "no Mathverse Core found. Searched:\n  - {}\nA Core directory must hold a \
             manifest.json or mathverse-manifest.json. Fetch one with \
             `clean mathverse download` (or `clean mathverse download --from <server-url>`), \
             or pass --core <dir>.",
            searched.join("\n  - ")
        ),
    )))
}

/// Ordered Core candidate directories.
fn core_candidates(explicit: Option<&Path>) -> Vec<PathBuf> {
    let mut out = Vec::new();
    if let Some(p) = explicit {
        out.push(p.to_path_buf());
        return out; // explicit is authoritative — do not silently fall through
    }
    if let Some(v) = non_empty_env("MATHVERSE_CORE_DIR") {
        out.push(PathBuf::from(v));
    }
    if let Some(v) = non_empty_env("MATHVERSE_LIBRARY_PATH") {
        out.push(PathBuf::from(v));
    }
    out.push(PathBuf::from("data/mathverse-library"));
    if let Some(home) = non_empty_env("HOME") {
        out.push(PathBuf::from(home).join(".mathverse/library"));
    }
    out
}

fn non_empty_env(key: &str) -> Option<String> {
    std::env::var(key).ok().filter(|s| !s.is_empty())
}

/// Read a cheap corpus summary (shard count + declaration count) from the
/// Core's manifest without loading any shard bodies.
///
/// # Errors
/// Propagates a manifest read/parse failure.
pub fn core_summary(core_dir: &Path) -> MathverseResult<CoreSummary> {
    let manifest = crate::manifest::LibraryLoader::new(core_dir.to_path_buf()).load_manifest()?;
    Ok(CoreSummary {
        shard_count: manifest.all_shards().len(),
        total_constants: manifest.total_constants,
    })
}

/// Ensure `core_dir/baseline.mvix` exists, building it from the shards if
/// missing. Returns `true` when a new index was built, `false` when one was
/// already present or the corpus has no indexable constants.
///
/// # Errors
/// Propagates a baseline-index build failure. The command layer treats this as
/// non-fatal (the server loads and serves fine without the novelty index), so
/// it logs a warning rather than aborting.
pub fn ensure_baseline_index(core_dir: &Path) -> MathverseResult<bool> {
    let index_path = core_dir.join(BASELINE_INDEX_FILENAME);
    if index_path.is_file() {
        return Ok(false);
    }
    let stats = crate::graduate::build_baseline_index(core_dir, &index_path)?;
    if stats.names == 0 {
        // Empty/garbage corpus — drop the empty index so a constant-free Core
        // does not ship a meaningless file.
        let _ = std::fs::remove_file(&index_path);
        return Ok(false);
    }
    Ok(true)
}

/// Locate the `mathverse_serve` binary: `$MATHVERSE_SERVE_BIN`, then a sibling
/// of the current executable (the installed-side-by-side case). Returns `None`
/// when neither resolves so the caller can print a build/install hint.
#[must_use]
pub fn locate_serve_bin() -> Option<PathBuf> {
    if let Some(v) = non_empty_env(SERVE_BIN_ENV) {
        let p = PathBuf::from(v);
        if p.is_file() {
            return Some(p);
        }
    }
    let exe = std::env::current_exe().ok()?;
    let sibling = exe.parent()?.join("mathverse_serve");
    sibling.is_file().then_some(sibling)
}

/// Build the `mathverse_serve` invocation: the binary plus the environment the
/// server reads (`$MATHVERSE_CORE_DIR`, `$PORT`, optional
/// `$MATHVERSE_DOWNLOAD_BASE`). Spawning + waiting is the caller's job.
#[must_use]
pub fn serve_command(
    serve_bin: &Path,
    core_dir: &Path,
    port: u16,
    download_base: Option<&str>,
) -> Command {
    let mut cmd = Command::new(serve_bin);
    cmd.env("MATHVERSE_CORE_DIR", core_dir)
        .env("PORT", port.to_string());
    if let Some(base) = download_base {
        cmd.env("MATHVERSE_DOWNLOAD_BASE", base);
    }
    cmd
}

/// The local URL a freshly-started server is reachable at.
#[must_use]
pub fn local_url(port: u16) -> String {
    format!("http://127.0.0.1:{port}")
}

/// Hint shown when the server binary cannot be located.
#[must_use]
pub fn serve_bin_missing_hint() -> String {
    format!(
        "could not locate the `mathverse_serve` binary. Build it with \
         `cargo build --locked -p clean-mathverse --bin mathverse_serve` and either put it \
         next to the `clean` binary or set ${SERVE_BIN_ENV} to its path."
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_core_dir_detects_both_manifests() {
        let dir = tempfile::tempdir().expect("tempdir");
        assert!(!is_core_dir(dir.path()));
        std::fs::write(dir.path().join("manifest.json"), b"{}").expect("write");
        assert!(is_core_dir(dir.path()));

        let dir2 = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir2.path().join(crate::manifest::RELEASE_MANIFEST_FILENAME),
            b"{}",
        )
        .expect("write");
        assert!(is_core_dir(dir2.path()));
    }

    #[test]
    fn test_resolve_core_dir_explicit_wins() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("manifest.json"), b"{}").expect("write");
        let resolved = resolve_core_dir(Some(dir.path())).expect("explicit core");
        assert_eq!(resolved, dir.path());
    }

    #[test]
    fn test_resolve_core_dir_missing_explicit_errors_with_hint() {
        let dir = tempfile::tempdir().expect("tempdir");
        let empty = dir.path().join("not-a-core");
        let err = resolve_core_dir(Some(&empty)).expect_err("no manifest");
        let msg = err.to_string();
        assert!(
            msg.contains("clean mathverse download"),
            "must hint download: {msg}"
        );
    }

    #[test]
    fn test_serve_command_sets_env() {
        let cmd = serve_command(
            Path::new("/usr/local/bin/mathverse_serve"),
            Path::new("/data/core"),
            9090,
            Some("https://cdn.example/base"),
        );
        let envs: Vec<(String, Option<String>)> = cmd
            .get_envs()
            .map(|(k, v)| {
                (
                    k.to_string_lossy().into_owned(),
                    v.map(|v| v.to_string_lossy().into_owned()),
                )
            })
            .collect();
        let get = |key: &str| {
            envs.iter()
                .find(|(k, _)| k == key)
                .and_then(|(_, v)| v.clone())
        };
        assert_eq!(get("MATHVERSE_CORE_DIR").as_deref(), Some("/data/core"));
        assert_eq!(get("PORT").as_deref(), Some("9090"));
        assert_eq!(
            get("MATHVERSE_DOWNLOAD_BASE").as_deref(),
            Some("https://cdn.example/base")
        );
    }

    #[test]
    fn test_serve_command_omits_download_base_when_none() {
        let cmd = serve_command(
            Path::new("/bin/mathverse_serve"),
            Path::new("/c"),
            8080,
            None,
        );
        let has_base = cmd
            .get_envs()
            .any(|(k, _)| k.to_string_lossy() == "MATHVERSE_DOWNLOAD_BASE");
        assert!(!has_base, "download base must be unset when None");
    }

    #[test]
    fn test_local_url() {
        assert_eq!(local_url(8080), "http://127.0.0.1:8080");
    }
}
