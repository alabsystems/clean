// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generic GitHub-Release artifact operations (list / download / extract /
//! verify) shared by `clean artifacts ...` and the Mathverse release pipeline.
//!
//! This module generalizes the machinery in [`crate::release`] (which is
//! specific to `mathverse-library-v*.tar.zst` corpus archives) to *any*
//! release tag and asset set of a repository:
//!
//! - [`list_releases`] / [`list_release_assets`] — release-index discovery.
//! - [`download_assets`] — single shared `gh release download` shell-out
//!   (replaces the private per-caller copies that used to live in
//!   `release.rs` and `clean-cli/src/cmd_mathverse.rs`).
//! - [`extract_archive`] — suffix-dispatched `.tar.zst` / `.tar.gz` / `.tgz`
//!   extraction.
//! - [`verify_entries`] — blake3 manifest verification with a built-in path
//!   traversal guard, the single implementation behind
//!   [`crate::release::verify_against_manifest`].
//!
//! The download mechanism is a `gh` CLI shell-out, the same mechanism
//! `release.rs` has always used: auth and private-repo access are `gh`'s
//! problem, not ours. See `designs/2026-06-09-master-design-v2.md` §5.6 for
//! the artifact-system context; the v1 backend is GitHub Releases.

use std::collections::BTreeSet;
use std::ffi::OsString;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::Command;

use serde::{Deserialize, Serialize};

use crate::error::MathverseResult;
use crate::release::{io_err, ReleaseShardEntry, VerifyFailure, VerifyResult};

/// Filename suffix that marks a release asset (or extracted file) as an
/// artifact manifest. Covers the Mathverse `mathverse-manifest.json`
/// convention as well as generic `*manifest.json` names.
pub const MANIFEST_SUFFIX: &str = "manifest.json";

// ---------------------------------------------------------------------------
// Release discovery
// ---------------------------------------------------------------------------

/// One release in a repository's release index.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ReleaseInfo {
    /// Release tag (e.g. `"mathverse-v1.2.0"`).
    #[serde(rename = "tagName")]
    pub tag: String,
    /// ISO-8601 publication timestamp as reported by GitHub.
    #[serde(rename = "publishedAt", default)]
    pub published_at: String,
    /// Whether GitHub marks this release as the latest.
    #[serde(rename = "isLatest", default)]
    pub is_latest: bool,
}

/// One downloadable asset attached to a release.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AssetInfo {
    /// Asset filename (e.g. `"mathverse-library-v1.2.0.tar.zst"`).
    pub name: String,
    /// Asset size in bytes.
    #[serde(default)]
    pub size: u64,
}

#[derive(Deserialize)]
struct GhReleaseView {
    #[serde(default)]
    assets: Vec<AssetInfo>,
}

/// List the most recent releases of `repo` via `gh release list`.
pub fn list_releases(repo: &str, limit: usize) -> MathverseResult<Vec<ReleaseInfo>> {
    let output = Command::new("gh")
        .args([
            "release",
            "list",
            "--repo",
            repo,
            "--limit",
            &limit.to_string(),
            "--json",
            "tagName,publishedAt,isLatest",
        ])
        .output()?;
    if !output.status.success() {
        return Err(io_err(
            std::io::ErrorKind::Other,
            format!(
                "gh release list failed for {repo}: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        ));
    }
    let releases: Vec<ReleaseInfo> = serde_json::from_slice(&output.stdout)?;
    Ok(releases)
}

/// List the assets attached to release `tag` of `repo` via `gh release view`.
pub fn list_release_assets(repo: &str, tag: &str) -> MathverseResult<Vec<AssetInfo>> {
    let output = Command::new("gh")
        .args(["release", "view", tag, "--repo", repo, "--json", "assets"])
        .output()?;
    if !output.status.success() {
        return Err(io_err(
            std::io::ErrorKind::Other,
            format!(
                "gh release view failed for {repo} tag {tag}: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        ));
    }
    let view: GhReleaseView = serde_json::from_slice(&output.stdout)?;
    Ok(view.assets)
}

// ---------------------------------------------------------------------------
// Download
// ---------------------------------------------------------------------------

/// Download release assets from `repo`/`tag` into `dest_dir` via
/// `gh release download`, optionally restricted to a `--pattern` glob.
///
/// Returns the paths of the files the download added to `dest_dir`
/// (pre-existing files are excluded), sorted by filename.
pub fn download_assets(
    repo: &str,
    tag: &str,
    pattern: Option<&str>,
    dest_dir: &Path,
) -> MathverseResult<Vec<PathBuf>> {
    fs::create_dir_all(dest_dir)?;
    let before = dir_file_names(dest_dir)?;

    let mut cmd = Command::new("gh");
    cmd.args(["release", "download", tag, "--repo", repo]);
    if let Some(glob) = pattern {
        cmd.args(["--pattern", glob]);
    }
    cmd.arg("--dir").arg(dest_dir);
    let status = cmd.status()?;
    if !status.success() {
        let scope = pattern.map_or(String::new(), |glob| format!(" (pattern {glob})"));
        return Err(io_err(
            std::io::ErrorKind::Other,
            format!("gh release download failed for {repo} tag {tag}{scope}"),
        ));
    }

    let mut downloaded: Vec<PathBuf> = dir_file_names(dest_dir)?
        .into_iter()
        .filter(|name| !before.contains(name))
        .map(|name| dest_dir.join(name))
        .collect();
    downloaded.sort();
    Ok(downloaded)
}

/// Names of the regular files directly inside `dir` (non-recursive).
fn dir_file_names(dir: &Path) -> MathverseResult<BTreeSet<OsString>> {
    let mut names = BTreeSet::new();
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        if entry.file_type()?.is_file() {
            names.insert(entry.file_name());
        }
    }
    Ok(names)
}

// ---------------------------------------------------------------------------
// Extraction
// ---------------------------------------------------------------------------

/// Extract `archive` into `dest_dir`, dispatching on the filename suffix.
///
/// Supported formats: `.tar.zst` (tar + zstd), `.tar.gz` / `.tgz` (tar +
/// gzip). Anything else is a typed error — extraction never guesses.
pub fn extract_archive(
    archive: &Path,
    dest_dir: &Path,
    strip_components: u32,
) -> MathverseResult<()> {
    let name = archive
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or_default();
    if name.ends_with(".tar.zst") {
        crate::release::extract_tar_zst(archive, dest_dir, strip_components)
    } else if name.ends_with(".tar.gz") || name.ends_with(".tgz") {
        extract_tar_gz(archive, dest_dir, strip_components)
    } else {
        Err(io_err(
            std::io::ErrorKind::InvalidInput,
            format!(
                "unsupported archive format `{}`: expected .tar.zst, .tar.gz, or .tgz",
                archive.display()
            ),
        ))
    }
}

/// Extract a tar.gz archive into `dest_dir` (mirrors the tar.zst fallback
/// style in `release.rs`: `tar -xzf` first, `gzip -dc | tar` fallback).
fn extract_tar_gz(archive: &Path, dest_dir: &Path, strip_components: u32) -> MathverseResult<()> {
    fs::create_dir_all(dest_dir)?;
    let strip = format!("--strip-components={strip_components}");

    let status = Command::new("tar")
        .arg("-xzf")
        .arg(archive)
        .arg("-C")
        .arg(dest_dir)
        .arg(&strip)
        .status();
    if matches!(status, Ok(ref s) if s.success()) {
        return Ok(());
    }

    // Fallback: gzip -dc | tar -x
    let gzip = Command::new("gzip")
        .args(["-dc"])
        .arg(archive)
        .stdout(std::process::Stdio::piped())
        .spawn()?;
    let stdout = gzip
        .stdout
        .ok_or_else(|| io_err(std::io::ErrorKind::BrokenPipe, "gzip stdout capture failed"))?;
    let tar = Command::new("tar")
        .args(["-xf", "-", "-C"])
        .arg(dest_dir)
        .arg(&strip)
        .stdin(stdout)
        .status()?;
    if !tar.success() {
        return Err(io_err(
            std::io::ErrorKind::Other,
            "tar.gz extraction failed",
        ));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Manifest discovery and verification
// ---------------------------------------------------------------------------

/// Find an artifact manifest directly inside `dir` (non-recursive): the
/// lexicographically first regular file whose name ends with
/// [`MANIFEST_SUFFIX`] (`mathverse-manifest.json`, `manifest.json`, ...).
#[must_use]
pub fn find_manifest(dir: &Path) -> Option<PathBuf> {
    let names = dir_file_names(dir).ok()?;
    names
        .into_iter()
        .filter_map(|name| name.into_string().ok())
        .find(|name| name.ends_with(MANIFEST_SUFFIX))
        .map(|name| dir.join(name))
}

/// Verify manifest `entries` against files under `base_dir`, checking each
/// entry's blake3 hash.
///
/// Fail-closed guards:
/// - any entry whose `path` is empty, absolute, or contains a non-normal
///   component (`..`, `.`,  prefix, root) is a hard error — a hostile
///   manifest must not be able to direct hashing (or any later copy step)
///   outside `base_dir`;
/// - entries missing on disk are reported in [`VerifyResult::missing`];
/// - hash mismatches are reported in [`VerifyResult::failures`].
pub fn verify_entries(
    entries: &[ReleaseShardEntry],
    base_dir: &Path,
) -> MathverseResult<VerifyResult> {
    let mut result = VerifyResult {
        checked: 0,
        passed: 0,
        failures: Vec::new(),
        missing: Vec::new(),
    };
    for entry in entries {
        ensure_safe_relative_path(&entry.path)?;
        result.checked += 1;
        let abs_path = base_dir.join(&entry.path);
        if !abs_path.exists() {
            result.missing.push(entry.path.clone());
            continue;
        }
        let data = fs::read(&abs_path)?;
        let actual_hash = blake3::hash(&data).to_hex().to_string();
        if actual_hash == entry.blake3 {
            result.passed += 1;
        } else {
            result.failures.push(VerifyFailure {
                path: entry.path.clone(),
                expected: entry.blake3.clone(),
                actual: actual_hash,
            });
        }
    }
    Ok(result)
}

/// Reject manifest entry paths that could escape the verification root.
///
/// Shared with the server-download client ([`crate::corpus_download`]), which
/// must apply the same guard *before* writing a pulled shard to disk so a
/// hostile manifest can never direct the write outside the output directory.
pub(crate) fn ensure_safe_relative_path(path: &str) -> MathverseResult<()> {
    let candidate = Path::new(path);
    if path.is_empty()
        || candidate.is_absolute()
        || candidate
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(io_err(
            std::io::ErrorKind::InvalidInput,
            format!("invalid manifest entry path (absolute or traversal): {path}"),
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(path: &str, blake3: &str) -> ReleaseShardEntry {
        ReleaseShardEntry {
            path: path.to_string(),
            size: 0,
            blake3: blake3.to_string(),
        }
    }

    #[test]
    fn test_extract_archive_unknown_suffix_returns_error() {
        let dir = tempfile::tempdir().expect("tempdir");
        let archive = dir.path().join("bundle.zip");
        fs::write(&archive, b"not a tarball").expect("write");
        let err = extract_archive(&archive, &dir.path().join("out"), 1)
            .expect_err("zip must be rejected");
        assert!(err.to_string().contains("unsupported archive format"));
    }

    #[test]
    fn test_find_manifest_matches_suffix_convention() {
        let dir = tempfile::tempdir().expect("tempdir");
        assert_eq!(find_manifest(dir.path()), None);

        fs::write(dir.path().join("data.tar.zst"), b"x").expect("write");
        assert_eq!(find_manifest(dir.path()), None);

        fs::write(dir.path().join("mathverse-manifest.json"), b"{}").expect("write");
        let found = find_manifest(dir.path()).expect("manifest");
        assert_eq!(
            found.file_name().and_then(|n| n.to_str()),
            Some("mathverse-manifest.json")
        );
    }

    #[test]
    fn test_verify_entries_reports_pass_mismatch_and_missing() {
        let dir = tempfile::tempdir().expect("tempdir");
        fs::write(dir.path().join("good.bin"), b"payload").expect("write");
        fs::write(dir.path().join("bad.bin"), b"tampered").expect("write");
        let good_hash = blake3::hash(b"payload").to_hex().to_string();

        let entries = vec![
            entry("good.bin", &good_hash),
            entry("bad.bin", &"0".repeat(64)),
            entry("absent.bin", &good_hash),
        ];
        let result = verify_entries(&entries, dir.path()).expect("verify");
        assert_eq!(result.checked, 3);
        assert_eq!(result.passed, 1);
        assert_eq!(result.failures.len(), 1);
        assert_eq!(result.failures[0].path, "bad.bin");
        assert_eq!(result.missing, vec!["absent.bin".to_string()]);
        assert!(!result.is_ok());
    }

    #[test]
    fn test_verify_entries_rejects_path_traversal() {
        let dir = tempfile::tempdir().expect("tempdir");
        let entries = vec![entry("../escape.bin", &"0".repeat(64))];
        let err = verify_entries(&entries, dir.path()).expect_err("traversal must fail");
        assert!(err.to_string().contains("invalid manifest entry path"));
        assert!(err.to_string().contains("../escape.bin"));
    }

    #[test]
    fn test_verify_entries_rejects_absolute_and_empty_paths() {
        let dir = tempfile::tempdir().expect("tempdir");
        for bad in ["/etc/passwd", ""] {
            let entries = vec![entry(bad, &"0".repeat(64))];
            let err = verify_entries(&entries, dir.path())
                .expect_err("absolute/empty manifest paths must be rejected");
            assert!(
                err.to_string().contains("invalid manifest entry path"),
                "path `{bad}` produced unexpected error: {err}"
            );
        }
    }

    #[test]
    fn test_verify_entries_empty_manifest_is_vacuously_ok() {
        let dir = tempfile::tempdir().expect("tempdir");
        let result = verify_entries(&[], dir.path()).expect("verify");
        assert_eq!(result.checked, 0);
        assert!(result.is_ok(), "callers enforce non-empty where required");
    }
}
