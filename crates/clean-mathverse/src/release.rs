// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Release packaging, download, and verification for Mathverse Library shard archives.
//!
//! Provides programmatic equivalents of the shell scripts:
//! - `scripts/package_mathverse_release.sh` -> [`package_release`]
//! - `scripts/download_mathverse_library.sh` -> [`download_release`]
//!
//! The release manifest (`mathverse-manifest.json`) lists every `.mathverse` shard
//! with its size and blake3 checksum for integrity verification.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde::{Deserialize, Serialize};

use crate::error::{MathverseError, MathverseResult};

/// RAII guard that removes a temporary directory on drop.
struct TempDirGuard(PathBuf);

impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Shorthand for creating an `MathverseError::Io` with a message.
pub(crate) fn io_err(kind: std::io::ErrorKind, msg: impl Into<String>) -> MathverseError {
    MathverseError::Io(std::io::Error::new(kind, msg.into()))
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for downloading a release from GitHub.
#[derive(Clone, Debug)]
pub struct ReleaseConfig {
    /// GitHub repository (e.g. `"alabsystems/clean"`).
    pub repo: String,
    /// Release version (e.g. `"0.9.0"`). `None` means "latest".
    pub version: Option<String>,
    /// Destination directory for extracted shards.
    pub output_dir: PathBuf,
}

/// Public GitHub repository used by default download commands.
pub const DEFAULT_CLEAN_RELEASE_REPO: &str = "alabsystems/clean";

const MATHVERSE_LIBRARY_ARCHIVE_GLOB: &str = "mathverse-library-v*.tar.zst";

/// Filename of the shipped `MVBIDX01` baseline novelty index, relative to the
/// shard directory / archive root.
pub const BASELINE_INDEX_FILENAME: &str = "baseline.mvix";

impl ReleaseConfig {
    /// Create a config for the default clean repository.
    #[must_use]
    pub fn default_for_clean(output_dir: impl Into<PathBuf>) -> Self {
        Self {
            repo: DEFAULT_CLEAN_RELEASE_REPO.to_string(),
            version: None,
            output_dir: output_dir.into(),
        }
    }
}

// ---------------------------------------------------------------------------
// Manifest
// ---------------------------------------------------------------------------

/// Release manifest listing all shards with checksums.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ReleaseManifest {
    pub manifest_version: u32,
    pub release_version: String,
    pub created_at: String,
    /// Manifest entries. Serialized as `shards` for the Mathverse corpus
    /// convention; generic artifact manifests may use the `files` key
    /// (accepted via serde alias) — see `crate::artifacts`.
    #[serde(alias = "files")]
    pub shards: Vec<ReleaseShardEntry>,
    pub total_bytes: u64,
    pub total_shards: usize,
    /// Relative path (within the archive) of the shipped `MVBIDX01` baseline
    /// novelty index, e.g. `"baseline.mvix"`. `None` for releases packaged
    /// before the index was wired in, or for corpora with no indexable
    /// constants. Backward-compatible: defaults to `None` when the field is
    /// absent from older manifests.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub baseline_index: Option<String>,
}

/// A single shard entry in the release manifest.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ReleaseShardEntry {
    /// Relative path within the archive (e.g. `"base/Init.mathverse"`).
    pub path: String,
    /// File size in bytes.
    pub size: u64,
    /// Blake3 hex digest of the file contents.
    pub blake3: String,
}

impl ReleaseManifest {
    /// Build a manifest by scanning all `.mathverse` files under `shard_dir`.
    pub fn from_directory(shard_dir: &Path, version: &str) -> MathverseResult<Self> {
        let mut shards = Vec::new();
        let mut total_bytes: u64 = 0;
        collect_mathverse_files(shard_dir, shard_dir, &mut shards, &mut total_bytes)?;
        shards.sort_by(|a, b| a.path.cmp(&b.path));
        let total_shards = shards.len();
        Ok(Self {
            manifest_version: 1,
            release_version: version.to_string(),
            created_at: now_iso8601(),
            shards,
            total_bytes,
            total_shards,
            baseline_index: None,
        })
    }

    /// Serialize to pretty-printed JSON.
    pub fn to_json(&self) -> MathverseResult<String> {
        serde_json::to_string_pretty(self).map_err(MathverseError::from)
    }

    /// Deserialize from a JSON string.
    pub fn from_json(json: &str) -> MathverseResult<Self> {
        serde_json::from_str(json).map_err(MathverseError::from)
    }

    /// Read manifest from a file on disk.
    ///
    /// Failures name the manifest path and how to obtain one: the manifest is
    /// written by [`package_release`] and shipped inside every
    /// `mathverse-library-v*.tar.zst` release archive.
    pub fn from_file(path: &Path) -> MathverseResult<Self> {
        let json = fs::read_to_string(path).map_err(|e| {
            io_err(
                e.kind(),
                format!(
                    "cannot read release manifest `{}`: {e}; the manifest is written by \
                     `package_release` and shipped inside mathverse-library-v*.tar.zst \
                     archives — fetch a complete release with `clean mathverse download` \
                     (or `clean artifacts get`), or point at the directory that contains \
                     the *manifest.json",
                    path.display()
                ),
            )
        })?;
        Self::from_json(&json)
            .map_err(|e| e.with_context(&format!("parsing release manifest `{}`", path.display())))
    }

    /// Write manifest to a file on disk.
    pub fn write_to_file(&self, path: &Path) -> MathverseResult<()> {
        fs::write(path, self.to_json()?)?;
        Ok(())
    }
}

/// Recursively collect `.mathverse` files and compute their blake3 hashes.
fn collect_mathverse_files(
    base_dir: &Path,
    current_dir: &Path,
    out: &mut Vec<ReleaseShardEntry>,
    total_bytes: &mut u64,
) -> MathverseResult<()> {
    for entry in fs::read_dir(current_dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_mathverse_files(base_dir, &path, out, total_bytes)?;
        } else if path.extension().and_then(|e| e.to_str()) == Some("mathverse") {
            let data = fs::read(&path)?;
            let size = data.len() as u64;
            let blake3 = blake3::hash(&data).to_hex().to_string();
            let rel_path = path
                .strip_prefix(base_dir)
                .map_err(|e| io_err(std::io::ErrorKind::Other, e.to_string()))?
                .to_string_lossy()
                .to_string();
            *total_bytes += size;
            out.push(ReleaseShardEntry {
                path: rel_path,
                size,
                blake3,
            });
        }
    }
    Ok(())
}

/// Generate a basic ISO-8601 timestamp string (UTC).
pub(crate) fn now_iso8601() -> String {
    Command::new("date")
        .args(["-u", "+%Y-%m-%dT%H:%M:%SZ"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

// ---------------------------------------------------------------------------
// Package
// ---------------------------------------------------------------------------

/// Create a tar.zst archive from a directory of `.mathverse` shards.
///
/// Writes `mathverse-manifest.json` into `shard_dir`, then creates
/// `mathverse-library-v{version}.tar.zst` in `output_dir`.
pub fn package_release(
    shard_dir: &Path,
    version: &str,
    output_dir: &Path,
) -> MathverseResult<PathBuf> {
    package_release_with_stamp(shard_dir, version, output_dir, None)
}

/// Package a release, optionally stamping `KernelVerified` into the shard bytes
/// first (WS5).
///
/// When `kernel_verified_manifest` names a `kernel-verified.json`
/// ([`crate::verify::kernel_verified_manifest::KernelVerifiedManifest`]), the
/// shards under `shard_dir` are **destructively rewritten** so that every
/// kernel-re-verified constant carries [`crate::types::ImportConfidence::KernelVerified`]
/// in its persisted header byte
/// ([`crate::library::stamp_shard_dir_kernel_verified`]). This happens *before*
/// the release manifest is built, so the recorded blake3 digests cover the
/// stamped bytes — a downstream `verify` over those digests therefore proves
/// the stamp persisted. The function then asserts that the stored
/// `KernelVerified` count equals the manifest's verified-name length, failing
/// with [`MathverseError::KernelVerifiedStampMismatch`] if the stamp did not
/// take across the shards present on disk.
///
/// With `kernel_verified_manifest == None` this is exactly the legacy
/// [`package_release`] behavior: shards are packaged as-is.
///
/// SOUNDNESS: the manifest is the kernel's own verdict set
/// (`verify_corpus_incremental`); no heuristic confidence is ever promoted here.
///
/// # Errors
/// Returns an error if the shard directory is missing, a shard cannot be
/// stamped, the stored count does not match the manifest, or archiving fails.
pub fn package_release_with_stamp(
    shard_dir: &Path,
    version: &str,
    output_dir: &Path,
    kernel_verified_manifest: Option<&Path>,
) -> MathverseResult<PathBuf> {
    if !shard_dir.is_dir() {
        return Err(io_err(
            std::io::ErrorKind::NotFound,
            format!("shard directory not found: {}", shard_dir.display()),
        ));
    }

    // WS5: persist the kernel-verified stamp into the shard bytes *before*
    // hashing, so the release manifest's blake3 digests cover the stamped bytes.
    if let Some(manifest_path) = kernel_verified_manifest {
        let manifest = crate::verify::kernel_verified_manifest::KernelVerifiedManifest::from_file(
            manifest_path,
        )?;
        crate::library::stamp_shard_dir_kernel_verified(shard_dir, &manifest)?;
        // A green release must *prove* the stamp persisted: the count of headers
        // carrying KernelVerified in the bytes on disk must equal the number of
        // manifest names that are actually present in the shards on disk. (The
        // manifest may be a global corpus verdict spanning more shards than this
        // directory holds, so we intersect with the names present here.)
        let expected =
            crate::library::count_present_names(shard_dir, &manifest.kernel_verified_names)?;
        let (stored, _) = crate::library::count_stored_kernel_verified(shard_dir)?;
        if stored != expected {
            return Err(MathverseError::KernelVerifiedStampMismatch {
                shard_dir: shard_dir.display().to_string(),
                manifest: expected,
                stored,
            });
        }
    }

    // Build + include the `MVBIDX01` baseline novelty index alongside the
    // shards so a downloaded corpus is queryable without rescanning all of it.
    // The index lands in `shard_dir` (not a `.mathverse` file, so it is excluded
    // from the manifest's shard list) and is swept into the tar automatically.
    // An empty corpus (no indexable constants) is skipped gracefully.
    let baseline_index_rel = build_and_include_baseline_index(shard_dir)?;

    let mut manifest = ReleaseManifest::from_directory(shard_dir, version)?;
    manifest.baseline_index = baseline_index_rel;
    manifest.write_to_file(&shard_dir.join("mathverse-manifest.json"))?;
    fs::create_dir_all(output_dir)?;

    let archive_name = format!("mathverse-library-v{version}.tar.zst");
    let archive_path = output_dir.join(&archive_name);
    let parent = shard_dir
        .parent()
        .ok_or_else(|| io_err(std::io::ErrorKind::InvalidInput, "shard dir has no parent"))?;
    let name = shard_dir
        .file_name()
        .ok_or_else(|| io_err(std::io::ErrorKind::InvalidInput, "shard dir has no name"))?;

    // Try tar --zstd first, then tar | zstd fallback
    let status = Command::new("tar")
        .args(["--zstd", "-cf"])
        .arg(&archive_path)
        .arg("-C")
        .arg(parent)
        .arg(name)
        .status();

    if !matches!(status, Ok(ref s) if s.success()) {
        let tar = Command::new("tar")
            .args(["-cf", "-", "-C"])
            .arg(parent)
            .arg(name)
            .stdout(std::process::Stdio::piped())
            .spawn()?;
        let stdout = tar
            .stdout
            .ok_or_else(|| io_err(std::io::ErrorKind::BrokenPipe, "tar stdout capture failed"))?;
        let zstd = Command::new("zstd")
            .arg("-o")
            .arg(&archive_path)
            .stdin(stdout)
            .status()?;
        if !zstd.success() {
            return Err(io_err(std::io::ErrorKind::Other, "zstd compression failed"));
        }
    }

    if !archive_path.exists() {
        return Err(io_err(
            std::io::ErrorKind::NotFound,
            format!("archive not created: {}", archive_path.display()),
        ));
    }
    Ok(archive_path)
}

/// Build the `MVBIDX01` baseline novelty index over the shards in `shard_dir`
/// and write it as [`BASELINE_INDEX_FILENAME`] inside `shard_dir`, so it is
/// swept into the release tar automatically.
///
/// Returns the relative path to record in the manifest's `baseline_index`
/// field, or `None` when the corpus has no indexable constants (an empty
/// corpus yields an empty but valid index; we skip recording it so a
/// constant-free release stays lean and the manifest field stays meaningful —
/// "the queryable baseline is here"). A benign build failure is logged and
/// downgraded to `None` rather than aborting the release: the index is an
/// accelerator, not a correctness gate.
fn build_and_include_baseline_index(shard_dir: &Path) -> MathverseResult<Option<String>> {
    let index_path = shard_dir.join(BASELINE_INDEX_FILENAME);
    match crate::graduate::build_baseline_index(shard_dir, &index_path) {
        Ok(stats) if stats.names == 0 => {
            // No indexable constants — drop the empty index file and skip the
            // manifest reference so an empty corpus does not error.
            let _ = fs::remove_file(&index_path);
            eprintln!(
                "  Baseline index: 0 indexable constants across {} shard(s) — skipping",
                stats.shards
            );
            Ok(None)
        }
        Ok(stats) => {
            eprintln!(
                "  Baseline index: {} ({} names, {} statement hashes, {} semantic) from {} shard(s)",
                BASELINE_INDEX_FILENAME,
                stats.names,
                stats.hashes,
                stats.semantic_hashes,
                stats.shards
            );
            Ok(Some(BASELINE_INDEX_FILENAME.to_string()))
        }
        Err(e) => {
            // Benign: leave no partial file, record no reference, keep packaging.
            let _ = fs::remove_file(&index_path);
            eprintln!("  Baseline index: build skipped ({e})");
            Ok(None)
        }
    }
}

// ---------------------------------------------------------------------------
// Download
// ---------------------------------------------------------------------------

/// Download and extract an mathverse library release from GitHub.
///
/// Uses `gh release download` for the archive, extracts to `config.output_dir`.
pub fn download_release(config: &ReleaseConfig) -> MathverseResult<PathBuf> {
    let tag = resolve_release_tag(config)?;
    let tmp = std::env::temp_dir().join(format!("mathverse-download-{}", std::process::id()));
    fs::create_dir_all(&tmp)?;
    let _cleanup = TempDirGuard(tmp.clone());

    crate::artifacts::download_assets(
        &config.repo,
        &tag,
        Some(MATHVERSE_LIBRARY_ARCHIVE_GLOB),
        &tmp,
    )?;
    let archive = find_tar_zst(&tmp)?;
    let extract_dir = tmp.join("extract");
    extract_tar_zst(&archive, &extract_dir, 1)?;
    let shard_count = count_mathverse_shards(&extract_dir)?;
    if shard_count == 0 {
        return Err(io_err(
            std::io::ErrorKind::InvalidData,
            format!(
                "extracted archive {} contains no .mathverse shard files",
                archive.display()
            ),
        ));
    }

    fs::create_dir_all(&config.output_dir)?;
    copy_dir_contents(&extract_dir, &config.output_dir)?;
    Ok(config.output_dir.clone())
}

fn resolve_release_tag(config: &ReleaseConfig) -> MathverseResult<String> {
    if let Some(version) = &config.version {
        return Ok(format!("mathverse-v{version}"));
    }
    let output = Command::new("gh")
        .args([
            "release",
            "list",
            "--repo",
            &config.repo,
            "--limit",
            "20",
            "--json",
            "tagName",
            "--jq",
            "[.[] | select(.tagName | startswith(\"mathverse-v\"))][0].tagName // empty",
        ])
        .output()?;
    if !output.status.success() {
        return Err(io_err(
            std::io::ErrorKind::Other,
            format!(
                "gh release list failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ),
        ));
    }
    let tag = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if tag.is_empty() {
        return Err(io_err(
            std::io::ErrorKind::NotFound,
            format!(
                "no mathverse-v* release tag found in the 20 most recent releases of \
                 `{}` — the repo has releases but none tagged `mathverse-v*`; list them \
                 with `gh release list --repo {}` or pass an explicit version \
                 (ReleaseConfig.version / --version)",
                config.repo, config.repo
            ),
        ));
    }
    Ok(tag)
}

fn find_tar_zst(dir: &Path) -> MathverseResult<PathBuf> {
    for entry in fs::read_dir(dir)? {
        let path = entry?.path();
        if path
            .file_name()
            .and_then(|n| n.to_str())
            .is_some_and(is_mathverse_library_archive)
        {
            return Ok(path);
        }
    }
    Err(io_err(
        std::io::ErrorKind::NotFound,
        format!(
            "no {MATHVERSE_LIBRARY_ARCHIVE_GLOB} file found in {}",
            dir.display()
        ),
    ))
}

fn is_mathverse_library_archive(name: &str) -> bool {
    name.starts_with("mathverse-library-v") && name.ends_with(".tar.zst")
}

fn count_mathverse_shards(dir: &Path) -> MathverseResult<usize> {
    let mut count = 0;
    count_mathverse_shards_inner(dir, &mut count)?;
    Ok(count)
}

fn count_mathverse_shards_inner(dir: &Path, count: &mut usize) -> MathverseResult<()> {
    for entry in fs::read_dir(dir)? {
        let path = entry?.path();
        if path.is_dir() {
            count_mathverse_shards_inner(&path, count)?;
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("mathverse") {
            *count += 1;
        }
    }
    Ok(())
}

fn copy_dir_contents(src: &Path, dest: &Path) -> MathverseResult<()> {
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let src_path = entry.path();
        let dest_path = dest.join(entry.file_name());
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            fs::create_dir_all(&dest_path)?;
            copy_dir_contents(&src_path, &dest_path)?;
        } else if file_type.is_file() {
            fs::copy(&src_path, &dest_path)?;
        }
    }
    Ok(())
}

/// Extract a tar.zst archive into `dest_dir`, stripping `strip_components`
/// leading path components (the corpus release pipeline uses `1` because
/// archives wrap their contents in a single top-level directory).
pub(crate) fn extract_tar_zst(
    archive: &Path,
    dest_dir: &Path,
    strip_components: u32,
) -> MathverseResult<()> {
    fs::create_dir_all(dest_dir)?;
    let strip = format!("--strip-components={strip_components}");

    let status = Command::new("tar")
        .args(["--zstd", "-xf"])
        .arg(archive)
        .arg("-C")
        .arg(dest_dir)
        .arg(&strip)
        .status();
    if matches!(status, Ok(ref s) if s.success()) {
        return Ok(());
    }

    // Fallback: zstd -d | tar -x
    let zstd = Command::new("zstd")
        .args(["-d", "--stdout"])
        .arg(archive)
        .stdout(std::process::Stdio::piped())
        .spawn()?;
    let stdout = zstd
        .stdout
        .ok_or_else(|| io_err(std::io::ErrorKind::BrokenPipe, "zstd stdout capture failed"))?;
    let tar = Command::new("tar")
        .args(["-xf", "-", "-C"])
        .arg(dest_dir)
        .arg(&strip)
        .stdin(stdout)
        .status()?;
    if !tar.success() {
        return Err(io_err(std::io::ErrorKind::Other, "tar extraction failed"));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Verify
// ---------------------------------------------------------------------------

/// Verification result for a release directory.
#[derive(Clone, Debug)]
pub struct VerifyResult {
    pub checked: usize,
    pub passed: usize,
    /// Shards that failed checksum verification.
    pub failures: Vec<VerifyFailure>,
    /// Shards listed in manifest but missing from disk.
    pub missing: Vec<String>,
}

/// A single verification failure.
#[derive(Clone, Debug)]
pub struct VerifyFailure {
    pub path: String,
    pub expected: String,
    pub actual: String,
}

impl VerifyResult {
    /// Returns `true` if all shards passed and none are missing.
    #[must_use]
    pub fn is_ok(&self) -> bool {
        self.failures.is_empty() && self.missing.is_empty()
    }
}

/// Verify release integrity by reading `mathverse-manifest.json` from `release_dir`
/// and checking every shard's blake3 hash.
///
/// If a `kernel-verified.json`
/// ([`crate::verify::kernel_verified_manifest::KernelVerifiedManifest`]) sits
/// alongside the shards, this additionally asserts that the stored
/// `KernelVerified` count in the shard bytes matches the manifest (WS5) — so a
/// green verify *proves* the kernel-verified stamp persisted, not merely that
/// the bytes are uncorrupted. Absence of the manifest preserves the legacy
/// blake3-only behavior.
pub fn verify_release(release_dir: &Path) -> MathverseResult<VerifyResult> {
    let manifest = ReleaseManifest::from_file(&release_dir.join("mathverse-manifest.json"))?;
    let result = verify_against_manifest(&manifest, release_dir)?;
    assert_kernel_verified_stamp(release_dir)?;
    Ok(result)
}

/// If `release_dir` holds a `kernel-verified.json`, assert that the number of
/// constant headers carrying `KernelVerified` in the shard bytes equals the
/// number of manifest names present in those shards. Returns `Ok(())` when no
/// kernel-verified manifest is present (nothing to assert).
///
/// # Errors
/// Returns [`MathverseError::KernelVerifiedStampMismatch`] when the persisted
/// stamp count disagrees with the manifest, or an I/O/parse error if the
/// manifest or shards cannot be read.
pub fn assert_kernel_verified_stamp(release_dir: &Path) -> MathverseResult<()> {
    let manifest_path = release_dir.join("kernel-verified.json");
    if !manifest_path.exists() {
        return Ok(());
    }
    let manifest =
        crate::verify::kernel_verified_manifest::KernelVerifiedManifest::from_file(&manifest_path)?;
    let expected =
        crate::library::count_present_names(release_dir, &manifest.kernel_verified_names)?;
    let (stored, _) = crate::library::count_stored_kernel_verified(release_dir)?;
    if stored != expected {
        return Err(MathverseError::KernelVerifiedStampMismatch {
            shard_dir: release_dir.display().to_string(),
            manifest: expected,
            stored,
        });
    }
    Ok(())
}

/// Verify shards against a manifest, checking blake3 hashes.
///
/// Thin delegate over [`crate::artifacts::verify_entries`], which owns the
/// single verification implementation (including the manifest path-traversal
/// guard) for both the Mathverse release pipeline and `clean artifacts`.
pub fn verify_against_manifest(
    manifest: &ReleaseManifest,
    base_dir: &Path,
) -> MathverseResult<VerifyResult> {
    crate::artifacts::verify_entries(&manifest.shards, base_dir)
}

// ---------------------------------------------------------------------------
// Print helpers
// ---------------------------------------------------------------------------

/// Print a human-readable summary of the manifest.
pub fn print_manifest_summary(
    manifest: &ReleaseManifest,
    mut w: impl Write,
) -> std::io::Result<()> {
    writeln!(w, "Mathverse Library Release v{}", manifest.release_version)?;
    writeln!(w, "  Created: {}", manifest.created_at)?;
    writeln!(w, "  Shards:  {}", manifest.total_shards)?;
    writeln!(
        w,
        "  Size:    {:.1} MB",
        manifest.total_bytes as f64 / 1_048_576.0
    )?;
    writeln!(w)?;
    for entry in &manifest.shards {
        writeln!(
            w,
            "  {:>8}  {}  {}",
            format_bytes(entry.size),
            &entry.blake3[..16],
            entry.path
        )?;
    }
    Ok(())
}

fn format_bytes(bytes: u64) -> String {
    if bytes < 1024 {
        format!("{bytes} B")
    } else if bytes < 1_048_576 {
        format!("{:.1} KB", bytes as f64 / 1024.0)
    } else {
        format!("{:.1} MB", bytes as f64 / 1_048_576.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_config_uses_public_release_repo() {
        let config = ReleaseConfig::default_for_clean("mathverse-out");
        assert_eq!(config.repo, DEFAULT_CLEAN_RELEASE_REPO);
        assert_eq!(config.repo, "alabsystems/clean");
    }

    #[test]
    fn archive_matcher_accepts_only_mathverse_library_v_tar_zst() {
        assert!(is_mathverse_library_archive(
            "mathverse-library-v0.9.0.tar.zst"
        ));
        assert!(is_mathverse_library_archive(
            "mathverse-library-v2026.04.24.tar.zst"
        ));
        assert!(!is_mathverse_library_archive(
            "mathverse-library-0.9.0.tar.zst"
        ));
        assert!(!is_mathverse_library_archive("clean-source-v0.9.0.tar.zst"));
        assert!(!is_mathverse_library_archive(
            "mathverse-library-v0.9.0.zip"
        ));
    }

    #[test]
    fn archive_discovery_rejects_generic_tar_zst_assets() {
        let dir = tempfile::tempdir().expect("tempdir");
        fs::write(
            dir.path().join("source.tar.zst"),
            b"not an mathverse archive",
        )
        .expect("write");

        let err = find_tar_zst(dir.path()).expect_err("generic tar.zst should be rejected");
        assert!(err.to_string().contains(MATHVERSE_LIBRARY_ARCHIVE_GLOB));

        let compatible = dir.path().join("mathverse-library-v0.9.0.tar.zst");
        fs::write(&compatible, b"mathverse archive").expect("write");
        assert_eq!(
            find_tar_zst(dir.path()).expect("compatible archive"),
            compatible
        );
    }

    #[test]
    fn manifest_from_file_missing_names_path_and_remediation() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("mathverse-manifest.json");
        let msg = ReleaseManifest::from_file(&path)
            .expect_err("missing manifest must fail")
            .to_string();
        assert!(
            msg.contains("mathverse-manifest.json"),
            "missing-manifest error must name the manifest path, got: {msg}"
        );
        assert!(
            msg.contains("clean mathverse download"),
            "missing-manifest error must name the download remediation, got: {msg}"
        );
    }

    #[test]
    fn manifest_from_file_bad_json_names_path() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("broken-manifest.json");
        fs::write(&path, b"{ not json").expect("write");
        let msg = ReleaseManifest::from_file(&path)
            .expect_err("malformed manifest must fail")
            .to_string();
        assert!(
            msg.contains("broken-manifest.json"),
            "parse error must name WHICH manifest file is malformed, got: {msg}"
        );
    }

    #[test]
    fn mathverse_shard_counter_detects_zero_shard_extracts() {
        let dir = tempfile::tempdir().expect("tempdir");
        fs::create_dir_all(dir.path().join("metadata")).expect("mkdir");
        fs::write(
            dir.path().join("mathverse-manifest.json"),
            br#"{"shards":[]}"#,
        )
        .expect("write");
        fs::write(dir.path().join("metadata").join("readme.txt"), b"no shards").expect("write");

        assert_eq!(count_mathverse_shards(dir.path()).expect("count"), 0);

        let nested = dir.path().join("base");
        fs::create_dir_all(&nested).expect("mkdir");
        fs::write(nested.join("Init.mathverse"), b"shard").expect("write");
        assert_eq!(count_mathverse_shards(dir.path()).expect("count"), 1);
    }
}
