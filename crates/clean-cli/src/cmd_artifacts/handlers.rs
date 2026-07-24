// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Handlers for `clean artifacts <verb>`.
//!
//! Verification posture (fail-closed, per §5.6 of
//! `designs/2026-06-09-master-design-v2.md`):
//!
//! - a positive blake3 mismatch or a manifest entry missing from disk is
//!   ALWAYS a hard error — `--allow-unverified` never overrides it;
//! - `--allow-unverified` only bypasses the *absence* of verification (no
//!   manifest asset, or downloaded files not covered by the manifest), with
//!   a loud multi-line stderr warning and `"verified": false` in JSON;
//! - `--skip-verify` is explicitly rejected with an explanatory error,
//!   matching the `clean mathverse download --json` verified gate;
//! - downloads and extractions land in a temp directory and are only
//!   published into `--out` after verification passes.

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{anyhow, bail, Context};
use clean_mathverse::artifacts::{
    download_assets, extract_archive, find_manifest, list_release_assets, list_releases,
    verify_entries, MANIFEST_SUFFIX,
};
use clean_mathverse::release::{ReleaseManifest, ReleaseShardEntry, VerifyResult};
use serde::Serialize;

use super::args::{
    ArtifactsCommands, ArtifactsExtractArgs, ArtifactsGetArgs, ArtifactsListArgs,
    ArtifactsVerifyArgs,
};

/// RAII guard that removes a temporary directory on drop.
struct TempDirGuard(PathBuf);

impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Dispatch entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_artifacts_command(command: ArtifactsCommands) -> anyhow::Result<()> {
    // `#[non_exhaustive]` on `ArtifactsCommands` only affects downstream
    // crates; within this crate the match stays exhaustive, so a new verb
    // is a compile error until it gains a dispatch arm here.
    match command {
        ArtifactsCommands::List(args) => run_list(&args),
        ArtifactsCommands::Get(args) => run_get(&args),
        ArtifactsCommands::Verify(args) => run_verify(&args),
        ArtifactsCommands::Extract(args) => run_extract(&args),
    }
}

fn reject_skip_verify(skip_verify: bool) -> anyhow::Result<()> {
    if skip_verify {
        bail!(
            "clean artifacts is a fail-closed verification surface and does not \
             accept --skip-verify; use --allow-unverified to proceed when no \
             manifest covers the files (checksum mismatches always fail)"
        );
    }
    Ok(())
}

fn fresh_temp_dir(verb: &str) -> anyhow::Result<PathBuf> {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0);
    let tmp = std::env::temp_dir().join(format!(
        "clean-artifacts-{verb}-{}-{nanos}",
        std::process::id()
    ));
    fs::create_dir_all(&tmp)
        .with_context(|| format!("failed to create temp dir {}", tmp.display()))?;
    Ok(tmp)
}

// ---------------------------------------------------------------------------
// list
// ---------------------------------------------------------------------------

fn run_list(args: &ArtifactsListArgs) -> anyhow::Result<()> {
    if let Some(tag) = &args.tag {
        let assets = list_release_assets(&args.repo, tag)?;
        if args.json {
            let report = serde_json::json!({
                "repo": args.repo, "tag": tag, "assets": assets,
            });
            println!("{}", serde_json::to_string_pretty(&report)?);
        } else {
            println!("assets of {} {tag}:", args.repo);
            for asset in &assets {
                println!("  {:>12}  {}", asset.size, asset.name);
            }
        }
    } else {
        let releases = list_releases(&args.repo, args.limit)?;
        if args.json {
            let report = serde_json::json!({
                "repo": args.repo, "releases": releases,
            });
            println!("{}", serde_json::to_string_pretty(&report)?);
        } else {
            println!("releases of {}:", args.repo);
            for release in &releases {
                let latest = if release.is_latest { "  (latest)" } else { "" };
                println!("  {:<32} {}{latest}", release.tag, release.published_at);
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// get
// ---------------------------------------------------------------------------

#[derive(Debug, Serialize)]
struct GetReport {
    ok: bool,
    repo: String,
    tag: String,
    output_dir: String,
    manifest: Option<String>,
    /// True only when every published file was blake3-verified against the
    /// manifest. False under `--allow-unverified`.
    verified: bool,
    verified_files: Vec<String>,
    unverified_files: Vec<String>,
}

fn run_get(args: &ArtifactsGetArgs) -> anyhow::Result<()> {
    reject_skip_verify(args.skip_verify)?;
    let tmp = fresh_temp_dir("get")?;
    let _cleanup = TempDirGuard(tmp.clone());

    let mut files = download_assets(&args.repo, &args.tag, args.pattern.as_deref(), &tmp)?;
    // Always try to fetch a manifest asset, even when --pattern excludes it.
    // A release without one is handled fail-closed by verify_directory below.
    if find_manifest(&tmp).is_none() {
        if let Ok(extra) = download_assets(
            &args.repo,
            &args.tag,
            Some(&format!("*{MANIFEST_SUFFIX}")),
            &tmp,
        ) {
            files.extend(extra);
        }
    }
    if files.is_empty() {
        bail!(
            "no assets downloaded from {} {}{}",
            args.repo,
            args.tag,
            args.pattern
                .as_deref()
                .map(|glob| format!(" matching pattern {glob}"))
                .unwrap_or_default()
        );
    }

    let verification = verify_directory(&tmp, args.allow_unverified)
        .with_context(|| format!("refusing to publish unverified assets from {}", args.tag))?;

    // Publish only after verification: copy every downloaded file into --out.
    fs::create_dir_all(&args.out)
        .with_context(|| format!("failed to create output dir {}", args.out.display()))?;
    for file in &files {
        let name = file
            .file_name()
            .ok_or_else(|| anyhow!("downloaded asset has no file name: {}", file.display()))?;
        fs::copy(file, args.out.join(name))
            .with_context(|| format!("failed to publish {}", file.display()))?;
    }

    let report = GetReport {
        ok: true,
        repo: args.repo.clone(),
        tag: args.tag.clone(),
        output_dir: args.out.display().to_string(),
        manifest: verification.manifest.clone(),
        verified: verification.verified,
        verified_files: verification.verified_files.clone(),
        unverified_files: verification.unverified_files.clone(),
    };
    if args.json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        println!(
            "published {} file(s) from {} {} to {} (verified: {})",
            report.verified_files.len() + report.unverified_files.len(),
            report.repo,
            report.tag,
            report.output_dir,
            report.verified
        );
    }
    Ok(())
}

/// Outcome of fail-closed manifest verification over a directory of files.
#[derive(Debug)]
struct DirVerification {
    /// Manifest filename, when one was found.
    manifest: Option<String>,
    /// True when every non-manifest file was covered and blake3-verified.
    verified: bool,
    verified_files: Vec<String>,
    unverified_files: Vec<String>,
}

/// Verify the top-level files of `dir` against the manifest found in `dir`.
///
/// Fail-closed: checksum mismatches always error; files not covered by a
/// manifest (or a missing manifest) error unless `allow_unverified`, which
/// downgrades them to a loud stderr warning.
fn verify_directory(dir: &Path, allow_unverified: bool) -> anyhow::Result<DirVerification> {
    let mut file_names: Vec<String> = fs::read_dir(dir)
        .with_context(|| format!("failed to read {}", dir.display()))?
        .filter_map(Result::ok)
        .filter(|entry| entry.file_type().is_ok_and(|ty| ty.is_file()))
        .filter_map(|entry| entry.file_name().into_string().ok())
        .collect();
    file_names.sort();

    let Some(manifest_path) = find_manifest(dir) else {
        require_allow_unverified(allow_unverified, None, &file_names)?;
        return Ok(DirVerification {
            manifest: None,
            verified: false,
            verified_files: Vec::new(),
            unverified_files: file_names,
        });
    };
    let manifest_name = manifest_path
        .file_name()
        .map(|name| name.to_string_lossy().to_string())
        .unwrap_or_default();
    let manifest = ReleaseManifest::from_file(&manifest_path)
        .with_context(|| format!("failed to parse {}", manifest_path.display()))?;

    let mut covered: Vec<ReleaseShardEntry> = Vec::new();
    let mut verified_files: Vec<String> = Vec::new();
    let mut unverified_files: Vec<String> = Vec::new();
    for name in &file_names {
        if *name == manifest_name {
            continue;
        }
        match manifest.shards.iter().find(|entry| entry.path == *name) {
            Some(entry) => {
                covered.push(entry.clone());
                verified_files.push(name.clone());
            }
            None => unverified_files.push(name.clone()),
        }
    }

    let result = verify_entries(&covered, dir)?;
    ensure_verify_result_ok(&result)?;

    if !unverified_files.is_empty() {
        require_allow_unverified(allow_unverified, Some(&manifest_name), &unverified_files)?;
    }
    Ok(DirVerification {
        manifest: Some(manifest_name),
        verified: unverified_files.is_empty(),
        verified_files,
        unverified_files,
    })
}

/// Hard error on missing coverage unless `--allow-unverified`; in that case
/// emit the loud multi-line warning instead.
fn require_allow_unverified(
    allow_unverified: bool,
    manifest: Option<&str>,
    files: &[String],
) -> anyhow::Result<()> {
    if !allow_unverified {
        match manifest {
            None => bail!(
                "no *{MANIFEST_SUFFIX} found, so {} file(s) cannot be verified; \
                 refusing to proceed (pass --allow-unverified to accept \
                 unverified artifacts)",
                files.len()
            ),
            Some(name) => bail!(
                "{} file(s) are not covered by {name}: {}; refusing to proceed \
                 (pass --allow-unverified to accept unverified artifacts)",
                files.len(),
                files.join(", ")
            ),
        }
    }
    eprintln!(
        "WARNING: proceeding WITHOUT blake3 verification for {} file(s):",
        files.len()
    );
    for file in files {
        eprintln!("WARNING:   - {file}");
    }
    eprintln!(
        "WARNING: these artifacts are NOT covered by a manifest. Treat them as \
         untrusted input;"
    );
    eprintln!(
        "WARNING: for archives, `clean artifacts extract` verifies the extracted \
         tree against its embedded manifest."
    );
    Ok(())
}

fn ensure_verify_result_ok(result: &VerifyResult) -> anyhow::Result<()> {
    if result.is_ok() {
        return Ok(());
    }
    for failure in &result.failures {
        eprintln!(
            "FAIL {}: expected blake3 {}, got {}",
            failure.path, failure.expected, failure.actual
        );
    }
    for missing in &result.missing {
        eprintln!("MISSING {missing}");
    }
    if !result.failures.is_empty() {
        eprintln!(
            "note: a FAIL means the on-disk file differs from its manifest entry \
             (partial download, stale local copy, or tampering) — delete the file and \
             re-fetch it with `clean artifacts get`"
        );
    }
    if !result.missing.is_empty() {
        eprintln!(
            "note: a MISSING file is listed in the manifest but absent on disk — \
             re-download the release or re-extract the archive into this directory"
        );
    }
    bail!(
        "blake3 manifest verification failed: {} checksum failure(s), {} missing \
         file(s) out of {} checked (per-file FAIL/MISSING rows above name the \
         offending files; re-fetch via `clean artifacts get`)",
        result.failures.len(),
        result.missing.len(),
        result.checked
    );
}

// ---------------------------------------------------------------------------
// verify
// ---------------------------------------------------------------------------

#[derive(Debug, Serialize)]
struct VerifyReport {
    ok: bool,
    dir: String,
    manifest: String,
    checked: usize,
    passed: usize,
    failures: Vec<VerifyFailureRow>,
    missing: Vec<String>,
}

#[derive(Debug, Serialize)]
struct VerifyFailureRow {
    path: String,
    expected: String,
    actual: String,
}

fn run_verify(args: &ArtifactsVerifyArgs) -> anyhow::Result<()> {
    if !args.dir.is_dir() {
        bail!("artifact directory not found: {}", args.dir.display());
    }
    let manifest_path = match &args.manifest {
        Some(path) => path.clone(),
        None => find_manifest(&args.dir).ok_or_else(|| {
            anyhow!(
                "no *{MANIFEST_SUFFIX} found in {}; pass --manifest <FILE>",
                args.dir.display()
            )
        })?,
    };
    let manifest = ReleaseManifest::from_file(&manifest_path)
        .with_context(|| format!("failed to parse {}", manifest_path.display()))?;
    if manifest.shards.is_empty() {
        bail!(
            "manifest {} lists zero entries; refusing to report a vacuous pass",
            manifest_path.display()
        );
    }
    let result = verify_entries(&manifest.shards, &args.dir)?;

    let report = VerifyReport {
        ok: result.is_ok(),
        dir: args.dir.display().to_string(),
        manifest: manifest_path.display().to_string(),
        checked: result.checked,
        passed: result.passed,
        failures: result
            .failures
            .iter()
            .map(|failure| VerifyFailureRow {
                path: failure.path.clone(),
                expected: failure.expected.clone(),
                actual: failure.actual.clone(),
            })
            .collect(),
        missing: result.missing.clone(),
    };
    if args.json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        println!(
            "verified {} against {}: {}/{} passed",
            report.dir, report.manifest, report.passed, report.checked
        );
    }
    ensure_verify_result_ok(&result)
}

// ---------------------------------------------------------------------------
// extract
// ---------------------------------------------------------------------------

#[derive(Debug, Serialize)]
struct ExtractReport {
    ok: bool,
    archive: String,
    output_dir: String,
    manifest: Option<String>,
    verified: bool,
    checked: usize,
    passed: usize,
}

fn run_extract(args: &ArtifactsExtractArgs) -> anyhow::Result<()> {
    reject_skip_verify(args.skip_verify)?;
    if !args.archive.is_file() {
        bail!("archive not found: {}", args.archive.display());
    }
    let tmp = fresh_temp_dir("extract")?;
    let _cleanup = TempDirGuard(tmp.clone());
    let extract_dir = tmp.join("extract");
    extract_archive(&args.archive, &extract_dir, args.strip_components)?;

    let (manifest, result) = verify_extracted_tree(&extract_dir, args.allow_unverified)
        .with_context(|| {
            format!(
                "refusing to publish unverified extraction of {}",
                args.archive.display()
            )
        })?;

    fs::create_dir_all(&args.out)
        .with_context(|| format!("failed to create output dir {}", args.out.display()))?;
    copy_dir_contents(&extract_dir, &args.out)?;

    let report = ExtractReport {
        ok: true,
        archive: args.archive.display().to_string(),
        output_dir: args.out.display().to_string(),
        manifest: manifest.clone(),
        verified: manifest.is_some(),
        checked: result.as_ref().map_or(0, |r| r.checked),
        passed: result.as_ref().map_or(0, |r| r.passed),
    };
    if args.json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        println!(
            "extracted {} to {} (verified: {}, {}/{} entries passed)",
            report.archive, report.output_dir, report.verified, report.passed, report.checked
        );
    }
    Ok(())
}

/// Verify the extracted tree against its embedded manifest. Returns the
/// manifest filename (when found) and the verification result.
fn verify_extracted_tree(
    extract_dir: &Path,
    allow_unverified: bool,
) -> anyhow::Result<(Option<String>, Option<VerifyResult>)> {
    let Some(manifest_path) = find_manifest(extract_dir) else {
        require_allow_unverified(
            allow_unverified,
            None,
            &["<entire extracted tree>".to_string()],
        )?;
        return Ok((None, None));
    };
    let manifest = ReleaseManifest::from_file(&manifest_path)
        .with_context(|| format!("failed to parse {}", manifest_path.display()))?;
    if manifest.shards.is_empty() {
        bail!(
            "manifest {} lists zero entries; refusing to publish a vacuously \
             verified tree",
            manifest_path.display()
        );
    }
    let result = verify_entries(&manifest.shards, extract_dir)?;
    ensure_verify_result_ok(&result)?;
    let manifest_name = manifest_path
        .file_name()
        .map(|name| name.to_string_lossy().to_string());
    Ok((manifest_name, Some(result)))
}

fn copy_dir_contents(src: &Path, dest: &Path) -> anyhow::Result<()> {
    for entry in fs::read_dir(src).with_context(|| format!("failed to read {}", src.display()))? {
        let entry = entry?;
        let src_path = entry.path();
        let dest_path = dest.join(entry.file_name());
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            fs::create_dir_all(&dest_path)
                .with_context(|| format!("failed to create {}", dest_path.display()))?;
            copy_dir_contents(&src_path, &dest_path)?;
        } else if file_type.is_file() {
            fs::copy(&src_path, &dest_path)
                .with_context(|| format!("failed to publish {}", dest_path.display()))?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
