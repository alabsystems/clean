// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch the `clean mathverse <verb>` subcommand into the `clean-mathverse`
//! library's CLI module.
//!
//! The actual argument parsing (clap derives), formatting, and library access
//! live in [`clean_mathverse::cli`]. This wrapper exists only to convert the
//! typed [`MathverseCliError`](clean_mathverse::cli::MathverseCliError) into `anyhow`
//! context for the top-level CLI dispatcher (see `lib.rs::dispatch_sync`).
//!
//! Part of Epic #3436 and issue #3440: absorbs the deprecated standalone
//! `mathverse_search` binary into the unified `clean` CLI surface.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Component, Path, PathBuf};

use anyhow::{anyhow, Context};
use clean_mathverse::cli::{
    run as mathverse_run, AxiomAuditCommands, MathverseArgs, MathverseCommands,
};
use clean_mathverse::release::{
    verify_against_manifest, ReleaseManifest, DEFAULT_CLEAN_RELEASE_REPO,
};
use serde::Serialize;

use crate::cmd_axiom_audit_release_check::handle_axiom_audit_release_check_command;

const MATHVERSE_LIBRARY_ARCHIVE_GLOB: &str = "mathverse-library-v*.tar.zst";
const MATHVERSE_MANIFEST: &str = "mathverse-manifest.json";

#[derive(Debug, Clone)]
struct VerifiedDownloadArgs {
    version: String,
    output_dir: PathBuf,
    repo: String,
}

#[derive(Debug, Serialize)]
struct VerifiedDownloadReport {
    ok: bool,
    version: String,
    output_dir: String,
    archive: Option<String>,
    manifest_shards: usize,
    copied_shards: usize,
    removed_stale_shards: Vec<String>,
    error: Option<String>,
}

struct TempDirGuard(PathBuf);

impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_mathverse_command(args: MathverseArgs) -> anyhow::Result<()> {
    match args.command {
        MathverseCommands::Download(download_args)
            if wants_verified_json_gate(&download_args.rest) =>
        {
            run_verified_download_gate(&download_args.rest)
        }
        // `clean mathverse axiom-audit <verb>` is dispatched here (not in
        // `clean_mathverse::cli::run`) because the handler shells out to scripts
        // located via repo-root walk-up — a `clean-cli` concern, not a
        // library concern. The mathverse-lib dispatcher returns
        // `MathverseCliError::AxiomAuditDispatch` if this intercept is ever
        // bypassed (fail-closed). Bucket-B migration, Wave 87.
        MathverseCommands::AxiomAudit { command } => match command {
            AxiomAuditCommands::ReleaseCheck(rc_args) => {
                handle_axiom_audit_release_check_command(rc_args)
            }
            // `AxiomAuditCommands` is `#[non_exhaustive]` so future sibling
            // verbs (e.g. `recompute`, per the queued bucket-B migration)
            // can drop in without breaking this dispatcher. New variants
            // must gain a concrete arm here.
            #[allow(unreachable_patterns)]
            _ => unreachable!("unhandled AxiomAuditCommands variant; add a dispatch arm"),
        },
        // `isabelle-doctor` is intercepted here (not in `clean_mathverse::cli::run`)
        // so the doctor can report the RUNNING binary's real build identity — the
        // git SHA + build timestamp `clean-cli`'s `build.rs` embeds at compile
        // time, which the library crate cannot see. The library dispatch path
        // degrades to `BuildIdentity::unknown()` (a loud WARN) if this intercept
        // is ever bypassed.
        MathverseCommands::IsabelleDoctor(doctor_args) => {
            let build = clean_mathverse::cli::BuildIdentity::new(
                option_env!("CLEAN_BUILD_GIT_SHA").map(str::to_string),
                option_env!("CLEAN_BUILD_UNIX").and_then(|s| s.parse::<u64>().ok()),
            );
            clean_mathverse::cli::run_isabelle_doctor(doctor_args, build)
                .map_err(anyhow::Error::from)
        }
        // `isabelle-snapshot-preserve` is intercepted here for the SAME reason as
        // the doctor: it names the preserved binary copy by the RUNNING binary's
        // embedded git SHA, which only `clean-cli`'s `build.rs` can see. The
        // library dispatch path degrades to `BuildIdentity::unknown()` (a loud
        // `clean-unknown` copy + WARN) if this intercept is bypassed.
        MathverseCommands::IsabelleSnapshotPreserve(preserve_args) => {
            let build = clean_mathverse::cli::BuildIdentity::new(
                option_env!("CLEAN_BUILD_GIT_SHA").map(str::to_string),
                option_env!("CLEAN_BUILD_UNIX").and_then(|s| s.parse::<u64>().ok()),
            );
            clean_mathverse::cli::run_isabelle_snapshot_preserve(preserve_args, build)
                .map_err(anyhow::Error::from)
        }
        command => mathverse_run(MathverseArgs { command }).map_err(anyhow::Error::from),
    }
}

fn wants_verified_json_gate(args: &[String]) -> bool {
    args.iter().any(|arg| arg == "--json")
}

fn run_verified_download_gate(args: &[String]) -> anyhow::Result<()> {
    let parsed = match parse_verified_download_args(args) {
        Ok(parsed) => parsed,
        Err(err) => {
            let report = parse_error_download_report(&err);
            print_json_report(&report)?;
            return Err(err);
        }
    };

    match verified_download(&parsed) {
        Ok(report) => {
            print_json_report(&report)?;
            Ok(())
        }
        Err(err) => {
            let report = download_error_report(&parsed, &err);
            print_json_report(&report)?;
            Err(err)
        }
    }
}

fn parse_error_download_report(err: &anyhow::Error) -> VerifiedDownloadReport {
    VerifiedDownloadReport {
        ok: false,
        version: String::new(),
        output_dir: String::new(),
        archive: None,
        manifest_shards: 0,
        copied_shards: 0,
        removed_stale_shards: Vec::new(),
        error: Some(err.to_string()),
    }
}

fn download_error_report(
    parsed: &VerifiedDownloadArgs,
    err: &anyhow::Error,
) -> VerifiedDownloadReport {
    VerifiedDownloadReport {
        ok: false,
        version: parsed.version.clone(),
        output_dir: parsed.output_dir.display().to_string(),
        archive: None,
        manifest_shards: 0,
        copied_shards: 0,
        removed_stale_shards: Vec::new(),
        error: Some(err.to_string()),
    }
}

fn parse_verified_download_args(args: &[String]) -> anyhow::Result<VerifiedDownloadArgs> {
    let mut version = None;
    let mut output_dir = None;
    let mut repo = DEFAULT_CLEAN_RELEASE_REPO.to_string();
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        match arg.as_str() {
            "--json" | "--force" => {}
            "--version" => {
                i += 1;
                version = args.get(i).cloned();
            }
            "--output-dir" => {
                i += 1;
                output_dir = args.get(i).map(PathBuf::from);
            }
            "--repo" => {
                i += 1;
                repo = args
                    .get(i)
                    .cloned()
                    .ok_or_else(|| anyhow!("--repo requires a value"))?;
            }
            "--skip-verify" => {
                return Err(anyhow!(
                    "clean mathverse download --json is a verified launch gate and does not accept --skip-verify"
                ));
            }
            other if other.starts_with("--version=") => {
                version = Some(other.trim_start_matches("--version=").to_string());
            }
            other if other.starts_with("--output-dir=") => {
                output_dir = Some(PathBuf::from(other.trim_start_matches("--output-dir=")));
            }
            other if other.starts_with("--repo=") => {
                repo = other.trim_start_matches("--repo=").to_string();
            }
            other => {
                return Err(anyhow!(
                    "unknown verified mathverse download option: {other}"
                ))
            }
        }
        i += 1;
    }

    let version = version
        .filter(|value| !value.trim().is_empty())
        .ok_or_else(|| anyhow!("--version <version> is required for the verified JSON gate"))?;
    let output_dir = output_dir
        .filter(|value| !value.as_os_str().is_empty())
        .ok_or_else(|| anyhow!("--output-dir <dir> is required for the verified JSON gate"))?;

    Ok(VerifiedDownloadArgs {
        version,
        output_dir,
        repo,
    })
}

fn verified_download(args: &VerifiedDownloadArgs) -> anyhow::Result<VerifiedDownloadReport> {
    let tmp = std::env::temp_dir().join(format!(
        "clean-mathverse-download-{}-{}",
        std::process::id(),
        monotonic_nanos()
    ));
    fs::create_dir_all(&tmp)
        .with_context(|| format!("failed to create temp download dir {}", tmp.display()))?;
    let _cleanup = TempDirGuard(tmp.clone());

    let tag = format!("mathverse-v{}", args.version);
    download_archive(&args.repo, &tag, &tmp)?;
    let archive = find_exact_archive(&tmp, &args.version)?;
    let extract_dir = tmp.join("extract");
    extract_tar_zst(&archive, &extract_dir)?;
    let publish = verify_extracted_release(&args.version, &extract_dir)
        .with_context(|| format!("refusing to publish unverified Mathverse release {tag}"))?;
    let removed_stale_shards =
        publish_verified_release(&extract_dir, &args.output_dir, &publish.manifest_paths)?;

    Ok(VerifiedDownloadReport {
        ok: true,
        version: args.version.clone(),
        output_dir: args.output_dir.display().to_string(),
        archive: archive
            .file_name()
            .map(|name| name.to_string_lossy().to_string()),
        manifest_shards: publish.manifest_paths.len(),
        copied_shards: publish.manifest_paths.len(),
        removed_stale_shards,
        error: None,
    })
}

/// Download the corpus archive via the shared artifact-system shell-out
/// ([`clean_mathverse::artifacts::download_assets`]); this used to be a
/// private `gh release download` copy.
fn download_archive(repo: &str, tag: &str, dest_dir: &Path) -> anyhow::Result<()> {
    clean_mathverse::artifacts::download_assets(
        repo,
        tag,
        Some(MATHVERSE_LIBRARY_ARCHIVE_GLOB),
        dest_dir,
    )
    .with_context(|| {
        format!("could not find compatible {MATHVERSE_LIBRARY_ARCHIVE_GLOB} asset for {tag}")
    })?;
    Ok(())
}

fn find_exact_archive(dir: &Path, version: &str) -> anyhow::Result<PathBuf> {
    let expected = format!("mathverse-library-v{version}.tar.zst");
    let mut compatible = Vec::new();
    for entry in fs::read_dir(dir).with_context(|| format!("failed to read {}", dir.display()))? {
        let path = entry?.path();
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if name == expected {
            return Ok(path);
        }
        if name.starts_with("mathverse-library-v") && name.ends_with(".tar.zst") {
            compatible.push(name.to_string());
        }
    }

    if compatible.is_empty() {
        Err(anyhow!(
            "could not find compatible {MATHVERSE_LIBRARY_ARCHIVE_GLOB} asset"
        ))
    } else {
        Err(anyhow!(
            "release did not provide expected asset {expected}; found {}",
            compatible.join(", ")
        ))
    }
}

/// Extract the corpus archive via the shared suffix-dispatched extractor
/// ([`clean_mathverse::artifacts::extract_archive`]); this used to be a
/// private `tar --zstd` shell-out copy.
fn extract_tar_zst(archive: &Path, dest_dir: &Path) -> anyhow::Result<()> {
    clean_mathverse::artifacts::extract_archive(archive, dest_dir, 1)
        .with_context(|| format!("temp extraction failed for {}", archive.display()))?;
    Ok(())
}

#[derive(Debug)]
struct VerifiedExtract {
    manifest_paths: BTreeSet<String>,
}

fn verify_extracted_release(version: &str, extract_dir: &Path) -> anyhow::Result<VerifiedExtract> {
    let manifest_path = extract_dir.join(MATHVERSE_MANIFEST);
    if !manifest_path.is_file() {
        return Err(anyhow!(
            "{MATHVERSE_MANIFEST} not found; refusing to use unverified Mathverse shards"
        ));
    }
    let manifest = ReleaseManifest::from_file(&manifest_path)
        .with_context(|| format!("failed to parse {}", manifest_path.display()))?;
    validate_manifest(version, &manifest)?;

    let extracted_paths = collect_relative_mathverse_paths(extract_dir)?;
    if extracted_paths.is_empty() {
        return Err(anyhow!(
            "extracted archive contains no .mathverse shard files"
        ));
    }

    let manifest_paths = manifest
        .shards
        .iter()
        .map(|entry| validate_manifest_path(&entry.path))
        .collect::<anyhow::Result<BTreeSet<_>>>()?;
    if manifest_paths != extracted_paths {
        return Err(anyhow!(
            "{MATHVERSE_MANIFEST} does not match extracted .mathverse shard set; refusing to publish unmanifested or missing Mathverse shards"
        ));
    }

    for entry in &manifest.shards {
        let path = extract_dir.join(&entry.path);
        let actual = fs::metadata(&path)
            .with_context(|| format!("failed to stat {}", path.display()))?
            .len();
        if actual != entry.size {
            return Err(anyhow!(
                "manifest size mismatch for {}: expected size: {}, actual size: {}",
                entry.path,
                entry.size,
                actual
            ));
        }
    }

    let verify = verify_against_manifest(&manifest, extract_dir)?;
    if !verify.is_ok() {
        return Err(anyhow!(
            "manifest checksum verification failed: {} hash failures, {} missing shards",
            verify.failures.len(),
            verify.missing.len()
        ));
    }

    Ok(VerifiedExtract { manifest_paths })
}

fn validate_manifest(version: &str, manifest: &ReleaseManifest) -> anyhow::Result<()> {
    let expected_total_bytes = manifest
        .shards
        .iter()
        .try_fold(0_u64, |acc, shard| acc.checked_add(shard.size))
        .ok_or_else(|| anyhow!("{MATHVERSE_MANIFEST} total_bytes overflow"))?;

    if manifest.manifest_version != 1
        || manifest.release_version != version
        || manifest.total_shards != manifest.shards.len()
        || manifest.total_bytes != expected_total_bytes
    {
        return Err(anyhow!(
            "{MATHVERSE_MANIFEST} is not compatible with release mathverse-v{version}; expected manifest_version=1, release_version={version}, and total_shards/total_bytes matching shard entries"
        ));
    }
    if manifest.total_shards == 0 || manifest.shards.is_empty() {
        return Err(anyhow!(
            "{MATHVERSE_MANIFEST} contains zero shards; refusing to publish empty Mathverse release"
        ));
    }
    Ok(())
}

fn validate_manifest_path(path: &str) -> anyhow::Result<String> {
    let candidate = Path::new(path);
    if path.is_empty()
        || candidate.is_absolute()
        || candidate
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
        || candidate.extension().and_then(|ext| ext.to_str()) != Some("mathverse")
    {
        return Err(anyhow!("invalid manifest shard path: {path}"));
    }
    Ok(path.replace('\\', "/"))
}

fn publish_verified_release(
    extract_dir: &Path,
    output_dir: &Path,
    manifest_paths: &BTreeSet<String>,
) -> anyhow::Result<Vec<String>> {
    fs::create_dir_all(output_dir)
        .with_context(|| format!("failed to create output dir {}", output_dir.display()))?;
    copy_dir_contents(extract_dir, output_dir)?;
    remove_stale_mathverse_shards(output_dir, output_dir, manifest_paths)
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
            if let Some(parent) = dest_path.parent() {
                fs::create_dir_all(parent)
                    .with_context(|| format!("failed to create {}", parent.display()))?;
            }
            fs::copy(&src_path, &dest_path).with_context(|| {
                format!(
                    "failed to copy verified Mathverse artifact {} to {}",
                    src_path.display(),
                    dest_path.display()
                )
            })?;
        }
    }
    Ok(())
}

fn remove_stale_mathverse_shards(
    base_dir: &Path,
    current_dir: &Path,
    manifest_paths: &BTreeSet<String>,
) -> anyhow::Result<Vec<String>> {
    let mut removed = Vec::new();
    if !current_dir.is_dir() {
        return Ok(removed);
    }
    for entry in fs::read_dir(current_dir)
        .with_context(|| format!("failed to read {}", current_dir.display()))?
    {
        let entry = entry?;
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            removed.extend(remove_stale_mathverse_shards(
                base_dir,
                &path,
                manifest_paths,
            )?);
        } else if file_type.is_file()
            && path.extension().and_then(|ext| ext.to_str()) == Some("mathverse")
        {
            let rel = path
                .strip_prefix(base_dir)
                .with_context(|| format!("failed to relativize {}", path.display()))?
                .to_string_lossy()
                .replace('\\', "/");
            if !manifest_paths.contains(&rel) {
                fs::remove_file(&path)
                    .with_context(|| format!("failed to remove stale shard {}", path.display()))?;
                removed.push(rel);
            }
        }
    }
    removed.sort();
    Ok(removed)
}

fn collect_relative_mathverse_paths(base_dir: &Path) -> anyhow::Result<BTreeSet<String>> {
    let mut paths = BTreeSet::new();
    collect_relative_mathverse_paths_inner(base_dir, base_dir, &mut paths)?;
    Ok(paths)
}

fn collect_relative_mathverse_paths_inner(
    base_dir: &Path,
    current_dir: &Path,
    out: &mut BTreeSet<String>,
) -> anyhow::Result<()> {
    for entry in fs::read_dir(current_dir)
        .with_context(|| format!("failed to read {}", current_dir.display()))?
    {
        let entry = entry?;
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            collect_relative_mathverse_paths_inner(base_dir, &path, out)?;
        } else if file_type.is_file()
            && path.extension().and_then(|ext| ext.to_str()) == Some("mathverse")
        {
            let rel = path
                .strip_prefix(base_dir)
                .with_context(|| format!("failed to relativize {}", path.display()))?
                .to_string_lossy()
                .replace('\\', "/");
            out.insert(rel);
        }
    }
    Ok(())
}

fn print_json_report(report: &VerifiedDownloadReport) -> anyhow::Result<()> {
    println!("{}", serde_json::to_string_pretty(report)?);
    Ok(())
}

fn monotonic_nanos() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_mathverse::release::ReleaseManifest;

    fn write_manifest_from_dir(dir: &Path, version: &str) {
        let manifest = ReleaseManifest::from_directory(dir, version).expect("manifest");
        manifest
            .write_to_file(&dir.join(MATHVERSE_MANIFEST))
            .expect("write manifest");
    }

    #[test]
    fn verified_json_gate_requires_version_and_output_dir() {
        let err = parse_verified_download_args(&["--json".to_string()]).expect_err("must fail");
        assert!(err.to_string().contains("--version <version> is required"));

        let err = parse_verified_download_args(&[
            "--json".to_string(),
            "--version".to_string(),
            "9.9.9".to_string(),
        ])
        .expect_err("must fail");
        assert!(err.to_string().contains("--output-dir <dir> is required"));
    }

    #[test]
    fn verified_json_gate_skip_verify_failure_has_json_shape() {
        let err = parse_verified_download_args(&[
            "--json".to_string(),
            "--version".to_string(),
            "9.9.9".to_string(),
            "--output-dir".to_string(),
            "mathverse-out".to_string(),
            "--skip-verify".to_string(),
        ])
        .expect_err("must fail");
        let report = parse_error_download_report(&err);
        let json = serde_json::to_value(&report).expect("json report");

        assert_eq!(json["ok"], false);
        assert_eq!(json["version"], "");
        assert_eq!(json["output_dir"], "");
        assert_eq!(json["archive"], serde_json::Value::Null);
        assert_eq!(json["manifest_shards"], 0);
        assert_eq!(json["copied_shards"], 0);
        assert_eq!(json["removed_stale_shards"], serde_json::json!([]));
        assert!(json["error"]
            .as_str()
            .expect("error string")
            .contains("does not accept --skip-verify"));
    }

    #[test]
    fn exact_archive_lookup_rejects_incompatible_version_assets() {
        let dir = tempfile::tempdir().expect("tmp");
        fs::write(
            dir.path().join("mathverse-library-v9.9.8.tar.zst"),
            b"archive",
        )
        .expect("write");
        let err = find_exact_archive(dir.path(), "9.9.9").expect_err("must fail");
        assert!(err
            .to_string()
            .contains("did not provide expected asset mathverse-library-v9.9.9.tar.zst"));
    }

    #[test]
    fn extracted_release_rejects_zero_shards() {
        let dir = tempfile::tempdir().expect("tmp");
        fs::write(
            dir.path().join(MATHVERSE_MANIFEST),
            r#"{"manifest_version":1,"release_version":"9.9.9","created_at":"test","shards":[],"total_bytes":0,"total_shards":0}"#,
        )
        .expect("write");

        let err = verify_extracted_release("9.9.9", dir.path()).expect_err("must fail");
        assert!(err.to_string().contains("zero shards"));
    }

    #[test]
    fn extracted_release_rejects_manifest_checksum_mismatch() {
        let dir = tempfile::tempdir().expect("tmp");
        fs::write(dir.path().join("core.mathverse"), b"mathverse shard\n").expect("write shard");
        fs::write(
            dir.path().join(MATHVERSE_MANIFEST),
            r#"{"manifest_version":1,"release_version":"9.9.9","created_at":"test","shards":[{"path":"core.mathverse","size":16,"blake3":"0000000000000000000000000000000000000000000000000000000000000000"}],"total_bytes":16,"total_shards":1}"#,
        )
        .expect("write");

        let err = verify_extracted_release("9.9.9", dir.path()).expect_err("must fail");
        assert!(err
            .to_string()
            .contains("manifest checksum verification failed"));
    }

    #[test]
    fn extracted_release_rejects_unmanifested_shards() {
        let dir = tempfile::tempdir().expect("tmp");
        fs::write(dir.path().join("core.mathverse"), b"mathverse shard\n").expect("write shard");
        fs::write(dir.path().join("extra.mathverse"), b"extra shard\n").expect("write extra");
        fs::write(
            dir.path().join(MATHVERSE_MANIFEST),
            r#"{"manifest_version":1,"release_version":"9.9.9","created_at":"test","shards":[{"path":"core.mathverse","size":12,"blake3":"ignored"}],"total_bytes":12,"total_shards":1}"#,
        )
        .expect("write");

        let err = verify_extracted_release("9.9.9", dir.path()).expect_err("must fail");
        assert!(err
            .to_string()
            .contains("does not match extracted .mathverse shard set"));
    }

    #[test]
    fn extracted_release_rejects_manifest_path_traversal() {
        let dir = tempfile::tempdir().expect("tmp");
        fs::write(dir.path().join("core.mathverse"), b"mathverse shard\n").expect("write shard");
        fs::write(
            dir.path().join(MATHVERSE_MANIFEST),
            r#"{"manifest_version":1,"release_version":"9.9.9","created_at":"test","shards":[{"path":"../core.mathverse","size":12,"blake3":"ignored"}],"total_bytes":12,"total_shards":1}"#,
        )
        .expect("write");

        let err = verify_extracted_release("9.9.9", dir.path()).expect_err("must fail");
        assert!(err
            .to_string()
            .contains("invalid manifest shard path: ../core.mathverse"));
    }

    #[test]
    fn extracted_release_rejects_manifest_total_bytes_drift() {
        let dir = tempfile::tempdir().expect("tmp");
        fs::write(dir.path().join("core.mathverse"), b"mathverse shard\n").expect("write shard");
        fs::write(
            dir.path().join(MATHVERSE_MANIFEST),
            r#"{"manifest_version":1,"release_version":"9.9.9","created_at":"test","shards":[{"path":"core.mathverse","size":12,"blake3":"ignored"}],"total_bytes":13,"total_shards":1}"#,
        )
        .expect("write");

        let err = verify_extracted_release("9.9.9", dir.path()).expect_err("must fail");
        assert!(err
            .to_string()
            .contains("total_shards/total_bytes matching shard entries"));
    }

    #[test]
    fn publish_verified_release_removes_stale_output_shards() {
        let extract = tempfile::tempdir().expect("extract");
        fs::write(extract.path().join("core.mathverse"), b"mathverse shard\n")
            .expect("write shard");
        write_manifest_from_dir(extract.path(), "9.9.9");
        let verified = verify_extracted_release("9.9.9", extract.path()).expect("verified");

        let output = tempfile::tempdir().expect("output");
        fs::write(output.path().join("stale.mathverse"), b"old\n").expect("write stale");
        fs::write(output.path().join("notes.txt"), b"preserve\n").expect("write notes");

        let removed =
            publish_verified_release(extract.path(), output.path(), &verified.manifest_paths)
                .expect("publish");

        assert_eq!(removed, vec!["stale.mathverse"]);
        assert!(output.path().join("core.mathverse").is_file());
        assert!(!output.path().join("stale.mathverse").exists());
        assert_eq!(
            fs::read_to_string(output.path().join("notes.txt")).expect("notes"),
            "preserve\n"
        );
    }
}
