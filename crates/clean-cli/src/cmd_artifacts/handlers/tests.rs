// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the `clean artifacts` fail-closed verification handlers.

use std::fs;
use std::path::Path;

use clap::Parser;

use super::*;
use crate::cli_args::{Cli, Commands};

fn manifest_json(entries: &[(&str, u64, &str)]) -> String {
    let shards: Vec<String> = entries
        .iter()
        .map(|(path, size, blake3)| {
            format!(r#"{{"path":"{path}","size":{size},"blake3":"{blake3}"}}"#)
        })
        .collect();
    let total_bytes: u64 = entries.iter().map(|(_, size, _)| size).sum();
    format!(
        r#"{{"manifest_version":1,"release_version":"9.9.9","created_at":"test","shards":[{}],"total_bytes":{total_bytes},"total_shards":{}}}"#,
        shards.join(","),
        entries.len()
    )
}

fn write_payload_with_manifest(dir: &Path, name: &str, payload: &[u8]) {
    fs::write(dir.join(name), payload).expect("write payload");
    let hash = blake3::hash(payload).to_hex().to_string();
    fs::write(
        dir.join("artifact-manifest.json"),
        manifest_json(&[(name, payload.len() as u64, &hash)]),
    )
    .expect("write manifest");
}

fn parse_artifacts(argv: &[&str]) -> ArtifactsCommands {
    let cli = Cli::try_parse_from(argv).expect("argv should parse");
    match cli.command {
        Commands::Artifacts { command } => command,
        _ => panic!("expected `clean artifacts` to route to Commands::Artifacts"),
    }
}

// -- clap surface ----------------------------------------------------------

#[test]
fn test_clap_get_parses_tag_repo_pattern_out_and_json() {
    let command = parse_artifacts(&[
        "clean",
        "artifacts",
        "get",
        "mathverse-v1.2.0",
        "--repo",
        "alabsystems/clean",
        "--pattern",
        "*.tar.zst",
        "--out",
        "downloads",
        "--json",
    ]);
    match command {
        ArtifactsCommands::Get(args) => {
            assert_eq!(args.tag, "mathverse-v1.2.0");
            assert_eq!(args.repo, "alabsystems/clean");
            assert_eq!(args.pattern.as_deref(), Some("*.tar.zst"));
            assert_eq!(args.out, PathBuf::from("downloads"));
            assert!(args.json, "--json must be threaded through");
            assert!(!args.allow_unverified);
            assert!(!args.skip_verify);
        }
        other => panic!("expected Get, got {other:?}"),
    }
}

#[test]
fn test_clap_defaults_repo_and_strip_components() {
    let command = parse_artifacts(&["clean", "artifacts", "list"]);
    match command {
        ArtifactsCommands::List(args) => {
            assert_eq!(
                args.repo,
                clean_mathverse::release::DEFAULT_CLEAN_RELEASE_REPO
            );
            assert_eq!(args.limit, 30);
        }
        other => panic!("expected List, got {other:?}"),
    }
    let command = parse_artifacts(&["clean", "artifacts", "extract", "a.tar.zst", "--out", "o"]);
    match command {
        ArtifactsCommands::Extract(args) => assert_eq!(args.strip_components, 1),
        other => panic!("expected Extract, got {other:?}"),
    }
}

#[test]
fn test_skip_verify_is_rejected_with_explanatory_error() {
    for argv in [
        vec![
            "clean",
            "artifacts",
            "get",
            "some-tag",
            "--out",
            "o",
            "--skip-verify",
        ],
        vec![
            "clean",
            "artifacts",
            "extract",
            "a.tar.zst",
            "--out",
            "o",
            "--skip-verify",
        ],
    ] {
        let command = parse_artifacts(&argv);
        let err = handle_artifacts_command(command).expect_err("--skip-verify must be rejected");
        assert!(
            err.to_string().contains("does not accept --skip-verify"),
            "error must explain the rejection, got: {err}"
        );
    }
}

// -- verify_directory (the post-download gate) -----------------------------

#[test]
fn test_verify_directory_without_manifest_mentions_allow_unverified() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(dir.path().join("blob.bin"), b"payload").expect("write");

    let err = verify_directory(dir.path(), false).expect_err("must fail without manifest");
    assert!(
        err.to_string().contains("--allow-unverified"),
        "error must name the override flag, got: {err}"
    );

    let verification = verify_directory(dir.path(), true).expect("allow-unverified path");
    assert!(!verification.verified);
    assert_eq!(verification.unverified_files, vec!["blob.bin".to_string()]);
}

#[test]
fn test_verify_directory_checksum_mismatch_fails_even_with_allow_unverified() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(dir.path().join("blob.bin"), b"tampered payload").expect("write");
    fs::write(
        dir.path().join("artifact-manifest.json"),
        manifest_json(&[("blob.bin", 16, &"0".repeat(64))]),
    )
    .expect("write manifest");

    for allow_unverified in [false, true] {
        let err = verify_directory(dir.path(), allow_unverified)
            .expect_err("checksum mismatch must always fail");
        assert!(
            err.to_string().contains("checksum failure"),
            "expected checksum failure error, got: {err}"
        );
        // Four-question standard: the failure must point at the per-file
        // rows (WHAT) and name the re-fetch remediation (WHAT NOW).
        assert!(
            err.to_string().contains("clean artifacts get"),
            "verification failure must carry the re-fetch remediation, got: {err}"
        );
    }
}

#[test]
fn test_verify_directory_uncovered_files_require_allow_unverified() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_payload_with_manifest(dir.path(), "covered.bin", b"payload");
    fs::write(dir.path().join("rogue.bin"), b"unmanifested").expect("write");

    let err = verify_directory(dir.path(), false).expect_err("uncovered file must fail closed");
    assert!(err.to_string().contains("rogue.bin"));
    assert!(err.to_string().contains("--allow-unverified"));

    let verification = verify_directory(dir.path(), true).expect("override accepted");
    assert!(!verification.verified);
    assert_eq!(verification.verified_files, vec!["covered.bin".to_string()]);
    assert_eq!(verification.unverified_files, vec!["rogue.bin".to_string()]);
}

#[test]
fn test_verify_directory_fully_covered_passes_verified() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_payload_with_manifest(dir.path(), "covered.bin", b"payload");

    let verification = verify_directory(dir.path(), false).expect("verified download");
    assert!(verification.verified);
    assert_eq!(
        verification.manifest.as_deref(),
        Some("artifact-manifest.json")
    );
    assert_eq!(verification.verified_files, vec!["covered.bin".to_string()]);
    assert!(verification.unverified_files.is_empty());
}

// -- verify verb ------------------------------------------------------------

#[test]
fn test_run_verify_passes_on_intact_directory() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_payload_with_manifest(dir.path(), "shardlike.bin", b"intact bytes");

    let args = ArtifactsVerifyArgs {
        dir: dir.path().to_path_buf(),
        manifest: None,
        json: true,
    };
    run_verify(&args).expect("intact directory must verify");
}

#[test]
fn test_run_verify_fails_on_checksum_mismatch_and_missing() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(dir.path().join("present.bin"), b"tampered").expect("write");
    fs::write(
        dir.path().join("artifact-manifest.json"),
        manifest_json(&[
            ("present.bin", 8, &"0".repeat(64)),
            ("absent.bin", 4, &"0".repeat(64)),
        ]),
    )
    .expect("write manifest");

    let args = ArtifactsVerifyArgs {
        dir: dir.path().to_path_buf(),
        manifest: None,
        json: false,
    };
    let err = run_verify(&args).expect_err("mismatch + missing must fail");
    assert!(err.to_string().contains("1 checksum failure(s)"));
    assert!(err.to_string().contains("1 missing"));
}

#[test]
fn test_run_verify_rejects_zero_entry_manifest() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(
        dir.path().join("artifact-manifest.json"),
        manifest_json(&[]),
    )
    .expect("write manifest");

    let args = ArtifactsVerifyArgs {
        dir: dir.path().to_path_buf(),
        manifest: None,
        json: false,
    };
    let err = run_verify(&args).expect_err("zero-entry manifest must fail");
    assert!(err.to_string().contains("zero entries"));
}

#[test]
fn test_run_verify_rejects_manifest_path_traversal() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(
        dir.path().join("artifact-manifest.json"),
        manifest_json(&[("../escape.bin", 4, &"0".repeat(64))]),
    )
    .expect("write manifest");

    let args = ArtifactsVerifyArgs {
        dir: dir.path().to_path_buf(),
        manifest: None,
        json: false,
    };
    let err = run_verify(&args).expect_err("traversal entry must fail");
    assert!(err.to_string().contains("invalid manifest entry path"));
}

#[test]
fn test_run_verify_missing_manifest_names_flag() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(dir.path().join("blob.bin"), b"payload").expect("write");

    let args = ArtifactsVerifyArgs {
        dir: dir.path().to_path_buf(),
        manifest: None,
        json: false,
    };
    let err = run_verify(&args).expect_err("no manifest must fail");
    assert!(err.to_string().contains("--manifest"));
}

#[test]
fn test_run_verify_accepts_generic_files_manifest_key() {
    // Generic artifact manifests may use `files` instead of `shards`
    // (serde alias on `ReleaseManifest::shards`).
    let dir = tempfile::tempdir().expect("tempdir");
    let payload = b"generic artifact";
    fs::write(dir.path().join("artifact.bin"), payload).expect("write");
    let hash = blake3::hash(payload).to_hex().to_string();
    fs::write(
        dir.path().join("bundle-manifest.json"),
        format!(
            r#"{{"manifest_version":1,"release_version":"0.1.0","created_at":"test","files":[{{"path":"artifact.bin","size":{},"blake3":"{hash}"}}],"total_bytes":{},"total_shards":1}}"#,
            payload.len(),
            payload.len()
        ),
    )
    .expect("write manifest");

    let args = ArtifactsVerifyArgs {
        dir: dir.path().to_path_buf(),
        manifest: None,
        json: true,
    };
    run_verify(&args).expect("`files` manifest key must verify");
}

// -- extract verb ------------------------------------------------------------

#[test]
fn test_run_extract_rejects_unsupported_archive_suffix() {
    let dir = tempfile::tempdir().expect("tempdir");
    let archive = dir.path().join("bundle.zip");
    fs::write(&archive, b"not a tarball").expect("write");

    let args = ArtifactsExtractArgs {
        archive,
        out: dir.path().join("out"),
        strip_components: 1,
        allow_unverified: false,
        json: false,
        skip_verify: false,
    };
    let err = run_extract(&args).expect_err("zip must be rejected");
    assert!(err.to_string().contains("unsupported archive format"));
}

#[test]
fn test_run_extract_missing_archive_errors() {
    let dir = tempfile::tempdir().expect("tempdir");
    let args = ArtifactsExtractArgs {
        archive: dir.path().join("nope.tar.zst"),
        out: dir.path().join("out"),
        strip_components: 1,
        allow_unverified: false,
        json: false,
        skip_verify: false,
    };
    let err = run_extract(&args).expect_err("missing archive must fail");
    assert!(err.to_string().contains("archive not found"));
}

#[test]
fn test_verify_extracted_tree_requires_manifest_or_override() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(dir.path().join("loose.bin"), b"payload").expect("write");

    let err = verify_extracted_tree(dir.path(), false).expect_err("no manifest must fail");
    assert!(err.to_string().contains("--allow-unverified"));

    let (manifest, result) = verify_extracted_tree(dir.path(), true).expect("override accepted");
    assert!(manifest.is_none());
    assert!(result.is_none());
}

#[test]
fn test_verify_extracted_tree_verifies_nested_manifest_entries() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::create_dir_all(dir.path().join("base")).expect("mkdir");
    let payload = b"nested shard bytes";
    fs::write(dir.path().join("base/Init.bin"), payload).expect("write");
    let hash = blake3::hash(payload).to_hex().to_string();
    fs::write(
        dir.path().join("artifact-manifest.json"),
        manifest_json(&[("base/Init.bin", payload.len() as u64, &hash)]),
    )
    .expect("write manifest");

    let (manifest, result) =
        verify_extracted_tree(dir.path(), false).expect("nested tree must verify");
    assert_eq!(manifest.as_deref(), Some("artifact-manifest.json"));
    let result = result.expect("verify result present");
    assert_eq!(result.checked, 1);
    assert_eq!(result.passed, 1);
}
