// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the release packaging, download, and verification module.

use std::fs;
use std::path::Path;

use super::release::{
    package_release, verify_against_manifest, verify_release, ReleaseManifest, ReleaseShardEntry,
    VerifyResult,
};

// ---------------------------------------------------------------------------
// Manifest generation
// ---------------------------------------------------------------------------

#[test]
fn test_manifest_from_empty_directory() {
    let dir = tempfile::tempdir().unwrap();
    let manifest = ReleaseManifest::from_directory(dir.path(), "1.0.0")
        .expect("empty directory should succeed");
    assert_eq!(manifest.total_shards, 0);
    assert_eq!(manifest.total_bytes, 0);
    assert!(manifest.shards.is_empty());
    assert_eq!(manifest.release_version, "1.0.0");
    assert_eq!(manifest.manifest_version, 1);
}

#[test]
fn test_manifest_from_directory_with_shards() {
    let dir = tempfile::tempdir().unwrap();
    let base = dir.path().join("base");
    fs::create_dir_all(&base).unwrap();

    // Create fake shard files with known content.
    let content_a = b"shard-alpha-content";
    let content_b = b"shard-beta-content-longer";
    fs::write(base.join("alpha.mathverse"), content_a).unwrap();
    fs::write(base.join("beta.mathverse"), content_b).unwrap();

    // Non-.mathverse files should be ignored.
    fs::write(base.join("readme.txt"), b"not a shard").unwrap();

    let manifest = ReleaseManifest::from_directory(dir.path(), "2.0.0").unwrap();
    assert_eq!(manifest.total_shards, 2);
    assert_eq!(
        manifest.total_bytes,
        content_a.len() as u64 + content_b.len() as u64
    );

    // Shards should be sorted by path.
    assert!(manifest.shards[0].path.contains("alpha"));
    assert!(manifest.shards[1].path.contains("beta"));

    // Verify blake3 hashes.
    let expected_hash_a = blake3::hash(content_a).to_hex().to_string();
    assert_eq!(manifest.shards[0].blake3, expected_hash_a);
    assert_eq!(manifest.shards[0].size, content_a.len() as u64);
}

#[test]
fn test_manifest_nested_directories() {
    let dir = tempfile::tempdir().unwrap();
    let base = dir.path().join("base");
    let delta = dir.path().join("delta");
    fs::create_dir_all(&base).unwrap();
    fs::create_dir_all(&delta).unwrap();

    fs::write(base.join("init.mathverse"), b"init-data").unwrap();
    fs::write(delta.join("patch.mathverse"), b"patch-data").unwrap();

    let manifest = ReleaseManifest::from_directory(dir.path(), "0.1.0").unwrap();
    assert_eq!(manifest.total_shards, 2);

    let paths: Vec<&str> = manifest.shards.iter().map(|s| s.path.as_str()).collect();
    assert!(paths.iter().any(|p| p.contains("init")));
    assert!(paths.iter().any(|p| p.contains("patch")));
}

// ---------------------------------------------------------------------------
// Manifest serialization
// ---------------------------------------------------------------------------

#[test]
fn test_manifest_json_roundtrip() {
    let manifest = ReleaseManifest {
        manifest_version: 1,
        release_version: "3.0.0".to_string(),
        created_at: "2026-04-15T00:00:00Z".to_string(),
        shards: vec![ReleaseShardEntry {
            path: "base/test.mathverse".to_string(),
            size: 42,
            blake3: "abc123".to_string(),
        }],
        total_bytes: 42,
        total_shards: 1,
        baseline_index: Some("baseline.mvix".to_string()),
    };

    let json = manifest.to_json().expect("serialize");
    let back = ReleaseManifest::from_json(&json).expect("deserialize");
    assert_eq!(back.release_version, "3.0.0");
    assert_eq!(back.total_shards, 1);
    assert_eq!(back.shards[0].path, "base/test.mathverse");
    assert_eq!(back.shards[0].blake3, "abc123");
    assert_eq!(back.baseline_index.as_deref(), Some("baseline.mvix"));
}

#[test]
fn test_manifest_file_io() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("test-manifest.json");

    let manifest = ReleaseManifest {
        manifest_version: 1,
        release_version: "1.0.0".to_string(),
        created_at: "2026-01-01T00:00:00Z".to_string(),
        shards: vec![],
        total_bytes: 0,
        total_shards: 0,
        baseline_index: None,
    };

    manifest.write_to_file(&path).expect("write");
    let loaded = ReleaseManifest::from_file(&path).expect("read");
    assert_eq!(loaded.release_version, "1.0.0");
    assert_eq!(loaded.manifest_version, 1);
    assert_eq!(loaded.baseline_index, None);
}

// ---------------------------------------------------------------------------
// Checksum verification
// ---------------------------------------------------------------------------

#[test]
fn test_verify_against_manifest_all_valid() {
    let dir = tempfile::tempdir().unwrap();
    let content = b"valid-shard-data";
    let shard_path = dir.path().join("test.mathverse");
    fs::write(&shard_path, content).unwrap();

    let hash = blake3::hash(content).to_hex().to_string();
    let manifest = ReleaseManifest {
        manifest_version: 1,
        release_version: "1.0.0".to_string(),
        created_at: "test".to_string(),
        shards: vec![ReleaseShardEntry {
            path: "test.mathverse".to_string(),
            size: content.len() as u64,
            blake3: hash,
        }],
        total_bytes: content.len() as u64,
        total_shards: 1,
        baseline_index: None,
    };

    let result = verify_against_manifest(&manifest, dir.path()).unwrap();
    assert_eq!(result.checked, 1);
    assert_eq!(result.passed, 1);
    assert!(result.failures.is_empty());
    assert!(result.missing.is_empty());
    assert!(result.is_ok());
}

#[test]
fn test_verify_against_manifest_checksum_mismatch() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("bad.mathverse"), b"actual-data").unwrap();

    let manifest = ReleaseManifest {
        manifest_version: 1,
        release_version: "1.0.0".to_string(),
        created_at: "test".to_string(),
        shards: vec![ReleaseShardEntry {
            path: "bad.mathverse".to_string(),
            size: 11,
            blake3: "0000000000000000000000000000000000000000000000000000000000000000".to_string(),
        }],
        total_bytes: 11,
        total_shards: 1,
        baseline_index: None,
    };

    let result = verify_against_manifest(&manifest, dir.path()).unwrap();
    assert_eq!(result.checked, 1);
    assert_eq!(result.passed, 0);
    assert_eq!(result.failures.len(), 1);
    assert_eq!(result.failures[0].path, "bad.mathverse");
    assert!(!result.is_ok());
}

#[test]
fn test_verify_against_manifest_missing_file() {
    let dir = tempfile::tempdir().unwrap();

    let manifest = ReleaseManifest {
        manifest_version: 1,
        release_version: "1.0.0".to_string(),
        created_at: "test".to_string(),
        shards: vec![ReleaseShardEntry {
            path: "missing.mathverse".to_string(),
            size: 100,
            blake3: "deadbeef".to_string(),
        }],
        total_bytes: 100,
        total_shards: 1,
        baseline_index: None,
    };

    let result = verify_against_manifest(&manifest, dir.path()).unwrap();
    assert_eq!(result.checked, 1);
    assert_eq!(result.passed, 0);
    assert_eq!(result.missing.len(), 1);
    assert_eq!(result.missing[0], "missing.mathverse");
    assert!(!result.is_ok());
}

#[test]
fn test_verify_against_manifest_mixed() {
    let dir = tempfile::tempdir().unwrap();
    let base = dir.path().join("base");
    fs::create_dir_all(&base).unwrap();

    let good_content = b"good-shard";
    let bad_content = b"bad-shard";
    fs::write(base.join("good.mathverse"), good_content).unwrap();
    fs::write(base.join("bad.mathverse"), bad_content).unwrap();

    let good_hash = blake3::hash(good_content).to_hex().to_string();

    let manifest = ReleaseManifest {
        manifest_version: 1,
        release_version: "1.0.0".to_string(),
        created_at: "test".to_string(),
        shards: vec![
            ReleaseShardEntry {
                path: "base/good.mathverse".to_string(),
                size: good_content.len() as u64,
                blake3: good_hash,
            },
            ReleaseShardEntry {
                path: "base/bad.mathverse".to_string(),
                size: bad_content.len() as u64,
                blake3: "wrong-hash".to_string(),
            },
            ReleaseShardEntry {
                path: "base/ghost.mathverse".to_string(),
                size: 50,
                blake3: "ghost-hash".to_string(),
            },
        ],
        total_bytes: 100,
        total_shards: 3,
        baseline_index: None,
    };

    let result = verify_against_manifest(&manifest, dir.path()).unwrap();
    assert_eq!(result.checked, 3);
    assert_eq!(result.passed, 1);
    assert_eq!(result.failures.len(), 1);
    assert_eq!(result.missing.len(), 1);
    assert!(!result.is_ok());
}

// ---------------------------------------------------------------------------
// verify_release (end-to-end with manifest on disk)
// ---------------------------------------------------------------------------

#[test]
fn test_verify_release_end_to_end() {
    let dir = tempfile::tempdir().unwrap();
    let content = b"roundtrip-shard-data";
    fs::write(dir.path().join("rt.mathverse"), content).unwrap();

    // Build and write manifest
    let manifest = ReleaseManifest::from_directory(dir.path(), "0.5.0").unwrap();
    manifest
        .write_to_file(&dir.path().join("mathverse-manifest.json"))
        .unwrap();

    let result = verify_release(dir.path()).unwrap();
    assert!(result.is_ok(), "all shards should pass verification");
    assert_eq!(result.checked, 1);
    assert_eq!(result.passed, 1);
}

// ---------------------------------------------------------------------------
// Archive roundtrip (package + extract + verify)
// ---------------------------------------------------------------------------

#[test]
fn test_package_and_verify_roundtrip() {
    let dir = tempfile::tempdir().unwrap();
    let shard_dir = dir.path().join("shards");
    let output_dir = dir.path().join("output");
    let extract_dir = dir.path().join("extracted");
    fs::create_dir_all(&shard_dir).unwrap();

    // Create test shards.
    fs::write(shard_dir.join("alpha.mathverse"), b"alpha-shard-data").unwrap();
    fs::write(shard_dir.join("beta.mathverse"), b"beta-shard-data-longer").unwrap();

    // Package
    let archive =
        package_release(&shard_dir, "1.2.3", &output_dir).expect("packaging should succeed");
    assert!(archive.exists(), "archive file should exist");
    assert!(
        archive
            .file_name()
            .unwrap()
            .to_str()
            .unwrap()
            .contains("1.2.3"),
        "archive name should contain version"
    );

    // Verify the manifest was written inside shard_dir.
    let manifest_in_shards = shard_dir.join("mathverse-manifest.json");
    assert!(
        manifest_in_shards.exists(),
        "manifest should exist in shard dir"
    );

    // Extract and verify.
    fs::create_dir_all(&extract_dir).unwrap();
    super::release::extract_tar_zst(&archive, &extract_dir, 1).expect("extraction should succeed");

    // The extracted directory should contain mathverse-manifest.json.
    let manifest_path = extract_dir.join("mathverse-manifest.json");
    assert!(
        manifest_path.exists(),
        "extracted dir should contain manifest: {:?}",
        fs::read_dir(&extract_dir)
            .unwrap()
            .map(|e| e.unwrap().path())
            .collect::<Vec<_>>()
    );

    let result = verify_release(&extract_dir).expect("verify should succeed");
    assert!(result.is_ok(), "all shards should verify after roundtrip");
}

// ---------------------------------------------------------------------------
// print_manifest_summary
// ---------------------------------------------------------------------------

#[test]
fn test_print_manifest_summary() {
    let manifest = ReleaseManifest {
        manifest_version: 1,
        release_version: "1.0.0".to_string(),
        created_at: "2026-01-01T00:00:00Z".to_string(),
        shards: vec![ReleaseShardEntry {
            path: "base/init.mathverse".to_string(),
            size: 1_500_000,
            blake3: "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789".to_string(),
        }],
        total_bytes: 1_500_000,
        total_shards: 1,
        baseline_index: None,
    };

    let mut buf = Vec::new();
    super::release::print_manifest_summary(&manifest, &mut buf).unwrap();
    let output = String::from_utf8(buf).unwrap();
    assert!(output.contains("1.0.0"));
    assert!(output.contains("1.4 MB"));
    assert!(output.contains("init.mathverse"));
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_package_release_nonexistent_dir() {
    let dir = tempfile::tempdir().unwrap();
    let result = package_release(
        &dir.path().join("nonexistent"),
        "1.0.0",
        &dir.path().join("out"),
    );
    assert!(result.is_err(), "packaging nonexistent dir should fail");
}

#[test]
fn test_verify_result_is_ok() {
    let ok = VerifyResult {
        checked: 5,
        passed: 5,
        failures: vec![],
        missing: vec![],
    };
    assert!(ok.is_ok());

    let with_failure = VerifyResult {
        checked: 5,
        passed: 4,
        failures: vec![super::release::VerifyFailure {
            path: "x.mathverse".to_string(),
            expected: "a".to_string(),
            actual: "b".to_string(),
        }],
        missing: vec![],
    };
    assert!(!with_failure.is_ok());

    let with_missing = VerifyResult {
        checked: 5,
        passed: 4,
        failures: vec![],
        missing: vec!["y.mathverse".to_string()],
    };
    assert!(!with_missing.is_ok());
}

// ---------------------------------------------------------------------------
// Baseline index ships in the archive (Distribution Tier-1)
// ---------------------------------------------------------------------------

/// Write a real (parseable) `.mathverse` shard carrying one theorem,
/// `Dist.imp_self : ∀ (p : Prop), p → p`, into `dir`.
fn write_real_shard(dir: &Path) {
    use clean_kernel::{BinderInfo, Declaration, Expr, Name};

    use crate::export::kernel_export::KernelShardBuilder;

    let bd = BinderInfo::Default;
    let ty = Expr::pi(bd, Expr::prop(), Expr::pi(bd, Expr::bvar(0), Expr::bvar(1)));
    let val = Expr::lam(
        bd,
        Expr::prop(),
        Expr::lam(bd, Expr::bvar(0), Expr::bvar(0)),
    );
    let decl = Declaration::Theorem {
        name: Name::from_string("Dist.imp_self"),
        level_params: vec![],
        type_: ty,
        value: val,
    };
    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(&decl, &[])
        .expect("export Dist.imp_self");
    builder
        .write_to_file(dir.join("dist.mathverse"))
        .expect("write real shard");
}

#[test]
fn test_package_ships_baseline_index_in_archive_and_manifest() {
    use super::graduate::BaselineIndex;
    use super::release::BASELINE_INDEX_FILENAME;

    let dir = tempfile::tempdir().unwrap();
    let shard_dir = dir.path().join("shards");
    let output_dir = dir.path().join("output");
    let extract_dir = dir.path().join("extracted");
    fs::create_dir_all(&shard_dir).unwrap();
    write_real_shard(&shard_dir);

    // Package: the baseline index is built + swept into the tar automatically.
    let archive =
        package_release(&shard_dir, "9.9.9", &output_dir).expect("packaging should succeed");
    assert!(archive.exists(), "archive file should exist");

    // The index landed alongside the shards in the source directory.
    assert!(
        shard_dir.join(BASELINE_INDEX_FILENAME).exists(),
        "baseline.mvix should be written into the shard dir"
    );

    // The manifest references it (relative path).
    let manifest = ReleaseManifest::from_file(&shard_dir.join("mathverse-manifest.json"))
        .expect("read manifest");
    assert_eq!(
        manifest.baseline_index.as_deref(),
        Some(BASELINE_INDEX_FILENAME),
        "manifest must reference the shipped baseline index"
    );

    // Extract and confirm the index is INSIDE the archive (not just the source dir).
    fs::create_dir_all(&extract_dir).unwrap();
    super::release::extract_tar_zst(&archive, &extract_dir, 1).expect("extraction should succeed");
    let extracted_index = extract_dir.join(BASELINE_INDEX_FILENAME);
    assert!(
        extracted_index.exists(),
        "baseline.mvix must be present in the extracted archive: {:?}",
        fs::read_dir(&extract_dir)
            .unwrap()
            .map(|e| e.unwrap().path())
            .collect::<Vec<_>>()
    );

    // The shipped index loads (fail-closed validation) and is non-empty.
    let index = BaselineIndex::load(&extracted_index).expect("shipped index must load");
    assert!(
        index.contains_name("Dist.imp_self"),
        "shipped index must be queryable for the corpus constant"
    );
    assert!(index.name_count() >= 1);

    // The manifest still verifies after the roundtrip (index is excluded from
    // the .mathverse shard list, so checksum verification is unaffected).
    let result = verify_release(&extract_dir).expect("verify should succeed");
    assert!(result.is_ok(), "shards should verify after roundtrip");
}

#[test]
fn test_package_empty_corpus_skips_baseline_index() {
    use super::release::BASELINE_INDEX_FILENAME;

    let dir = tempfile::tempdir().unwrap();
    let shard_dir = dir.path().join("shards");
    let output_dir = dir.path().join("output");
    fs::create_dir_all(&shard_dir).unwrap();
    // No .mathverse shards -> no indexable constants.

    let archive =
        package_release(&shard_dir, "0.0.1", &output_dir).expect("empty packaging should succeed");
    assert!(archive.exists());

    // No index file written, and the manifest does not reference one.
    assert!(
        !shard_dir.join(BASELINE_INDEX_FILENAME).exists(),
        "empty corpus must not write a baseline index"
    );
    let manifest = ReleaseManifest::from_file(&shard_dir.join("mathverse-manifest.json"))
        .expect("read manifest");
    assert_eq!(
        manifest.baseline_index, None,
        "empty corpus manifest must not reference a baseline index"
    );
}
