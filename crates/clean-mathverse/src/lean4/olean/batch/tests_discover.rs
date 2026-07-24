// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the batch `.olean` import pipeline: file-failure handling,
//! discovery edge cases, and import-file error paths.

use std::path::PathBuf;

use super::*;
use crate::lean4::olean::alpha::ImportStats;
use crate::shard::ShardWriter;

// ---------------------------------------------------------------------------
// File failure handling
// ---------------------------------------------------------------------------

#[test]
fn test_file_failure_graceful() {
    let mut r = BatchImportResult {
        total_files: 3,
        ..Default::default()
    };
    let ok = ImportStats {
        total: 5,
        kernel_verified: 5,
        kernel_verified_from_tc: 0,
        axiomatized: 0,
        skipped: 0,
    };
    r.accum(&ok);
    r.accum(&ok);
    r.files_failed
        .push((PathBuf::from("bad.olean"), "corrupt header".into()));
    assert_eq!(r.total_constants, 10);
    assert_eq!(r.files_failed.len(), 1);
}

// ---------------------------------------------------------------------------
// Discover edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_discover_nonexistent_root() {
    let cfg = Lean4BatchConfig::new(PathBuf::from("/nonexistent/path/xyz"));
    let err = Lean4BatchImporter::new(cfg).discover_files().unwrap_err();
    assert!(err.to_string().contains("not found"), "got: {err}");
}

#[test]
fn test_discover_empty_dir() {
    let dir = tempfile::tempdir().expect("tempdir");
    let cfg = Lean4BatchConfig::new(dir.path().to_path_buf());
    assert!(Lean4BatchImporter::new(cfg)
        .discover_files()
        .unwrap()
        .is_empty());
}

#[test]
fn test_discover_ignores_non_olean() {
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(dir.path().join("foo.olean"), b"").unwrap();
    std::fs::write(dir.path().join("bar.lean"), b"").unwrap();
    std::fs::write(dir.path().join("baz.txt"), b"").unwrap();

    let files = Lean4BatchImporter::new(Lean4BatchConfig::new(dir.path().to_path_buf()))
        .discover_files()
        .unwrap();
    assert_eq!(files.len(), 1);
    assert!(files[0].extension().unwrap() == "olean");
}

// ---------------------------------------------------------------------------
// Import file error path
// ---------------------------------------------------------------------------

#[test]
fn test_import_file_bad_data() {
    let dir = tempfile::tempdir().expect("tempdir");
    let bad = dir.path().join("bad.olean");
    std::fs::write(&bad, b"not a real olean").unwrap();

    let err = Lean4BatchImporter::new(Lean4BatchConfig::new(dir.path().to_path_buf()))
        .import_file(&bad, &mut ShardWriter::new())
        .unwrap_err();
    assert!(err.to_string().contains("Lean4"), "got: {err}");
}
