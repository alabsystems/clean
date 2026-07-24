// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Coq .vo pipeline (directory processing, stats).

use super::pipeline::*;
use std::path::Path;

// ---------------------------------------------------------------------------
// Pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_config_default() {
    let config = PipelineConfig::default();
    assert_eq!(config.max_file_size, 256 * 1024 * 1024);
    assert!(config.collect_declarations);
    assert_eq!(config.extensions, vec!["vo"]);
}

#[test]
fn test_pipeline_stats_merge() {
    let mut s1 = PipelineStats {
        files_found: 10,
        files_parsed: 8,
        files_failed: 2,
        constants: 50,
        inductives: 10,
        ..Default::default()
    };
    let s2 = PipelineStats {
        files_found: 5,
        files_parsed: 5,
        constants: 20,
        inductives: 5,
        ..Default::default()
    };
    s1.merge(&s2);
    assert_eq!(s1.files_found, 15);
    assert_eq!(s1.files_parsed, 13);
    assert_eq!(s1.files_failed, 2);
    assert_eq!(s1.constants, 70);
    assert_eq!(s1.inductives, 15);
}

#[test]
fn test_pipeline_stats_summary() {
    let stats = PipelineStats {
        files_found: 100,
        files_parsed: 95,
        files_failed: 3,
        files_skipped: 2,
        total_declarations: 5000,
        constants: 4000,
        inductives: 500,
        modules: 500,
        bytes_processed: 50 * 1024 * 1024,
        ..Default::default()
    };
    let summary = stats.summary();
    assert!(summary.contains("100 files"));
    assert!(summary.contains("95 ok"));
    assert!(summary.contains("5000 decls"));
}

#[test]
fn test_pipeline_empty_directory() {
    let dir = tempfile::tempdir().unwrap();
    let config = PipelineConfig::default();
    let (stats, decls) =
        process_directory(dir.path(), &config).expect("should handle empty directory");
    assert_eq!(stats.files_found, 0);
    assert!(decls.is_empty());
}

#[test]
fn test_pipeline_nonexistent_directory() {
    let config = PipelineConfig::default();
    let (stats, decls) = process_directory(Path::new("/nonexistent/path/to/coq/libs"), &config)
        .expect("should handle nonexistent directory gracefully");
    assert_eq!(stats.files_found, 0);
    assert!(decls.is_empty());
}

#[test]
fn test_count_vo_files_empty() {
    let dir = tempfile::tempdir().unwrap();
    assert_eq!(count_vo_files(dir.path()), 0);
}

#[test]
fn test_pipeline_with_non_vo_files() {
    let dir = tempfile::tempdir().unwrap();
    // Create some non-.vo files.
    std::fs::write(dir.path().join("test.v"), "Theorem t : True.").unwrap();
    std::fs::write(dir.path().join("test.glob"), "").unwrap();
    let config = PipelineConfig::default();
    let (stats, _) = process_directory(dir.path(), &config).expect("should skip non-vo files");
    assert_eq!(stats.files_found, 0);
}

#[test]
fn test_pipeline_real_init_theories() {
    let Some(home) = std::env::var_os("HOME") else {
        eprintln!("SKIP: no HOME");
        return;
    };
    let dir = std::path::PathBuf::from(home).join(".opam/mathverse-serapi/lib/coq/theories/Init");
    if !dir.is_dir() {
        eprintln!("SKIP: Coq 8.20 Init theories not present on this machine");
        return;
    }
    let config = PipelineConfig::default();
    let (stats, decls) = process_directory(&dir, &config).expect("should process Init dir");
    assert_eq!(
        stats.files_failed, 0,
        "all Init .vo files must parse: {:?}",
        stats.errors
    );
    assert_eq!(stats.files_parsed, stats.files_found);
    assert!(stats.files_found >= 10);
    assert!(
        stats.constants > 500,
        "Init has >500 constants, got {}",
        stats.constants
    );
    assert!(stats.inductives >= 25, "got {}", stats.inductives);
    assert!(stats.opaque_count > 50, "got {}", stats.opaque_count);
    assert!(decls.iter().any(|d| d.name == "Coq.Init.Logic.eq_sym"));
    // Nat.vo declares nested-module content (Coq.Init.Nat.add etc.).
    assert!(decls.iter().any(|d| d.name == "Coq.Init.Nat.add"));
}

#[test]
fn test_pipeline_exclude_prefixes() {
    let config = PipelineConfig {
        exclude_prefixes: vec!["deprecated".to_string()],
        ..Default::default()
    };
    assert!(!config.exclude_prefixes.is_empty());
    // The exclude logic is tested via process_single_file; here we just
    // verify the config propagates.
}
