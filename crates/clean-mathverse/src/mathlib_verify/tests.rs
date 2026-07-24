// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Mathlib verification pipeline.

use super::*;

// ════════════════════════════════════════════════════════════════════════════
// Error classification tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_classify_error_heartbeat() {
    assert_eq!(
        classify_error("deterministic timeout (heartbeat exceeded)"),
        MathLibErrorKind::HeartbeatExceeded,
    );
    assert_eq!(
        classify_error("heartbeat limit reached at 200000"),
        MathLibErrorKind::HeartbeatExceeded,
    );
}

#[test]
fn test_classify_error_stack_overflow() {
    assert_eq!(
        classify_error("thread 'main' has overflowed its stack"),
        MathLibErrorKind::StackOverflow,
    );
    assert_eq!(
        classify_error("stack_overflow in deep term reduction"),
        MathLibErrorKind::StackOverflow,
    );
}

#[test]
fn test_classify_error_shard_write() {
    assert_eq!(
        classify_error("shard serialization error: disk full"),
        MathLibErrorKind::ShardWriteFailed,
    );
    assert_eq!(
        classify_error("write failed: permission denied"),
        MathLibErrorKind::ShardWriteFailed,
    );
}

#[test]
fn test_classify_error_olean_load() {
    assert_eq!(
        classify_error("failed to load .olean: invalid header"),
        MathLibErrorKind::OleanLoadFailed,
    );
    assert_eq!(
        classify_error("parse error in module header"),
        MathLibErrorKind::OleanLoadFailed,
    );
    assert_eq!(
        classify_error("olean version mismatch"),
        MathLibErrorKind::OleanLoadFailed,
    );
}

#[test]
fn test_classify_error_typecheck_default() {
    assert_eq!(
        classify_error("type mismatch: expected Nat, got Bool"),
        MathLibErrorKind::TypeCheckFailed,
    );
    assert_eq!(
        classify_error("universe level error"),
        MathLibErrorKind::TypeCheckFailed,
    );
}

// ════════════════════════════════════════════════════════════════════════════
// MathLibErrorKind display tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_error_kind_display() {
    assert_eq!(
        MathLibErrorKind::OleanLoadFailed.to_string(),
        "olean_load_failed"
    );
    assert_eq!(
        MathLibErrorKind::TypeCheckFailed.to_string(),
        "type_check_failed"
    );
    assert_eq!(
        MathLibErrorKind::HeartbeatExceeded.to_string(),
        "heartbeat_exceeded"
    );
    assert_eq!(
        MathLibErrorKind::StackOverflow.to_string(),
        "stack_overflow"
    );
    assert_eq!(
        MathLibErrorKind::ShardWriteFailed.to_string(),
        "shard_write_failed"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Module group name extraction tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_module_group_name_three_parts() {
    assert_eq!(module_group_name("Mathlib.Data.Nat.Basic"), "Mathlib.Data");
}

#[test]
fn test_module_group_name_two_parts() {
    assert_eq!(module_group_name("Mathlib.Data"), "Mathlib.Data");
}

#[test]
fn test_module_group_name_single_part() {
    assert_eq!(module_group_name("Init"), "Init");
}

#[test]
fn test_module_group_name_deep_path() {
    assert_eq!(
        module_group_name("Mathlib.Algebra.Group.Basic"),
        "Mathlib.Algebra",
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Config default tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_config_default_values() {
    let config = MathLibVerifyConfig::default();
    assert_eq!(config.progress_interval, 100);
    assert_eq!(config.stack_size_bytes, 0);
    assert_eq!(config.heartbeat_limit, 0);
    assert!(config.report_path.is_none());
    assert!(config.extra_search_paths.is_empty());
}

// ════════════════════════════════════════════════════════════════════════════
// Report building tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_build_report_empty() {
    let batch = BatchSummary {
        root_dir: "/tmp/mathlib".to_string(),
        total_files: 0,
        processed_files: 0,
        load_success: 0,
        load_failure: 0,
        total_constants: 0,
        tc_pass: 0,
        tc_fail: 0,
        total_skipped: 0,
        total_elapsed_secs: 0.0,
        pass_rate_pct: 0.0,
        validation_mode: clean_olean::verify_batch::ValidationMode::InferOnly,
        validation_label: "type-only-infer".to_string(),
        error_categories: BTreeMap::new(),
        modules: Vec::new(),
    };
    let report = build_report(
        Path::new("/tmp/mathlib"),
        &batch,
        Vec::new(),
        Duration::from_secs(0),
    );
    assert_eq!(report.total_olean_files, 0);
    assert_eq!(report.modules_processed, 0);
    assert!(report.error_breakdown.is_empty());
    assert!(report.module_groups.is_empty());
}

/// Build a mixed-results report for reuse in multiple assertions.
fn build_mixed_report() -> MathLibVerifyReport {
    let files = vec![
        FileResult {
            module_name: "Mathlib.Data.Nat.Basic".to_string(),
            rel_path: "Mathlib/Data/Nat/Basic.olean".to_string(),
            verified_ok: true,
            constants_added: 50,
            tc_pass: 50,
            tc_fail: 0,
            elapsed_ms: 100,
            error_kind: None,
            error_detail: None,
        },
        FileResult {
            module_name: "Mathlib.Data.List.Defs".to_string(),
            rel_path: "Mathlib/Data/List/Defs.olean".to_string(),
            verified_ok: false,
            constants_added: 30,
            tc_pass: 25,
            tc_fail: 5,
            elapsed_ms: 200,
            error_kind: Some(MathLibErrorKind::TypeCheckFailed),
            error_detail: Some("type mismatch".to_string()),
        },
        FileResult {
            module_name: "Mathlib.Algebra.Group.Basic".to_string(),
            rel_path: "Mathlib/Algebra/Group/Basic.olean".to_string(),
            verified_ok: false,
            constants_added: 0,
            tc_pass: 0,
            tc_fail: 0,
            elapsed_ms: 10,
            error_kind: Some(MathLibErrorKind::OleanLoadFailed),
            error_detail: Some("failed to load .olean".to_string()),
        },
    ];

    let batch = BatchSummary {
        root_dir: "/tmp/mathlib".to_string(),
        total_files: 3,
        processed_files: 3,
        load_success: 2,
        load_failure: 1,
        total_constants: 80,
        tc_pass: 75,
        tc_fail: 5,
        total_skipped: 0,
        total_elapsed_secs: 0.31,
        pass_rate_pct: 93.75,
        validation_mode: clean_olean::verify_batch::ValidationMode::InferOnly,
        validation_label: "type-only-infer".to_string(),
        error_categories: BTreeMap::new(),
        modules: Vec::new(),
    };

    build_report(
        Path::new("/tmp/mathlib"),
        &batch,
        files,
        Duration::from_millis(310),
    )
}

#[test]
fn test_build_report_mixed_counts() {
    let report = build_mixed_report();
    assert_eq!(report.total_olean_files, 3);
    assert_eq!(report.modules_processed, 3);
    assert_eq!(report.tc_pass, 75);
    assert_eq!(report.tc_fail, 5);
}

#[test]
fn test_build_report_mixed_error_breakdown() {
    let report = build_mixed_report();
    assert_eq!(report.error_breakdown.len(), 2);
    assert_eq!(report.error_breakdown.get("type_check_failed"), Some(&1));
    assert_eq!(report.error_breakdown.get("olean_load_failed"), Some(&1));
}

#[test]
fn test_build_report_mixed_module_groups() {
    let report = build_mixed_report();
    assert_eq!(report.module_groups.len(), 2);

    let data_stats = report.module_groups.get("Mathlib.Data").unwrap();
    assert_eq!(data_stats.module_count, 2);
    assert_eq!(data_stats.tc_pass, 75);
    assert_eq!(data_stats.tc_fail, 5);

    let algebra_stats = report.module_groups.get("Mathlib.Algebra").unwrap();
    assert_eq!(algebra_stats.module_count, 1);
    assert_eq!(algebra_stats.load_failures, 1);
}

// ════════════════════════════════════════════════════════════════════════════
// FileResult construction tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_convert_module_result_success() {
    let mr = ModuleResult {
        path: "Mathlib/Data/Nat.olean".to_string(),
        module_name: "Mathlib.Data.Nat".to_string(),
        load_ok: true,
        constants_added: 42,
        constants_skipped: 0,
        tc_pass: 42,
        tc_fail: 0,
        elapsed_ms: 55,
        load_error: None,
        tc_errors: BTreeMap::new(),
    };
    let fr = convert_module_result(&mr);
    assert!(fr.verified_ok);
    assert_eq!(fr.constants_added, 42);
    assert_eq!(fr.tc_pass, 42);
    assert!(fr.error_kind.is_none());
    assert!(fr.error_detail.is_none());
}

#[test]
fn test_convert_module_result_load_failure() {
    let mr = ModuleResult {
        path: "Mathlib/Bad.olean".to_string(),
        module_name: "Mathlib.Bad".to_string(),
        load_ok: false,
        constants_added: 0,
        constants_skipped: 0,
        tc_pass: 0,
        tc_fail: 0,
        elapsed_ms: 5,
        load_error: Some("failed to load .olean file".to_string()),
        tc_errors: BTreeMap::new(),
    };
    let fr = convert_module_result(&mr);
    assert!(!fr.verified_ok);
    assert_eq!(fr.error_kind, Some(MathLibErrorKind::OleanLoadFailed));
    assert!(fr.error_detail.unwrap().contains("load"));
}

#[test]
fn test_convert_module_result_tc_failure() {
    let mut tc_errors = BTreeMap::new();
    tc_errors.insert("Foo.bar".to_string(), "type mismatch".to_string());
    let mr = ModuleResult {
        path: "Mathlib/Foo.olean".to_string(),
        module_name: "Mathlib.Foo".to_string(),
        load_ok: true,
        constants_added: 10,
        constants_skipped: 0,
        tc_pass: 8,
        tc_fail: 2,
        elapsed_ms: 30,
        load_error: None,
        tc_errors,
    };
    let fr = convert_module_result(&mr);
    assert!(!fr.verified_ok);
    assert_eq!(fr.error_kind, Some(MathLibErrorKind::TypeCheckFailed));
}

// ════════════════════════════════════════════════════════════════════════════
// MathLibVerifyError tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_verify_error_path_not_found() {
    let err = MathLibVerifyError::PathNotFound(PathBuf::from("/nonexistent"));
    let msg = err.to_string();
    assert!(msg.contains("/nonexistent"));
    assert!(msg.contains("does not exist"));
}

#[test]
fn test_verify_error_no_olean() {
    let err = MathLibVerifyError::NoOleanFiles(PathBuf::from("/empty"));
    let msg = err.to_string();
    assert!(msg.contains("/empty"));
    assert!(msg.contains("no .olean"));
}

// ════════════════════════════════════════════════════════════════════════════
// Config serde round-trip
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_config_serde_roundtrip() {
    let config = MathLibVerifyConfig {
        mathlib_path: PathBuf::from("/data/mathlib"),
        progress_interval: 50,
        stack_size_bytes: 8_388_608,
        heartbeat_limit: 200_000,
        report_path: Some(PathBuf::from("/tmp/report.json")),
        extra_search_paths: vec![PathBuf::from("/extra")],
    };
    let json = serde_json::to_string(&config).unwrap();
    let restored: MathLibVerifyConfig = serde_json::from_str(&json).unwrap();
    assert_eq!(config, restored);
}

// ════════════════════════════════════════════════════════════════════════════
// Report serde round-trip
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_report_serde_roundtrip() {
    let report = MathLibVerifyReport {
        mathlib_path: "/data/mathlib".to_string(),
        total_olean_files: 100,
        modules_processed: 100,
        modules_loaded: 95,
        modules_failed: 5,
        total_constants: 5000,
        tc_pass: 4800,
        tc_fail: 200,
        total_skipped: 0,
        pass_rate_pct: 96.0,
        total_elapsed_secs: 42.5,
        error_breakdown: BTreeMap::from([
            ("type_check_failed".to_string(), 3),
            ("olean_load_failed".to_string(), 2),
        ]),
        module_groups: BTreeMap::new(),
        files: Vec::new(),
    };
    let json = serde_json::to_string_pretty(&report).unwrap();
    let restored: MathLibVerifyReport = serde_json::from_str(&json).unwrap();
    assert_eq!(restored.total_olean_files, 100);
    assert_eq!(restored.tc_pass, 4800);
    assert_eq!(restored.error_breakdown.len(), 2);
}

// ════════════════════════════════════════════════════════════════════════════
// run_mathlib_verify error paths
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_run_mathlib_verify_path_not_found() {
    let config = MathLibVerifyConfig {
        mathlib_path: PathBuf::from("/nonexistent/mathlib/path"),
        ..Default::default()
    };
    let result = run_mathlib_verify(&config);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err, MathLibVerifyError::PathNotFound(_)));
}

#[test]
fn test_run_mathlib_verify_empty_dir() {
    let dir = tempfile::tempdir().unwrap();
    let config = MathLibVerifyConfig {
        mathlib_path: dir.path().to_path_buf(),
        ..Default::default()
    };
    let result = run_mathlib_verify(&config);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err, MathLibVerifyError::NoOleanFiles(_)));
}
