// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `verify_report` module.

use crate::verify_batch::{error_category, BatchSummary, ModuleResult};
use crate::verify_report::{
    abbreviate, build_verification_report, compute_timing_stats, format_epoch_as_iso8601,
    write_report_to_file,
};
use std::collections::BTreeMap;

fn make_module(name: &str, pass: usize, fail: usize, ms: u64) -> ModuleResult {
    ModuleResult {
        path: format!("{name}.olean"),
        module_name: name.to_string(),
        load_ok: true,
        constants_added: pass + fail,
        constants_skipped: 0,
        tc_pass: pass,
        tc_fail: fail,
        elapsed_ms: ms,
        load_error: None,
        tc_errors: BTreeMap::new(),
    }
}

fn make_failing_module(name: &str, errors: Vec<(&str, &str)>) -> ModuleResult {
    let mut tc_errors = BTreeMap::new();
    for (cname, msg) in &errors {
        tc_errors.insert(cname.to_string(), msg.to_string());
    }
    ModuleResult {
        path: format!("{name}.olean"),
        module_name: name.to_string(),
        load_ok: true,
        constants_added: errors.len(),
        constants_skipped: 0,
        tc_pass: 0,
        tc_fail: errors.len(),
        elapsed_ms: 10,
        load_error: None,
        tc_errors,
    }
}

fn make_summary(modules: Vec<ModuleResult>) -> BatchSummary {
    let tc_pass: usize = modules.iter().map(|m| m.tc_pass).sum();
    let tc_fail: usize = modules.iter().map(|m| m.tc_fail).sum();
    let total_constants: usize = modules.iter().map(|m| m.constants_added).sum();
    let pass_rate = if tc_pass + tc_fail > 0 {
        tc_pass as f64 / (tc_pass + tc_fail) as f64 * 100.0
    } else {
        0.0
    };
    let mut error_categories = BTreeMap::new();
    for m in &modules {
        for err in m.tc_errors.values() {
            *error_categories
                .entry(error_category(err))
                .or_insert(0usize) += 1;
        }
    }
    BatchSummary {
        root_dir: "/test".to_string(),
        total_files: modules.len(),
        processed_files: modules.len(),
        load_success: modules.iter().filter(|m| m.load_ok).count(),
        load_failure: modules.iter().filter(|m| !m.load_ok).count(),
        total_constants,
        tc_pass,
        tc_fail,
        total_skipped: 0,
        total_elapsed_secs: 1.5,
        pass_rate_pct: pass_rate,
        validation_mode: crate::verify_batch::ValidationMode::InferOnly,
        validation_label: crate::verify_batch::ValidationMode::InferOnly
            .honest_label()
            .to_string(),
        error_categories,
        modules,
    }
}

#[test]
fn test_build_report_empty_modules() {
    let summary = make_summary(vec![]);
    let report = build_verification_report(&summary, None);
    assert_eq!(report.version, "1.0");
    assert_eq!(report.constants_total, 0);
    assert_eq!(report.types_ok, 0);
    assert_eq!(report.types_fail, 0);
    assert!(report.failures.is_empty());
    assert_eq!(report.timing_stats.count, 0);
    assert!(report.modules.is_empty());
}

#[test]
fn test_build_report_all_pass() {
    let modules = vec![
        make_module("Init.Prelude", 100, 0, 50),
        make_module("Init.Core", 200, 0, 30),
    ];
    let summary = make_summary(modules);
    let report = build_verification_report(&summary, None);

    assert_eq!(report.constants_total, 300);
    assert_eq!(report.types_ok, 300);
    assert_eq!(report.types_fail, 0);
    assert_eq!(report.pass_rate_pct, 100.0);
    assert!(report.failures.is_empty());
    assert_eq!(report.modules.len(), 2);
}

#[test]
fn test_build_report_with_failures() {
    let mut modules = vec![make_module("Init.Prelude", 100, 0, 50)];
    modules.push(make_failing_module(
        "Init.Core",
        vec![
            ("Nat.add", "HeartbeatExceeded"),
            ("Bool.and", "type mismatch in application"),
        ],
    ));
    let summary = make_summary(modules);
    let report = build_verification_report(&summary, None);

    assert_eq!(report.types_fail, 2);
    assert_eq!(report.failures.len(), 2);

    let hb_failure = report
        .failures
        .iter()
        .find(|f| f.constant == "Nat.add")
        .expect("should have Nat.add failure");
    assert_eq!(hb_failure.category, "HeartbeatExceeded");
    assert_eq!(hb_failure.module, "Init.Core");

    let tm_failure = report
        .failures
        .iter()
        .find(|f| f.constant == "Bool.and")
        .expect("should have Bool.and failure");
    assert_eq!(tm_failure.category, "TypeMismatch");
}

#[test]
fn test_timing_stats_single_module() {
    let modules = vec![make_module("A", 10, 0, 42)];
    let stats = compute_timing_stats(&modules);
    assert_eq!(stats.count, 1);
    assert_eq!(stats.min_ms, 42);
    assert_eq!(stats.max_ms, 42);
    assert!((stats.avg_ms - 42.0).abs() < f64::EPSILON);
    assert_eq!(stats.median_ms, 42);
    assert_eq!(stats.p99_ms, 42);
    assert_eq!(stats.total_ms, 42);
}

#[test]
fn test_timing_stats_multiple_modules() {
    let modules = vec![
        make_module("A", 1, 0, 10),
        make_module("B", 1, 0, 20),
        make_module("C", 1, 0, 30),
        make_module("D", 1, 0, 100),
    ];
    let stats = compute_timing_stats(&modules);
    assert_eq!(stats.count, 4);
    assert_eq!(stats.min_ms, 10);
    assert_eq!(stats.max_ms, 100);
    assert!((stats.avg_ms - 40.0).abs() < f64::EPSILON);
    // median of [10, 20, 30, 100] at index 2 = 30
    assert_eq!(stats.median_ms, 30);
    assert_eq!(stats.p99_ms, 100);
    assert_eq!(stats.total_ms, 160);
}

#[test]
fn test_abbreviate_short_string() {
    let s = "hello";
    assert_eq!(abbreviate(s, 10), "hello");
}

#[test]
fn test_abbreviate_long_string() {
    let s = "a".repeat(300);
    let result = abbreviate(&s, 200);
    assert!(result.len() <= 200);
    assert!(result.ends_with("..."));
}

#[test]
fn test_iso8601_epoch_zero() {
    let ts = format_epoch_as_iso8601(0);
    assert_eq!(ts, "1970-01-01T00:00:00Z");
}

#[test]
fn test_iso8601_known_date() {
    // 2026-01-01T00:00:00Z = 1767225600
    let ts = format_epoch_as_iso8601(1_767_225_600);
    assert_eq!(ts, "2026-01-01T00:00:00Z");
}

#[test]
fn test_report_serializes_to_json() {
    let modules = vec![
        make_module("Init.Prelude", 50, 0, 25),
        make_failing_module("Init.Core", vec![("Nat.add", "HeartbeatExceeded")]),
    ];
    let summary = make_summary(modules);
    let report = build_verification_report(&summary, None);
    let json = serde_json::to_string_pretty(&report).expect("report should serialize");
    assert!(json.contains("\"version\": \"1.0\""));
    assert!(json.contains("\"types_ok\": 50"));
    assert!(json.contains("\"HeartbeatExceeded\""));
    // AUDIT-CRITICAL: the honest validation-mode label must be present in the
    // serialized report. make_summary uses InferOnly (type-only), so the report
    // must NOT claim the proof values were kernel-verified.
    assert!(
        json.contains("\"validation_mode\": \"type-only-infer\""),
        "report JSON must carry the honest type-only label"
    );
    assert!(
        json.contains("\"kernel_verified_values\": false"),
        "type-only report must not claim kernel-verified values"
    );
}

#[test]
fn test_write_report_to_file() {
    let dir = tempfile::tempdir().expect("should create tempdir");
    let path = dir.path().join("subdir").join("report.json");

    let modules = vec![make_module("Init", 10, 0, 5)];
    let summary = make_summary(modules);
    let report = build_verification_report(&summary, None);
    write_report_to_file(&report, &path).expect("should write report");

    let contents = std::fs::read_to_string(&path).expect("should read file");
    let parsed: serde_json::Value = serde_json::from_str(&contents).expect("should parse JSON");
    assert_eq!(parsed["version"], "1.0");
    assert_eq!(parsed["types_ok"], 10);
}

#[test]
fn test_report_error_categories_from_error_summary() {
    use crate::verify_parallel::{CategoryDetail, ErrorSummary};

    let modules = vec![make_failing_module(
        "Init.Core",
        vec![("Nat.add", "HeartbeatExceeded")],
    )];
    let summary = make_summary(modules);

    let mut by_category = BTreeMap::new();
    by_category.insert(
        "HeartbeatExceeded".to_string(),
        CategoryDetail {
            count: 1,
            examples: vec!["Nat.add".to_string()],
        },
    );
    let error_summary = ErrorSummary {
        total_errors: 1,
        by_category,
    };

    let report = build_verification_report(&summary, Some(&error_summary));
    assert_eq!(report.error_categories.get("HeartbeatExceeded"), Some(&1));
}

#[test]
fn test_load_failure_module_in_report() {
    let fail_mod = ModuleResult {
        path: "Bad.olean".to_string(),
        module_name: "Bad".to_string(),
        load_ok: false,
        constants_added: 0,
        constants_skipped: 0,
        tc_pass: 0,
        tc_fail: 0,
        elapsed_ms: 1,
        load_error: Some("I/O error: not found".to_string()),
        tc_errors: BTreeMap::new(),
    };
    let summary = make_summary(vec![fail_mod]);
    let report = build_verification_report(&summary, None);

    assert_eq!(report.modules_load_fail, 1);
    assert!(!report.modules[0].load_ok);
    assert!(report.modules[0].load_error.is_some());
}
