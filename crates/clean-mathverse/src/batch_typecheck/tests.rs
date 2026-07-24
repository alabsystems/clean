// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use tempfile::tempdir;

use super::*;

fn statement(name: &str, paper_id: &str, lean_code: &str) -> Statement {
    Statement {
        name: name.to_owned(),
        paper_id: paper_id.to_owned(),
        lean_code: lean_code.to_owned(),
    }
}

fn statuses(results: &[StatementResult]) -> Vec<&TypecheckStatus> {
    results.iter().map(|r| &r.status).collect()
}

#[test]
fn test_batch_typecheck_empty_input() {
    let report = batch_typecheck(&[], &BatchTypecheckConfig::default());
    assert_eq!(report.total, 0);
    assert_eq!(report.passed, 0);
    assert_eq!(report.failed, 0);
    assert_eq!(report.timed_out, 0);
    assert_eq!(report.skipped, 0);
    assert_eq!(report.pass_rate, 0.0);
    assert!(report.results.is_empty());
}

#[test]
fn test_batch_typecheck_all_pass() {
    let stmts = vec![
        statement("thm1", "2401.00001", "theorem foo : True := by trivial"),
        statement("thm2", "2401.00001", "def bar : Nat := 3"),
    ];
    let report = batch_typecheck(&stmts, &BatchTypecheckConfig::default());
    assert_eq!(report.total, 2);
    assert_eq!(report.passed, 2);
    assert!(report
        .results
        .iter()
        .all(|r| matches!(r.status, TypecheckStatus::Passed)));
}

#[test]
fn test_batch_typecheck_sorry_skip() {
    let stmts = vec![statement(
        "thm1",
        "2401.00002",
        "theorem foo : True := by sorry",
    )];
    let report = batch_typecheck(&stmts, &BatchTypecheckConfig::default());
    assert_eq!(report.skipped, 1);
    assert_eq!(report.passed, 0);
    assert!(matches!(
        &report.results[0].status,
        TypecheckStatus::Skipped(_)
    ));
}

#[test]
fn test_batch_typecheck_sorry_allowed() {
    let stmts = vec![statement(
        "thm1",
        "2401.00003",
        "theorem foo : True := by sorry",
    )];
    let config = BatchTypecheckConfig {
        allow_sorry: true,
        ..Default::default()
    };
    let report = batch_typecheck(&stmts, &config);
    assert_eq!(report.passed, 1);
    assert!(matches!(&report.results[0].status, TypecheckStatus::Passed));
}

#[test]
fn test_batch_typecheck_invalid_code() {
    let stmts = vec![statement("bad", "2401.00004", "axiom foo : True")];
    let report = batch_typecheck(&stmts, &BatchTypecheckConfig::default());
    assert_eq!(report.failed, 1);
    assert!(matches!(
        &report.results[0].status,
        TypecheckStatus::Failed(_)
    ));
}

#[test]
fn test_batch_typecheck_mixed() {
    let stmts = vec![
        statement("pass", "2401.00005", "theorem ok : True := by trivial"),
        statement("fail", "2401.00005", "axiom bad : True"),
        statement("skip", "2401.00005", "def tmp : Nat := by sorry"),
    ];
    let report = batch_typecheck(&stmts, &BatchTypecheckConfig::default());
    assert_eq!(report.total, 3);
    assert_eq!(report.passed, 1);
    assert_eq!(report.failed, 1);
    assert_eq!(report.skipped, 1);
}

#[test]
fn test_timing_stats_computation() {
    let timings = [10, 20, 30, 40, 50];
    let (mean, median, p99) = compute_timing_stats(&timings);
    assert_eq!(mean, 30.0);
    assert_eq!(median, 30.0);
    assert_eq!(p99, 50.0);
}

#[test]
fn test_save_load_round_trip() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("report.json");
    let report = BatchReport {
        total: 1,
        passed: 1,
        failed: 0,
        timed_out: 0,
        skipped: 0,
        pass_rate: 1.0,
        mean_elapsed_ms: 12.0,
        median_elapsed_ms: 12.0,
        p99_elapsed_ms: 12.0,
        total_elapsed_ms: 12,
        results: vec![StatementResult {
            name: "thm1".to_owned(),
            paper_id: "2401.00006".to_owned(),
            lean_code: "theorem foo : True := by trivial".to_owned(),
            status: TypecheckStatus::Passed,
            elapsed_ms: 12,
            error_detail: None,
        }],
    };
    save_report(&report, &path).unwrap();
    let loaded = load_report(&path).unwrap();
    assert_eq!(loaded, report);
}

#[test]
fn test_parallel_same_as_serial() {
    let stmts = vec![
        statement("a", "2401.00007", "theorem a : True := by trivial"),
        statement("b", "2401.00007", "axiom b : True"),
        statement("c", "2401.00007", "def c : Nat := by sorry"),
        statement("d", "2401.00007", "def d : Nat := 42"),
    ];
    let serial = batch_typecheck(
        &stmts,
        &BatchTypecheckConfig {
            max_parallel: 1,
            ..Default::default()
        },
    );
    let parallel = batch_typecheck(
        &stmts,
        &BatchTypecheckConfig {
            max_parallel: 4,
            ..Default::default()
        },
    );
    assert_eq!(serial.total, parallel.total);
    assert_eq!(serial.passed, parallel.passed);
    assert_eq!(serial.failed, parallel.failed);
    assert_eq!(serial.skipped, parallel.skipped);
    assert_eq!(statuses(&serial.results), statuses(&parallel.results));
}
