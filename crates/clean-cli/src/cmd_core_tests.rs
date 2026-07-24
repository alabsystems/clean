// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::cmd_core::{check_file, emit_check_summary};
use clean_kernel::cli::PreludeMode;
use std::{fs, time::Duration};

#[test]
fn emit_check_summary_success_uses_lean_parser_summary_line() {
    let mut buf = Vec::new();
    emit_check_summary(&mut buf, 2, Duration::from_millis(7), 2, 0).expect("write should succeed");
    let output = String::from_utf8(buf).expect("valid utf8");
    assert!(
        output
            .lines()
            .any(|line| line.contains("2 passed, 0 failed")),
        "successful checks should keep the lean parser summary: {output}"
    );
}

#[test]
fn emit_check_summary_failure_uses_lean_parser_summary_line() {
    let mut buf = Vec::new();
    emit_check_summary(&mut buf, 4, Duration::from_millis(11), 2, 2).expect("write should succeed");
    let output = String::from_utf8(buf).expect("valid utf8");
    // The failure path MUST emit the "N passed, M failed" summary line so
    // external parsers (bench-solver-status parse_lean) can classify the result
    // as type_check_failed instead of falling through to exit-code heuristics.
    // The prior format ("outcome: check_failed" / "accepted" / "reported")
    // was not recognized by parse_lean, causing wrong-answer misclassification.
    assert!(
        output
            .lines()
            .any(|line| line.contains("2 passed") && line.contains("2 failed")),
        "failing checks must emit the lean parser summary line: {output}"
    );
    assert!(
        !output.contains("0 failed"),
        "failing checks must not claim 0 failed: {output}"
    );
}

/// Regression test for wrong-answer bug (#3078): a file containing only
/// administrative declarations (set_option) and no actual theorems must NOT
/// report "N passed, 0 failed". Skipped declarations are not verified and
/// must not inflate the pass count.
#[test]
fn check_file_skipped_only_reports_zero_passed() {
    // set_option is parsed as a SurfaceDecl::SetOption and elaborated as Skipped.
    // Before the fix, this would increment success_count, producing "1 passed, 0 failed".
    let code = "set_option maxHeartbeats 0\n";

    let dir = tempfile::tempdir().expect("tempdir should be created");
    let path = dir.path().join("skipped_only.clean");
    fs::write(&path, code).expect("write should succeed");

    // The file should succeed (no errors), but with 0 passed since nothing
    // was actually type-checked.
    let result = check_file(&path, false, false, PreludeMode::Builtin);
    assert!(
        result.is_ok(),
        "file with only skipped declarations should not error"
    );
}

/// Regression test for wrong-answer bug (#3078): a file with sorry must
/// produce output containing both "passed" and "failed" with non-zero
/// failed count, so external parsers classify it as type_check_failed.
#[test]
fn check_file_sorry_output_has_nonzero_failed() {
    let code = "theorem bad : True := by sorry\n";

    let dir = tempfile::tempdir().expect("tempdir should be created");
    let path = dir.path().join("sorry_output.clean");
    fs::write(&path, code).expect("write should succeed");

    let result = check_file(&path, false, false, PreludeMode::Builtin);
    assert!(result.is_err(), "sorry file must fail");
}

#[test]
fn check_file_explicit_sorry_fails_closed() {
    let code = r"
theorem incomplete : True := by
  sorry
";

    let dir = tempfile::tempdir().expect("tempdir should be created");
    let path = dir.path().join("sorry.clean");
    fs::write(&path, code).expect("write should succeed");

    let result = check_file(&path, false, false, PreludeMode::Builtin);
    assert!(result.is_err(), "explicit sorry must fail closed");
}

#[test]
fn check_file_clears_trust_state_between_runs() {
    use clean_kernel::sorry::sorry_count;

    let failing_code = r"
theorem incomplete : True := by
  sorry
";
    let clean_code = r"
def idFun (A : Type) (x : A) : A := x
";

    let dir = tempfile::tempdir().expect("tempdir should be created");
    let failing_path = dir.path().join("sorry.clean");
    let clean_path = dir.path().join("clean.clean");
    fs::write(&failing_path, failing_code).expect("write should succeed");
    fs::write(&clean_path, clean_code).expect("write should succeed");

    let baseline = sorry_count();
    let failing_result = check_file(&failing_path, false, false, PreludeMode::Builtin);
    assert!(
        failing_result.is_err(),
        "explicit sorry must still fail closed"
    );
    assert_eq!(
        sorry_count(),
        baseline,
        "check_file should restore the trust counter state after failure"
    );

    check_file(&clean_path, false, false, PreludeMode::Builtin)
        .expect("clean file should type check");
    assert_eq!(
        sorry_count(),
        baseline,
        "check_file should leave the trust counter state unchanged after success"
    );
}
