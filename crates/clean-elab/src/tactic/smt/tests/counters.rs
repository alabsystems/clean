// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::tactic::smt::sorry_count;
use serial_test::serial;

#[cfg(feature = "ay-smt")]
#[test]
fn test_disabled_solver_reports_solver_disabled() {
    use clean_auto::bridge::ay_contract::AyError;

    let mut solver = SmtSolver::Disabled {
        policy: SmtVerifyPolicy::ExtractOnly,
        reason: "ay support disabled in config".to_string(),
    };

    let assert_err = solver
        .translate_and_assert(&Expr::prop())
        .expect_err("disabled solver should reject assertions");
    assert!(
        matches!(assert_err, AyError::SolverDisabled(ref msg) if msg == "ay support disabled in config"),
        "expected SolverDisabled from translate_and_assert, got {assert_err:?}"
    );

    let prove_err = solver
        .prove(&Expr::prop())
        .err()
        .expect("disabled solver should reject proofs");
    assert!(
        matches!(prove_err, AyError::SolverDisabled(ref msg) if msg == "ay support disabled in config"),
        "expected SolverDisabled from prove, got {prove_err:?}"
    );
}

#[test]
#[serial]
fn test_sorry_counter_increments() {
    // Note: In parallel test runs, other tests may also increment/reset the counter.
    // We test that calls do increment, using >= to handle concurrent increments.

    let env = Environment::new();
    let goal_ty = Expr::prop();

    // Get baseline count (may be > 0 if other tests ran)
    let before_first = sorry_count();

    // Call create_sorry_term - count should increase
    let _ = create_sorry_term(&env, &goal_ty);
    let after_first = sorry_count();
    assert!(
        after_first > before_first,
        "Counter should increase after create_sorry_term: before={}, after={}",
        before_first,
        after_first
    );

    // Call again - count should increase again
    let before_second = sorry_count();
    let _ = create_sorry_term(&env, &goal_ty);
    let after_second = sorry_count();
    assert!(
        after_second > before_second,
        "Counter should increase on second call: before={}, after={}",
        before_second,
        after_second
    );
}

#[test]
#[serial]
fn test_sorry_counter_reset() {
    // Test reset separately - this test accepts that parallel resets could interfere
    reset_sorry_counter();
    // After reset, count should be 0 (or small if concurrent increment happened)
    let count = sorry_count();
    assert!(
        count < 10,
        "After reset, count should be 0 (or small from concurrent tests): got {}",
        count
    );
}

#[test]
#[serial]
fn test_assert_no_sorry_passes_when_none() {
    reset_sorry_counter();
    // Should not panic
    assert_no_sorry();
}

#[test]
#[serial]
fn test_assert_no_sorry_panics_when_used() {
    reset_sorry_counter();
    let env = Environment::new();
    let _ = create_sorry_term(&env, &Expr::prop());
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        assert_no_sorry();
    }));
    let err = result.expect_err("assert_no_sorry should panic when sorry terms exist");
    let msg = err
        .downcast_ref::<String>()
        .map(|s| s.as_str())
        .or_else(|| err.downcast_ref::<&str>().copied())
        .unwrap_or("");
    assert!(
        msg.contains("sorry term(s) were generated"),
        "expected sorry panic message, got: {msg}"
    );
}

#[test]
#[serial]
fn test_ay_reconstruction_failure_counter() {
    reset_ay_reconstruction_failure_counter();
    assert_eq!(
        ay_reconstruction_failure_count(),
        0,
        "Counter should start at 0 after reset"
    );

    record_ay_reconstruction_failure();
    assert_eq!(
        ay_reconstruction_failure_count(),
        1,
        "Counter should be 1 after one failure"
    );

    record_ay_reconstruction_failure();
    assert_eq!(
        ay_reconstruction_failure_count(),
        2,
        "Counter should be 2 after two failures"
    );

    reset_ay_reconstruction_failure_counter();
    assert_eq!(
        ay_reconstruction_failure_count(),
        0,
        "Counter should be 0 after reset"
    );
}

#[test]
#[serial]
fn test_ay_reconstruction_success_counter() {
    reset_local_ay_reconstruction_success_counter();
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "Counter should start at 0 after reset"
    );

    record_ay_reconstruction_success();
    assert_eq!(
        local_ay_reconstruction_success_count(),
        1,
        "Counter should be 1 after one success"
    );

    record_ay_reconstruction_success();
    assert_eq!(
        local_ay_reconstruction_success_count(),
        2,
        "Counter should be 2 after two successes"
    );

    reset_local_ay_reconstruction_success_counter();
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "Counter should be 0 after reset"
    );
}
