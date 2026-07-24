// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the elaboration error recovery module.

use clean_kernel::{Environment, Expr, Name};

use crate::error::ElabError;
use crate::error_recovery::{
    format_error_report, recover_decl, recover_expr, AccumulatedError, ErrorRecoveryCtx,
    RecoveredResult, RecoveryAction, RecoveryMode,
};

//Helpers

fn sample_error() -> ElabError {
    ElabError::UnknownIdent("x".into())
}

fn sample_type_error() -> ElabError {
    ElabError::TypeMismatch {
        expected: "Nat".into(),
        actual: "Bool".into(),
    }
}

fn sample_infer_error() -> ElabError {
    ElabError::CannotInfer
}

//RecoveryMode basics

#[test]
fn test_recovery_mode_strict_stops_immediately() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Strict);
    assert!(ctx.should_continue(), "no errors yet, should continue");

    ctx.record_error(sample_error(), None, "test", RecoveryAction::None);
    assert!(
        !ctx.should_continue(),
        "strict mode should stop after first error"
    );
}

#[test]
fn test_recovery_mode_lenient_continues_until_max() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Lenient).with_max_errors(3);

    ctx.record_error(sample_error(), None, "e1", RecoveryAction::InsertedSorry);
    assert!(ctx.should_continue(), "1 of 3 errors, should continue");

    ctx.record_error(sample_error(), None, "e2", RecoveryAction::InsertedSorry);
    assert!(ctx.should_continue(), "2 of 3 errors, should continue");

    ctx.record_error(sample_error(), None, "e3", RecoveryAction::InsertedSorry);
    assert!(
        !ctx.should_continue(),
        "3 of 3 errors, should stop in lenient mode"
    );
}

#[test]
fn test_recovery_mode_ide_never_stops() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Ide).with_max_errors(2);

    for i in 0..100 {
        ctx.record_error(
            sample_error(),
            None,
            &format!("e{i}"),
            RecoveryAction::InsertedSorry,
        );
        assert!(
            ctx.should_continue(),
            "IDE mode should always continue (after {i} errors)"
        );
    }
}

//Error accumulation

#[test]
fn test_error_count_and_has_errors() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Ide);
    assert_eq!(ctx.error_count(), 0);
    assert!(!ctx.has_errors());

    ctx.record_error(sample_error(), None, "", RecoveryAction::None);
    assert_eq!(ctx.error_count(), 1);
    assert!(ctx.has_errors());

    ctx.record_error(
        sample_type_error(),
        Some((10, 20)),
        "decl",
        RecoveryAction::InsertedSorry,
    );
    assert_eq!(ctx.error_count(), 2);
}

#[test]
fn test_sorry_count_tracks_inserted_sorry_only() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Ide);

    ctx.record_error(sample_error(), None, "", RecoveryAction::InsertedSorry);
    ctx.record_error(sample_error(), None, "", RecoveryAction::SkippedDeclaration);
    ctx.record_error(sample_error(), None, "", RecoveryAction::InsertedSorry);
    ctx.record_error(sample_error(), None, "", RecoveryAction::None);
    ctx.record_error(sample_error(), None, "", RecoveryAction::UsedFallbackType);

    assert_eq!(ctx.sorry_count(), 2, "only InsertedSorry should count");
    assert_eq!(ctx.error_count(), 5, "all errors should be recorded");
}

#[test]
fn test_record_error_preserves_span_and_context() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Ide);
    ctx.record_error(
        sample_error(),
        Some((42, 55)),
        "elaborating let-binding",
        RecoveryAction::InsertedSorry,
    );

    let result = ctx.into_result::<Expr>(None);
    assert_eq!(result.errors.len(), 1);

    let err = &result.errors[0];
    assert_eq!(err.span, Some((42, 55)));
    assert_eq!(err.context, "elaborating let-binding");
    assert_eq!(err.recovery_action, RecoveryAction::InsertedSorry);
}

//Sorry insertion

#[test]
fn test_make_sorry_term_returns_expr() {
    let env = Environment::new();
    let ctx = ErrorRecoveryCtx::new(RecoveryMode::Lenient);

    let sorry = ctx.make_sorry_term(&env, &Expr::prop());
    // The sorry term should be a well-formed Expr (not a panic).
    // We cannot check exact structure without inspecting the kernel internals,
    // but we can verify it does not panic and returns something.
    assert!(
        format!("{sorry:?}").contains("App") || format!("{sorry:?}").contains("Const"),
        "sorry term should be a kernel Expr, got: {sorry:?}"
    );
}

#[test]
fn test_make_sorry_type_returns_expr() {
    let env = Environment::new();
    let ctx = ErrorRecoveryCtx::new(RecoveryMode::Ide);

    let sorry = ctx.make_sorry_type(&env);
    assert!(
        format!("{sorry:?}").contains("App") || format!("{sorry:?}").contains("Const"),
        "sorry type should be a kernel Expr, got: {sorry:?}"
    );
}

#[test]
fn test_make_sorry_term_with_type_expr() {
    let env = Environment::new();
    let ctx = ErrorRecoveryCtx::new(RecoveryMode::Lenient);

    // sorry for Type universe
    let sorry = ctx.make_sorry_term(&env, &Expr::type_());
    let debug = format!("{sorry:?}");
    assert!(
        debug.contains("App") || debug.contains("Const"),
        "sorry for Type should be a valid Expr"
    );
}

//recover_expr

#[test]
fn test_recover_expr_with_known_type() {
    let env = Environment::new();
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Lenient);
    let expected_ty = Expr::prop();

    let sorry = recover_expr(
        &env,
        sample_error(),
        Some(&expected_ty),
        Some((0, 5)),
        "test expr",
        &mut ctx,
    );

    assert_eq!(ctx.error_count(), 1);
    assert_eq!(ctx.sorry_count(), 1);
    let debug = format!("{sorry:?}");
    assert!(
        debug.contains("App") || debug.contains("Const"),
        "should return a sorry Expr"
    );
}

#[test]
fn test_recover_expr_without_expected_type() {
    let env = Environment::new();
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Lenient);

    let sorry = recover_expr(&env, sample_error(), None, None, "no type", &mut ctx);

    assert_eq!(ctx.error_count(), 1);
    // UsedFallbackType does not count as InsertedSorry
    assert_eq!(ctx.sorry_count(), 0);
    let debug = format!("{sorry:?}");
    assert!(
        debug.contains("App") || debug.contains("Const"),
        "should return a sorry Expr even without expected type"
    );
}

//recover_decl

#[test]
fn test_recover_decl_records_skip() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Ide);
    let name = Name::from_string("MyDecl");

    let action = recover_decl(sample_error(), &name, &mut ctx);

    assert_eq!(action, RecoveryAction::SkippedDeclaration);
    assert_eq!(ctx.error_count(), 1);
    assert!(
        ctx.into_result::<()>(None).errors[0]
            .context
            .contains("MyDecl"),
        "context should mention declaration name"
    );
}

//RecoveredResult

#[test]
fn test_recovered_result_ok_is_complete() {
    let result = RecoveredResult::ok(42u64);
    assert!(result.is_complete);
    assert_eq!(result.sorry_count, 0);
    assert!(result.errors.is_empty());
    assert_eq!(result.value, Some(42));
}

#[test]
fn test_recovered_result_into_result_success() {
    let result = RecoveredResult::ok(99i32);
    let r = result.into_result();
    assert_eq!(r.expect("should be Ok"), 99);
}

#[test]
fn test_recovered_result_into_result_error() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Lenient);
    ctx.record_error(
        sample_type_error(),
        None,
        "test",
        RecoveryAction::InsertedSorry,
    );

    let result: RecoveredResult<Expr> = ctx.into_result(None);
    let err = result.into_result().expect_err("should be Err");
    match err {
        ElabError::TypeMismatch { expected, actual } => {
            assert_eq!(expected, "Nat");
            assert_eq!(actual, "Bool");
        }
        other => panic!("unexpected error variant: {other:?}"),
    }
}

#[test]
fn test_recovered_result_into_result_no_errors_no_value() {
    // Edge case: no errors but no value either (should not happen in practice).
    let ctx = ErrorRecoveryCtx::new(RecoveryMode::Strict);
    let result: RecoveredResult<i32> = ctx.into_result(None);
    // is_complete = true (no errors), but value = None, so into_result
    // falls through to Err.
    let err = result
        .into_result()
        .expect_err("should be Err with no value");
    matches!(err, ElabError::CannotInfer);
}

#[test]
fn test_into_result_from_ctx_with_value() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Lenient);
    ctx.record_error(sample_error(), None, "", RecoveryAction::InsertedSorry);

    let result = ctx.into_result(Some(42));
    assert!(!result.is_complete, "has errors, so not complete");
    assert_eq!(result.value, Some(42), "partial value should be preserved");
    assert_eq!(result.sorry_count, 1);
}

//format_error_report

#[test]
fn test_format_error_report_empty() {
    let report = format_error_report(&[]);
    assert_eq!(report, "no errors");
}

#[test]
fn test_format_error_report_single_error() {
    let errors = vec![AccumulatedError {
        error: sample_error(),
        span: Some((10, 20)),
        context: "elaborating x".into(),
        recovery_action: RecoveryAction::InsertedSorry,
    }];

    let report = format_error_report(&errors);
    assert!(report.contains("1 error(s):"), "header: {report}");
    assert!(report.contains("[10..20]"), "span: {report}");
    assert!(report.contains("elaborating x"), "context: {report}");
    assert!(report.contains("Unknown identifier: x"), "error: {report}");
    assert!(report.contains("inserted sorry"), "recovery: {report}");
}

#[test]
fn test_format_error_report_multiple_errors() {
    let errors = vec![
        AccumulatedError {
            error: sample_error(),
            span: None,
            context: String::new(),
            recovery_action: RecoveryAction::None,
        },
        AccumulatedError {
            error: sample_type_error(),
            span: Some((100, 200)),
            context: "let-binding".into(),
            recovery_action: RecoveryAction::InsertedSorry,
        },
        AccumulatedError {
            error: sample_infer_error(),
            span: None,
            context: "match arm".into(),
            recovery_action: RecoveryAction::SkippedDeclaration,
        },
    ];

    let report = format_error_report(&errors);
    assert!(report.contains("3 error(s):"), "count: {report}");
    assert!(report.contains("1."), "numbering: {report}");
    assert!(report.contains("2."), "numbering: {report}");
    assert!(report.contains("3."), "numbering: {report}");
}

//Mode accessor

#[test]
fn test_mode_accessor() {
    let ctx = ErrorRecoveryCtx::new(RecoveryMode::Strict);
    assert_eq!(ctx.mode(), RecoveryMode::Strict);

    let ctx = ErrorRecoveryCtx::new(RecoveryMode::Ide);
    assert_eq!(ctx.mode(), RecoveryMode::Ide);
}

//with_max_errors builder

#[test]
fn test_with_max_errors_one() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Lenient).with_max_errors(1);
    assert!(ctx.should_continue());

    ctx.record_error(sample_error(), None, "", RecoveryAction::None);
    assert!(!ctx.should_continue(), "max_errors=1 should stop after 1");
}

#[test]
fn test_with_max_errors_zero_stops_immediately() {
    let ctx = ErrorRecoveryCtx::new(RecoveryMode::Lenient).with_max_errors(0);
    // Even with 0 errors recorded, len (0) >= max (0), so should_continue = false
    assert!(!ctx.should_continue(), "max_errors=0 should never continue");
}

//AccumulatedError Display

#[test]
fn test_accumulated_error_display_with_all_fields() {
    let err = AccumulatedError {
        error: sample_error(),
        span: Some((5, 10)),
        context: "foo".into(),
        recovery_action: RecoveryAction::InsertedSorry,
    };
    let s = format!("{err}");
    assert!(s.contains("[5..10]"), "span: {s}");
    assert!(s.contains("(foo)"), "context: {s}");
    assert!(s.contains("Unknown identifier: x"), "error: {s}");
    assert!(s.contains("[recovery: inserted sorry]"), "recovery: {s}");
}

#[test]
fn test_accumulated_error_display_no_recovery_action() {
    let err = AccumulatedError {
        error: sample_error(),
        span: None,
        context: String::new(),
        recovery_action: RecoveryAction::None,
    };
    let s = format!("{err}");
    assert!(
        !s.contains("[recovery:"),
        "None recovery should not be shown: {s}"
    );
}

//RecoveryAction Display

#[test]
fn test_recovery_action_display() {
    assert_eq!(
        format!("{}", RecoveryAction::InsertedSorry),
        "inserted sorry"
    );
    assert_eq!(
        format!("{}", RecoveryAction::SkippedDeclaration),
        "skipped declaration"
    );
    assert_eq!(
        format!("{}", RecoveryAction::UsedFallbackType),
        "used fallback type"
    );
    assert_eq!(format!("{}", RecoveryAction::None), "none");
}

//Edge cases

#[test]
fn test_strict_mode_still_records_errors() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Strict);
    ctx.record_error(sample_error(), None, "a", RecoveryAction::None);
    ctx.record_error(sample_type_error(), None, "b", RecoveryAction::None);

    // Even though should_continue is false, errors are still accumulated
    assert_eq!(ctx.error_count(), 2);
    assert!(!ctx.should_continue());
}

#[test]
fn test_lenient_mode_default_max_errors() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Lenient);
    // Default max is 50 — record 49 and check
    for i in 0..49 {
        ctx.record_error(
            sample_error(),
            None,
            &format!("e{i}"),
            RecoveryAction::InsertedSorry,
        );
        assert!(ctx.should_continue(), "should continue at {i}");
    }
    ctx.record_error(sample_error(), None, "e49", RecoveryAction::InsertedSorry);
    assert!(
        !ctx.should_continue(),
        "should stop at default max_errors (50)"
    );
}

#[test]
fn test_multiple_sorry_insertions_count_correctly() {
    let env = Environment::new();
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Ide);

    for _ in 0..5 {
        let _ = recover_expr(
            &env,
            sample_error(),
            Some(&Expr::prop()),
            None,
            "",
            &mut ctx,
        );
    }

    assert_eq!(ctx.sorry_count(), 5);
    assert_eq!(ctx.error_count(), 5);
}

#[test]
fn test_recovered_result_preserves_all_errors() {
    let mut ctx = ErrorRecoveryCtx::new(RecoveryMode::Ide);
    ctx.record_error(sample_error(), None, "first", RecoveryAction::InsertedSorry);
    ctx.record_error(
        sample_type_error(),
        Some((1, 2)),
        "second",
        RecoveryAction::None,
    );
    ctx.record_error(
        sample_infer_error(),
        None,
        "third",
        RecoveryAction::SkippedDeclaration,
    );

    let result: RecoveredResult<()> = ctx.into_result(None);
    assert_eq!(result.errors.len(), 3);
    assert_eq!(result.errors[0].context, "first");
    assert_eq!(result.errors[1].context, "second");
    assert_eq!(result.errors[2].context, "third");
}
