// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the enhanced error recovery extension module.

use clean_kernel::{Environment, Expr};

use crate::error::ElabError;
use crate::error_recovery_ext::{
    format_error_report, merge_error_summaries, synthesize_sorry, try_elaborate_with_recovery,
    ErrorSeverity, ErrorSummary, LocatedError, LocatedWarning, RecoveryConfig, RecoveryContext,
    RecoveryResult, RecoveryStrategy,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

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

fn make_ctx() -> RecoveryContext {
    RecoveryContext::new(RecoveryConfig::default())
}

fn make_ctx_with_max(max: usize) -> RecoveryContext {
    RecoveryContext::new(RecoveryConfig::new().with_max_errors(max))
}

// ---------------------------------------------------------------------------
// RecoveryStrategy display
// ---------------------------------------------------------------------------

#[test]
fn test_recovery_strategy_display() {
    assert_eq!(format!("{}", RecoveryStrategy::InsertSorry), "insert sorry");
    assert_eq!(
        format!("{}", RecoveryStrategy::UseExpectedType),
        "use expected type"
    );
    assert_eq!(format!("{}", RecoveryStrategy::SkipToken), "skip token");
    assert_eq!(
        format!("{}", RecoveryStrategy::InsertPlaceholder),
        "insert placeholder"
    );
    assert_eq!(format!("{}", RecoveryStrategy::BestEffort), "best effort");
}

// ---------------------------------------------------------------------------
// ErrorSeverity
// ---------------------------------------------------------------------------

#[test]
fn test_error_severity_display() {
    assert_eq!(format!("{}", ErrorSeverity::Hint), "hint");
    assert_eq!(format!("{}", ErrorSeverity::Info), "info");
    assert_eq!(format!("{}", ErrorSeverity::Warning), "warning");
    assert_eq!(format!("{}", ErrorSeverity::Error), "error");
}

#[test]
fn test_error_severity_equality() {
    assert_eq!(ErrorSeverity::Error, ErrorSeverity::Error);
    assert_ne!(ErrorSeverity::Error, ErrorSeverity::Warning);
    assert_ne!(ErrorSeverity::Info, ErrorSeverity::Hint);
}

// ---------------------------------------------------------------------------
// LocatedError display
// ---------------------------------------------------------------------------

#[test]
fn test_located_error_display_full() {
    let err = LocatedError {
        error: sample_error(),
        span: Some((10, 20)),
        context: "let binding".into(),
        severity: ErrorSeverity::Error,
    };
    let s = format!("{err}");
    assert!(s.contains("error:"), "severity: {s}");
    assert!(s.contains("[10..20]"), "span: {s}");
    assert!(s.contains("(let binding)"), "context: {s}");
    assert!(s.contains("Unknown identifier: x"), "error message: {s}");
}

#[test]
fn test_located_error_display_no_span() {
    let err = LocatedError {
        error: sample_infer_error(),
        span: None,
        context: String::new(),
        severity: ErrorSeverity::Warning,
    };
    let s = format!("{err}");
    assert!(s.contains("warning:"), "severity: {s}");
    assert!(!s.contains('['), "no span: {s}");
}

#[test]
fn test_located_error_display_no_context() {
    let err = LocatedError {
        error: sample_type_error(),
        span: Some((0, 5)),
        context: String::new(),
        severity: ErrorSeverity::Error,
    };
    let s = format!("{err}");
    assert!(!s.contains("()"), "no empty context parens: {s}");
    assert!(s.contains("[0..5]"), "span present: {s}");
}

// ---------------------------------------------------------------------------
// LocatedWarning display
// ---------------------------------------------------------------------------

#[test]
fn test_located_warning_display_with_span() {
    let w = LocatedWarning {
        message: "unused variable".into(),
        span: Some((5, 8)),
    };
    let s = format!("{w}");
    assert!(s.contains("warning"), "prefix: {s}");
    assert!(s.contains("[5..8]"), "span: {s}");
    assert!(s.contains("unused variable"), "message: {s}");
}

#[test]
fn test_located_warning_display_no_span() {
    let w = LocatedWarning {
        message: "shadowed binding".into(),
        span: None,
    };
    let s = format!("{w}");
    assert!(s.contains("warning:"), "prefix: {s}");
    assert!(!s.contains('['), "no span: {s}");
}

// ---------------------------------------------------------------------------
// RecoveryConfig defaults and builder
// ---------------------------------------------------------------------------

#[test]
fn test_recovery_config_defaults() {
    let cfg = RecoveryConfig::default();
    assert_eq!(cfg.max_errors, 50);
    assert_eq!(cfg.recovery_depth_limit, 10);
    assert!(!cfg.strategies.is_empty());
}

#[test]
fn test_recovery_config_builder() {
    let cfg = RecoveryConfig::new()
        .with_max_errors(10)
        .with_recovery_depth_limit(5)
        .with_report_all(true)
        .with_strategies(vec![RecoveryStrategy::InsertSorry]);
    assert_eq!(cfg.max_errors, 10);
    assert_eq!(cfg.recovery_depth_limit, 5);
    assert!(cfg.report_all);
    assert_eq!(cfg.strategies.len(), 1);
}

// ---------------------------------------------------------------------------
// RecoveryContext basics
// ---------------------------------------------------------------------------

#[test]
fn test_recovery_context_initial_state() {
    let ctx = make_ctx();
    assert_eq!(ctx.errors.len(), 0);
    assert!(ctx.errors.is_empty());
    assert_eq!(ctx.sorry_terms.len(), 0);
    assert!(ctx.errors.len() < ctx.config.max_errors);
    assert_eq!(ctx.checkpoints.len(), 0);
}

#[test]
fn test_recovery_context_record_error() {
    let mut ctx = make_ctx();
    ctx.record_error(sample_error(), Some((1, 5)), "test", ErrorSeverity::Error);
    assert_eq!(ctx.errors.len(), 1);
    assert!(!ctx.errors.is_empty());
}

#[test]
fn test_recovery_context_into_summary_captures_warnings() {
    let mut ctx = make_ctx();
    // Access warnings via into_summary
    ctx.record_error(sample_error(), None, "err", ErrorSeverity::Error);
    let summary = ctx.into_summary();
    assert_eq!(summary.errors.len(), 1);
    assert_eq!(summary.warnings.len(), 0);
}

// ---------------------------------------------------------------------------
// Checkpoint push/pop/commit
// ---------------------------------------------------------------------------

#[test]
fn test_checkpoint_push_pop_discards_errors() {
    let mut ctx = make_ctx();
    ctx.record_error(sample_error(), None, "before", ErrorSeverity::Error);
    assert_eq!(ctx.errors.len(), 1);

    ctx.push_checkpoint();
    assert_eq!(ctx.checkpoints.len(), 1);

    ctx.record_error(sample_type_error(), None, "tentative", ErrorSeverity::Error);
    ctx.record_error(
        sample_infer_error(),
        None,
        "tentative2",
        ErrorSeverity::Error,
    );
    assert_eq!(ctx.errors.len(), 3);

    let popped = ctx.pop_checkpoint();
    assert!(popped, "should pop successfully");
    assert_eq!(ctx.errors.len(), 1, "tentative errors should be discarded");
    assert_eq!(ctx.checkpoints.len(), 0);
}

#[test]
fn test_checkpoint_commit_keeps_errors() {
    let mut ctx = make_ctx();
    ctx.push_checkpoint();
    ctx.record_error(sample_error(), None, "kept", ErrorSeverity::Error);
    ctx.record_error(sample_type_error(), None, "also kept", ErrorSeverity::Error);

    let committed = ctx.commit_checkpoint();
    assert!(committed, "should commit successfully");
    assert_eq!(ctx.errors.len(), 2, "committed errors should be kept");
    assert_eq!(ctx.checkpoints.len(), 0);
}

#[test]
fn test_pop_checkpoint_empty_stack() {
    let mut ctx = make_ctx();
    let popped = ctx.pop_checkpoint();
    assert!(!popped, "pop on empty stack should return false");
}

#[test]
fn test_commit_checkpoint_empty_stack() {
    let mut ctx = make_ctx();
    let committed = ctx.commit_checkpoint();
    assert!(!committed, "commit on empty stack should return false");
}

#[test]
fn test_nested_checkpoints() {
    let mut ctx = make_ctx();

    ctx.push_checkpoint();
    ctx.record_error(sample_error(), None, "level1", ErrorSeverity::Error);

    ctx.push_checkpoint();
    ctx.record_error(sample_type_error(), None, "level2", ErrorSeverity::Error);

    assert_eq!(ctx.errors.len(), 2);
    assert_eq!(ctx.checkpoints.len(), 2);

    // Pop inner checkpoint: discards level2 error
    ctx.pop_checkpoint();
    assert_eq!(ctx.errors.len(), 1);
    assert_eq!(ctx.checkpoints.len(), 1);

    // Commit outer checkpoint: keeps level1 error
    ctx.commit_checkpoint();
    assert_eq!(ctx.errors.len(), 1);
    assert_eq!(ctx.checkpoints.len(), 0);
}

// ---------------------------------------------------------------------------
// Max error limit enforcement
// ---------------------------------------------------------------------------

#[test]
fn test_max_error_limit() {
    let mut ctx = make_ctx_with_max(3);

    for _ in 0..3 {
        ctx.record_error(sample_error(), None, "", ErrorSeverity::Error);
    }
    assert!(
        ctx.errors.len() >= ctx.config.max_errors,
        "should be at limit after 3 errors"
    );

    let result = ctx.recover_with(RecoveryStrategy::SkipToken, sample_error());
    assert!(
        matches!(result, RecoveryResult::TooManyErrors),
        "expected TooManyErrors, got: {result:?}"
    );
}

#[test]
fn test_zero_max_errors_always_too_many() {
    let mut ctx = make_ctx_with_max(0);
    let result = ctx.recover_with(RecoveryStrategy::SkipToken, sample_error());
    assert!(matches!(result, RecoveryResult::TooManyErrors));
}

// ---------------------------------------------------------------------------
// Recovery: InsertSorry (needs prepare_strategy_term first)
// ---------------------------------------------------------------------------

#[test]
fn test_recover_insert_sorry_without_prepare_is_fatal() {
    let mut ctx = make_ctx();
    let result = ctx.recover_with(RecoveryStrategy::InsertSorry, sample_error());
    assert!(
        matches!(result, RecoveryResult::Fatal(_)),
        "InsertSorry without pending term should be Fatal, got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Recovery: SkipToken (works without prepare)
// ---------------------------------------------------------------------------

#[test]
fn test_recover_skip_token() {
    let mut ctx = make_ctx();
    let result = ctx.recover_with(RecoveryStrategy::SkipToken, sample_error());
    match result {
        RecoveryResult::Recovered { strategy_used, .. } => {
            assert_eq!(strategy_used, RecoveryStrategy::SkipToken);
        }
        other => panic!("expected Recovered, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Recovery: InsertPlaceholder (works without prepare)
// ---------------------------------------------------------------------------

#[test]
fn test_recover_insert_placeholder() {
    let mut ctx = make_ctx();
    let result = ctx.recover_with(RecoveryStrategy::InsertPlaceholder, sample_error());
    match result {
        RecoveryResult::Recovered { strategy_used, .. } => {
            assert_eq!(strategy_used, RecoveryStrategy::InsertPlaceholder);
        }
        other => panic!("expected Recovered, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Recovery: BestEffort (works without prepare)
// ---------------------------------------------------------------------------

#[test]
fn test_recover_best_effort() {
    let mut ctx = make_ctx();
    let result = ctx.recover_with(RecoveryStrategy::BestEffort, sample_error());
    assert!(
        matches!(result, RecoveryResult::Recovered { .. }),
        "BestEffort should recover, got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Depth limit
// ---------------------------------------------------------------------------

#[test]
fn test_recovery_depth_limit() {
    let config = RecoveryConfig::new().with_recovery_depth_limit(0);
    let mut ctx = RecoveryContext::new(config);
    ctx.current_depth = 1;
    let result = ctx.recover_with(RecoveryStrategy::SkipToken, sample_error());
    assert!(
        matches!(result, RecoveryResult::Fatal(_)),
        "expected Fatal at depth limit, got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Sorry term synthesis
// ---------------------------------------------------------------------------

#[test]
fn test_synthesize_sorry_prop() {
    let env = Environment::new();
    let sorry = synthesize_sorry(&env, &Expr::prop());
    let debug = format!("{sorry:?}");
    assert!(
        debug.contains("App") || debug.contains("Const"),
        "sorry for Prop: {debug}"
    );
}

#[test]
fn test_synthesize_sorry_type() {
    let env = Environment::new();
    let sorry = synthesize_sorry(&env, &Expr::type_());
    let debug = format!("{sorry:?}");
    assert!(
        debug.contains("App") || debug.contains("Const"),
        "sorry for Type: {debug}"
    );
}

// ---------------------------------------------------------------------------
// ErrorSummary
// ---------------------------------------------------------------------------

#[test]
fn test_error_summary_default_empty() {
    let summary = ErrorSummary::default();
    assert!(summary.errors.is_empty());
    assert_eq!(summary.errors.len() + summary.warnings.len(), 0);
    assert_eq!(summary.sorry_count, 0);
    assert_eq!(summary.recovered_count, 0);
}

#[test]
fn test_error_summary_with_errors() {
    let summary = ErrorSummary {
        errors: vec![LocatedError {
            error: sample_error(),
            span: None,
            context: String::new(),
            severity: ErrorSeverity::Error,
        }],
        ..ErrorSummary::default()
    };
    assert!(!summary.errors.is_empty());
    assert_eq!(summary.errors.len() + summary.warnings.len(), 1);
}

#[test]
fn test_error_summary_total_diagnostics() {
    let summary = ErrorSummary {
        errors: vec![LocatedError {
            error: sample_error(),
            span: None,
            context: String::new(),
            severity: ErrorSeverity::Error,
        }],
        warnings: vec![LocatedWarning {
            message: "test".into(),
            span: None,
        }],
        sorry_count: 1,
        recovered_count: 1,
    };
    assert_eq!(summary.errors.len() + summary.warnings.len(), 2);
}

// ---------------------------------------------------------------------------
// merge_error_summaries
// ---------------------------------------------------------------------------

#[test]
fn test_merge_empty_summaries() {
    let merged = merge_error_summaries(&[]);
    assert!(merged.errors.is_empty());
    assert_eq!(merged.sorry_count, 0);
    assert_eq!(merged.recovered_count, 0);
}

#[test]
fn test_merge_single_summary() {
    let s = ErrorSummary {
        errors: vec![LocatedError {
            error: sample_error(),
            span: None,
            context: String::new(),
            severity: ErrorSeverity::Error,
        }],
        warnings: vec![],
        sorry_count: 1,
        recovered_count: 1,
    };
    let merged = merge_error_summaries(&[s]);
    assert_eq!(merged.errors.len(), 1);
    assert_eq!(merged.sorry_count, 1);
    assert_eq!(merged.recovered_count, 1);
}

#[test]
fn test_merge_multiple_summaries() {
    let s1 = ErrorSummary {
        errors: vec![LocatedError {
            error: sample_error(),
            span: None,
            context: "first".into(),
            severity: ErrorSeverity::Error,
        }],
        warnings: vec![LocatedWarning {
            message: "w1".into(),
            span: None,
        }],
        sorry_count: 2,
        recovered_count: 1,
    };
    let s2 = ErrorSummary {
        errors: vec![
            LocatedError {
                error: sample_type_error(),
                span: Some((10, 20)),
                context: "second".into(),
                severity: ErrorSeverity::Error,
            },
            LocatedError {
                error: sample_infer_error(),
                span: None,
                context: "third".into(),
                severity: ErrorSeverity::Warning,
            },
        ],
        warnings: vec![],
        sorry_count: 1,
        recovered_count: 2,
    };

    let merged = merge_error_summaries(&[s1, s2]);
    assert_eq!(merged.errors.len(), 3);
    assert_eq!(merged.warnings.len(), 1);
    assert_eq!(merged.sorry_count, 3);
    assert_eq!(merged.recovered_count, 3);
}

// ---------------------------------------------------------------------------
// format_error_report
// ---------------------------------------------------------------------------

#[test]
fn test_format_error_report_empty() {
    let summary = ErrorSummary::default();
    let report = format_error_report(&summary);
    assert_eq!(report, "no diagnostics");
}

#[test]
fn test_format_error_report_single_error() {
    let summary = ErrorSummary {
        errors: vec![LocatedError {
            error: sample_error(),
            span: Some((5, 10)),
            context: "test context".into(),
            severity: ErrorSeverity::Error,
        }],
        warnings: vec![],
        sorry_count: 1,
        recovered_count: 1,
    };
    let report = format_error_report(&summary);
    assert!(report.contains("1 error(s)"), "count: {report}");
    assert!(report.contains("0 warning(s)"), "warnings: {report}");
    assert!(report.contains("1 sorry term(s)"), "sorry: {report}");
    assert!(report.contains("1 recovered"), "recovered: {report}");
    assert!(report.contains("[5..10]"), "span: {report}");
    assert!(report.contains("(test context)"), "context: {report}");
    assert!(report.contains("Unknown identifier: x"), "error: {report}");
}

#[test]
fn test_format_error_report_with_warnings() {
    let summary = ErrorSummary {
        errors: vec![LocatedError {
            error: sample_type_error(),
            span: None,
            context: String::new(),
            severity: ErrorSeverity::Error,
        }],
        warnings: vec![LocatedWarning {
            message: "unused import".into(),
            span: Some((100, 110)),
        }],
        sorry_count: 0,
        recovered_count: 0,
    };
    let report = format_error_report(&summary);
    assert!(report.contains("1 error(s)"), "errors: {report}");
    assert!(report.contains("1 warning(s)"), "warnings: {report}");
    assert!(report.contains("unused import"), "warning text: {report}");
}

#[test]
fn test_format_error_report_multiple_errors() {
    let summary = ErrorSummary {
        errors: vec![
            LocatedError {
                error: sample_error(),
                span: None,
                context: String::new(),
                severity: ErrorSeverity::Error,
            },
            LocatedError {
                error: sample_type_error(),
                span: Some((50, 60)),
                context: "decl".into(),
                severity: ErrorSeverity::Error,
            },
        ],
        warnings: vec![],
        sorry_count: 2,
        recovered_count: 2,
    };
    let report = format_error_report(&summary);
    assert!(report.contains("2 error(s)"), "count: {report}");
    assert!(report.contains("1."), "first numbering: {report}");
    assert!(report.contains("2."), "second numbering: {report}");
}

// ---------------------------------------------------------------------------
// try_elaborate_with_recovery
// ---------------------------------------------------------------------------

#[test]
fn test_try_elaborate_success() {
    let mut ctx = make_ctx();
    let env = Environment::new();

    let (result, errors) = try_elaborate_with_recovery(&mut ctx, &env, || Ok(Expr::prop()), None);
    assert!(result.is_some(), "should succeed");
    assert!(errors.is_empty(), "no errors on success");
    assert_eq!(ctx.errors.len(), 0);
}

#[test]
fn test_try_elaborate_failure_recovers() {
    let config = RecoveryConfig::new().with_report_all(true);
    let mut ctx = RecoveryContext::new(config);
    let env = Environment::new();

    let (result, errors) =
        try_elaborate_with_recovery(&mut ctx, &env, || Err(sample_error()), Some(&Expr::prop()));
    assert!(result.is_some(), "should recover with sorry");
    assert!(!errors.is_empty(), "should have errors");
}

#[test]
fn test_try_elaborate_failure_no_type() {
    let config = RecoveryConfig::new().with_report_all(true);
    let mut ctx = RecoveryContext::new(config);
    let env = Environment::new();

    let (result, errors) =
        try_elaborate_with_recovery(&mut ctx, &env, || Err(sample_error()), None);
    // Default strategies include SkipToken which works without expected type
    assert!(
        result.is_some() || !errors.is_empty(),
        "should attempt recovery"
    );
}

// ---------------------------------------------------------------------------
// into_summary
// ---------------------------------------------------------------------------

#[test]
fn test_into_summary_captures_errors() {
    let mut ctx = make_ctx();
    ctx.record_error(sample_error(), Some((0, 5)), "first", ErrorSeverity::Error);
    ctx.record_error(sample_type_error(), None, "second", ErrorSeverity::Error);

    let summary = ctx.into_summary();
    assert_eq!(summary.errors.len(), 2);
}

#[test]
fn test_into_summary_tracks_recovery() {
    let mut ctx = make_ctx();

    // SkipToken recovery works without prepare
    let _ = ctx.recover_with(RecoveryStrategy::SkipToken, sample_error());

    let summary = ctx.into_summary();
    assert!(!summary.errors.is_empty());
    assert_eq!(summary.recovered_count, 1);
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_zero_errors_summary() {
    let ctx = make_ctx();
    let summary = ctx.into_summary();
    assert!(summary.errors.is_empty());
    assert_eq!(summary.errors.len() + summary.warnings.len(), 0);
    assert_eq!(summary.sorry_count, 0);
    assert_eq!(summary.recovered_count, 0);
}

#[test]
fn test_config_accessor() {
    let config = RecoveryConfig::new().with_max_errors(42);
    let ctx = RecoveryContext::new(config);
    assert_eq!(ctx.config.max_errors, 42);
}

#[test]
fn test_checkpoint_depth_tracking() {
    let mut ctx = make_ctx();
    assert_eq!(ctx.checkpoints.len(), 0);

    ctx.push_checkpoint();
    assert_eq!(ctx.checkpoints.len(), 1);

    ctx.push_checkpoint();
    assert_eq!(ctx.checkpoints.len(), 2);

    ctx.push_checkpoint();
    assert_eq!(ctx.checkpoints.len(), 3);

    ctx.pop_checkpoint();
    assert_eq!(ctx.checkpoints.len(), 2);

    ctx.commit_checkpoint();
    assert_eq!(ctx.checkpoints.len(), 1);

    ctx.pop_checkpoint();
    assert_eq!(ctx.checkpoints.len(), 0);
}

#[test]
fn test_sorry_count_only_from_prepared_recovery() {
    let mut ctx = make_ctx();

    // Direct record_error does not increment sorry count
    ctx.record_error(sample_error(), None, "", ErrorSeverity::Error);
    ctx.record_error(sample_type_error(), None, "", ErrorSeverity::Error);
    assert_eq!(
        ctx.sorry_terms.len(),
        0,
        "direct errors don't add sorry terms"
    );

    // SkipToken without prepare doesn't add sorry either (uses Expr::prop fallback)
    let _ = ctx.recover_with(RecoveryStrategy::SkipToken, sample_infer_error());
    // pending_is_sorry was false, so sorry_terms is still 0
    assert_eq!(
        ctx.sorry_terms.len(),
        0,
        "SkipToken fallback is not a sorry"
    );
}

#[test]
fn test_multiple_recoveries_accumulate() {
    let mut ctx = make_ctx();

    for _ in 0..5 {
        let _ = ctx.recover_with(RecoveryStrategy::SkipToken, sample_error());
    }

    assert!(ctx.errors.len() >= 5);
    let summary = ctx.into_summary();
    assert_eq!(summary.recovered_count, 5);
}

#[test]
fn test_can_continue_tracks_budget() {
    let mut ctx = make_ctx_with_max(2);
    assert!(ctx.errors.len() < ctx.config.max_errors);

    ctx.record_error(sample_error(), None, "", ErrorSeverity::Error);
    assert!(ctx.errors.len() < ctx.config.max_errors);

    ctx.record_error(sample_error(), None, "", ErrorSeverity::Error);
    assert!(ctx.errors.len() >= ctx.config.max_errors);
}

#[test]
fn test_recovery_result_variants() {
    // Verify all variants can be constructed and matched
    let env = Environment::new();
    let sorry = synthesize_sorry(&env, &Expr::prop());

    let recovered = RecoveryResult::Recovered {
        synth_term: sorry,
        strategy_used: RecoveryStrategy::InsertSorry,
    };
    assert!(matches!(recovered, RecoveryResult::Recovered { .. }));

    let fatal = RecoveryResult::Fatal(sample_error());
    assert!(matches!(fatal, RecoveryResult::Fatal(_)));

    let too_many = RecoveryResult::TooManyErrors;
    assert!(matches!(too_many, RecoveryResult::TooManyErrors));
}

#[test]
fn test_located_error_all_severities() {
    for severity in [
        ErrorSeverity::Error,
        ErrorSeverity::Warning,
        ErrorSeverity::Info,
        ErrorSeverity::Hint,
    ] {
        let err = LocatedError {
            error: sample_error(),
            span: None,
            context: String::new(),
            severity,
        };
        let s = format!("{err}");
        assert!(
            s.contains(&format!("{severity}")),
            "display should contain severity: {s}"
        );
    }
}

#[test]
fn test_recovery_config_new_equals_default() {
    let new = RecoveryConfig::new();
    let def = RecoveryConfig::default();
    assert_eq!(new.max_errors, def.max_errors);
    assert_eq!(new.strategies, def.strategies);
    assert_eq!(new.report_all, def.report_all);
    assert_eq!(new.recovery_depth_limit, def.recovery_depth_limit);
}
