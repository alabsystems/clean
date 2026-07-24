// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended error recovery ext2 module.

use crate::error::ElabError;
use crate::error_recovery_ext2::{
    hint_for_error, CollectorConfig, Diagnostic, DiagnosticCollector, DiagnosticHint,
    DiagnosticSeverity, DiagnosticStats, ErrorContext, ExtRecoveryStrategy, RelatedInfo,
    SourceSpan,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn err_unknown(name: &str) -> ElabError {
    ElabError::UnknownIdent(name.into())
}

fn err_type_mismatch() -> ElabError {
    ElabError::TypeMismatch {
        expected: "Nat".into(),
        actual: "Bool".into(),
    }
}

fn err_cannot_infer() -> ElabError {
    ElabError::CannotInfer
}

fn err_not_impl() -> ElabError {
    ElabError::NotImplemented("do notation".into())
}

fn span(start: usize, end: usize) -> SourceSpan {
    SourceSpan {
        start,
        end,
        line: 0,
        column: start as u32,
    }
}

fn make_collector() -> DiagnosticCollector {
    DiagnosticCollector::new(CollectorConfig::default())
}

// ---------------------------------------------------------------------------
// DiagnosticSeverity
// ---------------------------------------------------------------------------

#[test]
fn test_severity_display() {
    assert_eq!(format!("{}", DiagnosticSeverity::Error), "error");
    assert_eq!(format!("{}", DiagnosticSeverity::Warning), "warning");
    assert_eq!(format!("{}", DiagnosticSeverity::Info), "info");
    assert_eq!(format!("{}", DiagnosticSeverity::Hint), "hint");
}

#[test]
fn test_severity_equality() {
    assert_eq!(DiagnosticSeverity::Error, DiagnosticSeverity::Error);
    assert_ne!(DiagnosticSeverity::Error, DiagnosticSeverity::Warning);
}

// ---------------------------------------------------------------------------
// SourceSpan
// ---------------------------------------------------------------------------

#[test]
fn test_source_span_display() {
    let s = SourceSpan {
        start: 10,
        end: 20,
        line: 2,
        column: 5,
    };
    let display = format!("{s}");
    assert!(display.contains("3:6"), "1-based line:col: {display}");
    assert!(display.contains("[10-20)"), "byte range: {display}");
}

#[test]
fn test_source_span_equality() {
    let a = span(0, 5);
    let b = span(0, 5);
    assert_eq!(a, b);
    assert_ne!(span(0, 5), span(0, 6));
}

#[test]
fn test_source_span_zero_offset() {
    let s = SourceSpan {
        start: 0,
        end: 0,
        line: 0,
        column: 0,
    };
    let display = format!("{s}");
    assert!(display.contains("1:1"), "zero origin: {display}");
}

// ---------------------------------------------------------------------------
// ExtRecoveryStrategy
// ---------------------------------------------------------------------------

#[test]
fn test_recovery_strategy_display() {
    assert_eq!(
        format!("{}", ExtRecoveryStrategy::InsertSorry),
        "insert sorry"
    );
    assert_eq!(
        format!("{}", ExtRecoveryStrategy::UseMetavariable),
        "use metavariable"
    );
    assert_eq!(
        format!("{}", ExtRecoveryStrategy::SkipDeclaration),
        "skip declaration"
    );
    assert_eq!(
        format!("{}", ExtRecoveryStrategy::FallbackType),
        "fallback type"
    );
}

#[test]
fn test_recovery_strategy_equality() {
    assert_eq!(
        ExtRecoveryStrategy::InsertSorry,
        ExtRecoveryStrategy::InsertSorry
    );
    assert_ne!(
        ExtRecoveryStrategy::InsertSorry,
        ExtRecoveryStrategy::FallbackType
    );
}

// ---------------------------------------------------------------------------
// DiagnosticHint
// ---------------------------------------------------------------------------

#[test]
fn test_hint_display_without_replacement() {
    let h = DiagnosticHint {
        message: "try this".into(),
        replacement: None,
    };
    assert_eq!(format!("{h}"), "try this");
}

#[test]
fn test_hint_display_with_replacement() {
    let h = DiagnosticHint {
        message: "add annotation".into(),
        replacement: Some(": Nat".into()),
    };
    let s = format!("{h}");
    assert!(s.contains("add annotation"), "message: {s}");
    assert!(s.contains("(try: `: Nat`)"), "replacement: {s}");
}

// ---------------------------------------------------------------------------
// hint_for_error
// ---------------------------------------------------------------------------

#[test]
fn test_hint_unknown_ident_lowercase() {
    let hints = hint_for_error(&err_unknown("x"));
    assert_eq!(hints.len(), 1);
    assert!(hints[0].message.contains("import"));
}

#[test]
fn test_hint_unknown_ident_uppercase() {
    let hints = hint_for_error(&err_unknown("Nat"));
    assert_eq!(hints.len(), 2, "uppercase gets extra hint");
    assert!(hints[1].message.contains("uppercase"));
}

#[test]
fn test_hint_type_mismatch() {
    let hints = hint_for_error(&err_type_mismatch());
    assert_eq!(hints.len(), 1);
    assert!(hints[0].message.contains("Expected"));
}

#[test]
fn test_hint_cannot_infer() {
    let hints = hint_for_error(&err_cannot_infer());
    assert_eq!(hints.len(), 1);
    assert!(hints[0].replacement.is_some());
}

#[test]
fn test_hint_not_implemented() {
    let hints = hint_for_error(&err_not_impl());
    assert_eq!(hints.len(), 1);
    assert!(hints[0].message.contains("do notation"));
}

#[test]
fn test_hint_too_many_args() {
    let err = ElabError::TooManyArguments {
        func_type: "Nat".into(),
        remaining_args: 2,
    };
    let hints = hint_for_error(&err);
    assert_eq!(hints.len(), 1);
    assert!(hints[0].message.contains("extra arguments"));
}

#[test]
fn test_hint_anon_ctor() {
    let hints = hint_for_error(&ElabError::AnonymousCtorNoExpectedType);
    assert_eq!(hints.len(), 1);
    assert!(hints[0].replacement.is_some());
}

#[test]
fn test_hint_no_hint_for_parse_error() {
    let hints = hint_for_error(&ElabError::ParseError("bad syntax".into()));
    assert!(hints.is_empty());
}

// ---------------------------------------------------------------------------
// Diagnostic display
// ---------------------------------------------------------------------------

#[test]
fn test_diagnostic_display_full() {
    let diag = Diagnostic {
        error: err_unknown("foo"),
        severity: DiagnosticSeverity::Error,
        span: Some(span(10, 20)),
        context_path: vec!["decl `bar`".into(), "let binding".into()],
        recovery: Some(ExtRecoveryStrategy::InsertSorry),
        hints: vec![],
        related: vec![],
    };
    let s = format!("{diag}");
    assert!(s.contains("error at"), "severity+span: {s}");
    assert!(s.contains("Unknown identifier: foo"), "error msg: {s}");
    assert!(s.contains("decl `bar` > let binding"), "context: {s}");
    assert!(s.contains("[recovered: insert sorry]"), "recovery: {s}");
}

#[test]
fn test_diagnostic_display_minimal() {
    let diag = Diagnostic {
        error: err_cannot_infer(),
        severity: DiagnosticSeverity::Warning,
        span: None,
        context_path: vec![],
        recovery: None,
        hints: vec![],
        related: vec![],
    };
    let s = format!("{diag}");
    assert!(s.starts_with("warning:"), "severity: {s}");
    assert!(!s.contains("(in"), "no context: {s}");
    assert!(!s.contains("[recovered"), "no recovery: {s}");
}

// ---------------------------------------------------------------------------
// DiagnosticStats
// ---------------------------------------------------------------------------

#[test]
fn test_stats_default() {
    let stats = DiagnosticStats::default();
    assert_eq!(stats.total(), 0);
    assert_eq!(stats.errors, 0);
    assert_eq!(stats.deduplicated, 0);
}

#[test]
fn test_stats_total() {
    let stats = DiagnosticStats {
        errors: 2,
        warnings: 1,
        infos: 3,
        hints: 4,
        ..Default::default()
    };
    assert_eq!(stats.total(), 10);
}

#[test]
fn test_stats_display() {
    let stats = DiagnosticStats {
        errors: 1,
        warnings: 2,
        recovered: 1,
        fatal: 0,
        ..Default::default()
    };
    let s = format!("{stats}");
    assert!(s.contains("1 error(s)"), "errors: {s}");
    assert!(s.contains("2 warning(s)"), "warnings: {s}");
    assert!(s.contains("1 recovered"), "recovered: {s}");
}

// ---------------------------------------------------------------------------
// CollectorConfig
// ---------------------------------------------------------------------------

#[test]
fn test_config_defaults() {
    let cfg = CollectorConfig::default();
    assert_eq!(cfg.error_budget, 100);
    assert!(cfg.deduplicate);
    assert_eq!(cfg.default_strategy, ExtRecoveryStrategy::InsertSorry);
}

#[test]
fn test_config_builder() {
    let cfg = CollectorConfig::default()
        .with_error_budget(5)
        .with_deduplicate(false)
        .with_default_strategy(ExtRecoveryStrategy::FallbackType);
    assert_eq!(cfg.error_budget, 5);
    assert!(!cfg.deduplicate);
    assert_eq!(cfg.default_strategy, ExtRecoveryStrategy::FallbackType);
}

// ---------------------------------------------------------------------------
// ErrorContext
// ---------------------------------------------------------------------------

#[test]
fn test_error_context_push_pop() {
    let mut ctx = ErrorContext::new();
    assert_eq!(ctx.depth(), 0);
    assert!(ctx.path().is_empty());

    ctx.push("def foo");
    ctx.push("let bar");
    assert_eq!(ctx.depth(), 2);
    assert_eq!(ctx.path(), &["def foo", "let bar"]);

    let popped = ctx.pop();
    assert_eq!(popped.as_deref(), Some("let bar"));
    assert_eq!(ctx.depth(), 1);
}

#[test]
fn test_error_context_pop_empty() {
    let mut ctx = ErrorContext::new();
    assert!(ctx.pop().is_none());
}

// ---------------------------------------------------------------------------
// DiagnosticCollector — basic
// ---------------------------------------------------------------------------

#[test]
fn test_collector_initial_state() {
    let c = make_collector();
    assert_eq!(c.count(), 0);
    assert!(!c.is_budget_exhausted());
    assert!(c.should_continue());
    assert_eq!(c.context_depth(), 0);
}

#[test]
fn test_collector_add_error() {
    let mut c = make_collector();
    let added = c.add_error(err_unknown("x"), Some(span(0, 1)));
    assert!(added);
    assert_eq!(c.count(), 1);
    assert_eq!(c.stats().errors, 1);
    assert_eq!(c.stats().recovered, 1); // default strategy = InsertSorry
}

#[test]
fn test_collector_add_warning() {
    let mut c = make_collector();
    c.add_warning(err_type_mismatch(), None);
    assert_eq!(c.stats().warnings, 1);
    assert_eq!(c.stats().recovered, 0);
}

#[test]
fn test_collector_add_info() {
    let mut c = make_collector();
    c.add_info(err_not_impl(), None);
    assert_eq!(c.stats().infos, 1);
}

#[test]
fn test_collector_add_fatal() {
    let mut c = make_collector();
    c.add_fatal(err_unknown("y"), None);
    assert_eq!(c.stats().errors, 1);
    assert_eq!(c.stats().fatal, 1);
    assert_eq!(c.stats().recovered, 0);
}

// ---------------------------------------------------------------------------
// Context propagation
// ---------------------------------------------------------------------------

#[test]
fn test_collector_context_propagation() {
    let mut c = make_collector();
    c.push_context("elaborating `Foo`");
    c.push_context("field `bar`");
    c.add_error(err_cannot_infer(), None);

    let diags = c.diagnostics();
    assert_eq!(
        diags[0].context_path,
        vec!["elaborating `Foo`", "field `bar`"]
    );
}

#[test]
fn test_collector_context_after_pop() {
    let mut c = make_collector();
    c.push_context("outer");
    c.push_context("inner");
    c.pop_context();
    c.add_error(err_cannot_infer(), None);
    assert_eq!(c.diagnostics()[0].context_path, vec!["outer"]);
}

// ---------------------------------------------------------------------------
// Deduplication
// ---------------------------------------------------------------------------

#[test]
fn test_dedup_same_error_same_span() {
    let mut c = make_collector();
    let s = Some(span(5, 10));
    c.add_error(err_unknown("x"), s);
    let added = c.add_error(err_unknown("x"), s);
    assert!(!added, "duplicate should not be added");
    assert_eq!(c.count(), 1);
    assert_eq!(c.stats().deduplicated, 1);
}

#[test]
fn test_dedup_same_error_different_span() {
    let mut c = make_collector();
    c.add_error(err_unknown("x"), Some(span(0, 1)));
    let added = c.add_error(err_unknown("x"), Some(span(10, 11)));
    assert!(added, "different span = not duplicate");
    assert_eq!(c.count(), 2);
}

#[test]
fn test_dedup_disabled() {
    let cfg = CollectorConfig::default().with_deduplicate(false);
    let mut c = DiagnosticCollector::new(cfg);
    let s = Some(span(0, 5));
    c.add_error(err_unknown("x"), s);
    let added = c.add_error(err_unknown("x"), s);
    assert!(added, "dedup disabled = always added");
    assert_eq!(c.count(), 2);
}

#[test]
fn test_dedup_merges_related_info() {
    let mut c = make_collector();
    let s = Some(span(0, 5));
    c.add_diagnostic(
        err_unknown("x"),
        DiagnosticSeverity::Error,
        s,
        None,
        vec![RelatedInfo {
            message: "first ref".into(),
            span: None,
        }],
    );
    c.add_diagnostic(
        err_unknown("x"),
        DiagnosticSeverity::Error,
        s,
        None,
        vec![RelatedInfo {
            message: "second ref".into(),
            span: None,
        }],
    );
    assert_eq!(c.count(), 1);
    assert_eq!(c.diagnostics()[0].related.len(), 2);
}

// ---------------------------------------------------------------------------
// Error budget
// ---------------------------------------------------------------------------

#[test]
fn test_budget_exhaustion() {
    let cfg = CollectorConfig::default().with_error_budget(2);
    let mut c = DiagnosticCollector::new(cfg);
    c.add_error(err_unknown("a"), None);
    assert!(c.should_continue());
    c.add_error(err_unknown("b"), None);
    assert!(!c.should_continue());
    assert!(c.is_budget_exhausted());
}

#[test]
fn test_budget_rejects_after_exhaustion() {
    let cfg = CollectorConfig::default().with_error_budget(1);
    let mut c = DiagnosticCollector::new(cfg);
    c.add_error(err_unknown("a"), None);
    let added = c.add_error(err_unknown("b"), None);
    assert!(!added, "should reject after budget exhausted");
    assert_eq!(c.count(), 1);
}

#[test]
fn test_budget_warnings_dont_count() {
    let cfg = CollectorConfig::default().with_error_budget(2);
    let mut c = DiagnosticCollector::new(cfg);
    for i in 0..10 {
        c.add_warning(err_unknown(&format!("w{i}")), None);
    }
    assert!(c.should_continue(), "warnings don't exhaust budget");
    assert_eq!(c.stats().warnings, 10);
}

// ---------------------------------------------------------------------------
// DiagnosticReport
// ---------------------------------------------------------------------------

#[test]
fn test_report_empty() {
    let c = make_collector();
    let report = c.into_report();
    assert!(!report.has_errors());
    let s = format!("{report}");
    assert_eq!(s, "no diagnostics");
}

#[test]
fn test_report_has_errors() {
    let mut c = make_collector();
    c.add_error(err_unknown("x"), None);
    let report = c.into_report();
    assert!(report.has_errors());
}

#[test]
fn test_report_filter_severity() {
    let mut c = make_collector();
    c.add_error(err_unknown("a"), None);
    c.add_warning(err_unknown("b"), None);
    c.add_info(err_unknown("c"), None);
    let report = c.into_report();
    assert_eq!(report.filter_severity(DiagnosticSeverity::Error).len(), 1);
    assert_eq!(report.filter_severity(DiagnosticSeverity::Warning).len(), 1);
    assert_eq!(report.filter_severity(DiagnosticSeverity::Info).len(), 1);
    assert_eq!(report.filter_severity(DiagnosticSeverity::Hint).len(), 0);
}

#[test]
fn test_report_display_with_diagnostics() {
    let mut c = make_collector();
    c.add_error(err_unknown("x"), Some(span(0, 3)));
    let report = c.into_report();
    let s = format!("{report}");
    assert!(s.contains("1 error(s)"), "stats header: {s}");
    assert!(s.contains("1."), "numbering: {s}");
    assert!(s.contains("hint:"), "hints shown: {s}");
}

#[test]
fn test_report_display_related_info() {
    let mut c = make_collector();
    c.add_diagnostic(
        err_unknown("x"),
        DiagnosticSeverity::Error,
        None,
        None,
        vec![RelatedInfo {
            message: "declared here".into(),
            span: Some(span(50, 55)),
        }],
    );
    let report = c.into_report();
    let s = format!("{report}");
    assert!(s.contains("related: declared here"), "related: {s}");
    assert!(s.contains("[50-55)"), "related span: {s}");
}

// ---------------------------------------------------------------------------
// Hints auto-attached to diagnostics
// ---------------------------------------------------------------------------

#[test]
fn test_hints_auto_attached_on_add() {
    let mut c = make_collector();
    c.add_error(err_cannot_infer(), None);
    let diags = c.diagnostics();
    assert!(
        !diags[0].hints.is_empty(),
        "hints auto-populated from hint_for_error"
    );
    assert!(diags[0].hints[0].message.contains("type annotation"));
}

// ---------------------------------------------------------------------------
// Mixed severity collection
// ---------------------------------------------------------------------------

#[test]
fn test_mixed_severity_stats() {
    let mut c = make_collector();
    c.add_error(err_unknown("a"), None);
    c.add_warning(err_unknown("b"), None);
    c.add_info(err_unknown("c"), None);
    c.add_diagnostic(
        err_unknown("d"),
        DiagnosticSeverity::Hint,
        None,
        None,
        vec![],
    );
    assert_eq!(c.stats().total(), 4);
    assert_eq!(c.stats().errors, 1);
    assert_eq!(c.stats().warnings, 1);
    assert_eq!(c.stats().infos, 1);
    assert_eq!(c.stats().hints, 1);
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_zero_budget() {
    let cfg = CollectorConfig::default().with_error_budget(0);
    let mut c = DiagnosticCollector::new(cfg);
    // First error should still be added (budget checked AFTER add)
    let added = c.add_error(err_unknown("x"), None);
    assert!(added);
    assert!(c.is_budget_exhausted());
}

#[test]
fn test_large_context_stack() {
    let mut c = make_collector();
    for i in 0..50 {
        c.push_context(&format!("level_{i}"));
    }
    c.add_error(err_unknown("deep"), None);
    assert_eq!(c.diagnostics()[0].context_path.len(), 50);
}
