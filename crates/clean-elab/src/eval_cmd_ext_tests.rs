// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended `#eval` command functionality (eval_cmd_ext + ext2).

use super::eval_cmd_ext::*;
use super::eval_cmd_ext2::*;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, Level};
use std::time::Duration;

// =============================================================================
// EvalLimits tests
// =============================================================================

#[test]
fn test_eval_limits_default_has_sensible_values() {
    let limits = EvalLimits::default();
    assert_eq!(limits.max_steps, Some(100_000));
    assert_eq!(limits.max_time, Some(Duration::from_secs(5)));
    assert_eq!(limits.max_depth, Some(1_000));
}

#[test]
fn test_eval_limits_unlimited() {
    let limits = EvalLimits::unlimited();
    assert_eq!(limits.max_steps, None);
    assert_eq!(limits.max_time, None);
    assert_eq!(limits.max_depth, None);
}

#[test]
fn test_eval_limits_with_max_steps() {
    let limits = EvalLimits::unlimited().with_max_steps(50);
    assert_eq!(limits.max_steps, Some(50));
    assert_eq!(limits.max_time, None);
}

#[test]
fn test_eval_limits_with_max_time() {
    let limits = EvalLimits::unlimited().with_max_time(Duration::from_millis(100));
    assert_eq!(limits.max_time, Some(Duration::from_millis(100)));
}

#[test]
fn test_eval_limits_with_max_depth() {
    let limits = EvalLimits::unlimited().with_max_depth(42);
    assert_eq!(limits.max_depth, Some(42));
}

#[test]
fn test_eval_limits_check_steps_within_limit() {
    let limits = EvalLimits::default().with_max_steps(100);
    assert!(limits.check_steps(50).is_ok());
    assert!(limits.check_steps(100).is_ok());
}

#[test]
fn test_eval_limits_check_steps_exceeded() {
    let limits = EvalLimits::default().with_max_steps(10);
    let err = limits.check_steps(11).unwrap_err();
    match err {
        EvalExtError::StepLimitExceeded { limit } => assert_eq!(limit, 10),
        other => panic!("expected StepLimitExceeded, got {other:?}"),
    }
}

#[test]
fn test_eval_limits_check_steps_unlimited() {
    let limits = EvalLimits::unlimited();
    assert!(limits.check_steps(u64::MAX).is_ok());
}

#[test]
fn test_eval_limits_check_time_within_limit() {
    let limits = EvalLimits::default().with_max_time(Duration::from_secs(10));
    assert!(limits.check_time(Duration::from_secs(5)).is_ok());
}

#[test]
fn test_eval_limits_check_time_exceeded() {
    let limits = EvalLimits::default().with_max_time(Duration::from_millis(1));
    let err = limits.check_time(Duration::from_millis(2)).unwrap_err();
    match err {
        EvalExtError::TimeLimitExceeded { limit } => {
            assert_eq!(limit, Duration::from_millis(1));
        }
        other => panic!("expected TimeLimitExceeded, got {other:?}"),
    }
}

#[test]
fn test_eval_limits_check_depth_within_limit() {
    let limits = EvalLimits::default().with_max_depth(100);
    assert!(limits.check_depth(50).is_ok());
}

#[test]
fn test_eval_limits_check_depth_exceeded() {
    let limits = EvalLimits::default().with_max_depth(5);
    let err = limits.check_depth(6).unwrap_err();
    match err {
        EvalExtError::DepthLimitExceeded { limit } => assert_eq!(limit, 5),
        other => panic!("expected DepthLimitExceeded, got {other:?}"),
    }
}

// =============================================================================
// EvalProfile tests
// =============================================================================

#[test]
fn test_eval_profile_new() {
    let profile = EvalProfile::new(Duration::from_millis(42), 100, 50, false);
    assert_eq!(profile.elapsed, Duration::from_millis(42));
    assert_eq!(profile.reduction_steps, 100);
    assert_eq!(profile.allocation_count, 50);
    assert!(!profile.cached);
}

#[test]
fn test_eval_profile_summary_not_cached() {
    let profile = EvalProfile::new(Duration::from_millis(10), 5, 3, false);
    let summary = profile.summary();
    assert!(summary.contains("steps=5"));
    assert!(summary.contains("allocs=3"));
    assert!(!summary.contains("[cached]"));
}

#[test]
fn test_eval_profile_summary_cached() {
    let profile = EvalProfile::new(Duration::from_millis(1), 0, 0, true);
    let summary = profile.summary();
    assert!(summary.starts_with("[cached]"));
}

// =============================================================================
// TypeCategory + classify_type tests
// =============================================================================

#[test]
fn test_classify_type_nat_literal() {
    let expr = Expr::nat_lit(42u64);
    assert_eq!(classify_type(&expr), TypeCategory::Nat);
}

#[test]
fn test_classify_type_string_literal() {
    let expr = Expr::str_lit("hello");
    assert_eq!(classify_type(&expr), TypeCategory::String);
}

#[test]
fn test_classify_type_sort() {
    let expr = Expr::sort(Level::zero());
    assert_eq!(classify_type(&expr), TypeCategory::Sort);
}

#[test]
fn test_classify_type_bool_true() {
    let expr = Expr::const_(Name::from_string("Bool.true"), vec![]);
    assert_eq!(classify_type(&expr), TypeCategory::Bool);
}

#[test]
fn test_classify_type_bool_false() {
    let expr = Expr::const_(Name::from_string("Bool.false"), vec![]);
    assert_eq!(classify_type(&expr), TypeCategory::Bool);
}

#[test]
fn test_classify_type_unit() {
    let expr = Expr::const_(Name::from_string("Unit.unit"), vec![]);
    assert_eq!(classify_type(&expr), TypeCategory::Unit);
}

#[test]
fn test_classify_type_list_nil() {
    let expr = Expr::const_(Name::from_string("List.nil"), vec![]);
    assert_eq!(classify_type(&expr), TypeCategory::List);
}

#[test]
fn test_classify_type_option_none() {
    let expr = Expr::const_(Name::from_string("Option.none"), vec![]);
    assert_eq!(classify_type(&expr), TypeCategory::Option);
}

#[test]
fn test_classify_type_nat_zero_const() {
    let expr = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert_eq!(classify_type(&expr), TypeCategory::Nat);
}

#[test]
fn test_classify_type_nat_succ_app() {
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let expr = Expr::app(succ, zero);
    assert_eq!(classify_type(&expr), TypeCategory::Nat);
}

#[test]
fn test_classify_type_list_cons_app() {
    let nil = Expr::const_(Name::from_string("List.nil"), vec![]);
    let cons = Expr::const_(Name::from_string("List.cons"), vec![]);
    let elem = Expr::nat_lit(1u64);
    let expr = Expr::app(Expr::app(cons, elem), nil);
    assert_eq!(classify_type(&expr), TypeCategory::List);
}

#[test]
fn test_classify_type_unknown_const() {
    let expr = Expr::const_(Name::from_string("Foo.bar"), vec![]);
    assert_eq!(classify_type(&expr), TypeCategory::Other);
}

#[test]
fn test_classify_type_bvar() {
    let expr = Expr::bvar(0);
    assert_eq!(classify_type(&expr), TypeCategory::Other);
}

// =============================================================================
// type_aware_display tests
// =============================================================================

#[test]
fn test_type_aware_display_nat() {
    let expr = Expr::nat_lit(99u64);
    assert_eq!(type_aware_display(&expr), "99");
}

#[test]
fn test_type_aware_display_string() {
    let expr = Expr::str_lit("world");
    assert_eq!(type_aware_display(&expr), "\"world\"");
}

#[test]
fn test_type_aware_display_bool_true() {
    let expr = Expr::const_(Name::from_string("Bool.true"), vec![]);
    assert_eq!(type_aware_display(&expr), "true");
}

#[test]
fn test_type_aware_display_unit() {
    let expr = Expr::const_(Name::from_string("Unit.unit"), vec![]);
    assert_eq!(type_aware_display(&expr), "()");
}

// =============================================================================
// EvalCache tests
// =============================================================================

#[test]
fn test_eval_cache_empty_by_default() {
    let cache = EvalCache::default();
    assert!(cache.is_empty());
    assert_eq!(cache.len(), 0);
}

#[test]
fn test_eval_cache_insert_and_get() {
    let mut cache = EvalCache::new(10);
    let expr = Expr::nat_lit(42u64);
    let result = crate::eval_cmd::EvalResult::Value("42".to_owned());
    cache.insert(&expr, result.clone(), Some("Nat".to_owned()));
    assert_eq!(cache.len(), 1);

    let (cached_result, cached_type) = cache.get(&expr).unwrap();
    assert_eq!(cached_result, &result);
    assert_eq!(cached_type, Some("Nat"));
}

#[test]
fn test_eval_cache_miss() {
    let cache = EvalCache::new(10);
    let expr = Expr::nat_lit(1u64);
    assert!(cache.get(&expr).is_none());
}

#[test]
fn test_eval_cache_clear() {
    let mut cache = EvalCache::new(10);
    let expr = Expr::nat_lit(1u64);
    let result = crate::eval_cmd::EvalResult::Value("1".to_owned());
    cache.insert(&expr, result, None);
    assert!(!cache.is_empty());
    cache.clear();
    assert!(cache.is_empty());
}

#[test]
fn test_eval_cache_eviction_at_capacity() {
    let mut cache = EvalCache::new(2);
    let e1 = Expr::nat_lit(1u64);
    let e2 = Expr::nat_lit(2u64);
    let e3 = Expr::nat_lit(3u64);
    let r = crate::eval_cmd::EvalResult::Value("x".to_owned());
    cache.insert(&e1, r.clone(), None);
    cache.insert(&e2, r.clone(), None);
    assert_eq!(cache.len(), 2);
    cache.insert(&e3, r, None);
    assert_eq!(cache.len(), 2);
}

// =============================================================================
// EvalHistory tests
// =============================================================================

#[test]
fn test_eval_history_empty_by_default() {
    let history = EvalHistory::new(10);
    assert!(history.is_empty());
    assert_eq!(history.len(), 0);
    assert!(history.last().is_none());
}

#[test]
fn test_eval_history_record_and_retrieve() {
    let mut history = EvalHistory::new(10);
    let profile = EvalProfile::new(Duration::from_millis(1), 1, 1, false);
    let result = crate::eval_cmd::EvalResult::Value("42".to_owned());
    history.record("42".to_owned(), result, profile, Some("Nat".to_owned()));
    assert_eq!(history.len(), 1);
    let last = history.last().unwrap();
    assert_eq!(last.expr_display, "42");
}

#[test]
fn test_eval_history_eviction_at_capacity() {
    let mut history = EvalHistory::new(2);
    let profile = EvalProfile::new(Duration::from_millis(1), 0, 0, false);
    let r = crate::eval_cmd::EvalResult::Value("x".to_owned());
    history.record("a".to_owned(), r.clone(), profile.clone(), None);
    history.record("b".to_owned(), r.clone(), profile.clone(), None);
    history.record("c".to_owned(), r, profile, None);
    assert_eq!(history.len(), 2);
    assert_eq!(history.entries()[0].expr_display, "b");
    assert_eq!(history.entries()[1].expr_display, "c");
}

#[test]
fn test_eval_history_clear() {
    let mut history = EvalHistory::new(10);
    let profile = EvalProfile::new(Duration::from_millis(1), 0, 0, false);
    let r = crate::eval_cmd::EvalResult::Value("x".to_owned());
    history.record("a".to_owned(), r, profile, None);
    assert!(!history.is_empty());
    history.clear();
    assert!(history.is_empty());
}

#[test]
fn test_eval_history_compare_last_two_insufficient() {
    let history = EvalHistory::new(10);
    assert!(history.compare_last_two().is_none());

    let mut history = EvalHistory::new(10);
    let profile = EvalProfile::new(Duration::from_millis(1), 0, 0, false);
    let r = crate::eval_cmd::EvalResult::Value("x".to_owned());
    history.record("a".to_owned(), r, profile, None);
    assert!(history.compare_last_two().is_none());
}

#[test]
fn test_eval_history_compare_last_two_returns_pair() {
    let mut history = EvalHistory::new(10);
    let profile = EvalProfile::new(Duration::from_millis(1), 0, 0, false);
    let r1 = crate::eval_cmd::EvalResult::Value("1".to_owned());
    let r2 = crate::eval_cmd::EvalResult::Value("2".to_owned());
    history.record("a".to_owned(), r1, profile.clone(), None);
    history.record("b".to_owned(), r2, profile, None);
    let (first, second) = history.compare_last_two().unwrap();
    assert_eq!(first.expr_display, "a");
    assert_eq!(second.expr_display, "b");
}

// =============================================================================
// Symbolic / partial evaluation tests
// =============================================================================

#[test]
fn test_make_symbolic_creates_const() {
    let sym = make_symbolic(0);
    assert!(is_symbolic(&sym));
}

#[test]
fn test_is_symbolic_false_for_regular_const() {
    let expr = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert!(!is_symbolic(&expr));
}

#[test]
fn test_is_symbolic_false_for_literal() {
    let expr = Expr::nat_lit(42u64);
    assert!(!is_symbolic(&expr));
}

#[test]
fn test_make_symbolic_different_indices() {
    let s0 = make_symbolic(0);
    let s1 = make_symbolic(1);
    assert_ne!(format!("{s0:?}"), format!("{s1:?}"));
}

#[test]
fn test_partial_eval_literal() {
    let env = Environment::new();
    let expr = Expr::nat_lit(42u64);
    let (display, sym_count) = partial_eval(&expr, &env);
    assert_eq!(display, "42");
    assert_eq!(sym_count, 0);
}

#[test]
fn test_partial_eval_symbolic() {
    let env = Environment::new();
    let sym = make_symbolic(0);
    let (_, sym_count) = partial_eval(&sym, &env);
    assert_eq!(sym_count, 1);
}

// =============================================================================
// count_sub_exprs tests
// =============================================================================

#[test]
fn test_count_sub_exprs_literal() {
    let expr = Expr::nat_lit(1u64);
    assert_eq!(count_sub_exprs(&expr), 1);
}

#[test]
fn test_count_sub_exprs_app() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::nat_lit(1u64);
    let expr = Expr::app(f, a);
    assert_eq!(count_sub_exprs(&expr), 3);
}

// =============================================================================
// eval_expression_ext integration tests
// =============================================================================

#[test]
fn test_eval_expression_ext_nat_literal() {
    let env = Environment::new();
    let expr = Expr::nat_lit(42u64);
    let limits = EvalLimits::unlimited();
    let mut cache = EvalCache::new(10);
    let mut history = EvalHistory::new(10);

    let result = eval_expression_ext(&expr, &env, &limits, &mut cache, &mut history)
        .expect("should evaluate nat literal");
    assert_eq!(format!("{}", result.result), "42");
    assert!(!result.profile.cached);
    assert_eq!(history.len(), 1);
    assert_eq!(cache.len(), 1);
}

#[test]
fn test_eval_expression_ext_cache_hit() {
    let env = Environment::new();
    let expr = Expr::nat_lit(7u64);
    let limits = EvalLimits::unlimited();
    let mut cache = EvalCache::new(10);
    let mut history = EvalHistory::new(10);

    let r1 = eval_expression_ext(&expr, &env, &limits, &mut cache, &mut history).unwrap();
    assert!(!r1.profile.cached);

    let r2 = eval_expression_ext(&expr, &env, &limits, &mut cache, &mut history).unwrap();
    assert!(r2.profile.cached);
    assert_eq!(format!("{}", r1.result), format!("{}", r2.result));
    assert_eq!(history.len(), 2);
}

#[test]
fn test_eval_expression_ext_step_limit_exceeded() {
    let env = Environment::new();
    let mut expr = Expr::nat_lit(0u64);
    for _ in 0..10 {
        let f = Expr::const_(Name::from_string("f"), vec![]);
        expr = Expr::app(f, expr);
    }
    let limits = EvalLimits::unlimited().with_max_steps(5);
    let mut cache = EvalCache::new(10);
    let mut history = EvalHistory::new(10);
    let err = eval_expression_ext(&expr, &env, &limits, &mut cache, &mut history);
    assert!(err.is_err());
    match err.unwrap_err() {
        EvalExtError::StepLimitExceeded { limit } => assert_eq!(limit, 5),
        other => panic!("expected StepLimitExceeded, got {other:?}"),
    }
}

#[test]
fn test_eval_expression_ext_depth_limit_exceeded() {
    let env = Environment::new();
    let mut expr = Expr::nat_lit(0u64);
    for _ in 0..50 {
        let f = Expr::const_(Name::from_string("f"), vec![]);
        expr = Expr::app(f, expr);
    }
    let limits = EvalLimits::unlimited().with_max_depth(5);
    let mut cache = EvalCache::new(10);
    let mut history = EvalHistory::new(10);
    let err = eval_expression_ext(&expr, &env, &limits, &mut cache, &mut history);
    assert!(err.is_err());
    match err.unwrap_err() {
        EvalExtError::DepthLimitExceeded { limit } => assert_eq!(limit, 5),
        other => panic!("expected DepthLimitExceeded, got {other:?}"),
    }
}

#[test]
fn test_eval_expression_ext_string_literal() {
    let env = Environment::new();
    let expr = Expr::str_lit("hello");
    let limits = EvalLimits::unlimited();
    let mut cache = EvalCache::new(10);
    let mut history = EvalHistory::new(10);

    let result = eval_expression_ext(&expr, &env, &limits, &mut cache, &mut history)
        .expect("should evaluate string literal");
    assert_eq!(format!("{}", result.result), "\"hello\"");
}

// =============================================================================
// ProfiledEvalResult display tests
// =============================================================================

#[test]
fn test_profiled_eval_result_display_with_profile() {
    let profile = EvalProfile::new(Duration::from_millis(5), 10, 8, false);
    let result = ProfiledEvalResult {
        result: crate::eval_cmd::EvalResult::Value("42".to_owned()),
        profile,
        type_info: Some("Nat".to_owned()),
    };
    let display = result.display_with_profile();
    assert!(display.contains("42"));
    assert!(display.contains(": Nat"));
    assert!(display.contains("steps=10"));
}

#[test]
fn test_profiled_eval_result_display_no_type() {
    let profile = EvalProfile::new(Duration::from_millis(1), 1, 1, false);
    let result = ProfiledEvalResult {
        result: crate::eval_cmd::EvalResult::Value("7".to_owned()),
        profile,
        type_info: None,
    };
    let display = result.display_with_profile();
    assert!(display.contains("7"));
    assert!(!display.contains(": "));
}

// =============================================================================
// format_result_annotated tests
// =============================================================================

#[test]
fn test_format_result_annotated_with_type() {
    let result = crate::eval_cmd::EvalResult::Value("42".to_owned());
    let formatted = format_result_annotated(&result, Some("Nat"));
    assert_eq!(formatted, "42 : Nat");
}

#[test]
fn test_format_result_annotated_without_type() {
    let result = crate::eval_cmd::EvalResult::Value("42".to_owned());
    let formatted = format_result_annotated(&result, None);
    assert_eq!(formatted, "42");
}

// =============================================================================
// format_history tests
// =============================================================================

#[test]
fn test_format_history_empty() {
    let history = EvalHistory::new(10);
    let formatted = format_history(&history);
    assert_eq!(formatted, "(no evaluations recorded)");
}

#[test]
fn test_format_history_single_entry() {
    let mut history = EvalHistory::new(10);
    let profile = EvalProfile::new(Duration::from_millis(1), 1, 1, false);
    let r = crate::eval_cmd::EvalResult::Value("42".to_owned());
    history.record("42".to_owned(), r, profile, Some("Nat".to_owned()));
    let formatted = format_history(&history);
    assert!(formatted.contains("[0]"));
    assert!(formatted.contains("42"));
    assert!(formatted.contains("Nat"));
}

// =============================================================================
// Error display tests
// =============================================================================

#[test]
fn test_eval_ext_error_display_step_limit() {
    let err = EvalExtError::StepLimitExceeded { limit: 100 };
    assert_eq!(format!("{err}"), "step limit exceeded: 100 steps");
}

#[test]
fn test_eval_ext_error_display_time_limit() {
    let err = EvalExtError::TimeLimitExceeded {
        limit: Duration::from_secs(5),
    };
    let msg = format!("{err}");
    assert!(msg.contains("time limit exceeded"));
}

#[test]
fn test_eval_ext_error_display_depth_limit() {
    let err = EvalExtError::DepthLimitExceeded { limit: 50 };
    assert_eq!(format!("{err}"), "depth limit exceeded: 50 levels");
}

#[test]
fn test_eval_ext_error_display_base_eval() {
    let err = EvalExtError::BaseEvalError("something went wrong".to_owned());
    assert_eq!(format!("{err}"), "evaluation error: something went wrong");
}
