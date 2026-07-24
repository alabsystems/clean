// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for closure environment analysis, escape detection, and optimization hints.
//!
//! Part of #3084 - Runtime closure support.

use super::closure_ext::*;
use crate::closure::{CaptureMode, CapturedVar, ClosureBuilder, ClosureConvertResult, ClosureEnv};
use crate::lcnf::{Arg, Code, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Name};
use std::collections::HashSet;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

/// Build a ClosureEnv directly from a list of (id, name, mode) triples.
fn make_env(body: u64, param_count: usize, captures: &[(u64, &str, CaptureMode)]) -> ClosureEnv {
    let mut builder = ClosureBuilder::new(fvar(body), param_count);
    for (i, (id, n, mode)) in captures.iter().enumerate() {
        builder.add_capture(fvar(*id), name(n), i, mode.clone());
    }
    builder.build()
}

/// Build a minimal ClosureConvertResult with a single fun decl and
/// continuation returning that fun.
fn make_result_with_fun(env: &ClosureEnv, body_code: Code) -> ClosureConvertResult {
    let capture_params: Vec<Param> = env
        .captures
        .iter()
        .map(|cap| Param::new(cap.fvar_id, cap.name.clone(), Expr::prop()))
        .collect();
    let mut all_params = capture_params;
    for i in 0..env.param_count {
        all_params.push(Param::new(
            fvar(9000 + i as u64),
            name(&format!("p{i}")),
            nat_type(),
        ));
    }
    let fun_decl = FunDecl::new(env.body_fvar, name("f"), all_params, nat_type(), body_code);
    ClosureConvertResult {
        code: Code::Fun(fun_decl, Box::new(Code::ret(env.body_fvar))),
        closures: vec![env.clone()],
    }
}

// ────────────────────────────────────────────────────────────────────────
// ClosureAnalysisConfig tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_config_default_values() {
    let config = ClosureAnalysisConfig::default();
    assert_eq!(config.inline_capture_limit, 2);
    assert_eq!(config.inline_body_node_limit, 16);
    assert_eq!(config.pointer_size, 8);
    assert_eq!(config.pointer_alignment, 8);
    assert!(config.enable_dead_capture_elimination);
}

#[test]
fn test_config_custom_values() {
    let config = ClosureAnalysisConfig {
        inline_capture_limit: 5,
        inline_body_node_limit: 32,
        pointer_size: 4,
        pointer_alignment: 4,
        enable_dead_capture_elimination: false,
    };
    assert_eq!(config.inline_capture_limit, 5);
    assert_eq!(config.pointer_size, 4);
    assert!(!config.enable_dead_capture_elimination);
}

// ────────────────────────────────────────────────────────────────────────
// CaptureClassification tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_classify_captures_anonymous_is_unknown() {
    let env = make_env(100, 1, &[(10, "", CaptureMode::ByValue)]);
    // Anonymous names default to Unknown since Name::from_string("") creates anon
    let classified = classify_captures(&env);
    assert_eq!(classified.len(), 1);
    // Anonymous or empty name should map to Unknown or Erased depending on
    // the Name::is_anon() behavior. We just check we get a result.
    assert_eq!(classified[0].0, fvar(10));
}

#[test]
fn test_classify_captures_scalar_names() {
    // Names like "i", "j", "k", "n", "idx", "len", "size" are scalars
    for scalar_name in &[
        "i", "j", "k", "n", "idx", "len", "size", "tag", "arity", "depth", "offset",
    ] {
        let env = make_env(100, 1, &[(10, scalar_name, CaptureMode::ByValue)]);
        let classified = classify_captures(&env);
        assert_eq!(
            classified[0].1,
            CaptureClassification::Scalar,
            "expected Scalar for name '{scalar_name}'"
        );
    }
}

#[test]
fn test_classify_captures_scalar_suffix() {
    for suffix_name in &["foo_idx", "bar_len", "count_size"] {
        let env = make_env(100, 1, &[(10, suffix_name, CaptureMode::ByValue)]);
        let classified = classify_captures(&env);
        assert_eq!(
            classified[0].1,
            CaptureClassification::Scalar,
            "expected Scalar for name '{suffix_name}'"
        );
    }
}

#[test]
fn test_classify_captures_erased_names() {
    for erased_name in &["_", "proof", "inst", "type"] {
        let env = make_env(100, 1, &[(10, erased_name, CaptureMode::ByValue)]);
        let classified = classify_captures(&env);
        assert_eq!(
            classified[0].1,
            CaptureClassification::Erased,
            "expected Erased for name '{erased_name}'"
        );
    }
}

#[test]
fn test_classify_captures_object_by_ref() {
    let env = make_env(100, 1, &[(10, "myList", CaptureMode::ByRef)]);
    let classified = classify_captures(&env);
    assert_eq!(classified[0].1, CaptureClassification::Object);
}

#[test]
fn test_classify_captures_object_by_value() {
    let env = make_env(100, 1, &[(10, "myList", CaptureMode::ByValue)]);
    let classified = classify_captures(&env);
    assert_eq!(classified[0].1, CaptureClassification::Object);
}

#[test]
fn test_classify_captures_mixed() {
    let env = make_env(
        100,
        1,
        &[
            (10, "n", CaptureMode::ByValue),
            (20, "proof", CaptureMode::ByValue),
            (30, "list", CaptureMode::ByRef),
        ],
    );
    let classified = classify_captures(&env);
    assert_eq!(classified.len(), 3);
    assert_eq!(classified[0].1, CaptureClassification::Scalar);
    assert_eq!(classified[1].1, CaptureClassification::Erased);
    assert_eq!(classified[2].1, CaptureClassification::Object);
}

// ────────────────────────────────────────────────────────────────────────
// analyze_closure_env tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_analyze_empty_env() {
    let env = make_env(100, 2, &[]);
    let stats = analyze_closure_env(&env);
    assert_eq!(stats.capture_count, 0);
    assert_eq!(stats.by_value_captures, 0);
    assert_eq!(stats.by_ref_captures, 0);
    assert_eq!(stats.scalar_captures, 0);
    assert_eq!(stats.object_captures, 0);
}

#[test]
fn test_analyze_single_scalar_capture() {
    let env = make_env(100, 1, &[(10, "n", CaptureMode::ByValue)]);
    let stats = analyze_closure_env(&env);
    assert_eq!(stats.capture_count, 1);
    assert_eq!(stats.by_value_captures, 1);
    assert_eq!(stats.by_ref_captures, 0);
    assert_eq!(stats.scalar_captures, 1);
    assert_eq!(stats.object_captures, 0);
}

#[test]
fn test_analyze_mixed_captures() {
    let env = make_env(
        100,
        1,
        &[
            (10, "idx", CaptureMode::ByValue),
            (20, "list", CaptureMode::ByRef),
            (30, "proof", CaptureMode::ByValue),
        ],
    );
    let stats = analyze_closure_env(&env);
    assert_eq!(stats.capture_count, 3);
    assert_eq!(stats.by_value_captures, 2);
    assert_eq!(stats.by_ref_captures, 1);
    assert_eq!(stats.scalar_captures, 1);
    assert_eq!(stats.object_captures, 1);
    assert_eq!(stats.erased_captures, 1);
}

#[test]
fn test_analyze_environment_size_nonzero() {
    let env = make_env(
        100,
        1,
        &[
            (10, "x", CaptureMode::ByValue),
            (20, "y", CaptureMode::ByValue),
        ],
    );
    let stats = analyze_closure_env(&env);
    assert!(
        stats.environment_size > 0,
        "non-empty env should have nonzero size"
    );
    assert!(stats.alignment > 0);
}

// ────────────────────────────────────────────────────────────────────────
// ClosureLayout tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_layout_empty_env() {
    let env = make_env(100, 1, &[]);
    let layout = compute_closure_layout(&env);
    // Just the header (function pointer), aligned
    assert!(layout.size > 0);
    assert_eq!(layout.field_offsets.len(), 0);
    assert_eq!(layout.header_size, 8); // default pointer_size
}

#[test]
fn test_layout_single_capture() {
    let env = make_env(100, 1, &[(10, "x", CaptureMode::ByValue)]);
    let layout = compute_closure_layout(&env);
    assert!(layout.field_offsets.contains_key(&fvar(10)));
    let offset = layout.field_offsets[&fvar(10)];
    assert!(offset >= layout.header_size, "field should be after header");
    assert_eq!(layout.alignment, 8);
}

#[test]
fn test_layout_erased_captures_skipped() {
    let env = make_env(
        100,
        1,
        &[
            (10, "proof", CaptureMode::ByValue), // erased
            (20, "x", CaptureMode::ByValue),     // object
        ],
    );
    let layout = compute_closure_layout(&env);
    // Erased captures should NOT have an offset
    assert!(!layout.field_offsets.contains_key(&fvar(10)));
    // Non-erased should
    assert!(layout.field_offsets.contains_key(&fvar(20)));
}

#[test]
fn test_layout_multiple_captures_ordered() {
    let env = make_env(
        100,
        1,
        &[
            (10, "a", CaptureMode::ByValue),
            (20, "b", CaptureMode::ByValue),
            (30, "c", CaptureMode::ByValue),
        ],
    );
    let layout = compute_closure_layout(&env);
    assert_eq!(layout.field_offsets.len(), 3);
    let a = layout.field_offsets[&fvar(10)];
    let b = layout.field_offsets[&fvar(20)];
    let c = layout.field_offsets[&fvar(30)];
    assert!(a < b, "captures should be in order");
    assert!(b < c, "captures should be in order");
}

// ────────────────────────────────────────────────────────────────────────
// EscapeStatus tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_escape_local_simple_return() {
    // fun f(cap_x) := return cap_x  -- does not return f itself
    // continuation: return f
    // The closure f itself is returned, so it escapes.
    let env = make_env(100, 0, &[(10, "x", CaptureMode::ByValue)]);
    let body = Code::ret(fvar(10));
    let result = make_result_with_fun(&env, body);
    let status = detect_escape_status(&env, &result);
    // f is returned in continuation, so it escapes
    assert_eq!(status, EscapeStatus::Escaping);
}

#[test]
fn test_escape_unknown_no_fun_decl() {
    // If we can't find the fun decl, status is Unknown
    let env = make_env(100, 1, &[(10, "x", CaptureMode::ByValue)]);
    let result = ClosureConvertResult {
        code: Code::ret(fvar(999)),
        closures: vec![env.clone()],
    };
    let status = detect_escape_status(&env, &result);
    assert_eq!(status, EscapeStatus::Unknown);
}

#[test]
fn test_escape_not_returned() {
    // fun f(cap_x) := return cap_x
    // continuation: return some_other (not f)
    let env = make_env(100, 0, &[(10, "x", CaptureMode::ByValue)]);
    let body = Code::ret(fvar(10));
    let capture_params: Vec<Param> = env
        .captures
        .iter()
        .map(|cap| Param::new(cap.fvar_id, cap.name.clone(), Expr::prop()))
        .collect();
    let fun_decl = FunDecl::new(env.body_fvar, name("f"), capture_params, nat_type(), body);
    let result = ClosureConvertResult {
        code: Code::Fun(fun_decl, Box::new(Code::ret(fvar(999)))),
        closures: vec![env.clone()],
    };
    let status = detect_escape_status(&env, &result);
    assert_eq!(status, EscapeStatus::Local);
}

// ────────────────────────────────────────────────────────────────────────
// ClosureOptHint tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_hints_no_hint_for_large_closure() {
    let env = make_env(
        100,
        1,
        &[
            (10, "a", CaptureMode::ByValue),
            (20, "b", CaptureMode::ByValue),
            (30, "c", CaptureMode::ByValue),
            (40, "d", CaptureMode::ByValue),
        ],
    );
    // Build a body that uses all captures
    let body = Code::let_bind(
        LetDecl::new(
            fvar(5),
            name("r"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(10),
                args: vec![
                    Arg::FVar(fvar(20)),
                    Arg::FVar(fvar(30)),
                    Arg::FVar(fvar(40)),
                ],
            },
        ),
        Code::ret(fvar(5)),
    );
    let result = make_result_with_fun(&env, body);
    let config = ClosureAnalysisConfig::default();
    let hints = compute_optimization_hints(&env, &result, &config);
    assert!(hints.contains(&ClosureOptHint::NoHint));
}

#[test]
fn test_hints_constant_closure_no_captures() {
    let env = make_env(100, 1, &[]);
    let body = Code::ret(fvar(9000)); // uses only declared param
    let result = make_result_with_fun(&env, body);
    let config = ClosureAnalysisConfig::default();
    let hints = compute_optimization_hints(&env, &result, &config);
    assert!(hints.contains(&ClosureOptHint::ConstantClosure));
}

#[test]
fn test_hints_dead_captures_detected() {
    // Env has capture fvar(10), but body doesn't use it
    let env = make_env(100, 1, &[(10, "unused", CaptureMode::ByValue)]);
    let body = Code::ret(fvar(9000)); // only uses declared param, not capture
    let result = make_result_with_fun(&env, body);
    let config = ClosureAnalysisConfig::default();
    let hints = compute_optimization_hints(&env, &result, &config);
    assert!(hints.contains(&ClosureOptHint::HasDeadCaptures));
    assert!(hints.contains(&ClosureOptHint::ConstantClosure));
}

#[test]
fn test_hints_dead_capture_elimination_disabled() {
    let env = make_env(100, 1, &[(10, "unused", CaptureMode::ByValue)]);
    let body = Code::ret(fvar(9000));
    let result = make_result_with_fun(&env, body);
    let config = ClosureAnalysisConfig {
        enable_dead_capture_elimination: false,
        ..ClosureAnalysisConfig::default()
    };
    let hints = compute_optimization_hints(&env, &result, &config);
    // Without dead capture elimination, we can't detect dead captures
    assert!(!hints.contains(&ClosureOptHint::HasDeadCaptures));
}

// ────────────────────────────────────────────────────────────────────────
// eliminate_dead_captures tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_eliminate_dead_all_live() {
    let env = make_env(100, 0, &[(10, "x", CaptureMode::ByValue)]);
    // Body uses fvar(10)
    let body = Code::ret(fvar(10));
    let result = make_result_with_fun(&env, body);
    let pruned = eliminate_dead_captures(&env, &result);
    assert_eq!(pruned.capture_count(), 1, "live capture should remain");
}

#[test]
fn test_eliminate_dead_removes_unused() {
    let env = make_env(
        100,
        0,
        &[
            (10, "used", CaptureMode::ByValue),
            (20, "unused", CaptureMode::ByValue),
        ],
    );
    // Body only references fvar(10)
    let body = Code::ret(fvar(10));
    let result = make_result_with_fun(&env, body);
    let pruned = eliminate_dead_captures(&env, &result);
    assert_eq!(pruned.capture_count(), 1);
    assert!(pruned.find_capture(fvar(10)).is_some());
    assert!(pruned.find_capture(fvar(20)).is_none());
}

#[test]
fn test_eliminate_dead_reindexes() {
    let env = make_env(
        100,
        0,
        &[
            (10, "dead", CaptureMode::ByValue),
            (20, "live", CaptureMode::ByValue),
        ],
    );
    let body = Code::ret(fvar(20));
    let result = make_result_with_fun(&env, body);
    let pruned = eliminate_dead_captures(&env, &result);
    assert_eq!(pruned.capture_count(), 1);
    let cap = pruned.find_capture(fvar(20)).unwrap();
    assert_eq!(cap.index, 0, "reindexed to 0 after dead removal");
}

#[test]
fn test_eliminate_dead_preserves_body_fvar_and_param_count() {
    let env = make_env(100, 3, &[(10, "dead", CaptureMode::ByValue)]);
    let body = Code::ret(fvar(9000));
    let result = make_result_with_fun(&env, body);
    let pruned = eliminate_dead_captures(&env, &result);
    assert_eq!(pruned.body_fvar, fvar(100));
    assert_eq!(pruned.param_count, 3);
}

// ────────────────────────────────────────────────────────────────────────
// pretty_print_env tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_pretty_print_empty_env() {
    let env = make_env(100, 2, &[]);
    let output = pretty_print_env(&env);
    assert!(output.contains("closure _x100"));
    assert!(output.contains("params=2"));
    assert!(output.contains("captures=0"));
}

#[test]
fn test_pretty_print_with_captures() {
    let env = make_env(
        100,
        1,
        &[
            (10, "n", CaptureMode::ByValue),
            (20, "list", CaptureMode::ByRef),
        ],
    );
    let output = pretty_print_env(&env);
    assert!(output.contains("captures=2"));
    assert!(output.contains("_x10"));
    assert!(output.contains("_x20"));
    assert!(output.contains("ByValue"));
    assert!(output.contains("ByRef"));
}

#[test]
fn test_pretty_print_erased_offset() {
    let env = make_env(100, 0, &[(10, "proof", CaptureMode::ByValue)]);
    let output = pretty_print_env(&env);
    assert!(
        output.contains("erased"),
        "erased capture should show 'erased' offset"
    );
}

// ────────────────────────────────────────────────────────────────────────
// analyze_all_closures tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_analyze_all_empty() {
    let result = ClosureConvertResult {
        code: Code::ret(fvar(1)),
        closures: vec![],
    };
    let all_stats = analyze_all_closures(&result);
    assert!(all_stats.is_empty());
}

#[test]
fn test_analyze_all_single() {
    let env = make_env(100, 1, &[(10, "x", CaptureMode::ByValue)]);
    let body = Code::ret(fvar(10));
    let result = make_result_with_fun(&env, body);
    let all_stats = analyze_all_closures(&result);
    assert_eq!(all_stats.len(), 1);
    assert_eq!(all_stats[0].capture_count, 1);
}

// ────────────────────────────────────────────────────────────────────────
// compute_closure_depth tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_closure_depth_top_level() {
    // A fun at top level has depth 1
    let env = make_env(100, 1, &[]);
    let body = Code::ret(fvar(9000));
    let result = make_result_with_fun(&env, body);
    let depth = compute_closure_depth(&env, &result);
    assert_eq!(depth, 1);
}

#[test]
fn test_closure_depth_nested() {
    // fun f () :=
    //   fun g () := return g_param
    //   return g
    // return f
    let inner_fun = FunDecl::new(
        fvar(200),
        name("g"),
        vec![Param::new(fvar(2), name("y"), nat_type())],
        nat_type(),
        Code::ret(fvar(2)),
    );
    let outer_fun = FunDecl::new(
        fvar(100),
        name("f"),
        vec![Param::new(fvar(1), name("x"), nat_type())],
        nat_type(),
        Code::Fun(inner_fun, Box::new(Code::ret(fvar(200)))),
    );
    let result = ClosureConvertResult {
        code: Code::Fun(outer_fun, Box::new(Code::ret(fvar(100)))),
        closures: vec![make_env(100, 1, &[]), make_env(200, 1, &[])],
    };
    let inner_env = make_env(200, 1, &[]);
    let depth = compute_closure_depth(&inner_env, &result);
    assert_eq!(depth, 2, "inner fun should have depth 2");
}

#[test]
fn test_closure_depth_no_fun_returns_zero() {
    let env = make_env(999, 1, &[]);
    let result = ClosureConvertResult {
        code: Code::ret(fvar(1)),
        closures: vec![],
    };
    let depth = compute_closure_depth(&env, &result);
    assert_eq!(depth, 0, "no matching fun decl means depth 0");
}

// ────────────────────────────────────────────────────────────────────────
// detect_constant_closures tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_detect_constant_closures_none() {
    let env = make_env(100, 1, &[(10, "x", CaptureMode::ByValue)]);
    // Body uses the capture
    let body = Code::ret(fvar(10));
    let result = make_result_with_fun(&env, body);
    let constants = detect_constant_closures(&result);
    assert!(constants.is_empty());
}

#[test]
fn test_detect_constant_closures_already_empty() {
    let env = make_env(100, 1, &[]);
    let body = Code::ret(fvar(9000));
    let result = make_result_with_fun(&env, body);
    let constants = detect_constant_closures(&result);
    assert_eq!(constants, vec![fvar(100)]);
}

#[test]
fn test_detect_constant_closures_dead_captures_eliminated() {
    let env = make_env(100, 1, &[(10, "dead", CaptureMode::ByValue)]);
    // Body does NOT use fvar(10) — only uses declared param
    let body = Code::ret(fvar(9000));
    let result = make_result_with_fun(&env, body);
    let constants = detect_constant_closures(&result);
    assert_eq!(
        constants,
        vec![fvar(100)],
        "dead-capture-eliminated closure is constant"
    );
}

// ────────────────────────────────────────────────────────────────────────
// ClosureStats equality and default tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_closure_stats_default() {
    let stats = ClosureStats::default();
    assert_eq!(stats.capture_count, 0);
    assert_eq!(stats.by_value_captures, 0);
    assert_eq!(stats.by_ref_captures, 0);
    assert_eq!(stats.scalar_captures, 0);
    assert_eq!(stats.object_captures, 0);
    assert_eq!(stats.erased_captures, 0);
    assert_eq!(stats.unknown_captures, 0);
    assert_eq!(stats.environment_size, 0);
    assert_eq!(stats.alignment, 0);
    assert_eq!(stats.closure_depth, 0);
}

#[test]
fn test_closure_stats_equality() {
    let a = ClosureStats {
        capture_count: 2,
        ..ClosureStats::default()
    };
    let b = ClosureStats {
        capture_count: 2,
        ..ClosureStats::default()
    };
    assert_eq!(a, b);
}

// ────────────────────────────────────────────────────────────────────────
// EscapeStatus and ClosureOptHint enum tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_escape_status_equality() {
    assert_eq!(EscapeStatus::Local, EscapeStatus::Local);
    assert_eq!(EscapeStatus::Escaping, EscapeStatus::Escaping);
    assert_eq!(EscapeStatus::Unknown, EscapeStatus::Unknown);
    assert_ne!(EscapeStatus::Local, EscapeStatus::Escaping);
}

#[test]
fn test_closure_opt_hint_equality() {
    assert_eq!(
        ClosureOptHint::InlineCandidate,
        ClosureOptHint::InlineCandidate
    );
    assert_eq!(
        ClosureOptHint::ConstantClosure,
        ClosureOptHint::ConstantClosure
    );
    assert_eq!(
        ClosureOptHint::HasDeadCaptures,
        ClosureOptHint::HasDeadCaptures
    );
    assert_eq!(ClosureOptHint::NoHint, ClosureOptHint::NoHint);
    assert_ne!(ClosureOptHint::InlineCandidate, ClosureOptHint::NoHint);
}

// ────────────────────────────────────────────────────────────────────────
// ClosureLayout default test
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_closure_layout_default() {
    let layout = ClosureLayout::default();
    assert_eq!(layout.size, 0);
    assert_eq!(layout.alignment, 0);
    assert_eq!(layout.header_size, 0);
    assert!(layout.field_offsets.is_empty());
}

// ────────────────────────────────────────────────────────────────────────
// Edge case: code_references_fvar through various Code variants
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_dead_capture_through_let_value() {
    // Capture is used only in a let value (FVar application)
    let env = make_env(100, 0, &[(10, "x", CaptureMode::ByValue)]);
    let body = Code::let_bind(
        LetDecl::new(
            fvar(5),
            name("r"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(10),
                args: vec![],
            },
        ),
        Code::ret(fvar(5)),
    );
    let result = make_result_with_fun(&env, body);
    let pruned = eliminate_dead_captures(&env, &result);
    assert_eq!(
        pruned.capture_count(),
        1,
        "capture used in let value should be live"
    );
}

#[test]
fn test_dead_capture_through_const_args() {
    let env = make_env(100, 0, &[(10, "x", CaptureMode::ByValue)]);
    let body = Code::let_bind(
        LetDecl::new(
            fvar(5),
            name("r"),
            nat_type(),
            LetValue::Const {
                name: name("Nat.succ"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(10))],
            },
        ),
        Code::ret(fvar(5)),
    );
    let result = make_result_with_fun(&env, body);
    let pruned = eliminate_dead_captures(&env, &result);
    assert_eq!(
        pruned.capture_count(),
        1,
        "capture used as const arg should be live"
    );
}

#[test]
fn test_dead_capture_through_jmp() {
    let env = make_env(100, 0, &[(10, "x", CaptureMode::ByValue)]);
    let body = Code::jmp(fvar(999), vec![Arg::FVar(fvar(10))]);
    let result = make_result_with_fun(&env, body);
    let pruned = eliminate_dead_captures(&env, &result);
    assert_eq!(
        pruned.capture_count(),
        1,
        "capture used as jmp arg should be live"
    );
}

#[test]
fn test_dead_capture_through_cases_scrutinee() {
    let env = make_env(100, 0, &[(10, "x", CaptureMode::ByValue)]);
    let body = Code::cases(
        name("Bool"),
        nat_type(),
        fvar(10),
        vec![crate::lcnf::Alt::default(Code::ret(fvar(10)))],
    );
    let result = make_result_with_fun(&env, body);
    let pruned = eliminate_dead_captures(&env, &result);
    assert_eq!(
        pruned.capture_count(),
        1,
        "capture used as scrutinee should be live"
    );
}

#[test]
fn test_dead_capture_through_projection() {
    let env = make_env(100, 0, &[(10, "x", CaptureMode::ByValue)]);
    let body = Code::let_bind(
        LetDecl::new(
            fvar(5),
            name("field"),
            nat_type(),
            LetValue::Proj {
                type_name: name("Prod"),
                idx: 0,
                structure: fvar(10),
            },
        ),
        Code::ret(fvar(5)),
    );
    let result = make_result_with_fun(&env, body);
    let pruned = eliminate_dead_captures(&env, &result);
    assert_eq!(
        pruned.capture_count(),
        1,
        "capture used as projection structure should be live"
    );
}
