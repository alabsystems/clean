// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended native evaluation: profiling, tracing, budget, analysis.
//!
//! Part of #3084 - Native type compilation for UInt and Float.

use std::collections::HashMap;

use crate::native_eval::NativeValue;
use crate::native_eval_ext::*;
use crate::native_types::{NativeExpr, NativeOp, NativeType};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn uint32(val: u64) -> NativeExpr {
    NativeExpr::Lit(NativeType::UInt32, val)
}

fn uint8(val: u64) -> NativeExpr {
    NativeExpr::Lit(NativeType::UInt8, val)
}

fn float_expr(val: f64) -> NativeExpr {
    NativeExpr::Lit(NativeType::Float, val.to_bits())
}

fn add(lhs: NativeExpr, rhs: NativeExpr) -> NativeExpr {
    NativeExpr::BinOp(NativeOp::Add, Box::new(lhs), Box::new(rhs))
}

fn mul(lhs: NativeExpr, rhs: NativeExpr) -> NativeExpr {
    NativeExpr::BinOp(NativeOp::Mul, Box::new(lhs), Box::new(rhs))
}

fn var(name: &str) -> NativeExpr {
    NativeExpr::Var(name.to_owned())
}

// ---------------------------------------------------------------------------
// inspect_value tests
// ---------------------------------------------------------------------------

#[test]
fn test_inspect_value_uint8() {
    let s = inspect_value(&NativeValue::UInt8(42));
    assert_eq!(s, "UInt8(42)");
}

#[test]
fn test_inspect_value_uint16() {
    let s = inspect_value(&NativeValue::UInt16(1000));
    assert_eq!(s, "UInt16(1000)");
}

#[test]
fn test_inspect_value_uint32_hex() {
    let s = inspect_value(&NativeValue::UInt32(255));
    assert!(s.contains("0x000000FF"), "got: {}", s);
    assert!(s.contains("255"), "got: {}", s);
}

#[test]
fn test_inspect_value_uint64_hex() {
    let s = inspect_value(&NativeValue::UInt64(0xDEAD));
    assert!(s.contains("0x000000000000DEAD"), "got: {}", s);
}

#[test]
fn test_inspect_value_usize() {
    let s = inspect_value(&NativeValue::USize(100));
    assert_eq!(s, "USize(100)");
}

#[test]
fn test_inspect_value_float_normal() {
    let s = inspect_value(&NativeValue::Float(1.25));
    assert!(s.starts_with("Float("), "got: {}", s);
    assert!(s.contains("1.25"), "got: {}", s);
}

#[test]
fn test_inspect_value_float_nan() {
    let s = inspect_value(&NativeValue::Float(f64::NAN));
    assert_eq!(s, "Float(NaN)");
}

#[test]
fn test_inspect_value_float_pos_inf() {
    let s = inspect_value(&NativeValue::Float(f64::INFINITY));
    assert_eq!(s, "Float(+Inf)");
}

#[test]
fn test_inspect_value_float_neg_inf() {
    let s = inspect_value(&NativeValue::Float(f64::NEG_INFINITY));
    assert_eq!(s, "Float(-Inf)");
}

#[test]
fn test_inspect_value_bool_true() {
    assert_eq!(inspect_value(&NativeValue::Bool(true)), "Bool(true)");
}

#[test]
fn test_inspect_value_bool_false() {
    assert_eq!(inspect_value(&NativeValue::Bool(false)), "Bool(false)");
}

// ---------------------------------------------------------------------------
// inspect_expr tests
// ---------------------------------------------------------------------------

#[test]
fn test_inspect_expr_literal() {
    let s = inspect_expr(&uint32(42));
    assert_eq!(s, "Lit(UInt32, 42)");
}

#[test]
fn test_inspect_expr_binop() {
    let expr = add(uint32(1), uint32(2));
    let s = inspect_expr(&expr);
    assert!(s.contains("Add"), "got: {}", s);
}

#[test]
fn test_inspect_expr_unaryop() {
    let expr = NativeExpr::UnaryOp(NativeOp::Complement, Box::new(uint8(0)));
    let s = inspect_expr(&expr);
    assert!(s.contains("Complement"), "got: {}", s);
}

#[test]
fn test_inspect_expr_var() {
    let s = inspect_expr(&var("x"));
    assert_eq!(s, "Var(x)");
}

#[test]
fn test_inspect_expr_call() {
    let expr = NativeExpr::Call("foo".to_owned(), vec![uint32(1), uint32(2)]);
    let s = inspect_expr(&expr);
    assert!(s.contains("Call(foo"), "got: {}", s);
}

// ---------------------------------------------------------------------------
// EvalBudget tests
// ---------------------------------------------------------------------------

#[test]
fn test_budget_default_has_limits() {
    let b = EvalBudget::default();
    assert!(b.max_steps > 0);
    assert!(b.max_allocations > 0);
    assert!(b.max_depth > 0);
}

#[test]
fn test_budget_unlimited_all_zero() {
    let b = EvalBudget::unlimited();
    assert_eq!(b.max_steps, 0);
    assert_eq!(b.max_allocations, 0);
    assert_eq!(b.max_depth, 0);
}

#[test]
fn test_budget_with_steps() {
    let b = EvalBudget::with_steps(500);
    assert_eq!(b.max_steps, 500);
    assert!(b.max_depth > 0, "depth should still be defaulted");
}

// ---------------------------------------------------------------------------
// eval_profiled — basic tests
// ---------------------------------------------------------------------------

#[test]
fn test_profiled_literal_steps() {
    let (val, profile) = eval_profiled(&uint32(42), &EvalBudget::unlimited(), TraceDetail::Minimal)
        .expect("literal should succeed");
    assert_eq!(val, NativeValue::UInt32(42));
    assert_eq!(profile.total_steps, 1);
    assert_eq!(profile.total_allocations, 0);
}

#[test]
fn test_profiled_binop_counts() {
    let expr = add(uint32(10), uint32(20));
    let (val, profile) = eval_profiled(&expr, &EvalBudget::unlimited(), TraceDetail::Minimal)
        .expect("add should succeed");
    assert_eq!(val, NativeValue::UInt32(30));
    // 1 step for the Add op + 2 steps for the two Lit children = 3 total
    assert_eq!(profile.total_steps, 3);
    assert!(profile.total_allocations >= 1);
}

#[test]
fn test_profiled_nested_binop() {
    // (1 + 2) * 3 = 9
    let expr = mul(add(uint32(1), uint32(2)), uint32(3));
    let (val, profile) = eval_profiled(&expr, &EvalBudget::unlimited(), TraceDetail::Minimal)
        .expect("nested op should succeed");
    assert_eq!(val, NativeValue::UInt32(9));
    // Mul(Add(Lit, Lit), Lit) => Mul:1 + Add:1 + Lit:3 = 5
    assert_eq!(profile.total_steps, 5);
}

#[test]
fn test_profiled_max_depth_tracked() {
    // depth 0: mul, depth 1: add + lit, depth 2: lit + lit
    let expr = mul(add(uint32(1), uint32(2)), uint32(3));
    let (_, profile) = eval_profiled(&expr, &EvalBudget::unlimited(), TraceDetail::Minimal)
        .expect("should succeed");
    assert_eq!(profile.max_depth_reached, 2);
}

// ---------------------------------------------------------------------------
// eval_profiled — trace tests
// ---------------------------------------------------------------------------

#[test]
fn test_profiled_steps_trace_non_empty() {
    let expr = add(uint32(1), uint32(2));
    let (_, profile) =
        eval_profiled(&expr, &EvalBudget::unlimited(), TraceDetail::Steps).expect("should succeed");
    assert!(
        !profile.trace.is_empty(),
        "Steps detail should produce trace entries"
    );
}

#[test]
fn test_profiled_minimal_trace_is_empty() {
    let expr = add(uint32(1), uint32(2));
    let (_, profile) = eval_profiled(&expr, &EvalBudget::unlimited(), TraceDetail::Minimal)
        .expect("should succeed");
    assert!(profile.trace.is_empty(), "Minimal should produce no trace");
}

#[test]
fn test_profiled_full_trace_has_details() {
    let expr = add(uint32(10), uint32(20));
    let (_, profile) =
        eval_profiled(&expr, &EvalBudget::unlimited(), TraceDetail::Full).expect("should succeed");
    // Full trace should contain value inspection strings
    let text = format_trace(&profile);
    assert!(
        text.contains("UInt32"),
        "Full trace should contain value details: {}",
        text
    );
}

// ---------------------------------------------------------------------------
// eval_profiled — budget exceeded tests
// ---------------------------------------------------------------------------

#[test]
fn test_profiled_step_budget_exceeded() {
    let expr = add(uint32(1), uint32(2));
    let budget = EvalBudget {
        max_steps: 1,
        max_allocations: 0,
        max_depth: 0,
    };
    let result = eval_profiled(&expr, &budget, TraceDetail::Minimal);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalExtError::StepBudgetExceeded { limit: 1, .. }),
        "expected StepBudgetExceeded, got: {:?}",
        err
    );
}

#[test]
fn test_profiled_depth_budget_exceeded() {
    // Build a chain deep enough: a + (b + (c + d))
    let deep = add(uint32(1), add(uint32(2), add(uint32(3), uint32(4))));
    let budget = EvalBudget {
        max_steps: 0,
        max_allocations: 0,
        max_depth: 2,
    };
    let result = eval_profiled(&deep, &budget, TraceDetail::Minimal);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalExtError::DepthBudgetExceeded { limit: 2, .. }),
        "expected DepthBudgetExceeded, got: {:?}",
        err
    );
}

#[test]
fn test_profiled_allocation_budget_exceeded() {
    // Each BinOp records an allocation; with budget of 1, second BinOp fails.
    let expr = add(add(uint32(1), uint32(2)), uint32(3));
    let budget = EvalBudget {
        max_steps: 0,
        max_allocations: 1,
        max_depth: 0,
    };
    let result = eval_profiled(&expr, &budget, TraceDetail::Minimal);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalExtError::AllocationBudgetExceeded { limit: 1, .. }),
        "expected AllocationBudgetExceeded, got: {:?}",
        err
    );
}

// ---------------------------------------------------------------------------
// eval_profiled — error propagation
// ---------------------------------------------------------------------------

#[test]
fn test_profiled_var_error() {
    let result = eval_profiled(&var("x"), &EvalBudget::unlimited(), TraceDetail::Minimal);
    assert!(result.is_err());
    assert!(
        matches!(result.unwrap_err(), EvalExtError::Eval(_)),
        "expected wrapped eval error"
    );
}

// ---------------------------------------------------------------------------
// EvalProfile Display
// ---------------------------------------------------------------------------

#[test]
fn test_profile_display_format() {
    let expr = add(uint32(1), uint32(2));
    let (_, profile) = eval_profiled(&expr, &EvalBudget::unlimited(), TraceDetail::Minimal)
        .expect("should succeed");
    let display = format!("{}", profile);
    assert!(display.contains("steps:"), "Display should show steps");
    assert!(
        display.contains("allocations:"),
        "Display should show allocations"
    );
}

// ---------------------------------------------------------------------------
// EvalStats tests
// ---------------------------------------------------------------------------

#[test]
fn test_stats_default_zeros() {
    let s = EvalStats::default();
    assert_eq!(s.eval_count, 0);
    assert_eq!(s.total_steps, 0);
    assert_eq!(s.cache_hit_rate(), 0.0);
    assert_eq!(s.avg_steps(), 0.0);
}

#[test]
fn test_stats_record_single() {
    let mut stats = EvalStats::default();
    let (_, profile) = eval_profiled(&uint32(42), &EvalBudget::unlimited(), TraceDetail::Minimal)
        .expect("should succeed");
    stats.record(&profile);
    assert_eq!(stats.eval_count, 1);
    assert_eq!(stats.total_steps, 1);
}

#[test]
fn test_stats_record_multiple() {
    let mut stats = EvalStats::default();
    for _ in 0..5 {
        let (_, profile) =
            eval_profiled(&uint32(0), &EvalBudget::unlimited(), TraceDetail::Minimal)
                .expect("should succeed");
        stats.record(&profile);
    }
    assert_eq!(stats.eval_count, 5);
    assert_eq!(stats.total_steps, 5);
    assert!((stats.avg_steps() - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_stats_cache_hit_rate() {
    let stats = EvalStats {
        cache_hits: 3,
        cache_misses: 7,
        ..EvalStats::default()
    };
    assert!((stats.cache_hit_rate() - 0.3).abs() < f64::EPSILON);
}

#[test]
fn test_stats_max_depth_across_evals() {
    let mut stats = EvalStats::default();

    let (_, p1) = eval_profiled(&uint32(1), &EvalBudget::unlimited(), TraceDetail::Minimal)
        .expect("should succeed");
    stats.record(&p1);

    let deep = add(uint32(1), add(uint32(2), uint32(3)));
    let (_, p2) = eval_profiled(&deep, &EvalBudget::unlimited(), TraceDetail::Minimal)
        .expect("should succeed");
    stats.record(&p2);

    assert_eq!(stats.max_depth_seen, 2);
}

// ---------------------------------------------------------------------------
// analyze_expr tests
// ---------------------------------------------------------------------------

#[test]
fn test_analyze_literal() {
    let a = analyze_expr(&uint32(42));
    assert_eq!(a.node_count, 1);
    assert_eq!(a.max_depth, 0);
    assert_eq!(a.lit_count, 1);
    assert_eq!(a.var_count, 0);
}

#[test]
fn test_analyze_binop_tree() {
    let expr = add(uint32(1), uint32(2));
    let a = analyze_expr(&expr);
    assert_eq!(a.node_count, 3); // Add + 2 Lits
    assert_eq!(a.max_depth, 1);
    assert_eq!(a.lit_count, 2);
}

#[test]
fn test_analyze_nested_tree() {
    // (a + b) * c where a,b,c are lits
    let expr = mul(add(uint32(1), uint32(2)), uint32(3));
    let a = analyze_expr(&expr);
    assert_eq!(a.node_count, 5); // Mul + Add + 3 Lits
    assert_eq!(a.max_depth, 2);
    assert_eq!(a.lit_count, 3);
}

#[test]
fn test_analyze_with_vars() {
    let expr = add(var("x"), uint32(1));
    let a = analyze_expr(&expr);
    assert_eq!(a.var_count, 1);
    assert_eq!(a.lit_count, 1);
    assert_eq!(a.node_count, 3);
}

#[test]
fn test_analyze_call() {
    let expr = NativeExpr::Call("foo".to_owned(), vec![uint32(1), uint32(2)]);
    let a = analyze_expr(&expr);
    assert_eq!(a.call_count, 1);
    assert_eq!(a.node_count, 3); // Call + 2 Lits
}

#[test]
fn test_analyze_op_histogram() {
    let expr = add(add(uint32(1), uint32(2)), uint32(3));
    let a = analyze_expr(&expr);
    assert_eq!(*a.op_histogram.get("Add").unwrap_or(&0), 2);
    assert_eq!(*a.op_histogram.get("Lit").unwrap_or(&0), 3);
}

// ---------------------------------------------------------------------------
// hot_ops tests
// ---------------------------------------------------------------------------

#[test]
fn test_hot_ops_empty_profile() {
    let profile = EvalProfile::default();
    let hot = hot_ops(&profile, 0.5);
    assert!(hot.is_empty());
}

#[test]
fn test_hot_ops_identifies_dominant_op() {
    let expr = add(add(add(uint32(1), uint32(2)), uint32(3)), uint32(4));
    let (_, profile) = eval_profiled(&expr, &EvalBudget::unlimited(), TraceDetail::Minimal)
        .expect("should succeed");
    let hot = hot_ops(&profile, 0.3);
    // Lit should be the most frequent (4 literals)
    assert!(!hot.is_empty(), "should have hot ops");
    assert_eq!(hot[0].0, "Lit", "Lit should be hottest op");
}

// ---------------------------------------------------------------------------
// format_trace tests
// ---------------------------------------------------------------------------

#[test]
fn test_format_trace_empty() {
    let profile = EvalProfile::default();
    let s = format_trace(&profile);
    assert!(s.is_empty());
}

#[test]
fn test_format_trace_non_empty() {
    let expr = add(uint32(1), uint32(2));
    let (_, profile) =
        eval_profiled(&expr, &EvalBudget::unlimited(), TraceDetail::Steps).expect("should succeed");
    let s = format_trace(&profile);
    assert!(!s.is_empty());
    assert!(s.contains("Lit"), "trace should show Lit entries");
}

// ---------------------------------------------------------------------------
// partial_eval tests
// ---------------------------------------------------------------------------

#[test]
fn test_partial_eval_literal_is_concrete() {
    let result = partial_eval(&uint32(42), &HashMap::new());
    assert_eq!(result, PartialValue::Concrete(NativeValue::UInt32(42)));
}

#[test]
fn test_partial_eval_var_unbound_is_symbolic() {
    let result = partial_eval(&var("x"), &HashMap::new());
    assert!(matches!(result, PartialValue::Symbolic(_)));
}

#[test]
fn test_partial_eval_var_bound_is_concrete() {
    let mut bindings = HashMap::new();
    bindings.insert("x".to_owned(), NativeValue::UInt32(10));
    let result = partial_eval(&var("x"), &bindings);
    assert_eq!(result, PartialValue::Concrete(NativeValue::UInt32(10)));
}

#[test]
fn test_partial_eval_binop_both_concrete() {
    let expr = add(uint32(10), uint32(20));
    let result = partial_eval(&expr, &HashMap::new());
    assert_eq!(result, PartialValue::Concrete(NativeValue::UInt32(30)));
}

#[test]
fn test_partial_eval_binop_one_symbolic() {
    let expr = add(var("x"), uint32(20));
    let result = partial_eval(&expr, &HashMap::new());
    assert!(matches!(result, PartialValue::Symbolic(_)));
}

#[test]
fn test_partial_eval_binop_with_binding() {
    let mut bindings = HashMap::new();
    bindings.insert("x".to_owned(), NativeValue::UInt32(10));
    let expr = add(var("x"), uint32(20));
    let result = partial_eval(&expr, &bindings);
    assert_eq!(result, PartialValue::Concrete(NativeValue::UInt32(30)));
}

#[test]
fn test_partial_eval_unary_concrete() {
    let expr = NativeExpr::UnaryOp(NativeOp::Complement, Box::new(uint8(0)));
    let result = partial_eval(&expr, &HashMap::new());
    assert_eq!(result, PartialValue::Concrete(NativeValue::UInt8(255)));
}

#[test]
fn test_partial_eval_unary_symbolic() {
    let expr = NativeExpr::UnaryOp(NativeOp::Complement, Box::new(var("x")));
    let result = partial_eval(&expr, &HashMap::new());
    assert!(matches!(result, PartialValue::Symbolic(_)));
}

#[test]
fn test_partial_eval_nested_partial_substitution() {
    // (x + 10) * 3 with x=5 => (5 + 10) * 3 = 45
    let mut bindings = HashMap::new();
    bindings.insert("x".to_owned(), NativeValue::UInt32(5));
    let expr = mul(add(var("x"), uint32(10)), uint32(3));
    let result = partial_eval(&expr, &bindings);
    assert_eq!(result, PartialValue::Concrete(NativeValue::UInt32(45)));
}

#[test]
fn test_partial_eval_float() {
    let expr = NativeExpr::BinOp(
        NativeOp::Add,
        Box::new(float_expr(1.5)),
        Box::new(float_expr(2.5)),
    );
    let result = partial_eval(&expr, &HashMap::new());
    assert_eq!(result, PartialValue::Concrete(NativeValue::Float(4.0)));
}

#[test]
fn test_partial_eval_call_symbolic() {
    let expr = NativeExpr::Call("foo".to_owned(), vec![uint32(1)]);
    let result = partial_eval(&expr, &HashMap::new());
    // Calls to unresolved functions remain symbolic
    assert!(matches!(result, PartialValue::Symbolic(_)));
}

// ---------------------------------------------------------------------------
// TraceEntry Display
// ---------------------------------------------------------------------------

#[test]
fn test_trace_entry_display_with_result() {
    let entry = TraceEntry {
        step: 0,
        depth: 1,
        description: "Lit(UInt32, 42)".to_owned(),
        result: Some(NativeValue::UInt32(42)),
    };
    let s = format!("{}", entry);
    assert!(s.contains("Lit(UInt32, 42)"), "got: {}", s);
    assert!(s.contains("UInt32(42)"), "got: {}", s);
}

#[test]
fn test_trace_entry_display_without_result() {
    let entry = TraceEntry {
        step: 5,
        depth: 0,
        description: "Var(x)".to_owned(),
        result: None,
    };
    let s = format!("{}", entry);
    assert!(s.contains("Var(x)"), "got: {}", s);
}

// ---------------------------------------------------------------------------
// TraceDetail ordering
// ---------------------------------------------------------------------------

#[test]
fn test_trace_detail_ordering() {
    assert!(TraceDetail::Minimal < TraceDetail::Steps);
    assert!(TraceDetail::Steps < TraceDetail::Full);
    assert!(TraceDetail::Minimal < TraceDetail::Full);
}

// ---------------------------------------------------------------------------
// EvalExtError Display
// ---------------------------------------------------------------------------

#[test]
fn test_error_display_step_budget() {
    let err = EvalExtError::StepBudgetExceeded {
        limit: 100,
        used: 100,
    };
    let s = format!("{}", err);
    assert!(s.contains("step budget exceeded"), "got: {}", s);
    assert!(s.contains("100"), "got: {}", s);
}

#[test]
fn test_error_display_depth_budget() {
    let err = EvalExtError::DepthBudgetExceeded {
        limit: 10,
        reached: 10,
    };
    let s = format!("{}", err);
    assert!(s.contains("depth budget exceeded"), "got: {}", s);
}

#[test]
fn test_error_display_allocation_budget() {
    let err = EvalExtError::AllocationBudgetExceeded { limit: 5, used: 5 };
    let s = format!("{}", err);
    assert!(s.contains("allocation budget exceeded"), "got: {}", s);
}
