// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for match_eval_ext: tracing, coverage, profiling, symbolic eval,
//! statistics, budgets, and result caching.

use clean_kernel::Name;

use crate::match_compile::{ConstructorTag, DecisionTree, Var};
use crate::match_eval::{MatchEnv, MatchValue};
use crate::match_eval_ext::*;
use crate::native_types::NativeType;

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

fn mk_var(name: &str) -> Var {
    Var {
        name: Name::from_string(name),
        type_: NativeType::UInt64,
    }
}

fn mk_tag(name: &str, arity: usize) -> ConstructorTag {
    ConstructorTag {
        name: Name::from_string(name),
        arity,
    }
}

fn mk_ctor_val(name: &str, fields: Vec<MatchValue>) -> MatchValue {
    MatchValue::Constructor(mk_tag(name, fields.len()), fields)
}

fn mk_env(pairs: &[(&str, MatchValue)]) -> MatchEnv {
    let bindings: Vec<(Name, MatchValue)> = pairs
        .iter()
        .map(|(n, v)| (Name::from_string(n), v.clone()))
        .collect();
    MatchEnv::new(&bindings)
}

/// Simple switch: x -> { A => Leaf(0), B => Leaf(1), default => Leaf(2) }
fn simple_switch_tree() -> DecisionTree {
    DecisionTree::Switch(
        mk_var("x"),
        vec![
            (mk_tag("A", 0), DecisionTree::Leaf(0)),
            (mk_tag("B", 0), DecisionTree::Leaf(1)),
        ],
        Some(Box::new(DecisionTree::Leaf(2))),
    )
}

/// Nested switch: x -> { Some => (x.Some.f0 -> { Just => Leaf(0) }), None => Leaf(1) }
fn nested_switch_tree() -> DecisionTree {
    let inner = DecisionTree::Switch(
        mk_var("x_Some_f0"),
        vec![(mk_tag("Just", 0), DecisionTree::Leaf(0))],
        Some(Box::new(DecisionTree::Leaf(2))),
    );
    DecisionTree::Switch(
        mk_var("x"),
        vec![
            (mk_tag("Some", 1), inner),
            (mk_tag("None", 0), DecisionTree::Leaf(1)),
        ],
        None,
    )
}

/// Guard tree: Guard(_, Leaf(0), Leaf(1))
fn guard_tree() -> DecisionTree {
    DecisionTree::Guard(
        clean_kernel::Expr::sort(clean_kernel::Level::zero()),
        Box::new(DecisionTree::Leaf(0)),
        Box::new(DecisionTree::Leaf(1)),
    )
}

// =========================================================================
// TraceStep and EvalTrace tests
// =========================================================================

#[test]
fn test_trace_simple_switch_branch_a() {
    let tree = simple_switch_tree();
    let env = mk_env(&[("x", mk_ctor_val("A", vec![]))]);
    let (arm, trace, _) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    assert_eq!(arm, 0);
    assert!(!trace.is_empty());
    assert_eq!(trace.result_arm(), Some(0));
    // First step must be EnterSwitch for "x"
    assert!(matches!(&trace.steps[0], TraceStep::EnterSwitch { .. }));
}

#[test]
fn test_trace_simple_switch_branch_b() {
    let tree = simple_switch_tree();
    let env = mk_env(&[("x", mk_ctor_val("B", vec![]))]);
    let (arm, trace, _) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    assert_eq!(arm, 1);
    assert_eq!(trace.result_arm(), Some(1));
}

#[test]
fn test_trace_simple_switch_default() {
    let tree = simple_switch_tree();
    let env = mk_env(&[("x", mk_ctor_val("C", vec![]))]);
    let (arm, trace, _) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    assert_eq!(arm, 2);
    // Should have a DefaultTaken step
    assert!(trace
        .steps
        .iter()
        .any(|s| matches!(s, TraceStep::DefaultTaken)));
}

#[test]
fn test_trace_leaf_value() {
    let tree = simple_switch_tree();
    let env = mk_env(&[("x", MatchValue::Leaf)]);
    let (arm, trace, _) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    assert_eq!(arm, 2);
    assert!(trace
        .steps
        .iter()
        .any(|s| matches!(s, TraceStep::DefaultTaken)));
}

#[test]
fn test_trace_nested_switch() {
    let tree = nested_switch_tree();
    let inner_val = mk_ctor_val("Just", vec![]);
    let env = mk_env(&[
        ("x", mk_ctor_val("Some", vec![inner_val.clone()])),
        ("x_Some_f0", inner_val),
    ]);
    let (arm, trace, _) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    assert_eq!(arm, 0);
    // Should have two EnterSwitch steps
    let switch_count = trace
        .steps
        .iter()
        .filter(|s| matches!(s, TraceStep::EnterSwitch { .. }))
        .count();
    assert_eq!(switch_count, 2);
}

#[test]
fn test_trace_guard_falls_through() {
    let tree = guard_tree();
    let env = mk_env(&[]);
    let (arm, trace, _) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    // Base eval_traced guard behavior falls through to failure
    assert_eq!(arm, 1);
    assert!(trace
        .steps
        .iter()
        .any(|s| matches!(s, TraceStep::EnterGuard)));
    assert!(trace
        .steps
        .iter()
        .any(|s| matches!(s, TraceStep::GuardResult { passed: false })));
}

#[test]
fn test_trace_non_exhaustive() {
    let tree = DecisionTree::Switch(
        mk_var("x"),
        vec![(mk_tag("A", 0), DecisionTree::Leaf(0))],
        None,
    );
    let env = mk_env(&[("x", mk_ctor_val("B", vec![]))]);
    let result = eval_traced(&tree, &env, &EvalBudget::default());
    assert!(result.is_err());
}

#[test]
fn test_trace_unbound_variable() {
    let tree = simple_switch_tree();
    let env = mk_env(&[]);
    let result = eval_traced(&tree, &env, &EvalBudget::default());
    assert!(result.is_err());
}

#[test]
fn test_eval_trace_empty() {
    let trace = EvalTrace::default();
    assert!(trace.is_empty());
    assert_eq!(trace.len(), 0);
    assert_eq!(trace.result_arm(), None);
}

// =========================================================================
// Profile tests
// =========================================================================

#[test]
fn test_profile_comparison_count_branch_a() {
    let tree = simple_switch_tree();
    let env = mk_env(&[("x", mk_ctor_val("A", vec![]))]);
    let (_, _, profile) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    assert_eq!(profile.comparison_count, 1);
    assert_eq!(profile.backtrack_count, 0);
}

#[test]
fn test_profile_comparison_count_branch_b() {
    let tree = simple_switch_tree();
    let env = mk_env(&[("x", mk_ctor_val("B", vec![]))]);
    let (_, _, profile) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    assert_eq!(profile.comparison_count, 2); // compared against A, then B
    assert_eq!(profile.backtrack_count, 0);
}

#[test]
fn test_profile_default_increments_backtrack() {
    let tree = simple_switch_tree();
    let env = mk_env(&[("x", mk_ctor_val("C", vec![]))]);
    let (_, _, profile) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    assert_eq!(profile.backtrack_count, 1);
}

#[test]
fn test_profile_nested_depth() {
    let tree = nested_switch_tree();
    let inner_val = mk_ctor_val("Just", vec![]);
    let env = mk_env(&[
        ("x", mk_ctor_val("Some", vec![inner_val.clone()])),
        ("x_Some_f0", inner_val),
    ]);
    let (_, _, profile) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    assert!(profile.max_depth >= 2);
}

#[test]
fn test_profile_guard_count() {
    let tree = guard_tree();
    let env = mk_env(&[]);
    let (_, _, profile) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    assert_eq!(profile.guard_count, 1);
}

#[test]
fn test_profile_default_values() {
    let profile = EvalProfile::default();
    assert_eq!(profile.comparison_count, 0);
    assert_eq!(profile.max_depth, 0);
    assert_eq!(profile.backtrack_count, 0);
    assert_eq!(profile.guard_count, 0);
}

// =========================================================================
// Coverage tests
// =========================================================================

#[test]
fn test_coverage_empty() {
    let cov = CoverageTracker::new();
    assert_eq!(cov.total_evaluations(), 0);
    assert_eq!(cov.distinct_arms_hit(), 0);
    assert!(cov.hit_arms().is_empty());
}

#[test]
fn test_coverage_record_hits() {
    let mut cov = CoverageTracker::new();
    cov.record_hit(0);
    cov.record_hit(1);
    cov.record_hit(0);
    assert_eq!(cov.total_evaluations(), 3);
    assert_eq!(cov.arm_hit_count(0), 2);
    assert_eq!(cov.arm_hit_count(1), 1);
    assert_eq!(cov.arm_hit_count(99), 0);
    assert_eq!(cov.distinct_arms_hit(), 2);
}

#[test]
fn test_coverage_hit_rate() {
    let mut cov = CoverageTracker::new();
    cov.record_hit(0);
    cov.record_hit(0);
    cov.record_hit(1);
    cov.record_miss();
    assert_eq!(cov.total_evaluations(), 4);
    let rate = cov.arm_hit_rate(0);
    assert!((rate - 0.5).abs() < 1e-9);
}

#[test]
fn test_coverage_hit_rate_empty() {
    let cov = CoverageTracker::new();
    assert_eq!(cov.arm_hit_rate(0), 0.0);
}

#[test]
fn test_coverage_hit_arms_sorted() {
    let mut cov = CoverageTracker::new();
    cov.record_hit(5);
    cov.record_hit(2);
    cov.record_hit(8);
    assert_eq!(cov.hit_arms(), vec![2, 5, 8]);
}

#[test]
fn test_coverage_record_miss() {
    let mut cov = CoverageTracker::new();
    cov.record_miss();
    cov.record_miss();
    assert_eq!(cov.total_evaluations(), 2);
    assert_eq!(cov.distinct_arms_hit(), 0);
}

// =========================================================================
// Budget tests
// =========================================================================

#[test]
fn test_budget_default() {
    let budget = EvalBudget::default();
    assert_eq!(budget.max_comparisons, 10_000);
    assert_eq!(budget.max_depth, 100);
}

#[test]
fn test_budget_custom() {
    let budget = EvalBudget::new(5, 3);
    assert_eq!(budget.max_comparisons, 5);
    assert_eq!(budget.max_depth, 3);
}

#[test]
fn test_budget_comparison_exceeded() {
    let tree = simple_switch_tree();
    let env = mk_env(&[("x", mk_ctor_val("B", vec![]))]);
    // Budget of 1 comparison: matching B requires 2 comparisons
    let budget = EvalBudget::new(1, 100);
    let result = eval_traced(&tree, &env, &budget);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(
        err,
        MatchEvalExtError::ComparisonBudgetExceeded { .. }
    ));
}

#[test]
fn test_budget_depth_exceeded() {
    // Build a deep chain: Switch -> Switch -> Switch -> Leaf
    let deep = DecisionTree::Switch(
        mk_var("a"),
        vec![(
            mk_tag("X", 0),
            DecisionTree::Switch(
                mk_var("b"),
                vec![(
                    mk_tag("Y", 0),
                    DecisionTree::Switch(
                        mk_var("c"),
                        vec![(mk_tag("Z", 0), DecisionTree::Leaf(0))],
                        None,
                    ),
                )],
                None,
            ),
        )],
        None,
    );
    let env = mk_env(&[
        ("a", mk_ctor_val("X", vec![])),
        ("b", mk_ctor_val("Y", vec![])),
        ("c", mk_ctor_val("Z", vec![])),
    ]);
    let budget = EvalBudget::new(100, 1); // depth limit of 1
    let result = eval_traced(&deep, &env, &budget);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        MatchEvalExtError::DepthBudgetExceeded { .. }
    ));
}

#[test]
fn test_budget_sufficient_passes() {
    let tree = simple_switch_tree();
    let env = mk_env(&[("x", mk_ctor_val("A", vec![]))]);
    let budget = EvalBudget::new(10, 10);
    let result = eval_traced(&tree, &env, &budget);
    assert!(result.is_ok());
}

// =========================================================================
// Statistics tests
// =========================================================================

#[test]
fn test_statistics_empty() {
    let stats = EvalStatistics::new();
    assert_eq!(stats.count(), 0);
    assert_eq!(stats.avg_comparisons(), 0.0);
    assert_eq!(stats.avg_depth(), 0.0);
    assert_eq!(stats.max_comparisons(), 0);
    assert_eq!(stats.max_depth(), 0);
    assert_eq!(stats.total_backtracks(), 0);
}

#[test]
fn test_statistics_record_and_query() {
    let mut stats = EvalStatistics::new();
    stats.record(EvalProfile {
        comparison_count: 2,
        max_depth: 1,
        backtrack_count: 0,
        guard_count: 0,
    });
    stats.record(EvalProfile {
        comparison_count: 4,
        max_depth: 3,
        backtrack_count: 1,
        guard_count: 1,
    });
    assert_eq!(stats.count(), 2);
    assert!((stats.avg_comparisons() - 3.0).abs() < 1e-9);
    assert!((stats.avg_depth() - 2.0).abs() < 1e-9);
    assert_eq!(stats.max_comparisons(), 4);
    assert_eq!(stats.max_depth(), 3);
    assert_eq!(stats.total_backtracks(), 1);
}

#[test]
fn test_statistics_single_profile() {
    let mut stats = EvalStatistics::new();
    stats.record(EvalProfile {
        comparison_count: 7,
        max_depth: 5,
        backtrack_count: 2,
        guard_count: 3,
    });
    assert_eq!(stats.count(), 1);
    assert!((stats.avg_comparisons() - 7.0).abs() < 1e-9);
    assert!((stats.avg_depth() - 5.0).abs() < 1e-9);
}

// =========================================================================
// Error type tests
// =========================================================================

#[test]
fn test_error_display_comparison_budget() {
    let err = MatchEvalExtError::ComparisonBudgetExceeded { limit: 5, used: 6 };
    let msg = format!("{err}");
    assert!(msg.contains("comparison budget exceeded"));
    assert!(msg.contains("5"));
    assert!(msg.contains("6"));
}

#[test]
fn test_error_display_depth_budget() {
    let err = MatchEvalExtError::DepthBudgetExceeded {
        limit: 3,
        reached: 4,
    };
    let msg = format!("{err}");
    assert!(msg.contains("depth budget exceeded"));
}

#[test]
fn test_error_from_match_error() {
    let me = crate::match_eval::MatchError::NonExhaustive;
    let ext: MatchEvalExtError = me.into();
    assert!(matches!(ext, MatchEvalExtError::MatchError(_)));
}

// =========================================================================
// Integration: traced eval with coverage + stats
// =========================================================================

#[test]
fn test_integrated_trace_coverage_stats() {
    let tree = simple_switch_tree();
    let budget = EvalBudget::default();
    let mut cov = CoverageTracker::new();
    let mut stats = EvalStatistics::new();

    for name in &["A", "B", "C", "A"] {
        let env = mk_env(&[("x", mk_ctor_val(name, vec![]))]);
        let (arm, _trace, profile) = eval_traced(&tree, &env, &budget).unwrap();
        cov.record_hit(arm);
        stats.record(profile);
    }

    assert_eq!(cov.total_evaluations(), 4);
    assert_eq!(cov.arm_hit_count(0), 2);
    assert_eq!(cov.arm_hit_count(1), 1);
    assert_eq!(cov.arm_hit_count(2), 1);
    assert_eq!(stats.count(), 4);
    assert!(stats.avg_comparisons() > 0.0);
}

#[test]
fn test_single_leaf_tree_traced() {
    let tree = DecisionTree::Leaf(42);
    let env = mk_env(&[]);
    let (arm, trace, profile) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    assert_eq!(arm, 42);
    assert_eq!(trace.len(), 1);
    assert!(matches!(
        &trace.steps[0],
        TraceStep::ReachedLeaf { arm_idx: 42 }
    ));
    assert_eq!(profile.comparison_count, 0);
    assert_eq!(profile.max_depth, 0);
}

#[test]
fn test_trace_branch_taken_field_count() {
    let tree = DecisionTree::Switch(
        mk_var("x"),
        vec![(mk_tag("Pair", 2), DecisionTree::Leaf(0))],
        None,
    );
    let env = mk_env(&[(
        "x",
        mk_ctor_val("Pair", vec![MatchValue::Leaf, MatchValue::Leaf]),
    )]);
    let (arm, trace, _) = eval_traced(&tree, &env, &EvalBudget::default()).unwrap();
    assert_eq!(arm, 0);
    assert!(trace
        .steps
        .iter()
        .any(|s| matches!(s, TraceStep::BranchTaken { field_count: 2, .. })));
}
