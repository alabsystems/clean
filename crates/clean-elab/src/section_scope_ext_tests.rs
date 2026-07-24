// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended section scope analysis and visualization.

use clean_kernel::expr::BinderInfo;
use clean_kernel::Expr;

use crate::section_scope::{SectionScope, SectionVariable};
use crate::section_scope_ext::{
    active_auto_bound_candidates, analyze_auto_bound_candidates, analyze_section_dependencies,
    compute_scope_stats, diff_scope_stacks, find_unused_variables, validate_scope_nesting,
    validate_scope_stack, visualize_scope_tree, ScopeValidationError,
};

// ---------------------------------------------------------------------------
// Helper
// ---------------------------------------------------------------------------

fn make_scope_with_vars(vars: &[(&str, BinderInfo)]) -> SectionScope {
    let mut scope = SectionScope::new();
    for &(name, bi) in vars {
        scope.add_variable(SectionVariable::new(
            name.to_owned(),
            Expr::const_str("Nat"),
            bi,
        ));
    }
    scope
}

// ---------------------------------------------------------------------------
// Visualization
// ---------------------------------------------------------------------------

#[test]
fn test_visualize_empty_stack() {
    let result = visualize_scope_tree(&[], &[]);
    assert!(result.is_empty());
}

#[test]
fn test_visualize_single_scope_no_vars() {
    let scopes = [SectionScope::new()];
    let result = visualize_scope_tree(&scopes, &["Foo"]);
    assert!(result.contains("section Foo"));
    assert!(result.contains("end Foo"));
}

#[test]
fn test_visualize_single_scope_with_vars() {
    let scope = make_scope_with_vars(&[
        ("n", BinderInfo::Default),
        ("alpha", BinderInfo::Implicit),
        ("inst", BinderInfo::InstImplicit),
    ]);
    let scopes = [scope];
    let result = visualize_scope_tree(&scopes, &["S"]);
    assert!(result.contains("variable (n : ...)"));
    assert!(result.contains("variable {alpha : ...}"));
    assert!(result.contains("variable [inst : ...]"));
}

#[test]
fn test_visualize_omitted_variable() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.omit_variable("x");

    let scopes = [scope];
    let result = visualize_scope_tree(&scopes, &["S"]);
    assert!(result.contains("-- omitted"));
}

#[test]
fn test_visualize_nested_scopes() {
    let outer = make_scope_with_vars(&[("x", BinderInfo::Default)]);
    let inner = make_scope_with_vars(&[("y", BinderInfo::Implicit)]);

    let scopes = [outer, inner];
    let result = visualize_scope_tree(&scopes, &["Outer", "Inner"]);
    assert!(result.contains("section Outer"));
    assert!(result.contains("  section Inner"));
    assert!(result.contains("  end Inner"));
    assert!(result.contains("end Outer"));
}

#[test]
fn test_visualize_anonymous_section() {
    let scope = SectionScope::new();
    let scopes = [scope];
    let result = visualize_scope_tree(&scopes, &[""]);
    assert!(result.contains("section <anon>"));
    assert!(result.contains("end <anon>"));
}

#[test]
fn test_visualize_universe_params() {
    let mut scope = SectionScope::new();
    scope.add_universe_param("u".to_owned());
    let scopes = [scope];
    let result = visualize_scope_tree(&scopes, &["S"]);
    assert!(result.contains("universe u"));
}

#[test]
fn test_visualize_strict_implicit() {
    let scope = make_scope_with_vars(&[("z", BinderInfo::StrictImplicit)]);
    let scopes = [scope];
    let result = visualize_scope_tree(&scopes, &["S"]);
    assert!(result.contains("variable {z : ...}"));
}

// ---------------------------------------------------------------------------
// Scope statistics
// ---------------------------------------------------------------------------

#[test]
fn test_stats_empty_stack() {
    let stats = compute_scope_stats(&[]);
    assert_eq!(stats.depth, 0);
    assert_eq!(stats.total_variables, 0);
    assert_eq!(stats.total_included, 0);
    assert_eq!(stats.total_universes, 0);
    assert!(stats.levels.is_empty());
}

#[test]
fn test_stats_single_scope() {
    let scope = make_scope_with_vars(&[
        ("a", BinderInfo::Default),
        ("b", BinderInfo::Implicit),
        ("c", BinderInfo::InstImplicit),
    ]);
    let stats = compute_scope_stats(&[scope]);
    assert_eq!(stats.depth, 1);
    assert_eq!(stats.total_variables, 3);
    assert_eq!(stats.total_included, 3);
    assert_eq!(stats.levels.len(), 1);
    assert_eq!(stats.levels[0].explicit_count, 1);
    assert_eq!(stats.levels[0].implicit_count, 1);
    assert_eq!(stats.levels[0].inst_implicit_count, 1);
    assert_eq!(stats.levels[0].omitted_count, 0);
}

#[test]
fn test_stats_with_omitted() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.add_variable(SectionVariable::explicit(
        "y".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.omit_variable("x");

    let stats = compute_scope_stats(&[scope]);
    assert_eq!(stats.levels[0].variable_count, 2);
    assert_eq!(stats.levels[0].included_count, 1);
    assert_eq!(stats.levels[0].omitted_count, 1);
    assert_eq!(stats.total_included, 1);
}

#[test]
fn test_stats_multiple_levels() {
    let s0 = make_scope_with_vars(&[("a", BinderInfo::Default)]);
    let s1 = make_scope_with_vars(&[("b", BinderInfo::Implicit), ("c", BinderInfo::Implicit)]);

    let stats = compute_scope_stats(&[s0, s1]);
    assert_eq!(stats.depth, 2);
    assert_eq!(stats.total_variables, 3);
    assert_eq!(stats.levels[0].depth, 0);
    assert_eq!(stats.levels[1].depth, 1);
    assert_eq!(stats.levels[1].variable_count, 2);
}

#[test]
fn test_stats_universe_counts() {
    let mut scope = SectionScope::new();
    scope.add_universe_param("u".to_owned());
    scope.add_universe_param("v".to_owned());

    let stats = compute_scope_stats(&[scope]);
    assert_eq!(stats.total_universes, 2);
    assert_eq!(stats.levels[0].universe_count, 2);
}

// ---------------------------------------------------------------------------
// Unused variable detection
// ---------------------------------------------------------------------------

#[test]
fn test_find_unused_empty() {
    let unused = find_unused_variables(&[]);
    assert!(unused.is_empty());
}

#[test]
fn test_find_unused_all_unused() {
    let scope = make_scope_with_vars(&[("a", BinderInfo::Default), ("b", BinderInfo::Default)]);
    let unused = find_unused_variables(&[scope]);
    // Neither variable is referenced in any type (both have type Nat, which is not "a" or "b")
    assert_eq!(unused.len(), 2);
    assert!(unused.contains(&"a".to_owned()));
    assert!(unused.contains(&"b".to_owned()));
}

#[test]
fn test_find_unused_one_referenced() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "a".to_owned(),
        Expr::const_str("Nat"),
    ));
    // "b" has type that references "a"
    scope.add_variable(SectionVariable::explicit(
        "b".to_owned(),
        Expr::const_str("a"),
    ));

    let unused = find_unused_variables(&[scope]);
    // "a" is referenced in b's type, but "b" is not referenced anywhere
    assert_eq!(unused, vec!["b".to_owned()]);
}

#[test]
fn test_find_unused_cross_scope_reference() {
    let s0 = make_scope_with_vars(&[("alpha", BinderInfo::Implicit)]);
    let mut s1 = SectionScope::new();
    s1.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("alpha"),
    ));

    let unused = find_unused_variables(&[s0, s1]);
    // "alpha" is referenced by "n"'s type, "n" is not referenced
    assert_eq!(unused, vec!["n".to_owned()]);
}

// ---------------------------------------------------------------------------
// Scope diff
// ---------------------------------------------------------------------------

#[test]
fn test_diff_identical_stacks() {
    let scope = make_scope_with_vars(&[("x", BinderInfo::Default)]);
    let diff = diff_scope_stacks(std::slice::from_ref(&scope), std::slice::from_ref(&scope));
    assert!(diff.added_variables.is_empty());
    assert!(diff.removed_variables.is_empty());
    assert!(diff.toggled_variables.is_empty());
    assert_eq!(diff.depth_change, 0);
}

#[test]
fn test_diff_added_variable() {
    let old = make_scope_with_vars(&[("x", BinderInfo::Default)]);
    let new = make_scope_with_vars(&[("x", BinderInfo::Default), ("y", BinderInfo::Default)]);

    let diff = diff_scope_stacks(&[old], &[new]);
    assert_eq!(diff.added_variables, vec!["y".to_owned()]);
    assert!(diff.removed_variables.is_empty());
}

#[test]
fn test_diff_removed_variable() {
    let old = make_scope_with_vars(&[("x", BinderInfo::Default), ("y", BinderInfo::Default)]);
    let new = make_scope_with_vars(&[("x", BinderInfo::Default)]);

    let diff = diff_scope_stacks(&[old], &[new]);
    assert!(diff.added_variables.is_empty());
    assert_eq!(diff.removed_variables, vec!["y".to_owned()]);
}

#[test]
fn test_diff_depth_change() {
    let s0 = SectionScope::new();
    let diff = diff_scope_stacks(std::slice::from_ref(&s0), &[s0.clone(), s0.clone()]);
    assert_eq!(diff.depth_change, 1);
}

#[test]
fn test_diff_toggled_variable() {
    let mut old_scope = SectionScope::new();
    old_scope.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));
    // x is included in old

    let mut new_scope = SectionScope::new();
    new_scope.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));
    new_scope.omit_variable("x");
    // x is omitted in new

    let diff = diff_scope_stacks(&[old_scope], &[new_scope]);
    assert_eq!(diff.toggled_variables, vec!["x".to_owned()]);
}

#[test]
fn test_diff_empty_to_populated() {
    let scope = make_scope_with_vars(&[("a", BinderInfo::Default)]);
    let diff = diff_scope_stacks(&[], &[scope]);
    assert_eq!(diff.added_variables, vec!["a".to_owned()]);
    assert_eq!(diff.depth_change, 1);
}

#[test]
fn test_diff_populated_to_empty() {
    let scope = make_scope_with_vars(&[("a", BinderInfo::Default)]);
    let diff = diff_scope_stacks(&[scope], &[]);
    assert_eq!(diff.removed_variables, vec!["a".to_owned()]);
    assert_eq!(diff.depth_change, -1);
}

#[test]
fn test_diff_universe_changes() {
    let mut old = SectionScope::new();
    old.add_universe_param("u".to_owned());

    let mut new = SectionScope::new();
    new.add_universe_param("v".to_owned());

    let diff = diff_scope_stacks(&[old], &[new]);
    assert_eq!(diff.added_universes, vec!["v".to_owned()]);
    assert_eq!(diff.removed_universes, vec!["u".to_owned()]);
}

// ---------------------------------------------------------------------------
// Auto-bound analysis
// ---------------------------------------------------------------------------

#[test]
fn test_auto_bound_empty() {
    let candidates = analyze_auto_bound_candidates(&[]);
    assert!(candidates.is_empty());
}

#[test]
fn test_auto_bound_all_included() {
    let scope = make_scope_with_vars(&[("x", BinderInfo::Default), ("y", BinderInfo::Implicit)]);
    let candidates = analyze_auto_bound_candidates(&[scope]);
    assert_eq!(candidates.len(), 2);
    assert!(candidates[0].is_included);
    assert!(!candidates[0].is_implicit);
    assert!(candidates[1].is_included);
    assert!(candidates[1].is_implicit);
}

#[test]
fn test_auto_bound_with_omitted() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.add_variable(SectionVariable::explicit(
        "y".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.omit_variable("x");

    let candidates = analyze_auto_bound_candidates(&[scope]);
    assert_eq!(candidates.len(), 2);
    assert!(!candidates[0].is_included); // x omitted
    assert!(candidates[1].is_included); // y included
}

#[test]
fn test_active_auto_bound_filters_omitted() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.add_variable(SectionVariable::explicit(
        "y".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.omit_variable("x");

    let active = active_auto_bound_candidates(&[scope]);
    assert_eq!(active.len(), 1);
    assert_eq!(active[0].name, "y");
}

#[test]
fn test_auto_bound_scope_depth_tracking() {
    let s0 = make_scope_with_vars(&[("a", BinderInfo::Default)]);
    let s1 = make_scope_with_vars(&[("b", BinderInfo::Implicit)]);

    let candidates = analyze_auto_bound_candidates(&[s0, s1]);
    assert_eq!(candidates.len(), 2);
    assert_eq!(candidates[0].scope_depth, 0);
    assert_eq!(candidates[0].name, "a");
    assert_eq!(candidates[1].scope_depth, 1);
    assert_eq!(candidates[1].name, "b");
}

// ---------------------------------------------------------------------------
// Section dependency analysis
// ---------------------------------------------------------------------------

#[test]
fn test_dependency_empty() {
    let deps = analyze_section_dependencies(&[]);
    assert!(deps.is_empty());
}

#[test]
fn test_dependency_single_scope_no_outer() {
    let scope = make_scope_with_vars(&[("x", BinderInfo::Default)]);
    let deps = analyze_section_dependencies(&[scope]);
    assert_eq!(deps.len(), 1);
    assert!(deps[0].outer_dependencies.is_empty());
    assert_eq!(deps[0].own_variables, vec!["x".to_owned()]);
}

#[test]
fn test_dependency_inner_depends_on_outer() {
    let s0 = make_scope_with_vars(&[("alpha", BinderInfo::Implicit)]);
    let mut s1 = SectionScope::new();
    s1.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("alpha"),
    ));

    let deps = analyze_section_dependencies(&[s0, s1]);
    assert_eq!(deps.len(), 2);
    assert!(deps[0].outer_dependencies.is_empty());
    assert_eq!(deps[1].outer_dependencies, vec!["alpha".to_owned()]);
}

#[test]
fn test_dependency_no_cross_reference() {
    let s0 = make_scope_with_vars(&[("x", BinderInfo::Default)]);
    let s1 = make_scope_with_vars(&[("y", BinderInfo::Default)]);

    let deps = analyze_section_dependencies(&[s0, s1]);
    assert!(deps[1].outer_dependencies.is_empty());
}

#[test]
fn test_dependency_scope_depth_correct() {
    let s0 = make_scope_with_vars(&[("a", BinderInfo::Default)]);
    let s1 = make_scope_with_vars(&[("b", BinderInfo::Default)]);
    let s2 = make_scope_with_vars(&[("c", BinderInfo::Default)]);

    let deps = analyze_section_dependencies(&[s0, s1, s2]);
    assert_eq!(deps[0].scope_depth, 0);
    assert_eq!(deps[1].scope_depth, 1);
    assert_eq!(deps[2].scope_depth, 2);
}

// ---------------------------------------------------------------------------
// Scope validation
// ---------------------------------------------------------------------------

#[test]
fn test_validate_empty_stack_ok() {
    assert!(validate_scope_stack(&[]).is_ok());
}

#[test]
fn test_validate_single_scope_ok() {
    let scope = make_scope_with_vars(&[("x", BinderInfo::Default), ("y", BinderInfo::Default)]);
    assert!(validate_scope_stack(&[scope]).is_ok());
}

#[test]
fn test_validate_cross_scope_duplicate_variable() {
    let s0 = make_scope_with_vars(&[("x", BinderInfo::Default)]);
    let s1 = make_scope_with_vars(&[("x", BinderInfo::Implicit)]);

    let result = validate_scope_stack(&[s0, s1]);
    assert!(result.is_err());
    match result.unwrap_err() {
        ScopeValidationError::DuplicateVariable { name, depth } => {
            assert_eq!(name, "x");
            assert_eq!(depth, 1);
        }
        other => panic!("expected DuplicateVariable, got {other:?}"),
    }
}

#[test]
fn test_validate_universe_variable_collision() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "u".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.add_universe_param("u".to_owned());

    let result = validate_scope_stack(&[scope]);
    assert!(result.is_err());
    match result.unwrap_err() {
        ScopeValidationError::UniverseVariableCollision { name, .. } => {
            assert_eq!(name, "u");
        }
        other => panic!("expected UniverseVariableCollision, got {other:?}"),
    }
}

#[test]
fn test_validate_no_collision_between_scopes() {
    let mut s0 = SectionScope::new();
    s0.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));

    let mut s1 = SectionScope::new();
    s1.add_universe_param("u".to_owned());

    // x and u don't collide across scopes
    assert!(validate_scope_stack(&[s0, s1]).is_ok());
}

#[test]
fn test_validate_nesting_matching_counts() {
    let scopes = [SectionScope::new(), SectionScope::new()];
    let names = ["A", "B"];
    assert!(validate_scope_nesting(&scopes, &names).is_ok());
}

#[test]
fn test_validate_nesting_mismatched_counts() {
    let scopes = [SectionScope::new(), SectionScope::new()];
    let names = ["A"];
    let result = validate_scope_nesting(&scopes, &names);
    assert!(result.is_err());
    match result.unwrap_err() {
        ScopeValidationError::NestingError { message } => {
            assert!(message.contains("does not match"));
        }
        other => panic!("expected NestingError, got {other:?}"),
    }
}

#[test]
fn test_validate_nesting_empty() {
    assert!(validate_scope_nesting(&[], &[]).is_ok());
}

// ---------------------------------------------------------------------------
// Error display
// ---------------------------------------------------------------------------

#[test]
fn test_error_display_duplicate_variable() {
    let err = ScopeValidationError::DuplicateVariable {
        name: "x".to_owned(),
        depth: 2,
    };
    let msg = err.to_string();
    assert!(msg.contains("duplicate variable 'x'"));
    assert!(msg.contains("depth 2"));
}

#[test]
fn test_error_display_nesting_error() {
    let err = ScopeValidationError::NestingError {
        message: "bad nesting".to_owned(),
    };
    assert!(err.to_string().contains("bad nesting"));
}

#[test]
fn test_error_display_collision() {
    let err = ScopeValidationError::UniverseVariableCollision {
        name: "u".to_owned(),
        depth: 0,
    };
    assert!(err.to_string().contains("universe parameter 'u'"));
}
