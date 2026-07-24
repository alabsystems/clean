// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended variable command analysis.

use std::collections::HashSet;

use clean_kernel::expr::BinderInfo;
use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

use crate::variable_cmd::VariableDecl;
use crate::variable_cmd_ext::*;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mk_type() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

fn mk_nat() -> Expr {
    Expr::const_str("Nat")
}

fn mk_bool() -> Expr {
    Expr::const_str("Bool")
}

fn mk_decl(name: &str, ty: Expr, bi: BinderInfo) -> VariableDecl {
    VariableDecl::new(Name::from_string(name), ty, bi)
}

fn mk_multi_decl(names: &[&str], ty: Expr, bi: BinderInfo) -> VariableDecl {
    VariableDecl::multi(names.iter().map(|n| Name::from_string(n)).collect(), ty, bi)
}

// ===========================================================================
// VariableUsageTracker tests
// ===========================================================================

#[test]
fn test_usage_tracker_new_tracks_all_names() {
    let decls = vec![
        mk_decl("alpha", mk_type(), BinderInfo::Implicit),
        mk_decl("n", mk_nat(), BinderInfo::Default),
    ];
    let tracker = VariableUsageTracker::new(&decls);
    assert!(tracker.is_tracked("alpha"));
    assert!(tracker.is_tracked("n"));
    assert!(!tracker.is_tracked("unknown"));
}

#[test]
fn test_usage_tracker_new_multi_name() {
    let decls = vec![mk_multi_decl(
        &["a", "b", "c"],
        mk_type(),
        BinderInfo::Implicit,
    )];
    let tracker = VariableUsageTracker::new(&decls);
    assert!(tracker.is_tracked("a"));
    assert!(tracker.is_tracked("b"));
    assert!(tracker.is_tracked("c"));
}

#[test]
fn test_usage_tracker_all_unused_initially() {
    let decls = vec![
        mk_decl("x", mk_type(), BinderInfo::Implicit),
        mk_decl("y", mk_nat(), BinderInfo::Default),
    ];
    let tracker = VariableUsageTracker::new(&decls);
    let unused = tracker.unused_variables();
    assert_eq!(unused.len(), 2);
    assert!(tracker.used_variables().is_empty());
}

#[test]
fn test_usage_tracker_record_usage_marks_used() {
    let decls = vec![
        mk_decl("alpha", mk_type(), BinderInfo::Implicit),
        mk_decl("n", mk_nat(), BinderInfo::Default),
    ];
    let mut tracker = VariableUsageTracker::new(&decls);

    // Expression referencing "alpha" only
    let expr = Expr::const_str("alpha");
    tracker.record_usage("my_def", &expr);

    assert_eq!(tracker.used_variables(), vec!["alpha"]);
    assert_eq!(tracker.unused_variables(), vec!["n"]);
    assert_eq!(tracker.reference_count("alpha"), 1);
    assert_eq!(tracker.reference_count("n"), 0);
}

#[test]
fn test_usage_tracker_multiple_defs_reference_same_var() {
    let decls = vec![mk_decl("alpha", mk_type(), BinderInfo::Implicit)];
    let mut tracker = VariableUsageTracker::new(&decls);

    tracker.record_usage("def1", &Expr::const_str("alpha"));
    tracker.record_usage("def2", &Expr::const_str("alpha"));

    assert_eq!(tracker.reference_count("alpha"), 2);
    let refs = tracker.referencing_defs("alpha");
    assert!(refs.contains(&"def1".to_owned()));
    assert!(refs.contains(&"def2".to_owned()));
}

#[test]
fn test_usage_tracker_ignores_non_tracked() {
    let decls = vec![mk_decl("alpha", mk_type(), BinderInfo::Implicit)];
    let mut tracker = VariableUsageTracker::new(&decls);

    // Expression referencing "Nat" which is not a tracked variable
    tracker.record_usage("my_def", &mk_nat());
    assert!(tracker.used_variables().is_empty());
}

#[test]
fn test_usage_tracker_empty_decls() {
    let tracker = VariableUsageTracker::new(&[]);
    assert!(tracker.unused_variables().is_empty());
    assert!(tracker.used_variables().is_empty());
    assert_eq!(tracker.reference_count("anything"), 0);
}

#[test]
fn test_usage_tracker_referencing_defs_unknown_var() {
    let tracker = VariableUsageTracker::new(&[]);
    assert!(tracker.referencing_defs("nonexistent").is_empty());
}

#[test]
fn test_usage_tracker_app_expr_references() {
    let decls = vec![
        mk_decl("alpha", mk_type(), BinderInfo::Implicit),
        mk_decl("n", mk_nat(), BinderInfo::Default),
    ];
    let mut tracker = VariableUsageTracker::new(&decls);

    // List alpha — App(Const("List"), Const("alpha"))
    let expr = Expr::app(Expr::const_str("List"), Expr::const_str("alpha"));
    tracker.record_usage("list_def", &expr);

    assert_eq!(tracker.reference_count("alpha"), 1);
    assert_eq!(tracker.reference_count("n"), 0);
}

// ===========================================================================
// Type dependency analysis tests
// ===========================================================================

#[test]
fn test_declaration_order_no_deps() {
    let decls = vec![
        mk_decl("a", mk_type(), BinderInfo::Implicit),
        mk_decl("b", mk_nat(), BinderInfo::Default),
    ];
    let order = compute_declaration_order(&decls).expect("should succeed");
    assert_eq!(order.len(), 2);
}

#[test]
fn test_declaration_order_simple_dep() {
    // b's type references a: b : List a
    let decls = vec![
        mk_decl("a", mk_type(), BinderInfo::Implicit),
        mk_decl(
            "b",
            Expr::app(Expr::const_str("List"), Expr::const_str("a")),
            BinderInfo::Default,
        ),
    ];
    let order = compute_declaration_order(&decls).expect("should succeed");
    let a_pos = order.iter().position(|n| n == "a").unwrap();
    let b_pos = order.iter().position(|n| n == "b").unwrap();
    assert!(a_pos < b_pos, "a must come before b");
}

#[test]
fn test_declaration_order_chain() {
    // c depends on b, b depends on a
    let decls = vec![
        mk_decl("a", mk_type(), BinderInfo::Implicit),
        mk_decl("b", Expr::const_str("a"), BinderInfo::Default),
        mk_decl("c", Expr::const_str("b"), BinderInfo::Default),
    ];
    let order = compute_declaration_order(&decls).expect("should succeed");
    let a_pos = order.iter().position(|n| n == "a").unwrap();
    let b_pos = order.iter().position(|n| n == "b").unwrap();
    let c_pos = order.iter().position(|n| n == "c").unwrap();
    assert!(a_pos < b_pos);
    assert!(b_pos < c_pos);
}

#[test]
fn test_declaration_order_cycle() {
    // a depends on b, b depends on a
    let decls = vec![
        mk_decl("a", Expr::const_str("b"), BinderInfo::Implicit),
        mk_decl("b", Expr::const_str("a"), BinderInfo::Default),
    ];
    let result = compute_declaration_order(&decls);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, VariableCmdExtError::DependencyCycle(_)),
        "expected DependencyCycle"
    );
}

#[test]
fn test_declaration_order_empty() {
    let order = compute_declaration_order(&[]).expect("should succeed");
    assert!(order.is_empty());
}

#[test]
fn test_type_dependencies_filters_to_known() {
    let known: HashSet<String> = ["alpha", "beta"].iter().map(|s| s.to_string()).collect();
    let decl = mk_decl(
        "x",
        Expr::app(Expr::const_str("List"), Expr::const_str("alpha")),
        BinderInfo::Default,
    );
    let deps = type_dependencies(&decl, &known);
    assert!(deps.contains("alpha"));
    assert!(!deps.contains("List")); // List is not a known variable
}

#[test]
fn test_type_dependencies_no_refs() {
    let known: HashSet<String> = ["alpha"].iter().map(|s| s.to_string()).collect();
    let decl = mk_decl("x", mk_nat(), BinderInfo::Default);
    let deps = type_dependencies(&decl, &known);
    assert!(deps.is_empty());
}

// ===========================================================================
// Redundancy detection tests
// ===========================================================================

#[test]
fn test_redundancy_exact_duplicate() {
    let decls = vec![
        mk_decl("x", mk_type(), BinderInfo::Implicit),
        mk_decl("x", mk_type(), BinderInfo::Implicit),
    ];
    let findings = detect_redundancies(&decls);
    assert!(findings
        .iter()
        .any(|f| matches!(f, RedundancyKind::ExactDuplicate { name } if name == "x")));
}

#[test]
fn test_redundancy_shadow_different_binder() {
    let decls = vec![
        mk_decl("x", mk_type(), BinderInfo::Implicit),
        mk_decl("x", mk_type(), BinderInfo::Default),
    ];
    let findings = detect_redundancies(&decls);
    assert!(findings.iter().any(|f| matches!(
        f,
        RedundancyKind::Shadow {
            name,
            first_binder: BinderInfo::Implicit,
            second_binder: BinderInfo::Default,
        } if name == "x"
    )));
}

#[test]
fn test_redundancy_mergeable() {
    let decls = vec![
        mk_decl("a", mk_type(), BinderInfo::Implicit),
        mk_decl("b", mk_type(), BinderInfo::Implicit),
    ];
    let findings = detect_redundancies(&decls);
    assert!(findings.iter().any(|f| matches!(
        f,
        RedundancyKind::Mergeable { names, binder_info: BinderInfo::Implicit }
            if names.contains(&"a".to_owned()) && names.contains(&"b".to_owned())
    )));
}

#[test]
fn test_redundancy_no_issues() {
    let decls = vec![
        mk_decl("a", mk_type(), BinderInfo::Implicit),
        mk_decl("n", mk_nat(), BinderInfo::Default),
    ];
    let findings = detect_redundancies(&decls);
    // Different types and different binders => no redundancy (except potentially
    // mergeable if both were same type+binder). Here they differ.
    assert!(findings
        .iter()
        .all(|f| !matches!(f, RedundancyKind::ExactDuplicate { .. })));
    assert!(findings
        .iter()
        .all(|f| !matches!(f, RedundancyKind::Shadow { .. })));
}

#[test]
fn test_redundancy_empty() {
    let findings = detect_redundancies(&[]);
    assert!(findings.is_empty());
}

#[test]
fn test_redundancy_multi_name_not_mergeable() {
    // A multi-name decl should not be flagged as mergeable with itself
    let decls = vec![mk_multi_decl(&["a", "b"], mk_type(), BinderInfo::Implicit)];
    let findings = detect_redundancies(&decls);
    // The multi-name decl has names.len() == 2, so it won't match the
    // single-name filter in detect_redundancies. No mergeable suggestion.
    assert!(findings
        .iter()
        .all(|f| !matches!(f, RedundancyKind::Mergeable { .. })));
}

// ===========================================================================
// Variable statistics tests
// ===========================================================================

#[test]
fn test_statistics_empty() {
    let stats = compute_statistics(&[]);
    assert_eq!(stats.total_count, 0);
    assert_eq!(stats.distinct_types, 0);
    assert_eq!(stats.avg_type_complexity, 0);
    assert_eq!(stats.max_type_complexity, 0);
    assert_eq!(stats.multi_name_decls, 0);
}

#[test]
fn test_statistics_single_decl() {
    let decls = vec![mk_decl("x", mk_nat(), BinderInfo::Default)];
    let stats = compute_statistics(&decls);
    assert_eq!(stats.total_count, 1);
    assert_eq!(*stats.by_binder.get(&BinderInfo::Default).unwrap_or(&0), 1);
    assert_eq!(stats.distinct_types, 1);
    assert_eq!(stats.multi_name_decls, 0);
}

#[test]
fn test_statistics_multi_name_decl() {
    let decls = vec![mk_multi_decl(
        &["a", "b", "c"],
        mk_type(),
        BinderInfo::Implicit,
    )];
    let stats = compute_statistics(&decls);
    assert_eq!(stats.total_count, 3);
    assert_eq!(*stats.by_binder.get(&BinderInfo::Implicit).unwrap_or(&0), 3);
    assert_eq!(stats.multi_name_decls, 1);
}

#[test]
fn test_statistics_mixed_binders() {
    let decls = vec![
        mk_decl("a", mk_type(), BinderInfo::Implicit),
        mk_decl("n", mk_nat(), BinderInfo::Default),
        mk_decl(
            "inst",
            Expr::app(Expr::const_str("Add"), Expr::const_str("a")),
            BinderInfo::InstImplicit,
        ),
    ];
    let stats = compute_statistics(&decls);
    assert_eq!(stats.total_count, 3);
    assert_eq!(*stats.by_binder.get(&BinderInfo::Implicit).unwrap_or(&0), 1);
    assert_eq!(*stats.by_binder.get(&BinderInfo::Default).unwrap_or(&0), 1);
    assert_eq!(
        *stats.by_binder.get(&BinderInfo::InstImplicit).unwrap_or(&0),
        1
    );
    assert_eq!(stats.distinct_types, 3);
}

#[test]
fn test_statistics_type_complexity() {
    // Simple type: Nat (1 node)
    // Complex type: List (App Nat) (3 nodes: App + Const + Const)
    let decls = vec![
        mk_decl("n", mk_nat(), BinderInfo::Default),
        mk_decl(
            "xs",
            Expr::app(Expr::const_str("List"), mk_nat()),
            BinderInfo::Default,
        ),
    ];
    let stats = compute_statistics(&decls);
    assert!(stats.max_type_complexity >= 1);
    assert!(stats.avg_type_complexity >= 1);
}

// ===========================================================================
// Scope impact analysis tests
// ===========================================================================

#[test]
fn test_scope_impact_implicit() {
    let decls = vec![mk_decl("a", mk_type(), BinderInfo::Implicit)];
    let impacts = analyze_scope_impact(&decls);
    assert_eq!(impacts.len(), 1);
    assert!(impacts[0].adds_implicit_arg);
    assert!(!impacts[0].adds_instance_arg);
    assert_eq!(impacts[0].name, "a");
}

#[test]
fn test_scope_impact_instance() {
    let decls = vec![mk_decl(
        "inst",
        Expr::app(Expr::const_str("Add"), Expr::const_str("a")),
        BinderInfo::InstImplicit,
    )];
    let impacts = analyze_scope_impact(&decls);
    assert_eq!(impacts.len(), 1);
    assert!(!impacts[0].adds_implicit_arg);
    assert!(impacts[0].adds_instance_arg);
}

#[test]
fn test_scope_impact_type_references() {
    let decls = vec![
        mk_decl("a", mk_type(), BinderInfo::Implicit),
        mk_decl(
            "xs",
            Expr::app(Expr::const_str("List"), Expr::const_str("a")),
            BinderInfo::Default,
        ),
    ];
    let impacts = analyze_scope_impact(&decls);
    let xs_impact = impacts.iter().find(|i| i.name == "xs").unwrap();
    assert!(xs_impact.type_references.contains(&"a".to_owned()));
    assert_eq!(xs_impact.binder_depth_contribution, 2); // 1 + 1 ref
}

#[test]
fn test_scope_impact_explicit() {
    let decls = vec![mk_decl("n", mk_nat(), BinderInfo::Default)];
    let impacts = analyze_scope_impact(&decls);
    assert_eq!(impacts.len(), 1);
    assert!(!impacts[0].adds_implicit_arg);
    assert!(!impacts[0].adds_instance_arg);
}

#[test]
fn test_scope_impact_empty() {
    let impacts = analyze_scope_impact(&[]);
    assert!(impacts.is_empty());
}

#[test]
fn test_scope_impact_multi_name() {
    let decls = vec![mk_multi_decl(&["a", "b"], mk_type(), BinderInfo::Implicit)];
    let impacts = analyze_scope_impact(&decls);
    assert_eq!(impacts.len(), 2);
    assert!(impacts.iter().all(|i| i.adds_implicit_arg));
}

// ===========================================================================
// Batch validation tests
// ===========================================================================

#[test]
fn test_validate_batch_ok() {
    let decls = vec![
        mk_decl("a", mk_type(), BinderInfo::Implicit),
        mk_decl("n", mk_nat(), BinderInfo::Default),
    ];
    assert!(validate_batch(&decls).is_ok());
}

#[test]
fn test_validate_batch_duplicate_name() {
    let decls = vec![
        mk_decl("x", mk_type(), BinderInfo::Implicit),
        mk_decl("x", mk_type(), BinderInfo::Implicit),
    ];
    let err = validate_batch(&decls).unwrap_err();
    assert!(matches!(err, VariableCmdExtError::DuplicateName(ref n) if n == "x"));
}

#[test]
fn test_validate_batch_binder_conflict() {
    let decls = vec![
        mk_decl("x", mk_type(), BinderInfo::Implicit),
        mk_decl("x", mk_type(), BinderInfo::Default),
    ];
    let err = validate_batch(&decls).unwrap_err();
    assert!(matches!(err, VariableCmdExtError::BinderConflict { .. }));
}

#[test]
fn test_validate_batch_cycle() {
    let decls = vec![
        mk_decl("a", Expr::const_str("b"), BinderInfo::Implicit),
        mk_decl("b", Expr::const_str("a"), BinderInfo::Default),
    ];
    let err = validate_batch(&decls).unwrap_err();
    assert!(matches!(err, VariableCmdExtError::DependencyCycle(_)));
}

#[test]
fn test_validate_batch_empty() {
    assert!(validate_batch(&[]).is_ok());
}

// ===========================================================================
// Suggestion tests
// ===========================================================================

#[test]
fn test_suggest_remove_unused() {
    let decls = vec![mk_decl("x", mk_nat(), BinderInfo::Default)];
    let tracker = VariableUsageTracker::new(&decls);
    // Never record usage => x is unused
    let suggestions = suggest_improvements(&decls, &tracker);
    assert!(suggestions.iter().any(|s| matches!(
        s,
        VariableSuggestion::RemoveUnused { name } if name == "x"
    )));
}

#[test]
fn test_suggest_make_implicit_for_sort_type() {
    let decls = vec![mk_decl("a", mk_type(), BinderInfo::Default)];
    let mut tracker = VariableUsageTracker::new(&decls);
    tracker.record_usage("some_def", &Expr::const_str("a"));
    let suggestions = suggest_improvements(&decls, &tracker);
    assert!(suggestions.iter().any(|s| matches!(
        s,
        VariableSuggestion::MakeImplicit { name } if name == "a"
    )));
}

#[test]
fn test_suggest_make_instance_for_class_app() {
    let decls = vec![mk_decl(
        "inst",
        Expr::app(Expr::const_str("Add"), Expr::const_str("a")),
        BinderInfo::Default,
    )];
    let tracker = VariableUsageTracker::new(&decls);
    let suggestions = suggest_improvements(&decls, &tracker);
    assert!(suggestions.iter().any(|s| matches!(
        s,
        VariableSuggestion::MakeInstance { name, class_name }
            if name == "inst" && class_name == "Add"
    )));
}

#[test]
fn test_suggest_merge_declarations() {
    let decls = vec![
        mk_decl("a", mk_type(), BinderInfo::Implicit),
        mk_decl("b", mk_type(), BinderInfo::Implicit),
    ];
    let tracker = VariableUsageTracker::new(&decls);
    let suggestions = suggest_improvements(&decls, &tracker);
    assert!(suggestions.iter().any(
        |s| matches!(s, VariableSuggestion::MergeDeclarations { names }
            if names.contains(&"a".to_owned()) && names.contains(&"b".to_owned())
        )
    ));
}

#[test]
fn test_suggest_no_suggestions_well_formed() {
    // A well-formed set: implicit type var, used, instance with class
    let decls = vec![mk_decl("a", mk_type(), BinderInfo::Implicit)];
    let mut tracker = VariableUsageTracker::new(&decls);
    tracker.record_usage("my_def", &Expr::const_str("a"));
    let suggestions = suggest_improvements(&decls, &tracker);
    // Should have no RemoveUnused (it's used) and no MakeImplicit (already implicit)
    assert!(suggestions
        .iter()
        .all(|s| !matches!(s, VariableSuggestion::RemoveUnused { .. })));
    assert!(suggestions
        .iter()
        .all(|s| !matches!(s, VariableSuggestion::MakeImplicit { .. })));
}

// ===========================================================================
// expr_node_count tests
// ===========================================================================

#[test]
fn test_expr_node_count_const() {
    assert_eq!(expr_node_count(&mk_nat()), 1);
}

#[test]
fn test_expr_node_count_app() {
    let expr = Expr::app(Expr::const_str("List"), mk_nat());
    assert_eq!(expr_node_count(&expr), 3); // App + Const + Const
}

#[test]
fn test_expr_node_count_sort() {
    assert_eq!(expr_node_count(&mk_type()), 1);
}

#[test]
fn test_expr_node_count_pi() {
    let expr = Expr::pi(BinderInfo::Default, mk_nat(), mk_bool());
    assert_eq!(expr_node_count(&expr), 3); // Pi + Const + Const
}

#[test]
fn test_expr_node_count_bvar() {
    assert_eq!(expr_node_count(&Expr::bvar(0)), 1);
}
