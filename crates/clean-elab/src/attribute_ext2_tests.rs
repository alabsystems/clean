// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for [`super::attribute_ext2`].

use clean_kernel::Name;

use super::attribute_ext2::*;

// ===========================================================================
// parse_attribute_list
// ===========================================================================

#[test]
fn test_parse_empty_input_returns_empty() {
    let result = parse_attribute_list("").unwrap();
    assert!(result.is_empty());
}

#[test]
fn test_parse_single_attribute() {
    let result = parse_attribute_list("simp").unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].name, "simp");
    assert!(result[0].args.is_empty());
    assert!(!result[0].is_removal);
}

#[test]
fn test_parse_multiple_attributes() {
    let result = parse_attribute_list("simp, inline, reducible").unwrap();
    assert_eq!(result.len(), 3);
    assert_eq!(result[0].name, "simp");
    assert_eq!(result[1].name, "inline");
    assert_eq!(result[2].name, "reducible");
}

#[test]
fn test_parse_attribute_with_argument() {
    let result = parse_attribute_list("priority 100").unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].name, "priority");
    assert_eq!(result[0].args, vec!["100"]);
}

#[test]
fn test_parse_deprecated_with_message() {
    let result = parse_attribute_list(r#"deprecated "use X instead""#).unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].name, "deprecated");
    assert_eq!(result[0].args, vec!["use X instead"]);
}

#[test]
fn test_parse_removal_syntax() {
    let result = parse_attribute_list("-simp").unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].name, "simp");
    assert!(result[0].is_removal);
}

#[test]
fn test_parse_mixed_normal_and_removal() {
    let result = parse_attribute_list("inline, -simp, reducible").unwrap();
    assert_eq!(result.len(), 3);
    assert!(!result[0].is_removal);
    assert!(result[1].is_removal);
    assert!(!result[2].is_removal);
}

#[test]
fn test_parse_whitespace_handling() {
    let result = parse_attribute_list("  simp ,  inline  ").unwrap();
    assert_eq!(result.len(), 2);
    assert_eq!(result[0].name, "simp");
    assert_eq!(result[1].name, "inline");
}

#[test]
fn test_parse_trailing_comma_ignored() {
    let result = parse_attribute_list("simp,").unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].name, "simp");
}

// ===========================================================================
// validate_attribute_for_decl
// ===========================================================================

#[test]
fn test_validate_simp_on_theorem_succeeds() {
    validate_attribute_for_decl("simp", DeclKind::Theorem)
        .expect("simp should be valid on theorem");
}

#[test]
fn test_validate_simp_on_inductive_fails() {
    let result = validate_attribute_for_decl("simp", DeclKind::Inductive);
    assert!(result.is_err());
}

#[test]
fn test_validate_class_on_structure_succeeds() {
    validate_attribute_for_decl("class", DeclKind::Structure)
        .expect("class should be valid on structure");
}

#[test]
fn test_validate_class_on_theorem_fails() {
    let result = validate_attribute_for_decl("class", DeclKind::Theorem);
    assert!(result.is_err());
}

#[test]
fn test_validate_inline_on_any_kind_succeeds() {
    // inline has no restrictions
    validate_attribute_for_decl("inline", DeclKind::Definition)
        .expect("inline should be valid on definition");
    validate_attribute_for_decl("inline", DeclKind::Theorem)
        .expect("inline should be valid on theorem");
    validate_attribute_for_decl("inline", DeclKind::Inductive)
        .expect("inline should be valid on inductive");
}

#[test]
fn test_validate_init_on_definition_succeeds() {
    validate_attribute_for_decl("init", DeclKind::Definition)
        .expect("init should be valid on definition");
}

#[test]
fn test_validate_init_on_structure_fails() {
    let result = validate_attribute_for_decl("init", DeclKind::Structure);
    assert!(result.is_err());
}

#[test]
fn test_validate_instance_on_instance_succeeds() {
    validate_attribute_for_decl("instance", DeclKind::Instance)
        .expect("instance should be valid on instance decl");
}

#[test]
fn test_supports_file_scope_attribute_removal_for_simp() {
    assert!(supports_file_scope_attribute_removal("simp"));
    assert!(!supports_file_scope_attribute_removal("inline"));
}

// ===========================================================================
// detect_conflicts
// ===========================================================================

#[test]
fn test_no_conflict_disjoint_attrs() {
    assert!(detect_conflicts(&["simp", "inline"]).is_none());
}

#[test]
fn test_conflict_inline_noinline() {
    let result = detect_conflicts(&["inline", "noinline"]);
    assert!(result.is_some());
    let (a, b) = result.unwrap();
    assert_eq!(a, "inline");
    assert_eq!(b, "noinline");
}

#[test]
fn test_conflict_reducible_irreducible() {
    let result = detect_conflicts(&["reducible", "irreducible"]);
    assert!(result.is_some());
}

#[test]
fn test_conflict_scoped_local() {
    let result = detect_conflicts(&["scoped", "local"]);
    assert!(result.is_some());
}

#[test]
fn test_no_conflict_single_attr() {
    assert!(detect_conflicts(&["inline"]).is_none());
}

#[test]
fn test_no_conflict_empty() {
    assert!(detect_conflicts(&[]).is_none());
}

// ===========================================================================
// ExtendedAttributeManager — apply
// ===========================================================================

fn make_attr(name: &str, decl: &str) -> AppliedAttribute {
    AppliedAttribute {
        attr_name: name.to_owned(),
        decl_name: Name::from_string(decl),
        args: Vec::new(),
        scope: Ext2Scope::Global,
    }
}

fn make_scoped_attr(name: &str, decl: &str, scope: Ext2Scope) -> AppliedAttribute {
    AppliedAttribute {
        attr_name: name.to_owned(),
        decl_name: Name::from_string(decl),
        args: Vec::new(),
        scope,
    }
}

#[test]
fn test_apply_attribute_basic() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_attr("simp", "my_lemma"))
        .expect("apply should succeed");
    assert!(mgr.has_attribute(&Name::from_string("my_lemma"), "simp"));
    assert_eq!(mgr.total_entries(), 1);
    assert_eq!(mgr.declaration_count(), 1);
}

#[test]
fn test_apply_multiple_attrs_same_decl() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_attr("simp", "f")).unwrap();
    mgr.apply_attribute(make_attr("inline", "f")).unwrap();
    let attrs = mgr.get_attributes(&Name::from_string("f"));
    assert_eq!(attrs.len(), 2);
}

#[test]
fn test_apply_conflicting_attrs_fails() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_attr("inline", "f")).unwrap();
    let result = mgr.apply_attribute(make_attr("noinline", "f"));
    assert!(result.is_err());
}

// ===========================================================================
// ExtendedAttributeManager — remove
// ===========================================================================

#[test]
fn test_remove_attribute_succeeds() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_attr("simp", "my_lemma")).unwrap();
    mgr.remove_attribute(&Name::from_string("my_lemma"), "simp")
        .expect("remove should succeed");
    assert!(!mgr.has_attribute(&Name::from_string("my_lemma"), "simp"));
}

#[test]
fn test_remove_nonexistent_attr_fails() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_attr("simp", "f")).unwrap();
    let result = mgr.remove_attribute(&Name::from_string("f"), "inline");
    assert!(result.is_err());
}

#[test]
fn test_remove_from_unknown_decl_fails() {
    let mut mgr = ExtendedAttributeManager::new();
    let result = mgr.remove_attribute(&Name::from_string("nonexistent"), "simp");
    // remove_attribute requires &mut self, so we need a mutable ref
    assert!(result.is_err());
}

// ===========================================================================
// ExtendedAttributeManager — scoped queries
// ===========================================================================

#[test]
fn test_get_scoped_attributes_global() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_scoped_attr("simp", "f", Ext2Scope::Global))
        .unwrap();
    mgr.apply_attribute(make_scoped_attr("inline", "f", Ext2Scope::Local))
        .unwrap();
    let global = mgr.get_scoped_attributes(&Name::from_string("f"), &Ext2Scope::Global);
    assert_eq!(global.len(), 1);
    assert_eq!(global[0].attr_name, "simp");
}

#[test]
fn test_get_scoped_attributes_local() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_scoped_attr("simp", "f", Ext2Scope::Local))
        .unwrap();
    let local = mgr.get_scoped_attributes(&Name::from_string("f"), &Ext2Scope::Local);
    assert_eq!(local.len(), 1);
}

#[test]
fn test_get_scoped_attributes_namespace() {
    let mut mgr = ExtendedAttributeManager::new();
    let ns = Name::from_string("Mathlib.Tactic");
    mgr.apply_attribute(make_scoped_attr("simp", "f", Ext2Scope::Scoped(ns.clone())))
        .unwrap();
    let scoped = mgr.get_scoped_attributes(&Name::from_string("f"), &Ext2Scope::Scoped(ns));
    assert_eq!(scoped.len(), 1);
}

// ===========================================================================
// ExtendedAttributeManager — custom attributes
// ===========================================================================

#[test]
fn test_register_custom_attribute() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.register_custom_attribute("my_attr", "A custom attribute", None)
        .expect("registration should succeed");
    assert!(mgr.is_custom_registered("my_attr"));
}

#[test]
fn test_register_duplicate_custom_attribute_fails() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.register_custom_attribute("my_attr", "First", None)
        .unwrap();
    let result = mgr.register_custom_attribute("my_attr", "Second", None);
    assert!(result.is_err());
}

#[test]
fn test_invoke_custom_handler_success() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    let mut mgr = ExtendedAttributeManager::new();
    let called = Arc::new(AtomicBool::new(false));
    let called_clone = Arc::clone(&called);

    mgr.register_custom_attribute(
        "track",
        "Tracking attribute",
        Some(Box::new(move |_name, _args| {
            called_clone.store(true, Ordering::SeqCst);
            Ok(())
        })),
    )
    .unwrap();

    let name = Name::from_string("test_fn");
    mgr.invoke_custom_handler("track", &name, &[])
        .expect("handler should succeed");
    assert!(called.load(Ordering::SeqCst));
}

#[test]
fn test_invoke_custom_handler_error() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.register_custom_attribute(
        "fail_attr",
        "Always fails",
        Some(Box::new(|_name, _args| {
            Err("intentional failure".to_owned())
        })),
    )
    .unwrap();

    let name = Name::from_string("test_fn");
    let result = mgr.invoke_custom_handler("fail_attr", &name, &[]);
    assert!(result.is_err());
}

#[test]
fn test_invoke_unknown_custom_handler_fails() {
    let mgr = ExtendedAttributeManager::new();
    let name = Name::from_string("test_fn");
    let result = mgr.invoke_custom_handler("nonexistent", &name, &[]);
    assert!(result.is_err());
}

// ===========================================================================
// ExtendedAttributeManager — inheritance
// ===========================================================================

#[test]
fn test_inherit_from_parent_basic() {
    let mut mgr = ExtendedAttributeManager::new();
    let parent = Name::from_string("Base");
    let child = Name::from_string("Derived");

    mgr.apply_attribute(make_attr("reducible", "Base")).unwrap();
    mgr.apply_attribute(make_attr("simp", "Base")).unwrap();
    mgr.register_parent(child.clone(), parent);

    let count = mgr.inherit_from_parent(&child);
    assert_eq!(count, 2);
    assert!(mgr.has_attribute(&child, "reducible"));
    assert!(mgr.has_attribute(&child, "simp"));
}

#[test]
fn test_inherit_skips_existing_attrs() {
    let mut mgr = ExtendedAttributeManager::new();
    let parent = Name::from_string("Base");
    let child = Name::from_string("Derived");

    mgr.apply_attribute(make_attr("simp", "Base")).unwrap();
    mgr.apply_attribute(make_attr("simp", "Derived")).unwrap();
    mgr.register_parent(child.clone(), parent);

    let count = mgr.inherit_from_parent(&child);
    assert_eq!(count, 0, "should not duplicate existing attr");
}

#[test]
fn test_inherit_no_parent_returns_zero() {
    let mut mgr = ExtendedAttributeManager::new();
    let child = Name::from_string("Standalone");
    let count = mgr.inherit_from_parent(&child);
    assert_eq!(count, 0);
}

#[test]
fn test_inherit_skips_conflicting_attrs() {
    let mut mgr = ExtendedAttributeManager::new();
    let parent = Name::from_string("Base");
    let child = Name::from_string("Derived");

    mgr.apply_attribute(make_attr("inline", "Base")).unwrap();
    mgr.apply_attribute(make_attr("noinline", "Derived"))
        .unwrap();
    mgr.register_parent(child.clone(), parent);

    // "inline" from parent conflicts with "noinline" on child
    let count = mgr.inherit_from_parent(&child);
    assert_eq!(count, 0, "conflicting attr should not be inherited");
}

// ===========================================================================
// Statistics
// ===========================================================================

#[test]
fn test_stats_applied_by_kind() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_attr("simp", "a")).unwrap();
    mgr.apply_attribute(make_attr("simp", "b")).unwrap();
    mgr.apply_attribute(make_attr("inline", "c")).unwrap();

    let stats = mgr.stats();
    assert_eq!(*stats.applied_by_kind.get("simp").unwrap_or(&0), 2);
    assert_eq!(*stats.applied_by_kind.get("inline").unwrap_or(&0), 1);
}

#[test]
fn test_stats_conflicts_detected() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_attr("inline", "f")).unwrap();
    let _ = mgr.apply_attribute(make_attr("noinline", "f"));
    assert_eq!(mgr.stats().conflicts_detected, 1);
}

#[test]
fn test_stats_removals_processed() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_attr("simp", "f")).unwrap();
    mgr.remove_attribute(&Name::from_string("f"), "simp")
        .unwrap();
    assert_eq!(mgr.stats().removals_processed, 1);
}

#[test]
fn test_stats_custom_registered() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.register_custom_attribute("a", "desc", None).unwrap();
    mgr.register_custom_attribute("b", "desc", None).unwrap();
    assert_eq!(mgr.stats().custom_registered, 2);
}

#[test]
fn test_stats_inherited() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_attr("simp", "Base")).unwrap();
    mgr.register_parent(Name::from_string("Derived"), Name::from_string("Base"));
    mgr.inherit_from_parent(&Name::from_string("Derived"));
    assert_eq!(mgr.stats().inherited, 1);
}

#[test]
fn test_reset_stats() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_attr("simp", "a")).unwrap();
    assert_eq!(*mgr.stats().applied_by_kind.get("simp").unwrap(), 1);
    mgr.reset_stats();
    assert!(mgr.stats().applied_by_kind.is_empty());
    assert_eq!(mgr.stats().conflicts_detected, 0);
}

// ===========================================================================
// Argument parsing helpers
// ===========================================================================

#[test]
fn test_parse_priority_arg_success() {
    let args = vec!["100".to_owned()];
    let result = parse_priority_arg(&args).unwrap();
    assert_eq!(result, 100);
}

#[test]
fn test_parse_priority_arg_missing() {
    let args: Vec<String> = vec![];
    let result = parse_priority_arg(&args);
    assert!(result.is_err());
}

#[test]
fn test_parse_priority_arg_non_numeric() {
    let args = vec!["abc".to_owned()];
    let result = parse_priority_arg(&args);
    assert!(result.is_err());
}

#[test]
fn test_parse_deprecated_arg_with_message() {
    let args = vec!["use X instead".to_owned()];
    assert_eq!(parse_deprecated_arg(&args), "use X instead");
}

#[test]
fn test_parse_deprecated_arg_empty() {
    let args: Vec<String> = vec![];
    assert_eq!(parse_deprecated_arg(&args), "");
}

#[test]
fn test_parse_extern_arg_success() {
    let args = vec!["lean_io_prim".to_owned()];
    let result = parse_extern_arg(&args).unwrap();
    assert_eq!(result, "lean_io_prim");
}

#[test]
fn test_parse_extern_arg_missing() {
    let args: Vec<String> = vec![];
    let result = parse_extern_arg(&args);
    assert!(result.is_err());
}

// ===========================================================================
// Debug / Default impls
// ===========================================================================

#[test]
fn test_manager_default_is_empty() {
    let mgr = ExtendedAttributeManager::default();
    assert_eq!(mgr.total_entries(), 0);
    assert_eq!(mgr.declaration_count(), 0);
}

#[test]
fn test_manager_debug_does_not_panic() {
    let mut mgr = ExtendedAttributeManager::new();
    mgr.apply_attribute(make_attr("simp", "f")).unwrap();
    let debug = format!("{mgr:?}");
    assert!(debug.contains("ExtendedAttributeManager"));
}
