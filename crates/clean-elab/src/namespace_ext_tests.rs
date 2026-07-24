// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended namespace management.

use crate::namespace::NamespaceState;
use crate::namespace_ext::{
    edit_distance, ExportFilter, NamespaceExt, NamespaceExtConfig, NamespaceExtError,
    OpenDirective, RenameRule,
};
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::Environment;
use std::collections::HashSet;

/// Helper: add an axiom constant to the environment.
fn add_const(env: &mut Environment, name: &str) {
    let n = Name::from_string(name);
    let decl = Declaration::Axiom {
        name: n,
        level_params: vec![],
        type_: clean_kernel::Expr::type_(),
    };
    env.add_decl_structural(decl)
        .expect("add_const should succeed");
}

// =========================================================================
// Protected names
// =========================================================================

#[test]
fn test_mark_and_check_protected() {
    let mut ext = NamespaceExt::new();
    let name = Name::from_string("Nat.succ");
    assert!(!ext.is_protected(&name));

    ext.mark_protected(name.clone());
    assert!(ext.is_protected(&name));
}

#[test]
fn test_protected_access_blocked_via_open() {
    let mut ext = NamespaceExt::new();
    ext.mark_protected(Name::from_string("Nat.internal"));

    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let err = ext.check_protected_access("internal", &state);
    assert!(err.is_some(), "should detect protected access");
    match err.unwrap() {
        NamespaceExtError::ProtectedAccess { name, qualified } => {
            assert_eq!(name, "internal");
            assert_eq!(qualified, "Nat.internal");
        }
        other => panic!("unexpected error: {other:?}"),
    }
}

#[test]
fn test_protected_access_allowed_when_not_opened() {
    let mut ext = NamespaceExt::new();
    ext.mark_protected(Name::from_string("Nat.internal"));

    let state = NamespaceState::new();
    // No namespace opened — no protection violation
    assert!(ext.check_protected_access("internal", &state).is_none());
}

#[test]
fn test_protected_name_excluded_from_open_ext() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.secret");

    let mut ext = NamespaceExt::new();
    ext.mark_protected(Name::from_string("Nat.secret"));

    let mut state = NamespaceState::new();
    ext.process_open_ext(&env, "Nat", &OpenDirective::All, &[], &mut state)
        .expect("open should succeed");

    assert!(state.resolve("add").is_some(), "add should be imported");
    assert!(
        state.resolve("secret").is_none(),
        "protected name should be excluded"
    );
}

// =========================================================================
// Open with hiding
// =========================================================================

#[test]
fn test_open_ext_hiding() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");
    add_const(&mut env, "Nat.zero");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();

    let hiding: HashSet<String> = ["mul".to_string()].into_iter().collect();
    ext.process_open_ext(&env, "Nat", &OpenDirective::Hiding(hiding), &[], &mut state)
        .expect("open should succeed");

    assert!(state.resolve("add").is_some());
    assert!(state.resolve("zero").is_some());
    assert!(state.resolve("mul").is_none(), "mul should be hidden");
}

#[test]
fn test_open_ext_hiding_multiple() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");
    add_const(&mut env, "Nat.zero");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();

    let hiding: HashSet<String> = ["mul".to_string(), "zero".to_string()]
        .into_iter()
        .collect();
    ext.process_open_ext(&env, "Nat", &OpenDirective::Hiding(hiding), &[], &mut state)
        .expect("open should succeed");

    assert!(state.resolve("add").is_some());
    assert!(state.resolve("mul").is_none());
    assert!(state.resolve("zero").is_none());
}

// =========================================================================
// Open with selective import
// =========================================================================

#[test]
fn test_open_ext_selective() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");
    add_const(&mut env, "Nat.zero");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();

    ext.process_open_ext(
        &env,
        "Nat",
        &OpenDirective::Selective(vec!["add".into(), "zero".into()]),
        &[],
        &mut state,
    )
    .expect("open should succeed");

    assert!(state.resolve("add").is_some());
    assert!(state.resolve("zero").is_some());
    assert!(state.resolve("mul").is_none());
}

// =========================================================================
// Open with renaming
// =========================================================================

#[test]
fn test_open_ext_renaming() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();

    let renamings = vec![RenameRule {
        from: "add".into(),
        to: "plus".into(),
    }];
    ext.process_open_ext(&env, "Nat", &OpenDirective::All, &renamings, &mut state)
        .expect("open should succeed");

    assert_eq!(
        state.resolve("plus").unwrap().to_string(),
        "Nat.add",
        "add should be renamed to plus"
    );
    assert!(
        state.resolve("add").is_none(),
        "original name should not be accessible"
    );
    assert!(state.resolve("mul").is_some(), "mul should be unaffected");
}

#[test]
fn test_open_ext_renaming_with_selective() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();

    let renamings = vec![RenameRule {
        from: "add".into(),
        to: "natAdd".into(),
    }];
    ext.process_open_ext(
        &env,
        "Nat",
        &OpenDirective::Selective(vec!["add".into()]),
        &renamings,
        &mut state,
    )
    .expect("open should succeed");

    assert_eq!(state.resolve("natAdd").unwrap().to_string(), "Nat.add");
    assert!(state.resolve("add").is_none());
    assert!(state.resolve("mul").is_none());
}

// =========================================================================
// Open with hiding + renaming combined
// =========================================================================

#[test]
fn test_open_ext_hiding_and_renaming_combined() {
    let mut env = Environment::new();
    add_const(&mut env, "List.map");
    add_const(&mut env, "List.filter");
    add_const(&mut env, "List.foldl");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();

    let hiding: HashSet<String> = ["foldl".to_string()].into_iter().collect();
    let renamings = vec![RenameRule {
        from: "map".into(),
        to: "transform".into(),
    }];
    ext.process_open_ext(
        &env,
        "List",
        &OpenDirective::Hiding(hiding),
        &renamings,
        &mut state,
    )
    .expect("open should succeed");

    assert_eq!(state.resolve("transform").unwrap().to_string(), "List.map");
    assert!(state.resolve("map").is_none());
    assert!(state.resolve("filter").is_some());
    assert!(state.resolve("foldl").is_none());
}

// =========================================================================
// Export filtering
// =========================================================================

#[test]
fn test_export_ext_selected() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");
    add_const(&mut env, "Nat.zero");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();

    ext.process_export_ext(
        &env,
        "Nat",
        &ExportFilter::Selected(vec!["add".into(), "zero".into()]),
        Some("MyLib"),
        &mut state,
    )
    .expect("export should succeed");

    assert!(state.resolve("add").is_some());
    assert!(state.resolve("zero").is_some());
    assert!(state.resolve("mul").is_none());

    let exports = state.exports();
    assert_eq!(exports.len(), 2);
}

#[test]
fn test_export_ext_hiding() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();

    let hiding: HashSet<String> = ["mul".to_string()].into_iter().collect();
    ext.process_export_ext(&env, "Nat", &ExportFilter::Hiding(hiding), None, &mut state)
        .expect("export should succeed");

    assert!(state.resolve("add").is_some());
    assert!(state.resolve("mul").is_none());
}

#[test]
fn test_export_ext_all() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();

    ext.process_export_ext(&env, "Nat", &ExportFilter::All, None, &mut state)
        .expect("export should succeed");

    assert!(state.resolve("add").is_some());
    assert!(state.resolve("mul").is_some());
}

#[test]
fn test_export_ext_protected_blocked() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.secret");

    let mut ext = NamespaceExt::new();
    ext.mark_protected(Name::from_string("Nat.secret"));

    let mut state = NamespaceState::new();
    let result = ext.process_export_ext(&env, "Nat", &ExportFilter::All, None, &mut state);

    assert!(result.is_err(), "should block protected re-export");
    match result.unwrap_err() {
        NamespaceExtError::ProtectedReexport(name) => {
            assert!(name.contains("secret"));
        }
        other => panic!("unexpected error: {other:?}"),
    }
}

#[test]
fn test_export_ext_protected_allowed_with_config() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.secret");

    let config = NamespaceExtConfig {
        allow_protected_reexport: true,
        ..Default::default()
    };
    let mut ext = NamespaceExt::with_config(config);
    ext.mark_protected(Name::from_string("Nat.secret"));

    let mut state = NamespaceState::new();
    ext.process_export_ext(&env, "Nat", &ExportFilter::All, None, &mut state)
        .expect("should allow protected re-export with config");

    assert!(state.resolve("secret").is_some());
}

// =========================================================================
// Scoped attributes
// =========================================================================

#[test]
fn test_scoped_attr_register_and_query() {
    let mut ext = NamespaceExt::new();
    let ns = Name::from_string("Nat");
    let decl = Name::from_string("Nat.add_comm");

    ext.register_scoped_attr(ns.clone(), "simp", decl.clone());

    // Not active when namespace not opened
    let state = NamespaceState::new();
    let active = ext.get_active_scoped_attrs("simp", &state);
    assert!(active.is_empty(), "should be inactive when ns not opened");

    // Active when namespace opened
    let mut state = NamespaceState::new();
    state.open_namespace(ns);
    let active = ext.get_active_scoped_attrs("simp", &state);
    assert_eq!(active.len(), 1);
    assert_eq!(active[0].to_string(), "Nat.add_comm");
}

#[test]
fn test_scoped_attr_multiple_namespaces() {
    let mut ext = NamespaceExt::new();
    ext.register_scoped_attr(
        Name::from_string("Nat"),
        "simp",
        Name::from_string("Nat.add_zero"),
    );
    ext.register_scoped_attr(
        Name::from_string("Int"),
        "simp",
        Name::from_string("Int.add_zero"),
    );

    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));
    state.open_namespace(Name::from_string("Int"));

    let active = ext.get_active_scoped_attrs("simp", &state);
    assert_eq!(active.len(), 2);
}

#[test]
fn test_scoped_attr_get_all_ignores_open_state() {
    let mut ext = NamespaceExt::new();
    ext.register_scoped_attr(
        Name::from_string("Nat"),
        "simp",
        Name::from_string("Nat.add_zero"),
    );

    let all = ext.get_all_scoped_attrs("simp");
    assert_eq!(
        all.len(),
        1,
        "get_all should return all regardless of open state"
    );
}

// =========================================================================
// Resolution with suggestions
// =========================================================================

#[test]
fn test_resolve_with_suggestions_success() {
    // Closed Gap 12 in Wave 92: pin the policy. `open Nat` MUST resolve
    // a bare `add` to `Nat.add` without requiring an explicit alias,
    // matching Lean 4's `open` semantics. The resolver already walks
    // `state.open_namespaces()` after the alias / fully-qualified /
    // current-namespace checks; this test now hard-asserts the result
    // instead of accepting both behaviours.
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let result = ext.resolve_with_suggestions("add", &state, &env);
    assert_eq!(
        result
            .expect("`open Nat` must resolve bare `add`")
            .to_string(),
        "Nat.add",
        "open_namespace must unambiguously resolve bare names",
    );

    // Adding an explicit alias keeps working (alias takes precedence
    // over open_namespace walk, which is already the resolver order).
    state.insert_alias_pub("add".into(), Name::from_string("Nat.add"));
    let result = ext.resolve_with_suggestions("add", &state, &env);
    assert_eq!(result.unwrap().to_string(), "Nat.add");
}

#[test]
fn test_resolve_with_suggestions_open_namespace_does_not_invent_constants() {
    // Negative guard for Wave 92: `open Nat` must NOT make a bare
    // `garbage` resolve to `Nat.garbage` when no such constant exists
    // in the environment. The open_namespace walk must only succeed
    // when the qualified name is actually present in `env`.
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let result = ext.resolve_with_suggestions("garbage", &state, &env);
    assert!(
        result.is_err(),
        "open_namespace must not fabricate `Nat.garbage` from `garbage` \
         when no such const exists, got {result:?}",
    );
}

#[test]
fn test_resolve_with_suggestions_fully_qualified() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let ext = NamespaceExt::new();
    let state = NamespaceState::new();

    let result = ext.resolve_with_suggestions("Nat.add", &state, &env);
    assert_eq!(result.unwrap().to_string(), "Nat.add");
}

#[test]
fn test_resolve_with_suggestions_via_current_namespace() {
    let mut env = Environment::new();
    add_const(&mut env, "Foo.bar");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();
    state.enter_namespace(Name::from_string("Foo"));

    let result = ext.resolve_with_suggestions("bar", &state, &env);
    assert_eq!(result.unwrap().to_string(), "Foo.bar");
}

#[test]
fn test_resolve_with_suggestions_failure_provides_suggestions() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.addi");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();
    state.insert_alias_pub("add".into(), Name::from_string("Nat.add"));
    state.insert_alias_pub("addi".into(), Name::from_string("Nat.addi"));

    let result = ext.resolve_with_suggestions("addx", &state, &env);
    match result {
        Err(NamespaceExtError::UnresolvedWithSuggestions { name, suggestions }) => {
            assert_eq!(name, "addx");
            assert!(
                !suggestions.is_empty(),
                "should provide suggestions for near-miss"
            );
            // "add" and "addi" are both distance 1 from "addx"
            assert!(suggestions.contains(&"add".to_string()));
        }
        other => panic!("expected UnresolvedWithSuggestions, got: {other:?}"),
    }
}

#[test]
fn test_resolve_protected_name_gives_error() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.internal");

    let mut ext = NamespaceExt::new();
    ext.mark_protected(Name::from_string("Nat.internal"));

    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let result = ext.resolve_with_suggestions("internal", &state, &env);
    assert!(
        matches!(result, Err(NamespaceExtError::ProtectedAccess { .. })),
        "should return ProtectedAccess error"
    );
}

// =========================================================================
// Edit distance
// =========================================================================

#[test]
fn test_edit_distance_identical() {
    assert_eq!(edit_distance("hello", "hello"), 0);
}

#[test]
fn test_edit_distance_empty() {
    assert_eq!(edit_distance("", "abc"), 3);
    assert_eq!(edit_distance("abc", ""), 3);
    assert_eq!(edit_distance("", ""), 0);
}

#[test]
fn test_edit_distance_substitution() {
    assert_eq!(edit_distance("cat", "car"), 1);
}

#[test]
fn test_edit_distance_insertion_deletion() {
    assert_eq!(edit_distance("abc", "abcd"), 1);
    assert_eq!(edit_distance("abcd", "abc"), 1);
}

#[test]
fn test_edit_distance_complex() {
    assert_eq!(edit_distance("kitten", "sitting"), 3);
}

// =========================================================================
// Open on empty namespace is no-op
// =========================================================================

#[test]
fn test_open_ext_empty_namespace_is_noop() {
    let env = Environment::new();
    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();

    ext.process_open_ext(&env, "NonExistent", &OpenDirective::All, &[], &mut state)
        .expect("should not error on empty namespace");

    assert!(!state.has_opens());
}

// =========================================================================
// Config access
// =========================================================================

#[test]
fn test_config_defaults() {
    let ext = NamespaceExt::new();
    assert_eq!(ext.config().max_suggestions, 5);
    assert_eq!(ext.config().max_edit_distance, 3);
    assert!(!ext.config().allow_protected_reexport);
}

#[test]
fn test_config_custom() {
    let config = NamespaceExtConfig {
        max_suggestions: 10,
        max_edit_distance: 5,
        allow_protected_reexport: true,
    };
    let ext = NamespaceExt::with_config(config);
    assert_eq!(ext.config().max_suggestions, 10);
    assert!(ext.config().allow_protected_reexport);
}

// =========================================================================
// Nested namespaces are excluded (only direct children)
// =========================================================================

#[test]
fn test_open_ext_excludes_nested() {
    let mut env = Environment::new();
    add_const(&mut env, "Foo.bar");
    add_const(&mut env, "Foo.Inner.deep");

    let ext = NamespaceExt::new();
    let mut state = NamespaceState::new();

    ext.process_open_ext(&env, "Foo", &OpenDirective::All, &[], &mut state)
        .expect("open should succeed");

    assert!(state.resolve("bar").is_some());
    assert!(
        state.resolve("deep").is_none(),
        "nested names should not be imported"
    );
    assert!(state.resolve("Inner.deep").is_none());
}
