// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::Environment;
use clean_parser::OpenPath;
/// Helper: add a constant to the environment for testing.
fn add_const(env: &mut Environment, name: &str) {
    let n = Name::from_string(name);
    let decl = Declaration::Axiom {
        name: n,
        level_params: vec![],
        type_: Expr::type_(),
    };
    env.add_decl_structural(decl)
        .expect("add_const should succeed");
}

#[test]
fn test_open_full_namespace() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");
    add_const(&mut env, "Nat.zero");

    let mut state = NamespaceState::new();
    let path = OpenPath {
        path: vec!["Nat".into()],
        names: vec![],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path], &mut state).unwrap();

    assert_eq!(state.resolve("add").unwrap().to_string(), "Nat.add");
    assert_eq!(state.resolve("mul").unwrap().to_string(), "Nat.mul");
    assert_eq!(state.resolve("zero").unwrap().to_string(), "Nat.zero");
    assert!(state.resolve("nonexistent").is_none());
}

#[test]
fn test_open_selective() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");
    add_const(&mut env, "Nat.zero");

    let mut state = NamespaceState::new();
    let path = OpenPath {
        path: vec!["Nat".into()],
        names: vec!["add".into(), "zero".into()],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path], &mut state).unwrap();

    assert!(state.resolve("add").is_some());
    assert!(state.resolve("zero").is_some());
    assert!(state.resolve("mul").is_none());
}

#[test]
fn test_open_hiding() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");
    add_const(&mut env, "Nat.zero");

    let mut state = NamespaceState::new();
    let path = OpenPath {
        path: vec!["Nat".into()],
        names: vec![],
        hiding: vec!["mul".into()],
        renaming: vec![],
    };
    process_open(&env, &[path], &mut state).unwrap();

    assert!(state.resolve("add").is_some());
    assert!(state.resolve("zero").is_some());
    assert!(state.resolve("mul").is_none());
}

#[test]
fn test_open_renaming() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let mut state = NamespaceState::new();
    let path = OpenPath {
        path: vec!["Nat".into()],
        names: vec![],
        hiding: vec![],
        renaming: vec![clean_parser::surface::OpenRename {
            from: "add".into(),
            to: "plus".into(),
        }],
    };
    process_open(&env, &[path], &mut state).unwrap();

    // "add" should be renamed to "plus"
    assert_eq!(state.resolve("plus").unwrap().to_string(), "Nat.add");
    // original short name "add" is no longer available
    assert!(state.resolve("add").is_none());
    // B13 flip: `open Nat renaming add → plus` imports ONLY the renamed pairs
    // (Lean `elabOpenRenaming` adds one `OpenDecl.explicit` per pair and
    // nothing else — `Lean/Elab/BuiltinCommand.lean`). This test previously
    // pinned the divergent full-open-with-renames behavior (`mul` visible),
    // which silently over-imported.
    assert!(state.resolve("mul").is_none());
}

#[test]
fn test_open_dotted_namespace() {
    let mut env = Environment::new();
    add_const(&mut env, "Foo.Bar.baz");
    add_const(&mut env, "Foo.Bar.qux");
    // Nested name should NOT be imported as direct child
    add_const(&mut env, "Foo.Bar.Inner.deep");

    let mut state = NamespaceState::new();
    let path = OpenPath {
        path: vec!["Foo".into(), "Bar".into()],
        names: vec![],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path], &mut state).unwrap();

    assert!(state.resolve("baz").is_some());
    assert!(state.resolve("qux").is_some());
    // Nested names are NOT imported (only direct children)
    assert!(state.resolve("deep").is_none());
    assert!(state.resolve("Inner.deep").is_none());
}

#[test]
fn test_scoped_open_push_pop() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let mut state = NamespaceState::new();

    // Open Nat at file level
    let path_nat = OpenPath {
        path: vec!["Nat".into()],
        names: vec!["add".into()],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path_nat], &mut state).unwrap();
    assert!(state.resolve("add").is_some());
    assert!(state.resolve("mul").is_none());

    // Push scope and open more
    state.push_scope();
    let path_mul = OpenPath {
        path: vec!["Nat".into()],
        names: vec!["mul".into()],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path_mul], &mut state).unwrap();
    assert!(state.resolve("add").is_some());
    assert!(state.resolve("mul").is_some());

    // Pop scope: mul should be gone, add should remain
    state.pop_scope();
    assert!(state.resolve("add").is_some());
    assert!(state.resolve("mul").is_none());
}

#[test]
fn test_scoped_open_overwrite_restore() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Int.add");

    let mut state = NamespaceState::new();

    // Open Nat.add as "add"
    let path_nat = OpenPath {
        path: vec!["Nat".into()],
        names: vec!["add".into()],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path_nat], &mut state).unwrap();
    assert_eq!(state.resolve("add").unwrap().to_string(), "Nat.add");

    // Push scope and shadow with Int.add
    state.push_scope();
    let path_int = OpenPath {
        path: vec!["Int".into()],
        names: vec!["add".into()],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path_int], &mut state).unwrap();
    assert_eq!(state.resolve("add").unwrap().to_string(), "Int.add");

    // Pop: should restore Nat.add
    state.pop_scope();
    assert_eq!(state.resolve("add").unwrap().to_string(), "Nat.add");
}

#[test]
fn test_export_basic() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let mut state = NamespaceState::new();
    process_export(
        &env,
        &["Nat".into()],
        &["add".into(), "mul".into()],
        Some("MyLib"),
        &mut state,
    )
    .unwrap();

    // B13 flip: the aliases live in the CURRENT namespace (Lean `elabExport`:
    // `addAlias (currNamespace ++ id)`), so inside `MyLib` they are registered
    // as `MyLib.add`/`MyLib.mul` — visible bare only from within `MyLib` (via
    // the outward walk in `elab_ident`), and as `MyLib.add` from anywhere. The
    // old behavior leaked the bare short names file-wide regardless of the
    // declaring namespace.
    assert!(state.resolve("add").is_none());
    assert_eq!(state.resolve("MyLib.add").unwrap().to_string(), "Nat.add");
    assert_eq!(state.resolve("MyLib.mul").unwrap().to_string(), "Nat.mul");

    // Check export records
    assert_eq!(state.exports().len(), 2);
    assert_eq!(state.exports()[0].short, "MyLib.add");
    assert_eq!(state.exports()[0].target.to_string(), "Nat.add");
}

#[test]
fn test_export_root_level() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let mut state = NamespaceState::new();
    process_export(&env, &["Nat".into()], &["add".into()], None, &mut state).unwrap();

    assert_eq!(state.exports()[0].short, "add");
}

#[test]
fn test_export_missing_name_is_loud() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let mut state = NamespaceState::new();
    // B13 flip: exporting a name that doesn't exist is a LOUD error (Lean
    // `elabExport` resolves each ident and errors on unknown constants). The
    // old silent skip hid typos: `export Nat (nonexistent)` vanished without a
    // trace and the use site then failed confusingly.
    let result = process_export(
        &env,
        &["Nat".into()],
        &["nonexistent".into()],
        None,
        &mut state,
    );

    assert!(
        matches!(result, Err(NamespaceError::NameNotFound { .. })),
        "missing export name must be a loud NameNotFound error, got {result:?}"
    );
    assert!(
        state.exports().is_empty(),
        "no alias should be created for missing name"
    );
}

#[test]
fn test_open_unknown_namespace_is_noop() {
    let env = Environment::new();
    let mut state = NamespaceState::new();
    let path = OpenPath {
        path: vec!["NonExistent".into()],
        names: vec![],
        hiding: vec![],
        renaming: vec![],
    };
    // Should not error (Lean 4 behavior)
    process_open(&env, &[path], &mut state).unwrap();
    assert!(!state.has_opens());
}

#[test]
fn test_multiple_opens() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Int.sub");

    let mut state = NamespaceState::new();
    let paths = vec![
        OpenPath {
            path: vec!["Nat".into()],
            names: vec![],
            hiding: vec![],
            renaming: vec![],
        },
        OpenPath {
            path: vec!["Int".into()],
            names: vec![],
            hiding: vec![],
            renaming: vec![],
        },
    ];
    process_open(&env, &paths, &mut state).unwrap();

    assert!(state.resolve("add").is_some());
    assert!(state.resolve("sub").is_some());
}

#[test]
fn test_pop_scope_empty_is_noop() {
    let mut state = NamespaceState::new();
    // Should not panic
    state.pop_scope();
    assert!(!state.has_opens());
}

#[test]
fn test_selective_open_with_renaming() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let mut state = NamespaceState::new();
    let path = OpenPath {
        path: vec!["Nat".into()],
        names: vec!["add".into()],
        hiding: vec![],
        renaming: vec![clean_parser::surface::OpenRename {
            from: "add".into(),
            to: "natAdd".into(),
        }],
    };
    process_open(&env, &[path], &mut state).unwrap();

    assert_eq!(state.resolve("natAdd").unwrap().to_string(), "Nat.add");
    assert!(state.resolve("add").is_none());
    assert!(state.resolve("mul").is_none());
}

// =========================================================================
// Namespace enter/exit tests
// =========================================================================

#[test]
fn test_namespace_enter_exit_changes_prefix() {
    let mut state = NamespaceState::new();
    assert!(
        state.current_namespace().is_anon(),
        "initial namespace should be anonymous"
    );

    state.enter_namespace(Name::from_string("Foo"));
    assert_eq!(state.current_namespace().to_string(), "Foo");

    state.enter_namespace(Name::from_string("Bar"));
    assert_eq!(state.current_namespace().to_string(), "Foo.Bar");

    state.exit_namespace();
    assert_eq!(state.current_namespace().to_string(), "Foo");

    state.exit_namespace();
    assert!(
        state.current_namespace().is_anon(),
        "should return to root after exiting all namespaces"
    );
}

#[test]
fn test_namespace_nested_three_deep() {
    let mut state = NamespaceState::new();

    state.enter_namespace(Name::from_string("A"));
    state.enter_namespace(Name::from_string("B"));
    state.enter_namespace(Name::from_string("C"));
    assert_eq!(state.current_namespace().to_string(), "A.B.C");

    state.exit_namespace();
    assert_eq!(state.current_namespace().to_string(), "A.B");

    state.exit_namespace();
    assert_eq!(state.current_namespace().to_string(), "A");

    state.exit_namespace();
    assert!(state.current_namespace().is_anon());
}

// =========================================================================
// Section variable tracking tests
// =========================================================================

#[test]
fn test_section_variable_tracking() {
    let mut state = NamespaceState::new();
    state.enter_section(Some(Name::from_string("MySection")));

    let var = SectionVariable {
        name: Name::from_string("x"),
        type_: Expr::type_(),
        binder_info: BinderInfo::Default,
    };
    state.add_section_variable(var);

    let vars = state.get_section_variables();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name.to_string(), "x");
    assert!(state.in_section());
    assert_eq!(state.section_depth(), 1);

    state.exit_section().expect("should exit section");
    assert!(!state.in_section());
    assert_eq!(state.section_depth(), 0);
}

#[test]
fn test_section_exit_restores_namespace() {
    let mut state = NamespaceState::new();
    state.enter_namespace(Name::from_string("Foo"));

    state.enter_section(Some(Name::from_string("S")));
    state.enter_namespace(Name::from_string("Bar"));
    assert_eq!(state.current_namespace().to_string(), "Foo.Bar");

    state.exit_section().expect("should exit section");
    assert_eq!(
        state.current_namespace().to_string(),
        "Foo",
        "section exit should restore namespace to state at entry"
    );
}

#[test]
fn test_section_exit_restores_open_namespaces() {
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    state.enter_section(None);
    state.open_namespace(Name::from_string("Int"));
    assert_eq!(
        state.open_namespaces().len(),
        2,
        "both Nat and Int should be open inside section"
    );

    state.exit_section().expect("should exit section");
    assert_eq!(
        state.open_namespaces().len(),
        1,
        "only Nat should remain after section exit"
    );
    assert_eq!(state.open_namespaces()[0].to_string(), "Nat");
}

#[test]
fn test_anonymous_section() {
    let mut state = NamespaceState::new();
    state.enter_section(None);
    assert!(state.in_section());

    let var = SectionVariable {
        name: Name::from_string("n"),
        type_: Expr::type_(),
        binder_info: BinderInfo::Implicit,
    };
    state.add_section_variable(var);

    let vars = state.get_section_variables();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name.to_string(), "n");

    state.exit_section().expect("should exit anonymous section");
    assert!(!state.in_section());
}

#[test]
fn test_nested_sections_variable_ordering() {
    let mut state = NamespaceState::new();

    state.enter_section(Some(Name::from_string("Outer")));
    state.add_section_variable(SectionVariable {
        name: Name::from_string("a"),
        type_: Expr::type_(),
        binder_info: BinderInfo::Default,
    });

    state.enter_section(Some(Name::from_string("Inner")));
    state.add_section_variable(SectionVariable {
        name: Name::from_string("b"),
        type_: Expr::type_(),
        binder_info: BinderInfo::Default,
    });

    let vars = state.get_section_variables();
    assert_eq!(vars.len(), 2, "should see variables from both sections");
    assert_eq!(vars[0].name.to_string(), "a", "outer variable first");
    assert_eq!(vars[1].name.to_string(), "b", "inner variable second");

    state.exit_section().expect("exit inner section");
    let vars = state.get_section_variables();
    assert_eq!(
        vars.len(),
        1,
        "only outer variable remains after inner exit"
    );
    assert_eq!(vars[0].name.to_string(), "a");

    state.exit_section().expect("exit outer section");
    let vars = state.get_section_variables();
    assert!(vars.is_empty(), "no variables after all sections exited");
}

#[test]
fn test_exit_section_with_no_section_returns_error() {
    let mut state = NamespaceState::new();
    let result = state.exit_section();
    assert!(
        result.is_err(),
        "exiting section when none is active should error"
    );
}

// =========================================================================
// Open/close namespace tracking tests
// =========================================================================

#[test]
fn test_open_close_namespace_tracking() {
    let mut state = NamespaceState::new();
    assert!(state.open_namespaces().is_empty());

    state.open_namespace(Name::from_string("Nat"));
    assert_eq!(state.open_namespaces().len(), 1);
    assert_eq!(state.open_namespaces()[0].to_string(), "Nat");

    // Opening same namespace again should not duplicate
    state.open_namespace(Name::from_string("Nat"));
    assert_eq!(state.open_namespaces().len(), 1);

    state.open_namespace(Name::from_string("Int"));
    assert_eq!(state.open_namespaces().len(), 2);

    state.close_namespace(&Name::from_string("Nat"));
    assert_eq!(state.open_namespaces().len(), 1);
    assert_eq!(state.open_namespaces()[0].to_string(), "Int");
}

// =========================================================================
// resolve_name tests
// =========================================================================

#[test]
fn test_resolve_name_with_namespace() {
    let mut state = NamespaceState::new();
    state.enter_namespace(Name::from_string("Foo"));

    let resolved = state.resolve_name(&Name::from_string("bar"));
    assert_eq!(resolved.to_string(), "Foo.bar");
}

#[test]
fn test_resolve_name_at_root() {
    let state = NamespaceState::new();
    let resolved = state.resolve_name(&Name::from_string("bar"));
    assert_eq!(
        resolved.to_string(),
        "bar",
        "at root namespace, name should be unchanged"
    );
}

// =========================================================================
// Name resolution module tests
// =========================================================================

#[test]
fn test_name_resolution_fully_qualified() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let state = NamespaceState::new();
    let result =
        crate::name_resolution::resolve_identifier(&Name::from_string("Nat.add"), &state, &env);
    assert_eq!(
        result
            .expect("should resolve fully-qualified name")
            .to_string(),
        "Nat.add"
    );
}

#[test]
fn test_name_resolution_via_current_namespace() {
    let mut env = Environment::new();
    add_const(&mut env, "Foo.bar");

    let mut state = NamespaceState::new();
    state.enter_namespace(Name::from_string("Foo"));

    let result =
        crate::name_resolution::resolve_identifier(&Name::from_string("bar"), &state, &env);
    assert_eq!(
        result
            .expect("should resolve via current namespace")
            .to_string(),
        "Foo.bar"
    );
}

#[test]
fn test_name_resolution_via_open_namespace() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let result =
        crate::name_resolution::resolve_identifier(&Name::from_string("add"), &state, &env);
    assert_eq!(
        result
            .expect("should resolve via open namespace")
            .to_string(),
        "Nat.add"
    );
}

#[test]
fn test_name_resolution_not_found() {
    let env = Environment::new();
    let state = NamespaceState::new();

    let result =
        crate::name_resolution::resolve_identifier(&Name::from_string("nonexistent"), &state, &env);
    assert!(result.is_none(), "should return None for unknown names");
}

#[test]
fn test_name_resolution_prefers_open_over_root() {
    let mut env = Environment::new();
    add_const(&mut env, "add"); // root-level add
    add_const(&mut env, "Nat.add"); // namespaced add

    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    // B03 flip: this test previously pinned the ROOT-first order ("add" won
    // over the opened `Nat.add`), which was the resolution-order bug behind
    // SILENT_WRONG p21. Lean treats a root name and an `open`ed name as one
    // ambiguous candidate bucket (`Lean/ResolveName.lean`
    // `resolveGlobalNameCore`); clean's deterministic order is
    // namespace-walk → opens → root, so the opened `Nat.add` wins here.
    let result =
        crate::name_resolution::resolve_identifier(&Name::from_string("add"), &state, &env);
    assert_eq!(
        result.expect("should find Nat.add via open").to_string(),
        "Nat.add",
        "opened-namespace match takes precedence over the root"
    );
}

#[test]
fn test_get_completions_basic() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");
    add_const(&mut env, "Int.sub");

    let mut state = NamespaceState::new();
    state.enter_namespace(Name::from_string("Nat"));

    let completions = crate::name_resolution::get_completions("a", &state, &env);
    let names: Vec<String> = completions.iter().map(|n| n.to_string()).collect();
    assert!(
        names.contains(&"Nat.add".to_string()),
        "should include Nat.add for prefix 'a' under namespace Nat"
    );
}
