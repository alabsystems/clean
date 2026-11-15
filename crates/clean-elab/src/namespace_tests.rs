// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::Environment;
use clean_parser::{OpenPath, SurfaceName};
/// Helper: add a constant to the environment for testing.
fn add_const(env: &mut Environment, name: &'static str) {
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
        path: SurfaceName::from_name(Name::anon().str("Nat")),
        names: vec![],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path], &mut state).unwrap();

    assert_eq!(
        state.resolve(&Name::from_string("add")).unwrap().clone(),
        Name::from_string("Nat.add")
    );
    assert_eq!(
        state.resolve(&Name::from_string("mul")).unwrap().clone(),
        Name::from_string("Nat.mul")
    );
    assert_eq!(
        state.resolve(&Name::from_string("zero")).unwrap().clone(),
        Name::from_string("Nat.zero")
    );
    assert!(state.resolve(&Name::from_string("nonexistent")).is_none());
}

#[test]
fn test_open_selective() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");
    add_const(&mut env, "Nat.zero");

    let mut state = NamespaceState::new();
    let path = OpenPath {
        path: SurfaceName::from_name(Name::anon().str("Nat")),
        names: vec![
            SurfaceName::generated_path("add"),
            SurfaceName::generated_path("zero"),
        ],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path], &mut state).unwrap();

    assert!(state.resolve(&Name::from_string("add")).is_some());
    assert!(state.resolve(&Name::from_string("zero")).is_some());
    assert!(state.resolve(&Name::from_string("mul")).is_none());
}

#[test]
fn test_open_hiding() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");
    add_const(&mut env, "Nat.zero");

    let mut state = NamespaceState::new();
    let path = OpenPath {
        path: SurfaceName::from_name(Name::anon().str("Nat")),
        names: vec![],
        hiding: vec![SurfaceName::generated_path("mul")],
        renaming: vec![],
    };
    process_open(&env, &[path], &mut state).unwrap();

    assert!(state.resolve(&Name::from_string("add")).is_some());
    assert!(state.resolve(&Name::from_string("zero")).is_some());
    assert!(state.resolve(&Name::from_string("mul")).is_none());
}

#[test]
fn test_open_renaming() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let mut state = NamespaceState::new();
    let path = OpenPath {
        path: SurfaceName::from_name(Name::anon().str("Nat")),
        names: vec![],
        hiding: vec![],
        renaming: vec![clean_parser::surface::OpenRename {
            from: SurfaceName::generated_path("add"),
            to: SurfaceName::generated_path("plus"),
        }],
    };
    process_open(&env, &[path], &mut state).unwrap();

    // "add" should be renamed to "plus"
    assert_eq!(
        state.resolve(&Name::from_string("plus")).unwrap().clone(),
        Name::from_string("Nat.add")
    );
    // original short name "add" is no longer available
    assert!(state.resolve(&Name::from_string("add")).is_none());
    // B13 flip: `open Nat renaming add → plus` imports ONLY the renamed pairs
    // (Lean `elabOpenRenaming` adds one `OpenDecl.explicit` per pair and
    // nothing else — `Lean/Elab/BuiltinCommand.lean`). This test previously
    // pinned the divergent full-open-with-renames behavior (`mul` visible),
    // which silently over-imported.
    assert!(state.resolve(&Name::from_string("mul")).is_none());
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
        path: SurfaceName::from_name(Name::anon().str("Foo").str("Bar")),
        names: vec![],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path], &mut state).unwrap();

    assert!(state.resolve(&Name::from_string("baz")).is_some());
    assert!(state.resolve(&Name::from_string("qux")).is_some());
    // Nested names are NOT imported (only direct children)
    assert!(state.resolve(&Name::from_string("deep")).is_none());
    assert!(state.resolve(&Name::from_string("Inner.deep")).is_none());
}

#[test]
fn test_scoped_open_push_pop() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let mut state = NamespaceState::new();

    // Open Nat at file level
    let path_nat = OpenPath {
        path: SurfaceName::from_name(Name::anon().str("Nat")),
        names: vec![SurfaceName::generated_path("add")],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path_nat], &mut state).unwrap();
    assert!(state.resolve(&Name::from_string("add")).is_some());
    assert!(state.resolve(&Name::from_string("mul")).is_none());

    // Push scope and open more
    state.push_scope();
    let path_mul = OpenPath {
        path: SurfaceName::from_name(Name::anon().str("Nat")),
        names: vec![SurfaceName::generated_path("mul")],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path_mul], &mut state).unwrap();
    assert!(state.resolve(&Name::from_string("add")).is_some());
    assert!(state.resolve(&Name::from_string("mul")).is_some());

    // Pop scope: mul should be gone, add should remain
    state.pop_scope();
    assert!(state.resolve(&Name::from_string("add")).is_some());
    assert!(state.resolve(&Name::from_string("mul")).is_none());
}

#[test]
fn test_scoped_open_overwrite_restore() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Int.add");

    let mut state = NamespaceState::new();

    // Open Nat.add as "add"
    let path_nat = OpenPath {
        path: SurfaceName::from_name(Name::anon().str("Nat")),
        names: vec![SurfaceName::generated_path("add")],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path_nat], &mut state).unwrap();
    assert_eq!(
        state.resolve(&Name::from_string("add")).unwrap().clone(),
        Name::from_string("Nat.add")
    );

    // Push scope and shadow with Int.add
    state.push_scope();
    let path_int = OpenPath {
        path: SurfaceName::from_name(Name::anon().str("Int")),
        names: vec![SurfaceName::generated_path("add")],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[path_int], &mut state).unwrap();
    assert_eq!(
        state.resolve(&Name::from_string("add")).unwrap().clone(),
        Name::from_string("Int.add")
    );

    // Pop: should restore Nat.add
    state.pop_scope();
    assert_eq!(
        state.resolve(&Name::from_string("add")).unwrap().clone(),
        Name::from_string("Nat.add")
    );
}

#[test]
fn test_export_basic() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let mut state = NamespaceState::new();
    process_export(
        &env,
        &SurfaceName::component("Nat", false),
        &[
            SurfaceName::generated_path("add"),
            SurfaceName::generated_path("mul"),
        ],
        Some(&SurfaceName::generated_path("MyLib")),
        &mut state,
    )
    .unwrap();

    // B13 flip: the aliases live in the CURRENT namespace (Lean `elabExport`:
    // `addAlias (currNamespace ++ id)`), so inside `MyLib` they are registered
    // as `MyLib.add`/`MyLib.mul` — visible bare only from within `MyLib` (via
    // the outward walk in `elab_ident`), and as `MyLib.add` from anywhere. The
    // old behavior leaked the bare short names file-wide regardless of the
    // declaring namespace.
    assert!(state.resolve(&Name::from_string("add")).is_none());
    assert_eq!(
        state
            .resolve(&Name::from_string("MyLib.add"))
            .unwrap()
            .clone(),
        Name::from_string("Nat.add")
    );
    assert_eq!(
        state
            .resolve(&Name::from_string("MyLib.mul"))
            .unwrap()
            .clone(),
        Name::from_string("Nat.mul")
    );

    // Check export records
    assert_eq!(state.exports().len(), 2);
    assert_eq!(state.exports()[0].short, Name::from_string("MyLib.add"));
    assert_eq!(
        state.exports()[0].target.clone(),
        Name::from_string("Nat.add")
    );
}

#[test]
fn test_export_root_level() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let mut state = NamespaceState::new();
    process_export(
        &env,
        &SurfaceName::component("Nat", false),
        &[SurfaceName::generated_path("add")],
        None,
        &mut state,
    )
    .unwrap();

    assert_eq!(state.exports()[0].short, Name::from_string("add"));
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
        &SurfaceName::component("Nat", false),
        &[SurfaceName::generated_path("nonexistent")],
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
        path: SurfaceName::from_name(Name::anon().str("NonExistent")),
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
            path: SurfaceName::from_name(Name::anon().str("Nat")),
            names: vec![],
            hiding: vec![],
            renaming: vec![],
        },
        OpenPath {
            path: SurfaceName::from_name(Name::anon().str("Int")),
            names: vec![],
            hiding: vec![],
            renaming: vec![],
        },
    ];
    process_open(&env, &paths, &mut state).unwrap();

    assert!(state.resolve(&Name::from_string("add")).is_some());
    assert!(state.resolve(&Name::from_string("sub")).is_some());
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
        path: SurfaceName::from_name(Name::anon().str("Nat")),
        names: vec![SurfaceName::generated_path("add")],
        hiding: vec![],
        renaming: vec![clean_parser::surface::OpenRename {
            from: SurfaceName::generated_path("add"),
            to: SurfaceName::generated_path("natAdd"),
        }],
    };
    process_open(&env, &[path], &mut state).unwrap();

    assert_eq!(
        state.resolve(&Name::from_string("natAdd")).unwrap().clone(),
        Name::from_string("Nat.add")
    );
    assert!(state.resolve(&Name::from_string("add")).is_none());
    assert!(state.resolve(&Name::from_string("mul")).is_none());
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
    assert_eq!(state.current_namespace().clone(), Name::from_string("Foo"));

    state.enter_namespace(Name::from_string("Bar"));
    assert_eq!(
        state.current_namespace().clone(),
        Name::from_string("Foo.Bar")
    );

    state.exit_namespace();
    assert_eq!(state.current_namespace().clone(), Name::from_string("Foo"));

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
    assert_eq!(
        state.current_namespace().clone(),
        Name::from_string("A.B.C")
    );

    state.exit_namespace();
    assert_eq!(state.current_namespace().clone(), Name::from_string("A.B"));

    state.exit_namespace();
    assert_eq!(state.current_namespace().clone(), Name::from_string("A"));

    state.exit_namespace();
    assert!(state.current_namespace().is_anon());
}

/// `namespace Alpha.Beta` / `end Alpha.Beta` closes BOTH components.
///
/// Ground truth, Lean 4.30.0-rc2 (`set_option pp.parens true`): after
/// `namespace Alpha.Beta … end Alpha.Beta`, a following `namespace Gamma`
/// registers `Gamma.g_inside`. `#check @Alpha.Gamma.g_inside` there is
/// `Unknown identifier`. Popping one component left `Alpha` open and minted
/// `Alpha.Gamma.g_inside` instead — a name no importing module can address.
#[test]
fn test_exit_namespace_dotted_entry_pops_every_component() {
    let mut state = NamespaceState::new();

    state.enter_namespace(Name::from_string("Alpha.Beta"));
    assert_eq!(state.current_namespace().to_string(), "Alpha.Beta");

    state.exit_namespace();
    assert!(
        state.current_namespace().is_anon(),
        "`end Alpha.Beta` closes both components, so the prefix returns to the \
         root; leaving `{}` open is the namespace-pop defect",
        state.current_namespace()
    );

    // The observable consequence: the NEXT namespace must not inherit a leak.
    state.enter_namespace(Name::from_string("Gamma"));
    assert_eq!(
        state.current_namespace().to_string(),
        "Gamma",
        "a sibling namespace after a dotted `end` must not be prefixed"
    );
}

/// The same, three components deep and nested under an outer namespace, so a
/// fix that special-cases "two components" or "at the root" does not pass.
#[test]
fn test_exit_namespace_dotted_entry_restores_outer_prefix() {
    let mut state = NamespaceState::new();

    state.enter_namespace(Name::from_string("Outer"));
    state.enter_namespace(Name::from_string("A.B.C"));
    assert_eq!(state.current_namespace().to_string(), "Outer.A.B.C");

    state.exit_namespace();
    assert_eq!(
        state.current_namespace().to_string(),
        "Outer",
        "exiting a 3-component entry restores the prefix that preceded it"
    );

    state.exit_namespace();
    assert!(state.current_namespace().is_anon());
}

/// Enter/exit are inverse for every shape, mixed and interleaved. This is the
/// property the fix actually establishes; the two cases above are its
/// Lean-pinned witnesses.
#[test]
fn test_enter_exit_namespace_are_inverse_for_mixed_shapes() {
    for entries in [
        vec!["Foo"],
        vec!["Alpha.Beta"],
        vec!["A.B.C.D"],
        vec!["Foo", "Alpha.Beta"],
        vec!["Alpha.Beta", "Foo"],
        vec!["Mathlib.Tactic.GCongr", "LE.le", "LT.lt"],
    ] {
        let mut state = NamespaceState::new();
        let mut expected = Vec::new();
        for entry in &entries {
            expected.push(state.current_namespace().to_string());
            state.enter_namespace(Name::from_string(entry));
        }
        for before in expected.iter().rev() {
            state.exit_namespace();
            assert_eq!(
                &state.current_namespace().to_string(),
                before,
                "exit must restore the prefix its matching enter saw, for {entries:?}"
            );
        }
        assert!(
            state.current_namespace().is_anon(),
            "balanced enter/exit over {entries:?} must return to the root, not `{}`",
            state.current_namespace()
        );
    }
}

/// `module_batch::exec::set_current_namespace` drains with
/// `while !is_anon() { exit_namespace() }` on a state it did NOT enter. That
/// loop must terminate and land at the root, so `exit_namespace` keeps a
/// one-component fallback when no frame was recorded.
#[test]
fn test_exit_namespace_drains_an_unframed_prefix_to_the_root() {
    let mut state = NamespaceState::new();
    // Build a prefix, then discard the frames the way a section restore does,
    // leaving a namespace with no matching enter frames.
    state.enter_namespace(Name::from_string("A.B.C"));
    state.enter_section(None);
    state.enter_namespace(Name::from_string("D"));
    state.exit_section().expect("section is active");
    assert_eq!(state.current_namespace().to_string(), "A.B.C");

    let mut steps = 0;
    while !state.current_namespace().is_anon() {
        state.exit_namespace();
        steps += 1;
        assert!(steps <= 8, "drain loop must terminate");
    }
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
    assert_eq!(vars[0].name.clone(), Name::from_string("x"));
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
    assert_eq!(
        state.current_namespace().clone(),
        Name::from_string("Foo.Bar")
    );

    state.exit_section().expect("should exit section");
    assert_eq!(
        state.current_namespace().clone(),
        Name::from_string("Foo"),
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
    assert_eq!(state.open_namespaces()[0].clone(), Name::from_string("Nat"));
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
    assert_eq!(vars[0].name.clone(), Name::from_string("n"));

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
    assert_eq!(
        vars[0].name.clone(),
        Name::from_string("a"),
        "outer variable first"
    );
    assert_eq!(
        vars[1].name.clone(),
        Name::from_string("b"),
        "inner variable second"
    );

    state.exit_section().expect("exit inner section");
    let vars = state.get_section_variables();
    assert_eq!(
        vars.len(),
        1,
        "only outer variable remains after inner exit"
    );
    assert_eq!(vars[0].name.clone(), Name::from_string("a"));

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
    assert_eq!(state.open_namespaces()[0].clone(), Name::from_string("Nat"));

    // Opening same namespace again should not duplicate
    state.open_namespace(Name::from_string("Nat"));
    assert_eq!(state.open_namespaces().len(), 1);

    state.open_namespace(Name::from_string("Int"));
    assert_eq!(state.open_namespaces().len(), 2);

    state.close_namespace(&Name::from_string("Nat"));
    assert_eq!(state.open_namespaces().len(), 1);
    assert_eq!(state.open_namespaces()[0].clone(), Name::from_string("Int"));
}

// =========================================================================
// resolve_name tests
// =========================================================================

#[test]
fn test_resolve_name_with_namespace() {
    let mut state = NamespaceState::new();
    state.enter_namespace(Name::from_string("Foo"));

    let resolved = state.resolve_name(&Name::from_string("bar"));
    assert_eq!(resolved.clone(), Name::from_string("Foo.bar"));
}

#[test]
fn test_resolve_name_at_root() {
    let state = NamespaceState::new();
    let resolved = state.resolve_name(&Name::from_string("bar"));
    assert_eq!(
        resolved.clone(),
        Name::from_string("bar"),
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
    let result = crate::name_resolution::resolve_identifier(
        &SurfaceName::generated_path("Nat.add"),
        &state,
        &env,
    );
    assert_eq!(
        result.expect("should resolve fully-qualified name").clone(),
        Name::from_string("Nat.add")
    );
}

#[test]
fn test_name_resolution_via_current_namespace() {
    let mut env = Environment::new();
    add_const(&mut env, "Foo.bar");

    let mut state = NamespaceState::new();
    state.enter_namespace(Name::from_string("Foo"));

    let result = crate::name_resolution::resolve_identifier(
        &SurfaceName::generated_path("bar"),
        &state,
        &env,
    );
    assert_eq!(
        result
            .expect("should resolve via current namespace")
            .clone(),
        Name::from_string("Foo.bar")
    );
}

#[test]
fn test_name_resolution_via_open_namespace() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let result = crate::name_resolution::resolve_identifier(
        &SurfaceName::generated_path("add"),
        &state,
        &env,
    );
    assert_eq!(
        result.expect("should resolve via open namespace").clone(),
        Name::from_string("Nat.add")
    );
}

#[test]
fn test_name_resolution_not_found() {
    let env = Environment::new();
    let state = NamespaceState::new();

    let result = crate::name_resolution::resolve_identifier(
        &SurfaceName::generated_path("nonexistent"),
        &state,
        &env,
    );
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
    let result = crate::name_resolution::resolve_identifier(
        &SurfaceName::generated_path("add"),
        &state,
        &env,
    );
    assert_eq!(
        result.expect("should find Nat.add via open").clone(),
        Name::from_string("Nat.add"),
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
    let names: Vec<Name> = completions.to_vec();
    assert!(
        names.contains(&Name::from_string("Nat.add")),
        "should include Nat.add for prefix 'a' under namespace Nat"
    );
}

#[test]
fn test_explicit_open_prefix_rule() {
    // Lean's `resolveOpenDecls` (`Lean/ResolveName.lean`): an
    // `OpenDecl.explicit openedId resolvedId` also resolves a name that
    // `openedId` is a proper PREFIX of, as `id.replacePrefix openedId
    // resolvedId` (lean4 `tests/elab/explicitOpenDeclIssue.lean`).
    let mut env = Environment::new();
    add_const(&mut env, "Foo.Bar");
    add_const(&mut env, "Foo.Bar.a");
    add_const(&mut env, "Foo.Baz");
    let foo = || SurfaceName::from_name(Name::anon().str("Foo"));
    let bar_a = || SurfaceName::from_name(Name::from_string("Bar.a"));

    let mut state = NamespaceState::new();
    state.push_scope();
    let explicit = OpenPath {
        path: foo(),
        names: vec![SurfaceName::generated_path("Bar")],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[explicit], &mut state).unwrap();
    assert_eq!(
        state.explicit_open_prefix_targets(&Name::from_string("Bar.a")),
        vec![Name::from_string("Foo.Bar.a")]
    );
    // The exact spelling is the alias table's; another name, or a TEXT
    // prefix that is not a structural one, is not the rule's.
    assert!(state
        .explicit_open_prefix_targets(&Name::from_string("Bar"))
        .is_empty());
    assert!(state
        .explicit_open_prefix_targets(&Name::from_string("Baz.a"))
        .is_empty());
    assert!(state
        .explicit_open_prefix_targets(&Name::from_string("BarX.a"))
        .is_empty());
    assert_eq!(
        crate::name_resolution::resolve_identifier(&bar_a(), &state, &env),
        Some(Name::from_string("Foo.Bar.a")),
        "the tactic resolver reads the explicit open's prefix"
    );
    state.pop_scope();
    // Gone with the scope that opened it.
    assert!(state
        .explicit_open_prefix_targets(&Name::from_string("Bar.a"))
        .is_empty());
    assert_eq!(
        crate::name_resolution::resolve_identifier(&bar_a(), &state, &env),
        None
    );

    // `open Foo renaming Bar → Qux` is one `OpenDecl.explicit Qux Foo.Bar`.
    let renaming = OpenPath {
        path: foo(),
        names: vec![],
        hiding: vec![],
        renaming: vec![clean_parser::surface::OpenRename {
            from: SurfaceName::generated_path("Bar"),
            to: SurfaceName::generated_path("Qux"),
        }],
    };
    process_open(&env, &[renaming], &mut state).unwrap();
    assert_eq!(
        state.explicit_open_prefix_targets(&Name::from_string("Qux.a")),
        vec![Name::from_string("Foo.Bar.a")]
    );
    assert!(state
        .explicit_open_prefix_targets(&Name::from_string("Bar.a"))
        .is_empty());

    // A simple `open Foo` records no explicit open: its members are reached
    // by the open-namespace walk, which already gives `Bar.a` as `Foo.Bar.a`.
    let mut simple_state = NamespaceState::new();
    let simple = OpenPath {
        path: foo(),
        names: vec![],
        hiding: vec![],
        renaming: vec![],
    };
    process_open(&env, &[simple], &mut simple_state).unwrap();
    assert!(simple_state
        .explicit_open_prefix_targets(&Name::from_string("Bar.a"))
        .is_empty());
}
