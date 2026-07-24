// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for declaration modifier propagation (private, protected, noncomputable,
//! partial, unsafe) through the parse -> elaborate -> register -> kernel pipeline.

use super::*;
use crate::register::register_elab_result;

/// Helper: parse, elaborate, and register a declaration, returning the env.
///
/// Initializes the kernel `Nat` environment so test fixtures of shape
/// `def x : Nat := 0` can typecheck. (Earlier this helper started with
/// `Environment::new()` and tests used `: Type := Type`, which the
/// elaborator now auto-binds as `def x.{u} : Type u+1 := Type u` and
/// the simpler `def x : Type := Type` no longer typechecks under the
/// universe-promotion rule.)
fn elab_and_register(input: &str) -> (Environment, ElabResult) {
    let mut env = Environment::new();
    env.init_nat().expect("Nat init should succeed");
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    let surface = parse_decl_with_tactics(input, &patterns).expect("parse should succeed");
    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elab_decl(&surface).expect("elab should succeed");
    register_elab_result(&mut env, &result).expect("registration should succeed");
    (env, result)
}

/// Helper: parse and elaborate a declaration (without registering).
fn elab_decl_result(input: &str) -> ElabResult {
    let mut env = Environment::new();
    env.init_nat().expect("Nat init should succeed");
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    let surface = parse_decl_with_tactics(input, &patterns).expect("parse should succeed");
    let mut ctx = ElabCtx::new(&env);
    ctx.elab_decl(&surface).expect("elab should succeed")
}

// ============================================================================
// Modifier storage: verify modifiers round-trip through parse -> elab -> register
// ============================================================================

#[test]
fn test_modifier_private_stored_in_env() {
    let (env, _) = elab_and_register("private def helper : Nat := 0");
    let name = Name::from_string("helper");
    assert!(
        env.is_private(&name),
        "private def should be marked private in environment"
    );
    assert!(
        !env.is_protected(&name),
        "private def should not be marked protected"
    );
}

#[test]
fn test_modifier_protected_stored_in_env() {
    let (env, _) = elab_and_register("protected def helper : Nat := 0");
    let name = Name::from_string("helper");
    assert!(
        env.is_protected(&name),
        "protected def should be marked protected in environment"
    );
    assert!(
        !env.is_private(&name),
        "protected def should not be marked private"
    );
}

#[test]
fn test_modifier_noncomputable_stored_in_env() {
    let (env, _) = elab_and_register("noncomputable def ncomp : Nat := 0");
    let name = Name::from_string("ncomp");
    assert!(
        env.is_noncomputable(&name),
        "noncomputable def should be marked noncomputable in environment"
    );
}

#[test]
fn test_modifier_partial_stored_in_env() {
    let (env, _) = elab_and_register("partial def loop : Nat := 0");
    let name = Name::from_string("loop");
    assert!(
        env.is_partial(&name),
        "partial def should be marked partial in environment"
    );
}

#[test]
fn test_modifier_unsafe_stored_in_env() {
    let (env, _) = elab_and_register("unsafe def danger : Nat := 0");
    let name = Name::from_string("danger");
    assert!(
        env.is_unsafe(&name),
        "unsafe def should be marked unsafe in environment"
    );
}

#[test]
fn test_modifier_default_not_stored() {
    let (env, _) = elab_and_register("def plain : Nat := 0");
    let name = Name::from_string("plain");
    assert!(!env.is_private(&name));
    assert!(!env.is_protected(&name));
    assert!(!env.is_noncomputable(&name));
    assert!(!env.is_partial(&name));
    assert!(!env.is_unsafe(&name));
}

#[test]
fn test_modifier_combination_private_noncomputable() {
    let (env, _) = elab_and_register("private noncomputable def secret : Nat := 0");
    let name = Name::from_string("secret");
    assert!(env.is_private(&name), "should be private");
    assert!(env.is_noncomputable(&name), "should be noncomputable");
    assert!(!env.is_partial(&name));
    assert!(!env.is_unsafe(&name));
}

// ============================================================================
// Modifier in ElabResult: verify modifiers are carried through elaboration
// ============================================================================

#[test]
fn test_elab_result_carries_private_modifier() {
    let result = elab_decl_result("private def x : Nat := 0");
    match &result {
        ElabResult::Definition { modifiers, .. } => {
            assert_eq!(
                modifiers.visibility,
                clean_parser::Visibility::Private,
                "ElabResult should carry Private visibility"
            );
        }
        other => panic!("expected Definition, got: {other:?}"),
    }
}

#[test]
fn test_elab_result_carries_noncomputable_modifier() {
    let result = elab_decl_result("noncomputable def nc : Nat := 0");
    match &result {
        ElabResult::Definition { modifiers, .. } => {
            assert!(
                modifiers.is_noncomputable,
                "ElabResult should carry is_noncomputable flag"
            );
        }
        other => panic!("expected Definition, got: {other:?}"),
    }
}

#[test]
fn test_elab_result_carries_partial_modifier() {
    let result = elab_decl_result("partial def p : Nat := 0");
    match &result {
        ElabResult::Definition { modifiers, .. } => {
            assert!(
                modifiers.is_partial,
                "ElabResult should carry is_partial flag"
            );
        }
        other => panic!("expected Definition, got: {other:?}"),
    }
}

#[test]
fn test_elab_result_carries_unsafe_modifier() {
    let result = elab_decl_result("unsafe def u : Nat := 0");
    match &result {
        ElabResult::Definition { modifiers, .. } => {
            assert!(
                modifiers.is_unsafe,
                "ElabResult should carry is_unsafe flag"
            );
        }
        other => panic!("expected Definition, got: {other:?}"),
    }
}

#[test]
fn test_elab_result_default_modifiers() {
    let result = elab_decl_result("def d : Nat := 0");
    match &result {
        ElabResult::Definition { modifiers, .. } => {
            assert!(
                modifiers.is_default(),
                "ElabResult modifiers should be default for unmodified def"
            );
        }
        other => panic!("expected Definition, got: {other:?}"),
    }
}

// ============================================================================
// Theorem and Axiom modifier propagation
// ============================================================================

#[test]
fn test_theorem_carries_private_modifier() {
    let result = elab_decl_result("private theorem t : Nat := 0");
    match &result {
        ElabResult::Theorem { modifiers, .. } => {
            assert_eq!(
                modifiers.visibility,
                clean_parser::Visibility::Private,
                "Theorem should carry Private visibility"
            );
        }
        other => panic!("expected Theorem, got: {other:?}"),
    }
}

#[test]
fn test_axiom_carries_protected_modifier() {
    let result = elab_decl_result("protected axiom ax : Type");
    match &result {
        ElabResult::Axiom { modifiers, .. } => {
            assert_eq!(
                modifiers.visibility,
                clean_parser::Visibility::Protected,
                "Axiom should carry Protected visibility"
            );
        }
        other => panic!("expected Axiom, got: {other:?}"),
    }
}

// ============================================================================
// Private visibility enforcement in name resolution
// ============================================================================

#[test]
fn test_private_def_visible_in_same_namespace() {
    // Register a private definition in namespace "Foo"
    let mut env = Environment::new();
    let name = Name::from_string("Foo.helper");
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.mark_private(name.clone());

    // Elaborate inside namespace "Foo" — should find it
    let mut ctx = ElabCtx::new(&env);
    ctx.namespace_prefix = "Foo".to_owned();
    let surface = parse_expr("Foo.helper")
        .map_err(|e| ElabError::ParseError(e.to_string()))
        .unwrap();
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "private Foo.helper should be visible inside namespace Foo, got: {result:?}"
    );
}

#[test]
fn test_private_def_not_visible_outside_namespace() {
    // Register a private definition in namespace "Foo"
    let mut env = Environment::new();
    let name = Name::from_string("Foo.helper");
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.mark_private(name.clone());

    // Elaborate at root namespace — should NOT find it
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("Foo.helper")
        .map_err(|e| ElabError::ParseError(e.to_string()))
        .unwrap();
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "private Foo.helper should NOT be visible from root namespace"
    );
}

#[test]
fn test_private_def_visible_in_child_namespace() {
    // Register a private definition in namespace "Foo"
    let mut env = Environment::new();
    let name = Name::from_string("Foo.helper");
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.mark_private(name.clone());

    // Elaborate inside namespace "Foo.Bar" (child of Foo) — should find it
    let mut ctx = ElabCtx::new(&env);
    ctx.namespace_prefix = "Foo.Bar".to_owned();
    let surface = parse_expr("Foo.helper")
        .map_err(|e| ElabError::ParseError(e.to_string()))
        .unwrap();
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "private Foo.helper should be visible inside child namespace Foo.Bar, got: {result:?}"
    );
}

#[test]
fn test_private_def_not_visible_from_sibling_namespace() {
    // Register a private definition in namespace "Foo"
    let mut env = Environment::new();
    let name = Name::from_string("Foo.helper");
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.mark_private(name.clone());

    // Elaborate inside namespace "Bar" — should NOT find it
    let mut ctx = ElabCtx::new(&env);
    ctx.namespace_prefix = "Bar".to_owned();
    let surface = parse_expr("Foo.helper")
        .map_err(|e| ElabError::ParseError(e.to_string()))
        .unwrap();
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "private Foo.helper should NOT be visible from sibling namespace Bar"
    );
}

#[test]
fn test_public_def_always_visible() {
    // Register a public definition
    let mut env = Environment::new();
    let name = Name::from_string("Foo.pub_helper");
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    // Not marked private or protected — default is public.

    // Should be visible from root
    let result = elab_with_env(&env, "Foo.pub_helper");
    assert!(
        result.is_ok(),
        "public Foo.pub_helper should be visible from root, got: {result:?}"
    );
}

// ============================================================================
// Inductive modifier propagation
// ============================================================================

#[test]
fn test_inductive_carries_private_modifier() {
    let result = elab_decl_result("private inductive MyBool where\n  | true\n  | false");
    match &result {
        ElabResult::Inductive { modifiers, .. } => {
            assert_eq!(
                modifiers.visibility,
                clean_parser::Visibility::Private,
                "Inductive should carry Private visibility"
            );
        }
        other => panic!("expected Inductive, got: {other:?}"),
    }
}

#[test]
fn test_inductive_default_modifiers() {
    let result = elab_decl_result("inductive MyUnit where\n  | unit");
    match &result {
        ElabResult::Inductive { modifiers, .. } => {
            assert!(
                modifiers.is_default(),
                "Unmodified inductive should have default modifiers"
            );
        }
        other => panic!("expected Inductive, got: {other:?}"),
    }
}

#[test]
fn test_inductive_private_stored_in_env() {
    let (env, _) = elab_and_register("private inductive MyBit where\n  | zero\n  | one");
    let name = Name::from_string("MyBit");
    assert!(
        env.is_private(&name),
        "private inductive should be marked private in environment"
    );
}

#[test]
fn test_inductive_protected_stored_in_env() {
    let (env, _) = elab_and_register("protected inductive MyPBit where\n  | zero\n  | one");
    let name = Name::from_string("MyPBit");
    assert!(
        env.is_protected(&name),
        "protected inductive should be marked protected in environment"
    );
}

// ============================================================================
// Structure modifier propagation
// ============================================================================

#[test]
fn test_structure_carries_private_modifier() {
    let result = elab_decl_result("private structure MyPair where\n  fst : Type\n  snd : Type");
    match &result {
        ElabResult::Structure { modifiers, .. } => {
            assert_eq!(
                modifiers.visibility,
                clean_parser::Visibility::Private,
                "Structure should carry Private visibility"
            );
        }
        other => panic!("expected Structure, got: {other:?}"),
    }
}

#[test]
fn test_structure_default_modifiers() {
    let result = elab_decl_result("structure MyPoint where\n  x : Type\n  y : Type");
    match &result {
        ElabResult::Structure { modifiers, .. } => {
            assert!(
                modifiers.is_default(),
                "Unmodified structure should have default modifiers"
            );
        }
        other => panic!("expected Structure, got: {other:?}"),
    }
}

#[test]
fn test_structure_private_stored_in_env() {
    let (env, _) = elab_and_register("private structure MySPair where\n  fst : Type\n  snd : Type");
    let name = Name::from_string("MySPair");
    assert!(
        env.is_private(&name),
        "private structure should be marked private in environment"
    );
}

#[test]
fn test_structure_protected_stored_in_env() {
    let (env, _) =
        elab_and_register("protected structure MyProtPair where\n  fst : Type\n  snd : Type");
    let name = Name::from_string("MyProtPair");
    assert!(
        env.is_protected(&name),
        "protected structure should be marked protected in environment"
    );
}

// ============================================================================
// Class modifier propagation
// ============================================================================

#[test]
fn test_class_carries_private_modifier() {
    let result = elab_decl_result("private class MyClass (α : Type) where\n  op : α");
    match &result {
        ElabResult::Structure { modifiers, .. } => {
            assert_eq!(
                modifiers.visibility,
                clean_parser::Visibility::Private,
                "Class should carry Private visibility (elaborated as Structure)"
            );
        }
        other => panic!("expected Structure (from class), got: {other:?}"),
    }
}

#[test]
fn test_class_default_modifiers() {
    let result = elab_decl_result("class MyPubClass (α : Type) where\n  op : α");
    match &result {
        ElabResult::Structure { modifiers, .. } => {
            assert!(
                modifiers.is_default(),
                "Unmodified class should have default modifiers"
            );
        }
        other => panic!("expected Structure (from class), got: {other:?}"),
    }
}
