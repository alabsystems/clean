// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Basic expression, lambda/pi, let binding, and declaration tests.

use super::common::{check_and_add_decl, check_expr};
use clean_kernel::{Environment, ExprKind, Name};

// =============================================================================
// Basic Expression Tests
// =============================================================================

#[test]
fn test_type_universe() {
    let env = Environment::new();
    let ty = check_expr(&env, "Type").unwrap();
    // Type : Type 1
    assert!(ty.is_sort());
}

#[test]
fn test_prop_universe() {
    let env = Environment::new();
    let ty = check_expr(&env, "Prop").unwrap();
    // Prop : Type
    assert!(ty.is_sort());
}

#[test]
fn test_arrow_type() {
    let env = Environment::new();
    let ty = check_expr(&env, "Type -> Type").unwrap();
    // (Type -> Type) : Type 2
    assert!(ty.is_sort());
}

#[test]
fn test_prop_arrow() {
    let env = Environment::new();
    let ty = check_expr(&env, "Prop -> Prop").unwrap();
    // (Prop -> Prop) : Type 1
    assert!(ty.is_sort());
}

// =============================================================================
// Lambda / Pi Type Tests
// =============================================================================

#[test]
fn test_identity_function() {
    let env = Environment::new();
    let ty = check_expr(&env, "fun (A : Type) (x : A) => x").unwrap();
    // fun (A : Type) (x : A). x : (A : Type) -> A -> A
    match ty.kind() {
        ExprKind::Pi(_, domain, codomain) => {
            // First arg is Type
            assert!(domain.is_sort());
            // Second is a Pi
            assert!(matches!(codomain.kind(), ExprKind::Pi(_, _, _)));
        }
        _ => panic!("Expected Pi type, got {ty:?}"),
    }
}

#[test]
fn test_const_function() {
    let env = Environment::new();
    let ty = check_expr(&env, "fun (A : Type) (B : Type) (x : A) (y : B) => x").unwrap();
    // fun (A B : Type) (x : A) (y : B). x : (A : Type) -> (B : Type) -> A -> B -> A
    match ty.kind() {
        ExprKind::Pi(_, _, _) => {} // OK - it's a Pi type
        _ => panic!("Expected Pi type"),
    }
}

#[test]
fn test_forall_type() {
    let env = Environment::new();
    let ty = check_expr(&env, "forall (A : Type), A -> A").unwrap();
    // (forall (A : Type), A -> A) : Type 1
    assert!(ty.is_sort());
}

#[test]
fn test_nested_lambda() {
    let env = Environment::new();
    let ty = check_expr(&env, "fun (f : Type -> Type) (x : Type) => f x").unwrap();
    // fun (f : Type -> Type) (x : Type). f x : (Type -> Type) -> Type -> Type
    match ty.kind() {
        ExprKind::Pi(_, _, _) => {}
        _ => panic!("Expected Pi type"),
    }
}

// =============================================================================
// Let Binding Tests
// =============================================================================

#[test]
fn test_let_simple() {
    let env = Environment::new();
    let ty = check_expr(&env, "let x : Type := Prop in x").unwrap();
    // let x : Type := Prop in x : Type
    // The result is Prop which has type Type 1
    assert!(ty.is_sort());
}

#[test]
fn test_let_with_function() {
    let env = Environment::new();
    // First test a simpler case
    let simple_ty = check_expr(&env, "let f : Type := Prop in f").unwrap();
    assert!(simple_ty.is_sort()); // Type of f is Type

    // Test lambda without explicit type annotation
    let lambda_ty = check_expr(&env, "fun (x : Type) => x").unwrap();
    assert!(matches!(lambda_ty.kind(), ExprKind::Pi(_, _, _)));

    // Test let with typed lambda (explicit type annotations required for now)
    let ty = check_expr(
        &env,
        "let f : Type -> Type := fun (x : Type) => x in f Prop",
    )
    .unwrap();
    // Result is Type 1 (type of f Prop where f is identity)
    assert!(ty.is_sort());
}

// =============================================================================
// Declaration Tests
// =============================================================================

#[test]
fn test_def_identity() {
    let mut env = Environment::new();
    check_and_add_decl(&mut env, "def id (A : Type) (x : A) := x").unwrap();

    // Verify the definition exists
    let const_name = Name::from_string("id");
    let _id = env.get_const(&const_name).expect("id should exist");
}

#[test]
fn test_def_const() {
    let mut env = Environment::new();
    check_and_add_decl(
        &mut env,
        "def const (A : Type) (B : Type) (x : A) (y : B) := x",
    )
    .unwrap();

    let const_name = Name::from_string("const");
    let _const_info = env.get_const(&const_name).expect("const should exist");
}

#[test]
fn test_def_compose() {
    let mut env = Environment::new();
    check_and_add_decl(
        &mut env,
        "def compose (A : Type) (B : Type) (C : Type) (f : B -> C) (g : A -> B) (x : A) := f (g x)",
    )
    .unwrap();

    let const_name = Name::from_string("compose");
    let _compose = env.get_const(&const_name).expect("compose should exist");
}

#[test]
fn test_axiom_simple() {
    let mut env = Environment::new();
    check_and_add_decl(&mut env, "axiom MyProp : Prop").unwrap();

    let const_name = Name::from_string("MyProp");
    let info = env.get_const(&const_name).unwrap();
    assert!(info.type_.is_prop());
}

#[test]
fn test_axiom_function() {
    let mut env = Environment::new();
    check_and_add_decl(&mut env, "axiom myFun (A : Type) : A -> A").unwrap();

    let const_name = Name::from_string("myFun");
    let _my_fun = env.get_const(&const_name).expect("myFun should exist");
}

// =============================================================================
// Using Defined Constants
// =============================================================================

#[test]
fn test_use_defined_constant() {
    let mut env = Environment::new();

    // Define id
    check_and_add_decl(&mut env, "def id (A : Type) (x : A) := x").unwrap();

    // Use id with a value of type Type (not Type itself which has higher universe)
    // id Prop P would work where P : Prop
    // First add a prop axiom
    check_and_add_decl(&mut env, "axiom P : Prop").unwrap();
    check_and_add_decl(&mut env, "def idProp := id Prop P").unwrap();

    let const_name = Name::from_string("idProp");
    let _id_prop = env.get_const(&const_name).expect("idProp should exist");
}

#[test]
fn test_use_multiple_constants() {
    let mut env = Environment::new();

    check_and_add_decl(&mut env, "def id (A : Type) (x : A) := x").unwrap();
    check_and_add_decl(
        &mut env,
        "def const (A : Type) (B : Type) (x : A) (y : B) := x",
    )
    .unwrap();
    check_and_add_decl(
        &mut env,
        "def flip (A : Type) (B : Type) (x : A) (y : B) := const B A y x",
    )
    .unwrap();

    let const_name = Name::from_string("flip");
    let _flip = env.get_const(&const_name).expect("flip should exist");
}

#[test]
fn test_implicit_argument_resolution() {
    let mut env = Environment::new();

    check_and_add_decl(&mut env, "axiom Nat : Type").unwrap();
    check_and_add_decl(&mut env, "axiom zero : Nat").unwrap();
    check_and_add_decl(&mut env, "def id [A : Type] (x : A) := x").unwrap();
    check_and_add_decl(&mut env, "def useId := id zero").unwrap();

    let use_id = Name::from_string("useId");
    let info = env.get_const(&use_id).expect("useId missing");
    assert!(
        matches!(info.type_.kind(), ExprKind::Const(ref n, _) if n.to_string() == "Nat"),
        "Expected type Nat, got {:?}",
        info.type_
    );
}
