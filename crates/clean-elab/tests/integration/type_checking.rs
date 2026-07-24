// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type checking tests: definitional equality, error cases, complex expressions,
//! prop/type distinction, and higher-order functions.

use super::common::{check_and_add_decl, check_expr};
use clean_kernel::{Environment, ExprKind, Name};

// =============================================================================
// Definitional Equality Tests
// =============================================================================

#[test]
fn test_beta_reduction_in_type_check() {
    let mut env = Environment::new();

    // Add an axiom with a specific type
    check_and_add_decl(&mut env, "axiom P : Prop").unwrap();

    // Define a function that uses beta reduction for type checking
    // The type of (fun x => x) P is definitionally equal to P
    check_and_add_decl(&mut env, "def test := (fun (x : Prop) => x) P").unwrap();

    let const_name = Name::from_string("test");
    let info = env.get_const(&const_name).unwrap();
    // The type of test should be Prop
    assert!(info.type_.is_prop());
}

// =============================================================================
// Error Cases
// =============================================================================

#[test]
fn test_unknown_identifier() {
    // Unknown identifiers should error in standalone expression context
    // Auto-implicit (#164) only applies in declaration contexts
    let env = Environment::new();
    let result = check_expr(&env, "unknownIdent");
    let err = result.unwrap_err();
    assert!(
        err.contains("Elab error"),
        "expected Elab error, got: {err}"
    );
}

#[test]
fn test_type_mismatch() {
    let mut env = Environment::new();
    check_and_add_decl(&mut env, "axiom P : Prop").unwrap();

    // Try to apply Prop to Type (Prop is not a function)
    let err = check_expr(&env, "P Type").unwrap_err();
    assert!(
        err.contains("Elab error") || err.contains("Type error"),
        "expected elaboration/type error for type mismatch, got: {err}"
    );
}

// =============================================================================
// Complex Expression Tests
// =============================================================================

#[test]
fn test_church_booleans() {
    let mut env = Environment::new();

    // Church encoding of booleans
    // Bool = forall A : Type. A -> A -> A
    // true = fun A x y. x
    // false = fun A x y. y
    check_and_add_decl(&mut env, "def CBool := forall (A : Type), A -> A -> A").unwrap();
    check_and_add_decl(
        &mut env,
        "def ctrue : CBool := fun (A : Type) (x : A) (y : A) => x",
    )
    .unwrap();
    check_and_add_decl(
        &mut env,
        "def cfalse : CBool := fun (A : Type) (x : A) (y : A) => y",
    )
    .unwrap();

    // Verify they type-check and exist in environment
    let ctrue_name = Name::from_string("ctrue");
    let cfalse_name = Name::from_string("cfalse");
    let _ctrue = env.get_const(&ctrue_name).expect("ctrue should exist");
    let _cfalse = env.get_const(&cfalse_name).expect("cfalse should exist");
}

#[test]
fn test_church_not() {
    let mut env = Environment::new();

    check_and_add_decl(&mut env, "def CBool := forall (A : Type), A -> A -> A").unwrap();
    check_and_add_decl(
        &mut env,
        "def cnot (b : CBool) : CBool := fun (A : Type) (x : A) (y : A) => b A y x",
    )
    .unwrap();

    let cnot_name = Name::from_string("cnot");
    let _cnot = env.get_const(&cnot_name).expect("cnot should exist");
}

#[test]
fn test_church_and() {
    let mut env = Environment::new();

    check_and_add_decl(&mut env, "def CBool := forall (A : Type), A -> A -> A").unwrap();
    check_and_add_decl(
        &mut env,
        "def cfalse : CBool := fun (A : Type) (x : A) (y : A) => y",
    )
    .unwrap();
    check_and_add_decl(&mut env, "def cand (a : CBool) (b : CBool) : CBool := fun (A : Type) (x : A) (y : A) => a A (b A x y) y").unwrap();

    let cand_name = Name::from_string("cand");
    let _cand = env.get_const(&cand_name).expect("cand should exist");
}

// =============================================================================
// Prop / Type Distinction Tests
// =============================================================================

#[test]
fn test_prop_impredicativity() {
    let env = Environment::new();

    // forall (P : Prop), P should be in Prop (impredicativity)
    let ty = check_expr(&env, "forall (P : Prop), P").unwrap();
    // Type is Sort(imax 0 0) = Sort 0 = Prop
    assert!(ty.is_prop());
}

#[test]
fn test_type_predicativity() {
    let env = Environment::new();

    // forall (A : Type), A should be in Type 1 (predicativity)
    let ty = check_expr(&env, "forall (A : Type), A").unwrap();
    // Type is Sort(imax 1 1) = Sort 1 = Type
    match ty.kind() {
        ExprKind::Sort(level) => {
            // Should be level 1, not level 0
            let normalized = level.normalize();
            assert!(!normalized.is_zero());
        }
        _ => panic!("Expected Sort"),
    }
}

// =============================================================================
// Higher-Order Functions
// =============================================================================

#[test]
fn test_apply() {
    let mut env = Environment::new();

    check_and_add_decl(
        &mut env,
        "def apply (A : Type) (B : Type) (f : A -> B) (x : A) := f x",
    )
    .unwrap();

    let apply_name = Name::from_string("apply");
    let _apply = env.get_const(&apply_name).expect("apply should exist");
}

#[test]
fn test_twice() {
    let mut env = Environment::new();

    check_and_add_decl(
        &mut env,
        "def twice (A : Type) (f : A -> A) (x : A) := f (f x)",
    )
    .unwrap();

    let twice_name = Name::from_string("twice");
    let _twice = env.get_const(&twice_name).expect("twice should exist");
}

#[test]
fn test_flip_function() {
    let mut env = Environment::new();

    check_and_add_decl(
        &mut env,
        "def flip (A : Type) (B : Type) (C : Type) (f : A -> B -> C) (y : B) (x : A) := f x y",
    )
    .unwrap();

    let flip_name = Name::from_string("flip");
    let _flip = env.get_const(&flip_name).expect("flip should exist");
}
