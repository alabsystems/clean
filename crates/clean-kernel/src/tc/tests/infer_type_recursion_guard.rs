// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression test for #3285: Environment::new() infinite loop in debug builds.
//!
//! The debug_assert in `infer_type` calls `infer_type` recursively to verify
//! the "type of type is Sort" invariant. Without the `in_infer_type_assert`
//! recursion guard, this creates `infer_type -> assert -> infer_type -> assert -> ...`
//! infinite recursion that manifests as a stack overflow.
//!
//! This test verifies that:
//! 1. `Environment::new()` completes without hanging (exercises add_decl -> infer_type)
//! 2. `TypeChecker::infer_type` on closed terms completes without hanging
//! 3. `Environment::with_prelude()` completes (heavier init chain)

use super::*;

/// Regression test: Environment::new() must complete in bounded time.
/// Before the fix in f0559fde7, this would stack-overflow in debug builds
/// due to infinite recursion in the infer_type debug_assert.
#[test]
fn test_env_new_completes_no_infinite_loop() {
    // This exercises add_decl -> TypeChecker::infer_type for sorry/trustedArith/trustedAy
    let env = Environment::new();
    // Verify the environment actually initialized
    assert!(
        env.get_const(&Name::from_string("sorry")).is_some(),
        "Environment::new() should register sorry axiom"
    );
    assert!(
        env.get_const(&Name::from_string("trustedArith")).is_some(),
        "Environment::new() should register trustedArith axiom"
    );
    assert!(
        env.get_const(&Name::from_string("trustedAy")).is_some(),
        "Environment::new() should register trustedAy axiom"
    );
}

/// Regression test: infer_type on closed terms must not infinitely recurse.
/// The debug_assert calls infer_type(type) to verify type-of-type is Sort.
/// Without the recursion guard, this is unbounded recursion.
#[test]
fn test_infer_type_closed_term_no_infinite_recursion() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Prop is a closed term — its type is Type 1, whose type is Type 2, etc.
    // The debug_assert should recurse once and then the guard prevents further recursion.
    let prop = Expr::prop();
    let ty = tc
        .infer_type(&prop)
        .expect("infer_type(Prop) should succeed");
    assert!(
        matches!(ty.kind(), ExprKind::Sort(_)),
        "type of Prop should be a Sort"
    );

    // Sort(1) is also closed — triggers the same path
    let type1 = Expr::sort(Level::succ(Level::zero()));
    let ty2 = tc
        .infer_type(&type1)
        .expect("infer_type(Type 1) should succeed");
    assert!(
        matches!(ty2.kind(), ExprKind::Sort(_)),
        "type of Type 1 should be a Sort"
    );
}

/// Regression test: add_decl with a definition value exercises the full
/// infer_type path including the debug_assert recursion guard.
#[test]
fn test_add_decl_exercises_infer_type_guard() {
    use crate::env::Declaration;

    let mut env = Environment::new();

    // Add a simple definition: `myConst : Prop := Prop`
    // This triggers infer_type on both the type and value during type checking.
    let decl = Declaration::Definition {
        name: Name::from_string("myConst"),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())), // Type 0
        value: Expr::prop(),                           // Prop : Type 0
        is_reducible: true,
    };

    env.add_decl(decl)
        .expect("add_decl should succeed without infinite recursion");
    assert!(
        env.get_const(&Name::from_string("myConst")).is_some(),
        "myConst should be registered after add_decl"
    );
}
