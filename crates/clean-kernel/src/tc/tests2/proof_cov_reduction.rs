// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests — reduction-based type checker paths.
//!
//! Covers:
//! - `instantiate_params` — Pi telescope instantiation
//! - `lazy_delta_reduction` — height-based definition unfolding

use super::*;

// ===== instantiate_params tests =====
// instantiate_params (tc/mod.rs:3405) instantiates a Pi telescope with arguments.
// Previously had zero direct tests.

/// Test instantiate_params: basic Pi instantiation.
#[test]
fn test_instantiate_params_basic() {
    use crate::env::Declaration;

    let mut env = Environment::new();

    // Create type: (x : Type) → (y : Type) → Type
    // i.e., Π (x : Type), Π (y : Type), Type
    let double_pi = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
    );

    // We need a definition so we can construct a TypeChecker
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("T"),
        level_params: vec![],
        type_: double_pi.clone(),
    })
    .expect("env setup: add axiom T");

    let tc = TypeChecker::new(&env);

    // Instantiate first param with Prop
    let args = [Expr::prop()];
    let result = tc.instantiate_params(&double_pi, args.iter());
    // After instantiating first param: Π (y : Type), Type
    assert!(
        matches!(&result.kind, ExprKind::Pi(_, _, _)),
        "One-argument instantiation should yield a Pi, got: {result:?}"
    );

    // Instantiate both params
    let args2 = [Expr::prop(), Expr::prop()];
    let result2 = tc.instantiate_params(&double_pi, args2.iter());
    // After instantiating both: Type
    assert!(
        matches!(&result2.kind, ExprKind::Sort(_)),
        "Two-argument instantiation should yield a Sort, got: {result2:?}"
    );
}

/// Test instantiate_params: silently stops on non-Pi.
#[test]
fn test_instantiate_params_non_pi_stops() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Try to instantiate a non-Pi type (Type) with arguments
    let type_ = Expr::type_();
    let args = [Expr::prop()];
    let result = tc.instantiate_params(&type_, args.iter());

    // Should return the original type unchanged (breaks early, doesn't panic)
    assert_eq!(
        result, type_,
        "instantiate_params on non-Pi should return original expression"
    );
}

/// Test instantiate_params: more args than Pi binders.
#[test]
fn test_instantiate_params_excess_args_stops() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // (x : Type) → Type — single binder
    let single_pi = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());

    // Try with 3 arguments (only 1 binder)
    let args = [Expr::prop(), Expr::prop(), Expr::prop()];
    let result = tc.instantiate_params(&single_pi, args.iter());

    // After consuming the single Pi binder with first arg, result is Type
    // The remaining args are silently dropped
    assert!(
        matches!(&result.kind, ExprKind::Sort(_)),
        "Excess args should be dropped, yielding Sort, got: {result:?}"
    );
}

// ===== lazy_delta_reduction tests =====
// lazy_delta_reduction (tc/mod.rs:4212) implements height-based definition unfolding.
// Previously had zero direct tests.

/// Test lazy_delta_reduction: two equal definitions resolve to Ok(true).
#[test]
fn test_lazy_delta_same_def_equal() {
    use crate::env::Declaration;

    let mut env = Environment::new();

    // Define f := Prop
    env.add_decl(Declaration::Definition {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    })
    .expect("env setup: add definition f");

    let tc = TypeChecker::new(&env);

    let f1 = Expr::const_(Name::from_string("f"), vec![]);
    let f2 = Expr::const_(Name::from_string("f"), vec![]);

    // Two references to the same definition should resolve to equal
    let result = tc.lazy_delta_reduction(&f1, &f2);
    assert_eq!(
        result,
        Ok(true),
        "Same definition should be def_eq via lazy delta"
    );
}

/// Test lazy_delta_reduction: two different definitions with same value.
#[test]
fn test_lazy_delta_different_defs_same_value() {
    use crate::env::Declaration;

    let mut env = Environment::new();

    // Define f := Prop, g := Prop
    env.add_decl(Declaration::Definition {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    })
    .expect("env setup: add definition f");

    env.add_decl(Declaration::Definition {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    })
    .expect("env setup: add definition g");

    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);

    // Both unfold to Prop, should be equal
    let result = tc.lazy_delta_reduction(&f, &g);
    assert_eq!(
        result,
        Ok(true),
        "Definitions with same value should be def_eq"
    );
}

/// Test lazy_delta_reduction: non-delta expressions return Err with final forms.
#[test]
fn test_lazy_delta_non_delta_returns_err() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let prop = Expr::prop();
    let type_ = Expr::type_();

    // Neither Prop nor Type is delta-reducible
    let result = tc.lazy_delta_reduction(&prop, &type_);
    assert!(
        result.is_err(),
        "Non-delta expressions should return Err (final forms)"
    );
}

/// Test lazy_delta_reduction: one delta, one non-delta.
#[test]
fn test_lazy_delta_one_side_delta() {
    use crate::env::Declaration;

    let mut env = Environment::new();

    // Define f := Prop
    env.add_decl(Declaration::Definition {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    })
    .expect("env setup: add definition f");

    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let prop = Expr::prop();

    // f unfolds to Prop, should match Prop on the other side
    let result = tc.lazy_delta_reduction(&f, &prop);
    assert_eq!(
        result,
        Ok(true),
        "f := Prop should be def_eq to Prop via lazy delta"
    );
}
