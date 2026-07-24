// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Implicit argument insertion and type ascription tests

use super::*;
use clean_kernel::env::TrustedEnvExt;

// ==== Helper environments ====

/// Create environment with a function that has implicit arguments
fn env_with_implicit_id() -> Environment {
    let mut env = Environment::new();

    // Add id : {A : Type} → A → A
    let id_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(), // A : Type
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // x : A
            Expr::bvar(1), // A
        ),
    );
    let id_value = Expr::lam(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("id"),
        level_params: vec![],
        type_: id_type,
        value: id_value,
        is_reducible: true,
    })
    .unwrap();

    // Add a simple type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add a value of that type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("zero"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    env
}

// ==== Implicit insertion tests ====

#[test]
fn test_implicit_insertion_basic() {
    // Test: id zero should elaborate to id Nat zero
    // where the implicit type argument is resolved via unification
    let env = env_with_implicit_id();
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_expr("id zero").unwrap();
    let expr = ctx.elaborate(&surface).unwrap();

    // The result should be App(App(id, Nat), zero)
    // i.e., the implicit argument should have been inserted and solved
    let args = expr.get_app_args();
    assert_eq!(
        args.len(),
        2,
        "Expected 2 arguments (implicit + explicit), got {}",
        args.len()
    );

    // First argument should be the inferred type 'Nat'
    assert!(
        matches!(args[0].kind(), ExprKind::Const(ref n, _) if n.to_string() == "Nat"),
        "Expected first arg to be 'Nat', got {:?}",
        args[0]
    );

    // Second argument should be the 'zero' constant
    assert!(
        matches!(args[1].kind(), ExprKind::Const(ref n, _) if n.to_string() == "zero"),
        "Expected second arg to be 'zero', got {:?}",
        args[1]
    );
}

#[test]
fn test_implicit_insertion_multiple() {
    // Test function with multiple implicit arguments
    let mut env = Environment::new();

    // Add compose : {A B C : Type} → (B → C) → (A → B) → A → C
    let compose_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(), // A : Type
        Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(), // B : Type
            Expr::pi(
                BinderInfo::Implicit,
                Expr::type_(), // C : Type
                Expr::pi(
                    BinderInfo::Default,
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(1), // B
                        Expr::bvar(1), // C
                    ), // g : B → C
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(3), // A
                            Expr::bvar(3), // B
                        ), // f : A → B
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(4), // x : A
                            Expr::bvar(3), // C
                        ),
                    ),
                ),
            ),
        ),
    );
    let compose_value = Expr::lam(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::lam(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::lam(
                BinderInfo::Implicit,
                Expr::type_(),
                Expr::lam(
                    BinderInfo::Default,
                    Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1)),
                    Expr::lam(
                        BinderInfo::Default,
                        Expr::pi(BinderInfo::Default, Expr::bvar(3), Expr::bvar(3)),
                        Expr::lam(
                            BinderInfo::Default,
                            Expr::bvar(4),
                            // g (f x) = App(BVar(2), App(BVar(1), BVar(0)))
                            Expr::app(Expr::bvar(2), Expr::app(Expr::bvar(1), Expr::bvar(0))),
                        ),
                    ),
                ),
            ),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("compose"),
        level_params: vec![],
        type_: compose_type,
        value: compose_value,
        is_reducible: true,
    })
    .unwrap();

    // Add simple functions to compose
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);

    // compose f f should insert 3 implicit metavariables
    let surface = parse_expr("compose f f").unwrap();
    let expr = ctx.elaborate(&surface).unwrap();

    // Expected: App(...App(compose, Nat), Nat), Nat), f), f)
    // 5 arguments total: 3 implicit (resolved) + 2 explicit
    let args = expr.get_app_args();
    assert_eq!(
        args.len(),
        5,
        "Expected 5 arguments (3 implicit + 2 explicit), got {}",
        args.len()
    );

    // First three should be the resolved implicit type arguments (Nat)
    for i in 0..3 {
        assert!(
            matches!(args[i].kind(), ExprKind::Const(ref n, _) if n.to_string() == "Nat"),
            "Expected arg {} to be 'Nat', got {:?}",
            i,
            args[i]
        );
    }

    // Last two should be 'f' constants
    for i in 3..5 {
        assert!(
            matches!(args[i].kind(), ExprKind::Const(ref n, _) if n.to_string() == "f"),
            "Expected arg {} to be 'f', got {:?}",
            i,
            args[i]
        );
    }
}

#[test]
fn test_no_implicit_insertion_for_explicit_function() {
    // Test that explicit arguments don't get metavariables inserted
    let mut env = Environment::new();

    // Add explicit_id : (A : Type) → A → A  (no implicit)
    let id_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let id_value = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("explicit_id"),
        level_params: vec![],
        type_: id_type,
        value: id_value,
        is_reducible: true,
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);

    // explicit_id Nat should NOT insert any metavariables
    let surface = parse_expr("explicit_id Nat").unwrap();
    let expr = ctx.elaborate(&surface).unwrap();

    let args = expr.get_app_args();
    assert_eq!(args.len(), 1, "Expected 1 argument, got {}", args.len());

    // The argument should be Nat (a constant), not a metavariable
    assert!(
        matches!(args[0].kind(), ExprKind::Const(ref n, _) if n.to_string() == "Nat"),
        "Expected arg to be 'Nat', got {:?}",
        args[0]
    );
}

#[test]
fn test_implicit_insertion_structure() {
    // Test that after implicit insertion, the elaborated expression has correct structure
    // with implicit arguments solved by unification.
    let env = env_with_implicit_id();
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_expr("id zero").unwrap();
    let expr = ctx.elaborate(&surface).unwrap();

    // Verify structure: App(App(Const(id), ?meta), Const(zero))
    match expr.kind() {
        ExprKind::App(inner, arg2) => {
            // arg2 should be 'zero'
            assert!(
                matches!(arg2.kind(), ExprKind::Const(ref n, _) if n.to_string() == "zero"),
                "Expected outer arg to be 'zero'"
            );

            match inner.kind() {
                ExprKind::App(id_const, meta) => {
                    // id_const should be the 'id' constant
                    assert!(
                        matches!(id_const.kind(), ExprKind::Const(ref n, _) if n.to_string() == "id"),
                        "Expected inner function to be 'id'"
                    );

                    // implicit argument should be the inferred type 'Nat'
                    assert!(
                        matches!(meta.kind(), ExprKind::Const(ref n, _) if n.to_string() == "Nat"),
                        "Expected implicit arg to be 'Nat'"
                    );
                }
                _ => panic!("Expected App(id, meta)"),
            }
        }
        _ => panic!("Expected App expression"),
    }
}

#[test]
fn test_implicit_insertion_with_instance() {
    // Test instance implicit [inst : T] is also handled
    let mut env = Environment::new();

    // Add a function with instance implicit: foo : [A : Type] → A → A
    let foo_type = Expr::pi(
        BinderInfo::InstImplicit,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let foo_value = Expr::lam(
        BinderInfo::InstImplicit,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("foo"),
        level_params: vec![],
        type_: foo_type,
        value: foo_value,
        is_reducible: true,
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("foo x").unwrap();
    let expr = ctx.elaborate(&surface).unwrap();

    let args = expr.get_app_args();
    assert_eq!(
        args.len(),
        2,
        "Expected 2 args (instance implicit + explicit)"
    );
    assert!(
        matches!(args[0].kind(), ExprKind::Sort(_)),
        "Expected first arg to be inferred type argument, got {:?}",
        args[0]
    );
}

// ==== Ascription type checking tests ====

#[test]
fn test_ascription_prop_has_type_type() {
    // (Prop : Type) should succeed - Prop has type Type
    let expr = elab("(Prop : Type)").unwrap();
    assert!(expr.is_prop());
}

#[test]
fn test_ascription_identity_function() {
    // Identity function with explicit type annotation
    let expr = elab("(fun (x : Type) => x : Type -> Type)").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Lam(_, _, _)));
}

#[test]
fn test_ascription_universe_levels() {
    // Type : Type fails because Type 0 has type Type 1 (different universe)
    // This is correct universe level checking
    let err = elab("(Type : Type)").unwrap_err();
    assert!(
        matches!(err, ElabError::TypeMismatch { .. }),
        "(Type : Type) should produce TypeMismatch due to universe level, got: {err}"
    );
}

#[test]
fn test_ascription_wrong_type() {
    // This should fail: Type is not of type Prop
    let err = elab("(Type : Prop)").unwrap_err();
    match err {
        ElabError::TypeMismatch {
            ref expected,
            ref actual,
        } => {
            // expected should mention Prop (Sort Zero)
            assert!(
                expected.contains("Sort") || expected.contains("Zero"),
                "expected field should mention Sort/Zero, got: {expected}"
            );
            // actual should mention higher universe
            assert!(
                actual.contains("Sort") || actual.contains("Succ"),
                "actual field should mention Sort/Succ, got: {actual}"
            );
        }
        _ => panic!("(Type : Prop) should produce TypeMismatch, got: {err}"),
    }
}

#[test]
fn test_ascription_nat_lit_wrong_type() {
    // Nat literal doesn't have type Type
    let err = elab("(42 : Type)").unwrap_err();
    assert!(
        matches!(err, ElabError::TypeMismatch { .. }),
        "(42 : Type) should produce TypeMismatch, got: {err}"
    );
}

#[test]
fn test_ascription_simple_lambda() {
    // A simple lambda with correct type annotation
    let expr = elab("(fun (x : Prop) => x : Prop -> Prop)").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Lam(_, _, _)));
}

#[test]
fn test_ascription_lambda_wrong_type() {
    // Lambda returning Prop annotated with Type -> Type should fail
    let err = elab("(fun (x : Prop) => x : Type -> Type)").unwrap_err();
    assert!(
        matches!(err, ElabError::TypeMismatch { .. }),
        "Prop lambda with Type->Type annotation should produce TypeMismatch, got: {err}"
    );
}

#[test]
fn test_ascription_preserves_value() {
    // Ascription should return the value, not the type
    let expr_with_ascription = elab("(fun (x : Type) => x : Type -> Type)").unwrap();
    let expr_without = elab("fun (x : Type) => x").unwrap();
    // Both should be the same lambda
    assert!(matches!(
        expr_with_ascription.kind(),
        ExprKind::Lam(_, _, _)
    ));
    assert!(matches!(expr_without.kind(), ExprKind::Lam(_, _, _)));
}

#[test]
fn test_ascription_arrow_pi_type() {
    // Ascription with arrow type that is Type
    // Prop -> Prop has type Type (impredicativity of Prop)
    let expr = elab("(Prop -> Prop : Type)").unwrap();
    // The ascripted expression is the arrow/Pi type
    assert!(matches!(expr.kind(), ExprKind::Pi(_, _, _)));
}

#[test]
fn test_ascription_arrow_pi_type_universe_mismatch() {
    // Type -> Type has type Type 1, not Type 0
    // This should fail because of universe level mismatch
    let err = elab("(Type -> Type : Type)").unwrap_err();
    assert!(
        matches!(err, ElabError::TypeMismatch { .. }),
        "(Type -> Type : Type) should produce TypeMismatch due to universe level, got: {err}"
    );
}

#[test]
fn test_ascription_with_arrow_type() {
    // Arrow type annotation
    let expr = elab("(fun (f : Type -> Type) => f : (Type -> Type) -> Type -> Type)").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Lam(_, _, _)));
}

// ==== @explicit marker tests (#1255) ====

#[test]
fn test_explicit_marker_parenthesized() {
    // @(id zero) should suppress implicit insertion: id gets both args explicitly
    // This form already worked before the fix.
    let env = env_with_implicit_id();
    let expr = elab_with_env(&env, "@(id Nat zero)").unwrap();
    let args = expr.get_app_args();
    assert_eq!(
        args.len(),
        2,
        "@(id Nat zero) should have 2 explicit args, got {}",
        args.len()
    );
}

#[test]
fn test_explicit_marker_without_parens() {
    // @id Nat zero should also suppress implicit insertion (#1255)
    // Before fix: @id only set explicit_mode during resolution of `id`,
    // then args were processed with implicit insertion active.
    let env = env_with_implicit_id();
    let expr = elab_with_env(&env, "@id Nat zero").unwrap();
    let args = expr.get_app_args();
    assert_eq!(
        args.len(),
        2,
        "@id Nat zero should have 2 explicit args, got {}",
        args.len()
    );
    // First arg should be Nat (the type, provided explicitly)
    assert!(
        matches!(args[0].kind(), ExprKind::Const(ref n, _) if n.to_string() == "Nat"),
        "Expected first arg to be 'Nat', got {:?}",
        args[0]
    );
    // Second arg should be zero
    assert!(
        matches!(args[1].kind(), ExprKind::Const(ref n, _) if n.to_string() == "zero"),
        "Expected second arg to be 'zero', got {:?}",
        args[1]
    );
}

#[test]
fn test_explicit_marker_no_implicit_meta_inserted() {
    // Without @: id zero should insert implicit meta for type, resolving to Nat
    // With @: id zero should fail because zero fills the {A : Type} slot but has type Nat
    let env = env_with_implicit_id();

    // Without @: id zero => App(App(id, ?meta), zero), meta solved to Nat => 2 args
    let normal = elab_with_env(&env, "id zero").unwrap();
    let normal_args = normal.get_app_args();
    assert_eq!(
        normal_args.len(),
        2,
        "id zero should have 2 args (implicit + explicit)"
    );

    // With @: @id zero should fail — zero : Nat fills the {A : Type} slot, type mismatch
    let explicit = elab_with_env(&env, "@id zero");
    assert!(
        explicit.is_err(),
        "@id zero should fail: zero : Nat doesn't match {{A : Type}}"
    );
}

#[test]
fn test_explicit_vs_normal_application() {
    // @id Nat zero should produce the same result as id zero
    // (both end up as App(App(id, Nat), zero))
    let env = env_with_implicit_id();

    let normal = elab_with_env(&env, "id zero").unwrap();
    let explicit = elab_with_env(&env, "@id Nat zero").unwrap();

    let normal_args = normal.get_app_args();
    let explicit_args = explicit.get_app_args();

    assert_eq!(
        normal_args.len(),
        explicit_args.len(),
        "id zero and @id Nat zero should produce same number of args"
    );
    assert_eq!(normal_args.len(), 2);
}

// ==== Named argument tests (#1230) ====

/// Create environment with a two-parameter function for named argument testing
fn env_with_two_param_fn() -> Environment {
    let mut env = Environment::new();

    // Nat : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // zero : Nat
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("zero"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    // one : Nat
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("one"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    // mk_pair : Nat → Nat → Nat (two explicit params: x and y)
    let mk_pair_type = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("Nat"), vec![]), // x : Nat
        Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("Nat"), vec![]), // y : Nat
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
    );
    let mk_pair_value = Expr::lam(
        BinderInfo::Default,
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::lam(
            BinderInfo::Default,
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::bvar(0), // just return y
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("mk_pair"),
        level_params: vec![],
        type_: mk_pair_type,
        value: mk_pair_value,
        is_reducible: true,
    })
    .unwrap();

    // Register parameter names so named arguments can be resolved
    env.set_param_names(
        Name::from_string("mk_pair"),
        vec!["x".to_string(), "y".to_string()],
    );

    env
}

#[test]
fn test_named_args_positional_order() {
    // mk_pair zero one should produce App(App(mk_pair, zero), one)
    let env = env_with_two_param_fn();
    let expr = elab_with_env(&env, "mk_pair zero one").unwrap();
    let args = expr.get_app_args();
    assert_eq!(args.len(), 2, "mk_pair zero one should have 2 args");
    assert!(matches!(args[0].kind(), ExprKind::Const(ref n, _) if n.to_string() == "zero"));
    assert!(matches!(args[1].kind(), ExprKind::Const(ref n, _) if n.to_string() == "one"));
}

#[test]
fn test_named_args_reordering() {
    // mk_pair (y := one) (x := zero) should reorder to App(App(mk_pair, zero), one)
    let env = env_with_two_param_fn();
    let expr = elab_with_env(&env, "mk_pair (y := one) (x := zero)").unwrap();
    let args = expr.get_app_args();
    assert_eq!(args.len(), 2, "Named args should produce 2 args");
    // x should be zero (first param), y should be one (second param)
    assert!(
        matches!(args[0].kind(), ExprKind::Const(ref n, _) if n.to_string() == "zero"),
        "First arg (x) should be zero, got {:?}",
        args[0]
    );
    assert!(
        matches!(args[1].kind(), ExprKind::Const(ref n, _) if n.to_string() == "one"),
        "Second arg (y) should be one, got {:?}",
        args[1]
    );
}

#[test]
fn test_named_args_skip_first() {
    // mk_pair (y := one) should provide only y, leaving x as a hole
    let env = env_with_two_param_fn();
    // Named arg (y := one) with x left as hole should succeed
    let expr = elab_with_env(&env, "mk_pair (y := one)")
        .expect("mk_pair (y := one) should elaborate with hole for x");
    // Result should be an application of mk_pair
    assert!(
        matches!(expr.kind(), ExprKind::App(..)),
        "mk_pair (y := one) should produce App, got: {expr:?}"
    );
}

#[test]
fn test_named_args_unknown_name_error() {
    // mk_pair (z := one) should fail because 'z' is not a parameter name
    let env = env_with_two_param_fn();
    let err = elab_with_env(&env, "mk_pair (z := one)").unwrap_err();
    match &err {
        ElabError::NamedArgBindingFailed { name, reason, .. } => {
            assert_eq!(name, "z", "the offending named argument must be reported");
            assert!(
                reason.contains("unknown named argument"),
                "expected 'unknown named argument' for 'z', got: {reason}"
            );
        }
        _ => panic!(
            "mk_pair (z := one) should produce NamedArgBindingFailed for unknown param, got: {err}"
        ),
    }
}

#[test]
fn test_named_args_duplicate_error() {
    // mk_pair (x := zero) (x := one) should fail because 'x' is duplicated
    let env = env_with_two_param_fn();
    let err = elab_with_env(&env, "mk_pair (x := zero) (x := one)").unwrap_err();
    match &err {
        ElabError::NamedArgBindingFailed { name, reason, .. } => {
            assert_eq!(name, "x", "the offending named argument must be reported");
            assert!(
                reason.contains("already bound"),
                "expected double-fill rejection for 'x', got: {reason}"
            );
        }
        _ => panic!("duplicate named arg should produce NamedArgBindingFailed, got: {err}"),
    }
}

#[test]
fn test_definition_body_partial_application_checks_without_outer_expected_type() {
    let mut env = Environment::with_prelude();
    let surface =
        parse_decl_for_elab("def natFromPEmpty : PEmpty -> Nat := PEmpty.rec (fun _ => Nat)")
            .expect("definition should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &surface);
    assert!(
        result.is_ok(),
        "definition body should accept recursor partial applications before retrying expected-type elaboration, got {result:?}"
    );
}

#[test]
#[serial_test::serial]
fn test_definition_body_instantiates_polymorphic_constant_after_inference() {
    crate::register::reset_kernel_check_counter();

    // The prelude now ships the Lean-core `id : {α : Sort u} → α → α`
    // (Brick P1, `init_fun_id`); registering a private twin here would be a
    // DuplicateName. The prelude constant is exactly the polymorphic-id this
    // test exercises.
    let mut env = Environment::with_prelude();
    let surface =
        parse_decl_for_elab("def idNat : Nat -> Nat := id").expect("definition should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &surface);
    assert!(
        result.is_ok(),
        "definition body should elaborate `id` from its inferred type and then check against `Nat -> Nat`, got {result:?}"
    );
    assert_eq!(crate::register::kernel_check_failure_count(), 0);

    let info = env
        .get_const(&Name::from_string("idNat"))
        .expect("idNat should be registered");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    assert_eq!(info.level_params, Vec::<Name>::new());
    assert_eq!(info.type_, Expr::pi(BinderInfo::Default, nat.clone(), nat));
}

/// #796: PEmpty.elim' without return type annotation (Lean 4 compat 276 pattern).
///
/// Tests that `def PEmpty.elim' {α : Type} := PEmpty.rec (fun _ => α)` elaborates
/// without an explicit return type. PEmpty.rec's result type should be inferred.
/// Verifies the elaborated value contains PEmpty.rec and the type has the right
/// implicit-binder structure.
#[test]
fn test_pempty_elim_no_return_type_annotation() {
    fn val_contains_const(expr: &Expr, needle: &str) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => name.to_string() == needle,
            ExprKind::App(f, a) => val_contains_const(f, needle) || val_contains_const(a, needle),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                val_contains_const(ty, needle) || val_contains_const(body, needle)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                val_contains_const(ty, needle)
                    || val_contains_const(val, needle)
                    || val_contains_const(body, needle)
            }
            ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                val_contains_const(inner, needle)
            }
            ExprKind::Proj(_, _, inner) => val_contains_const(inner, needle),
            _ => false,
        }
    }

    let mut env = Environment::with_prelude();
    let surface = parse_decl_for_elab("def PEmpty.elim' {α : Type} := PEmpty.rec (fun _ => α)")
        .expect("PEmpty.elim' definition should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &surface);
    let elab =
        result.expect("PEmpty.elim' without return type should elaborate via recursor inference");

    match elab {
        ElabResult::Definition { name, ty, val, .. } => {
            assert_eq!(
                name,
                Name::from_string("PEmpty.elim'"),
                "definition should be named PEmpty.elim'"
            );
            // The elaborated value must contain PEmpty.rec — not sorry or trustedArith
            assert!(
                val_contains_const(&val, "PEmpty.rec"),
                "elaborated value should contain PEmpty.rec, got: {:?}",
                val
            );
            assert!(
                !val_contains_const(&val, "sorry"),
                "elaborated value must not contain sorry"
            );
            // Type should be a Pi with implicit binder (α : Type) → PEmpty → α
            assert!(
                matches!(ty.kind(), ExprKind::Pi(bi, _, _) if bi.info == BinderInfo::Implicit),
                "type should start with implicit binder for α, got: {:?}",
                ty
            );
        }
        other => panic!("expected Definition, got: {:?}", other),
    }
}
