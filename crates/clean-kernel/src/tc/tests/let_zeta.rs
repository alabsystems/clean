// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for let/zeta reduction in the type checker.

use super::helpers::{build_nested_lets, run_with_timeout, SCALING_TEST_TIMEOUT};
use super::*;

fn let_expr(name: Name, ty: Expr, val: Expr, body: Expr) -> Expr {
    Expr::let_named(name, ty, val, body, false)
}

fn id_fn(arg_ty: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, arg_ty, Expr::bvar(0))
}

fn prop_to_prop() -> Expr {
    Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop())
}

fn sort_two() -> Expr {
    Expr::sort(Level::succ(Level::succ(Level::zero())))
}

#[test]
fn test_whnf_let_alias_reduces_to_prop() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let expr = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
    );
    let result = tc.whnf(&expr);

    assert_eq!(
        result,
        Expr::prop(),
        "let x : Type := Prop in x should zeta-reduce to Prop"
    );
}

#[test]
fn test_whnf_let_arrow_body_substitutes_bound_value() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // let x : Type := Prop in (x -> x)
    // In the Pi codomain, BVar(1) refers back to the let-bound x.
    let body = Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1));
    let expr = let_expr(Name::from_string("x"), Expr::type_(), Expr::prop(), body);
    let expected = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());

    assert_eq!(
        tc.whnf(&expr),
        expected,
        "let x : Type := Prop in (x -> x) should reduce to Prop -> Prop"
    );
}

#[test]
fn test_whnf_nested_let_alias_chain_reduces_to_prop() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let inner = let_expr(
        Name::from_string("y"),
        Expr::type_(),
        Expr::bvar(0),
        Expr::bvar(0),
    );
    let outer = let_expr(Name::from_string("x"), Expr::type_(), Expr::prop(), inner);

    assert_eq!(
        tc.whnf(&outer),
        Expr::prop(),
        "nested let aliases should zeta-reduce all the way to Prop"
    );
}

#[test]
fn test_whnf_let_unused_body_preserves_type() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let expr = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(),
        Expr::type_(),
    );

    assert_eq!(
        tc.whnf(&expr),
        Expr::type_(),
        "let x := Prop in Type should stay Type when the body ignores x"
    );
}

#[test]
fn test_whnf_let_under_app_beta_reduces_after_zeta() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let id_ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    let id = id_fn(Expr::type_());
    let let_id = let_expr(Name::from_string("f"), id_ty, id, Expr::bvar(0));
    let app = Expr::app(let_id, Expr::prop());

    assert_eq!(
        tc.whnf(&app),
        Expr::prop(),
        "(let f := fun x : Type => x in f) Prop should zeta-reduce, then beta-reduce to Prop"
    );
}

#[test]
fn test_def_eq_let_left_matches_prop() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let lhs = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
    );

    assert!(
        tc.is_def_eq(&lhs, &Expr::prop()),
        "let x := Prop in x should be definitionally equal to Prop"
    );
}

#[test]
fn test_def_eq_let_right_matches_prop() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let rhs = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
    );

    assert!(
        tc.is_def_eq(&Expr::prop(), &rhs),
        "definitional equality should be symmetric when the right-hand side is a let"
    );
}

#[test]
fn test_def_eq_let_both_sides_with_different_names_match() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let lhs = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
    );
    let rhs = let_expr(
        Name::from_string("y"),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
    );

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "let-bound names should not affect definitional equality after zeta reduction"
    );
}

#[test]
fn test_def_eq_nested_let_matches_prop() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let nested = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(),
        let_expr(
            Name::from_string("y"),
            Expr::type_(),
            Expr::bvar(0),
            Expr::bvar(0),
        ),
    );

    assert!(
        tc.is_def_eq(&nested, &Expr::prop()),
        "nested let aliases should be definitionally equal to Prop"
    );
}

#[test]
fn test_def_eq_let_same_value_different_annotations_matches() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let lhs = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
    );
    let rhs = let_expr(
        Name::from_string("x"),
        sort_two(),
        Expr::prop(),
        Expr::bvar(0),
    );

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "def_eq should follow zeta-normal forms even when let annotations differ"
    );
}

#[test]
fn test_def_eq_let_prop_and_type_do_not_match() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let lhs = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
    );

    assert!(
        !tc.is_def_eq(&lhs, &Expr::type_()),
        "let x := Prop in x should not be definitionally equal to Type"
    );
}

#[test]
fn test_infer_type_let_alias_has_type_type() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let expr = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
    );
    let inferred = tc.infer_type(&expr).unwrap();

    assert_eq!(
        inferred,
        Expr::type_(),
        "the body x should keep its declared type Type in let x : Type := Prop in x"
    );
    tc.check_type(&expr, &Expr::type_()).unwrap();
}

#[test]
fn test_infer_type_dependent_let_lambda_instantiates_pi() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // let x : Type 1 := Prop in (fun (y : x) => y)
    // BVar(0) in the lambda domain refers to the let-bound x.
    let expr = let_expr(
        Name::from_string("x"),
        Expr::sort(Level::succ(Level::zero())),
        Expr::prop(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    let inferred = tc.infer_type(&expr).unwrap();
    let expected = prop_to_prop();

    assert_eq!(
        inferred, expected,
        "dependent let should substitute Prop into the lambda domain and codomain"
    );
    assert!(
        !inferred.has_fvar_quick(),
        "dependent let inference should not leak FVars into the resulting Pi type"
    );
    tc.check_type(&expr, &expected).unwrap();
}

#[test]
fn test_infer_type_nested_let_alias_has_type_type() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let inner = let_expr(
        Name::from_string("y"),
        Expr::type_(),
        Expr::bvar(0),
        Expr::bvar(0),
    );
    let expr = let_expr(Name::from_string("x"), Expr::type_(), Expr::prop(), inner);
    let inferred = tc.infer_type(&expr).unwrap();

    assert_eq!(
        inferred,
        Expr::type_(),
        "nested let aliases should still infer to the declared type Type"
    );
    tc.check_type(&expr, &Expr::type_()).unwrap();
}

#[test]
fn test_dependent_let_arrow_body_infers_prop_sort() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // let A : Type := Prop in (A -> A)
    // This kernel infers the resulting arrow type at Type.
    let body = Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1));
    let expr = let_expr(Name::from_string("A"), Expr::type_(), Expr::prop(), body);
    let inferred = tc.infer_type(&expr).unwrap();

    assert!(
        inferred.is_sort(),
        "let A : Type := Prop in (A -> A) should infer to a sort, got {inferred:?}"
    );
    assert_eq!(
        inferred,
        Expr::type_(),
        "let A : Type := Prop in (A -> A) should infer Type in this kernel"
    );
    tc.check_type(&expr, &Expr::type_()).unwrap();
}

#[test]
fn test_dependent_let_function_application_after_let_infers_prop() {
    use crate::env::Declaration;

    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let tc = TypeChecker::new(&env);
    let p = Expr::const_(Name::from_string("p"), vec![]);
    let id_prop = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let expr = let_expr(
        Name::from_string("f"),
        prop_to_prop(),
        id_prop,
        Expr::app(Expr::bvar(0), p.clone()),
    );

    assert_eq!(
        tc.whnf(&expr),
        p,
        "let-bound Prop identity should zeta-reduce before beta-reducing its application"
    );

    let inferred = tc.infer_type(&expr).unwrap();
    assert_eq!(
        inferred,
        Expr::prop(),
        "applying a let-bound function of type Prop -> Prop should infer Prop"
    );
    tc.check_type(&expr, &Expr::prop()).unwrap();
}

#[test]
fn test_interaction_lambda_body_let_alias_is_def_eq_plain_lambda() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // λ x : Type. let y : Type := x in y
    // BVar(0) in the let value refers to the lambda-bound x.
    let lhs = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        let_expr(
            Name::from_string("y"),
            Expr::type_(),
            Expr::bvar(0),
            Expr::bvar(0),
        ),
    );
    let rhs = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let lam_ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());

    tc.check_type(&lhs, &lam_ty).unwrap();
    tc.check_type(&rhs, &lam_ty).unwrap();

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "lambda bodies should compare equal when one side only adds a let alias"
    );
}

#[test]
fn test_interaction_let_body_beta_redex_reduces_to_prop() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // let x := Prop in (fun y : Type => y) x
    let body = Expr::app(id_fn(Expr::type_()), Expr::bvar(0));
    let expr = let_expr(Name::from_string("x"), Expr::type_(), Expr::prop(), body);

    assert_eq!(
        tc.whnf(&expr),
        Expr::prop(),
        "zeta reduction should expose the inner beta redex and reduce it to Prop"
    );
}

#[test]
fn test_performance_nested_lets_terminate() {
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_performance_nested_lets_terminate",
        || {
            let env = Environment::new();
            let tc = TypeChecker::new(&env);
            let expr = build_nested_lets(512);
            let result = tc.whnf(&expr);

            assert_eq!(
                result,
                Expr::prop(),
                "a deep nest of lets should terminate and reduce to Prop"
            );
        },
    );
}

// ============================================================================
// FVar let-zeta tests
// ============================================================================

/// Push a let-bound FVar into the local context, then WHNF should zeta-reduce it.
#[test]
fn test_whnf_fvar_let_zeta_reduces_to_value() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let fvar_id = tc.ctx_push_let(Name::from_string("x"), Expr::type_(), Expr::prop());
    let fvar_expr = Expr::from_kind(ExprKind::FVar(fvar_id));

    let result = tc.whnf(&fvar_expr);
    assert_eq!(
        result,
        Expr::prop(),
        "FVar with let-binding should zeta-reduce to its value"
    );

    tc.ctx_pop();
}

/// FVar without a let-binding (regular binder) should NOT reduce in WHNF.
#[test]
fn test_whnf_fvar_no_let_stays_unreduced() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let fvar_id = tc.ctx_push(Name::from_string("x"), Expr::type_(), BinderInfo::Default);
    let fvar_expr = Expr::from_kind(ExprKind::FVar(fvar_id));

    let result = tc.whnf(&fvar_expr);
    assert_eq!(
        result, fvar_expr,
        "FVar without let-binding should remain unchanged in WHNF"
    );

    tc.ctx_pop();
}

/// Let-bound FVar used inside an application should reduce.
#[test]
fn test_whnf_fvar_let_in_app_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let id = id_fn(Expr::type_());
    let fn_type = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());

    let fvar_id = tc.ctx_push_let(Name::from_string("f"), fn_type, id);
    let fvar_expr = Expr::from_kind(ExprKind::FVar(fvar_id));

    let app = Expr::app(fvar_expr, Expr::prop());
    let result = tc.whnf(&app);
    assert_eq!(
        result,
        Expr::prop(),
        "Application of let-bound FVar should zeta+beta reduce"
    );

    tc.ctx_pop();
}

// ============================================================================
// Three-level nested let with cross-reference de Bruijn indexing
// ============================================================================

/// `let a := Prop in let b := Type in let c := a in c` reduces to `Prop`.
#[test]
fn test_whnf_three_level_nested_let_cross_reference() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Innermost: let c := BVar(1) in BVar(0)
    //   BVar(1) in value: refers to a (shifted past b's binder)
    //   BVar(0) in body: refers to c
    let inner = let_expr(
        Name::from_string("c"),
        Expr::type_(),
        Expr::bvar(1), // c := a
        Expr::bvar(0), // body = c
    );

    // Middle: let b := Type in inner
    let middle = let_expr(
        Name::from_string("b"),
        Expr::sort(Level::succ(Level::zero())),
        Expr::type_(),
        inner,
    );

    // Outer: let a := Prop in middle
    let outer = let_expr(Name::from_string("a"), Expr::type_(), Expr::prop(), middle);

    let result = tc.whnf(&outer);
    assert_eq!(
        result,
        Expr::prop(),
        "Three-level nested let with cross-references should reduce to Prop"
    );
}

// ============================================================================
// def_eq transitivity through let chains
// ============================================================================

/// Explicit transitivity: `let_let_prop == let_prop == Prop`.
#[test]
fn test_def_eq_let_transitivity_chain() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let b = let_expr(
        Name::from_string("y"),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
    );
    let a = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        b.clone(),
        Expr::bvar(0),
    );
    let c = Expr::prop();

    assert!(tc.is_def_eq(&a, &b), "a == b should hold");
    assert!(tc.is_def_eq(&b, &c), "b == c should hold");
    assert!(tc.is_def_eq(&a, &c), "Transitivity: a == c should hold");
}

/// def_eq between let and beta reduction that produce the same result.
#[test]
fn test_def_eq_let_vs_beta_reduction() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let let_side = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
    );
    let beta_side = Expr::app(id_fn(Expr::type_()), Expr::prop());

    assert!(
        tc.is_def_eq(&let_side, &beta_side),
        "let x := Prop in x should be def_eq to (fun a : Type => a) Prop"
    );
}

/// def_eq between let producing Pi and the Pi directly.
#[test]
fn test_def_eq_let_producing_pi_matches_plain_pi() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let let_pi = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let plain_pi = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());

    assert!(
        tc.is_def_eq(&let_pi, &plain_pi),
        "let x := Prop in (x -> x) should be def_eq to (Prop -> Prop)"
    );
}

// ============================================================================
// Let body is lambda
// ============================================================================

/// Let whose body is a lambda reduces to a lambda.
#[test]
fn test_whnf_let_body_is_lambda() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let body = Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0));
    let expr = let_expr(Name::from_string("x"), Expr::type_(), Expr::prop(), body);

    let result = tc.whnf(&expr);
    let expected = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    assert_eq!(
        result, expected,
        "let x := Prop in (fun a : x => a) should reduce to (fun a : Prop => a)"
    );
}

// ============================================================================
// Value that is itself a let expression
// ============================================================================

/// `let x := (let y := Prop in y) in x` should fully reduce to `Prop`.
#[test]
fn test_whnf_let_value_is_let() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let val = let_expr(
        Name::from_string("y"),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
    );
    let expr = let_expr(Name::from_string("x"), Expr::type_(), val, Expr::bvar(0));

    let result = tc.whnf(&expr);
    assert_eq!(
        result,
        Expr::prop(),
        "let with let-valued RHS should fully reduce"
    );
}

// ============================================================================
// Infer type edge cases
// ============================================================================

/// Let with mismatched declared type and value: `infer_type` succeeds (Lean 4
/// parity: infer_only mode skips let value checks), but `check_type` catches it.
#[test]
fn test_infer_let_type_mismatch_infer_only_skips() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // let x : Prop := Type in x  (Type has type Sort(1), not Prop)
    let expr = let_expr(
        Name::from_string("x"),
        Expr::prop(),
        Expr::type_(),
        Expr::bvar(0),
    );

    // infer_type uses infer_only=true, skipping value-type checking (Lean 4 behavior)
    let result = tc.infer_type(&expr);
    assert!(
        result.is_ok(),
        "infer_type (infer_only mode) should succeed even with let type mismatch"
    );

    // check_type uses infer_only=false, which catches the mismatch
    let check_result = tc.check_type(&expr, &Expr::prop());
    assert!(
        check_result.is_err(),
        "check_type should fail for let with type mismatch (declared Prop but value is Type)"
    );
}

/// Let with Sort as value: `let x : Sort 2 := Sort 1 in x`.
#[test]
fn test_infer_let_sort_value() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let expr = let_expr(
        Name::from_string("x"),
        sort_two(),
        Expr::sort(Level::succ(Level::zero())),
        Expr::bvar(0),
    );

    let ty = tc.infer_type(&expr).unwrap();
    assert!(
        ty.is_sort(),
        "let with sort value should have sort type, got {ty:?}"
    );
}

// ============================================================================
// Performance: def_eq and infer on nested lets
// ============================================================================

/// Nested let def_eq should not blow up (500 layers).
#[test]
fn test_performance_def_eq_nested_lets() {
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_performance_def_eq_nested_lets",
        || {
            let env = Environment::new();
            let tc = TypeChecker::new(&env);
            let deep_lets = build_nested_lets(500);
            assert!(
                tc.is_def_eq(&deep_lets, &Expr::prop()),
                "500 nested lets should be def_eq to Prop"
            );
        },
    );
}

/// Nested let type inference should not blow up (500 layers).
#[test]
fn test_performance_infer_nested_lets() {
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_performance_infer_nested_lets",
        || {
            let env = Environment::new();
            let tc = TypeChecker::new(&env);
            let deep_lets = build_nested_lets(500);
            let ty = tc.infer_type(&deep_lets).unwrap();
            assert!(
                ty.is_sort(),
                "Deeply nested lets should infer to a sort type"
            );
        },
    );
}

// ============================================================================
// WHNF idempotence for let expressions
// ============================================================================

/// WHNF of let is idempotent: `whnf(whnf(e)) == whnf(e)` for various let shapes.
#[test]
fn test_whnf_let_idempotent() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let test_cases: Vec<Expr> = vec![
        let_expr(Name::anon(), Expr::type_(), Expr::prop(), Expr::bvar(0)),
        let_expr(
            Name::anon(),
            Expr::type_(),
            let_expr(Name::anon(), Expr::type_(), Expr::prop(), Expr::bvar(0)),
            Expr::bvar(0),
        ),
        let_expr(
            Name::anon(),
            Expr::type_(),
            Expr::prop(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        ),
        Expr::app(
            let_expr(
                Name::anon(),
                Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
                id_fn(Expr::type_()),
                Expr::bvar(0),
            ),
            Expr::prop(),
        ),
    ];

    for (i, e) in test_cases.iter().enumerate() {
        let once = tc.whnf(e);
        let twice = tc.whnf(&once);
        assert_eq!(once, twice, "WHNF idempotence failed for test_cases[{i}]");
    }
}

// ============================================================================
// Let with body that uses value multiple times
// ============================================================================

/// `let f := id in f (f Prop)` should reduce to `Prop` via zeta+beta.
#[test]
fn test_whnf_let_double_use_of_bound_var() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let id = id_fn(Expr::type_());
    let inner_app = Expr::app(Expr::bvar(0), Expr::prop());
    let body = Expr::app(Expr::bvar(0), inner_app);

    let expr = let_expr(
        Name::from_string("f"),
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
        id,
        body,
    );

    let result = tc.whnf(&expr);
    assert_eq!(
        result,
        Expr::prop(),
        "let f := id in f (f Prop) should reduce to Prop"
    );
}

// ============================================================================
// Delta + zeta interaction
// ============================================================================

/// Let binding that references a declared constant via delta reduction.
/// `let x := c in x` where c is a definition reducing to Prop.
#[test]
fn test_whnf_let_with_delta_constant() {
    use crate::env::Declaration;

    let mut env = Environment::new();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("myProp"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    })
    .unwrap();

    let tc = TypeChecker::new(&env);
    let c = Expr::const_(Name::from_string("myProp"), vec![]);

    // let x := myProp in x
    let expr = let_expr(Name::from_string("x"), Expr::type_(), c, Expr::bvar(0));

    let result = tc.whnf(&expr);
    // Zeta gives myProp, then delta gives Prop
    assert_eq!(
        result,
        Expr::prop(),
        "let x := myProp in x should zeta to myProp, then delta to Prop"
    );
}

/// def_eq between let-bound constant and its definition.
#[test]
fn test_def_eq_let_with_delta_constant() {
    use crate::env::Declaration;

    let mut env = Environment::new();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("myProp"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    })
    .unwrap();

    let tc = TypeChecker::new(&env);
    let c = Expr::const_(Name::from_string("myProp"), vec![]);
    let expr = let_expr(Name::from_string("x"), Expr::type_(), c, Expr::bvar(0));

    assert!(
        tc.is_def_eq(&expr, &Expr::prop()),
        "let x := myProp in x should be def_eq to Prop via zeta+delta"
    );
}

// ============================================================================
// Zeta in all transparency modes
// ============================================================================

/// Zeta reduction should work regardless of transparency mode.
#[test]
fn test_whnf_let_all_transparency_modes() {
    use crate::env::TransparencyMode;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let expr = let_expr(
        Name::from_string("x"),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
    );

    for mode in [
        TransparencyMode::Reducible,
        TransparencyMode::Default,
        TransparencyMode::All,
    ] {
        let r = tc.whnf_with_transparency(&expr, mode);
        assert_eq!(
            r,
            Expr::prop(),
            "Zeta reduction should work in {mode:?} transparency mode"
        );
    }
}
