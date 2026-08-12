// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for quantifier flattening, BVar substitution, and index mapping.
//!
//! Covers `flattened_bvar_indices`, `flatten_forall`, `flatten_exists`,
//! `instantiate_bvars`, and `substitute_bvar` from `instantiate.rs`.
//!
//! Part of #2902 Wave A.

use super::*;
use clean_kernel::Level;

#[test]
fn test_flattened_bvar_indices_zero() {
    let indices = SmtBridge::flattened_bvar_indices(0);
    assert!(indices.is_empty());
}

#[test]
fn test_flattened_bvar_indices_one() {
    let indices = SmtBridge::flattened_bvar_indices(1);
    assert_eq!(indices, vec![0]);
}

#[test]
fn test_flattened_bvar_indices_three() {
    let indices = SmtBridge::flattened_bvar_indices(3);
    assert_eq!(indices, vec![2, 1, 0]);
}

#[test]
fn test_flatten_forall_single_pi() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let nat = Expr::const_(Name::from_string("A"), vec![]);
    // body uses BVar(0) so it's dependent
    let body = Expr::bvar(0);
    let (types, result_body) = bridge.flatten_forall(&nat, &body);

    assert_eq!(types.len(), 1, "single Pi should produce 1 binder type");
    assert!(
        matches!(types[0].kind(), ExprKind::Const(n, _) if n.to_string() == "A"),
        "binder type should be A"
    );
    assert!(
        matches!(result_body.kind(), ExprKind::BVar(0)),
        "body should be BVar(0)"
    );
}

#[test]
fn test_flatten_forall_nested_dependent_pis() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    // ∀ x : A, ∀ y : A, BVar(0) (using x is BVar(1), y is BVar(0))
    let inner_body = Expr::bvar(0);
    let inner_pi = Expr::pi(BinderInfo::Default, a_ty.clone(), inner_body);
    let (types, body) = bridge.flatten_forall(&a_ty, &inner_pi);

    assert_eq!(types.len(), 2, "nested Pi should produce 2 binder types");
    assert!(
        matches!(body.kind(), ExprKind::BVar(0)),
        "innermost body should be BVar(0)"
    );
}

#[test]
fn test_flatten_forall_stops_at_non_dependent() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    // body is a Pi that doesn't use the bound variable (non-dependent)
    let non_dep_pi = Expr::pi(
        BinderInfo::Default,
        a_ty.clone(),
        Expr::const_(Name::from_string("A"), vec![]), // no BVar
    );
    let (types, _body) = bridge.flatten_forall(&a_ty, &non_dep_pi);

    assert_eq!(types.len(), 1, "should stop flattening at non-dependent Pi");
}

#[test]
fn test_flatten_exists_single() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let body = Expr::bvar(0);
    let (types, result_body) = bridge.flatten_exists(&a_ty, &body);

    assert_eq!(types.len(), 1, "single Exists should produce 1 binder type");
    assert!(
        matches!(result_body.kind(), ExprKind::BVar(0)),
        "body should be BVar(0)"
    );
}

#[test]
fn test_flatten_exists_nested() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    // Inner: Exists A (fun y => BVar(0))
    let inner_exists = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            a_ty.clone(),
        ),
        Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(0)),
    );
    let (types, _body) = bridge.flatten_exists(&a_ty, &inner_exists);

    assert_eq!(
        types.len(),
        2,
        "nested Exists should produce 2 binder types"
    );
}

#[test]
fn test_substitute_bvar_replaces_target() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let replacement = Expr::const_(Name::from_string("a"), vec![]);
    let expr = Expr::bvar(0);
    let result = bridge.substitute_bvar(&expr, 0, &replacement);

    assert!(
        matches!(result.kind(), ExprKind::Const(n, _) if n.to_string() == "a"),
        "BVar(0) should be replaced with constant 'a'"
    );
}

#[test]
fn test_substitute_bvar_shifts_higher_indices() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let replacement = Expr::const_(Name::from_string("a"), vec![]);
    let expr = Expr::bvar(2);
    let result = bridge.substitute_bvar(&expr, 1, &replacement);

    assert!(
        matches!(result.kind(), ExprKind::BVar(1)),
        "BVar(2) should shift to BVar(1) when substituting idx=1, got {:?}",
        result.kind()
    );
}

#[test]
fn test_substitute_bvar_leaves_lower_indices() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let replacement = Expr::const_(Name::from_string("a"), vec![]);
    let expr = Expr::bvar(0);
    let result = bridge.substitute_bvar(&expr, 1, &replacement);

    assert!(
        matches!(result.kind(), ExprKind::BVar(0)),
        "BVar(0) should be unchanged when substituting idx=1"
    );
}

#[test]
fn test_substitute_bvar_recurses_into_app() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let expr = Expr::app(f, Expr::bvar(0));
    let replacement = Expr::const_(Name::from_string("a"), vec![]);
    let result = bridge.substitute_bvar(&expr, 0, &replacement);

    if let ExprKind::App(_, arg) = result.kind() {
        assert!(
            matches!(arg.kind(), ExprKind::Const(n, _) if n.to_string() == "a"),
            "App argument BVar(0) should be replaced"
        );
    } else {
        panic!("result should still be an App");
    }
}

#[test]
fn test_instantiate_bvars_multiple() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    // f(BVar(1), BVar(0)) with replacements for both
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let expr = Expr::app(Expr::app(f, Expr::bvar(1)), Expr::bvar(0));
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let replacements = vec![(1u32, a), (0u32, b)];
    let result = bridge.instantiate_bvars(&expr, &replacements);

    // After substitution, the outermost App structure should be preserved
    // with both BVars replaced by constants.
    assert!(
        !result.has_loose_bvars(),
        "all BVars should be substituted, got {result:?}"
    );
}

#[test]
fn test_substitute_bvar_adjusts_under_binder() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    // Lambda body has BVar(1) which refers to the outer scope (idx=0 after shift)
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let expr = Expr::lam(BinderInfo::Default, a_ty, Expr::bvar(1));
    let replacement = Expr::const_(Name::from_string("a"), vec![]);
    let result = bridge.substitute_bvar(&expr, 0, &replacement);

    // Under the binder, BVar(1) at idx+1=1 should be replaced
    if let ExprKind::Lam(_, _, body) = result.kind() {
        assert!(
            matches!(body.kind(), ExprKind::Const(n, _) if n.to_string() == "a"),
            "BVar(1) under binder should be replaced with 'a', got {:?}",
            body.kind()
        );
    } else {
        panic!("result should still be a Lam");
    }
}
