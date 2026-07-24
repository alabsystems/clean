// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests recovered from zone/rust-backend.
//!
//! These tests were deleted during the zone merge due to directory conflicts
//! (E0761). Ported from `bridge/tests/regression.rs` in origin/zone/rust-backend.
//!
//! Part of #2224: Recover valuable zone test expansions.

use super::test_helpers::{make_eq, setup_env};
use super::*;
use clean_kernel::expr::MDataValue;
use clean_kernel::tc::LocalContext;

/// Regression test for #2088: verify term_to_type is populated
/// at every level of a 3-deep nested App expression f(f(f(a))).
#[test]
fn test_translate_term_populates_term_to_type_deep_nesting() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);

    // Build f(f(f(a))) — 3 levels of App nesting
    let fa = Expr::app(f.clone(), a.clone());
    let ffa = Expr::app(f.clone(), fa.clone());
    let fffa = Expr::app(f.clone(), ffa.clone());

    let fffa_tid = bridge
        .translate_term(&fffa)
        .expect("Should translate f(f(f(a)))");

    assert!(
        bridge.term_to_type.contains_key(&fffa_tid),
        "term_to_type missing for top-level f(f(f(a)))"
    );

    let ffa_tid = bridge
        .translate_term(&ffa)
        .expect("Should translate f(f(a)) (cached)");
    assert!(
        bridge.term_to_type.contains_key(&ffa_tid),
        "term_to_type missing for 2nd-level f(f(a))"
    );

    let fa_tid = bridge
        .translate_term(&fa)
        .expect("Should translate f(a) (cached)");
    assert!(
        bridge.term_to_type.contains_key(&fa_tid),
        "term_to_type missing for 3rd-level f(a)"
    );

    let a_tid = bridge
        .translate_term(&a)
        .expect("Should translate a (cached)");
    assert!(
        bridge.term_to_type.contains_key(&a_tid),
        "term_to_type missing for leaf term a"
    );
}

/// Regression test for #2089: Multi-variable witness instantiation.
/// Exercises sorted-descending substitution with 2 bound variables.
#[test]
fn test_instantiate_body_with_multiple_witnesses() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let witness0 = bridge.create_witness_term("witness_0", &a_ty);
    let witness1 = bridge.create_witness_term("witness_1", &a_ty);

    let body = make_eq(a_ty.clone(), Expr::bvar(0), Expr::bvar(1));

    let result = bridge.instantiate_body_with_terms(&body, &[0, 1], &[witness0, witness1]);
    assert!(
        result.is_some(),
        "multi-variable instantiation must return Some"
    );

    let witness0_expr = bridge.term_to_expr.get(&witness0).unwrap();
    let witness1_expr = bridge.term_to_expr.get(&witness1).unwrap();
    assert_ne!(
        witness0_expr, witness1_expr,
        "two witnesses should have distinct FVar expressions"
    );

    let inst = result.unwrap();
    let (eq_a_lhs, rhs) = match inst.kind() {
        ExprKind::App(f, a) => (f.as_ref(), a.as_ref()),
        other => panic!("Expected outermost App, got {:?}", other),
    };
    let lhs = match eq_a_lhs.kind() {
        ExprKind::App(_, lhs) => lhs.as_ref(),
        other => panic!("Expected inner App, got {:?}", other),
    };
    assert_eq!(lhs, witness0_expr, "BVar(0) should map to witness0");
    assert_eq!(rhs, witness1_expr, "BVar(1) should map to witness1");
}

/// Regression test for #2095: cache_term populates term_to_type for FVar
/// expressions when a LocalContext is provided via set_local_ctx.
#[test]
fn test_cache_term_fvar_type_with_local_ctx() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let mut ctx = LocalContext::new();
    let x_id = ctx.push(Name::from_string("x"), a_ty.clone(), BinderInfo::Default);
    let y_id = ctx.push(Name::from_string("y"), a_ty.clone(), BinderInfo::Default);
    bridge.set_local_ctx(ctx);

    let x_expr = Expr::fvar(x_id);
    let y_expr = Expr::fvar(y_id);
    let t_x = bridge.translate_term(&x_expr).expect("translate x");
    let t_y = bridge.translate_term(&y_expr).expect("translate y");

    let x_inferred = bridge
        .term_to_type
        .get(&t_x)
        .expect("term_to_type should contain type for FVar x when LocalContext is set");
    let y_inferred = bridge
        .term_to_type
        .get(&t_y)
        .expect("term_to_type should contain type for FVar y when LocalContext is set");

    assert_eq!(
        x_inferred, &a_ty,
        "inferred type for x should be A, got {x_inferred:?}"
    );
    assert_eq!(
        y_inferred, &a_ty,
        "inferred type for y should be A, got {y_inferred:?}"
    );
}

/// Regression test for #2095 (pre-fix behavior): term_to_type is NOT populated
/// for FVars when no LocalContext is set.
#[test]
fn test_cache_term_fvar_type_without_local_ctx() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let x_id = FVarId::new(999);
    let x_expr = Expr::fvar(x_id);
    let t_x = bridge.translate_term(&x_expr).expect("translate x");

    assert!(
        !bridge.term_to_type.contains_key(&t_x),
        "term_to_type should NOT contain type for FVar without LocalContext"
    );
}

/// Regression test for #2110: substitute_bvar recurses into Let expressions.
#[test]
fn test_substitute_bvar_into_let_body() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a_const = Expr::const_(Name::from_string("a"), vec![]);

    let let_expr = Expr::let_named(
        Name::from_string("x"),
        a_ty.clone(),
        Expr::bvar(0),
        Expr::bvar(1),
        false,
    );

    let result = bridge.substitute_bvar(&let_expr, 0, &a_const);

    match result.kind() {
        ExprKind::Let(name, ty, val, body, _) => {
            assert_eq!(name.to_string(), "x");
            assert!(
                matches!(ty.kind(), ExprKind::Const(n, _) if n.to_string() == "A"),
                "ty should remain A, got {:?}",
                ty.kind()
            );
            assert!(
                matches!(val.kind(), ExprKind::Const(n, _) if n.to_string() == "a"),
                "val BVar(0) should be replaced with 'a', got {:?}",
                val.kind()
            );
            assert!(
                matches!(body.kind(), ExprKind::Const(n, _) if n.to_string() == "a"),
                "body BVar(1) should be replaced with 'a' (at depth idx+1), got {:?}",
                body.kind()
            );
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

/// Regression test for #2110: substitute_bvar recurses into Proj expressions.
#[test]
fn test_substitute_bvar_into_proj() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a_const = Expr::const_(Name::from_string("a"), vec![]);
    let proj_expr = Expr::proj(Name::from_string("Foo"), 0, Expr::bvar(0));

    let result = bridge.substitute_bvar(&proj_expr, 0, &a_const);

    match result.kind() {
        ExprKind::Proj(name, idx, inner) => {
            assert_eq!(name.to_string(), "Foo");
            assert_eq!(*idx, 0);
            assert!(
                matches!(inner.kind(), ExprKind::Const(n, _) if n.to_string() == "a"),
                "Proj inner BVar(0) should be replaced with 'a', got {:?}",
                inner.kind()
            );
        }
        other => panic!("Expected Proj, got {:?}", other),
    }
}

/// Regression test for #2110: substitute_bvar recurses into MData expressions.
#[test]
fn test_substitute_bvar_into_mdata() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a_const = Expr::const_(Name::from_string("a"), vec![]);
    let metadata = vec![(Name::from_string("key"), MDataValue::Bool(true))];
    let mdata_expr = Expr::mdata(metadata, Expr::bvar(0));

    let result = bridge.substitute_bvar(&mdata_expr, 0, &a_const);

    match result.kind() {
        ExprKind::MData(md, inner) => {
            assert_eq!(md.len(), 1);
            assert!(
                matches!(inner.kind(), ExprKind::Const(n, _) if n.to_string() == "a"),
                "MData inner BVar(0) should be replaced with 'a', got {:?}",
                inner.kind()
            );
        }
        other => panic!("Expected MData, got {:?}", other),
    }
}

/// Regression test for #2110: substitute_bvar composes idx+1 correctly across
/// nested binders (Let + Lam).
#[test]
fn test_substitute_bvar_nested_let_lam_depth_composition() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a_const = Expr::const_(Name::from_string("a"), vec![]);

    let lam_inner = Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(2));

    let let_expr = Expr::let_named(
        Name::from_string("x"),
        a_ty.clone(),
        Expr::bvar(0),
        lam_inner,
        false,
    );

    let result = bridge.substitute_bvar(&let_expr, 0, &a_const);

    match result.kind() {
        ExprKind::Let(_name, _ty, val, body, _) => {
            assert!(
                matches!(val.kind(), ExprKind::Const(n, _) if n.to_string() == "a"),
                "val BVar(0) should be replaced with 'a', got {:?}",
                val.kind()
            );
            match body.kind() {
                ExprKind::Lam(_info, _lam_ty, lam_body) => {
                    assert!(
                        matches!(lam_body.kind(), ExprKind::Const(n, _) if n.to_string() == "a"),
                        "nested BVar(2) should be replaced with 'a' at composed depth, got {:?}",
                        lam_body.kind()
                    );
                }
                other => panic!("Expected Lam in Let body, got {:?}", other),
            }
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}
