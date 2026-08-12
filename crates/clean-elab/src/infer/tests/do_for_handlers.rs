// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct helper tests for `elab_do_for_handlers.rs`.
//!
//! These pin the loop-accumulator helper behavior that the larger
//! `do_control_flow` tests only exercise indirectly.

use super::*;

fn expr_contains_const(expr: &Expr, name: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(n, _) => n.to_string() == name,
        ExprKind::App(f, a) => expr_contains_const(f, name) || expr_contains_const(a, name),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, name) || expr_contains_const(body, name)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, name)
                || expr_contains_const(val, name)
                || expr_contains_const(body, name)
        }
        _ => false,
    }
}

#[test]
fn test_build_loop_acc_value_without_return_uses_raw_accumulator() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let sigma = Expr::const_(Name::from_string("PUnit"), vec![]);
    let acc_fvar = ctx.push_local("__do_acc".to_string(), sigma.clone());

    ctx.do_loop_ctx = Some(DoLoopContext {
        sigma,
        acc_fvar,
        u_level: Level::zero(),
        mut_vars: vec![],
        return_type: None,
    });

    let acc_value = ctx.build_loop_acc_value().expect("raw loop accumulator");
    assert!(
        matches!(acc_value.kind(), ExprKind::FVar(id) if *id == acc_fvar),
        "loop accumulator without return/mut vars should stay as the raw fvar, got {acc_value:?}"
    );
}

#[test]
fn test_build_loop_acc_value_with_return_wraps_option_none() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let sigma = Expr::const_(Name::from_string("PUnit"), vec![]);
    let acc_fvar = ctx.push_local("__do_acc".to_string(), sigma.clone());

    ctx.do_loop_ctx = Some(DoLoopContext {
        sigma,
        acc_fvar,
        u_level: Level::zero(),
        mut_vars: vec![],
        return_type: Some(Expr::const_(Name::from_string("Nat"), vec![])),
    });

    let acc_value = ctx.build_loop_acc_value().expect("return loop accumulator");
    assert!(
        expr_contains_const(&acc_value, "Option.none"),
        "return-aware loop accumulator should prepend Option.none, got {acc_value:?}"
    );
    assert!(
        !expr_contains_const(&acc_value, "Prod.mk"),
        "return-only loop accumulator should not allocate a product, got {acc_value:?}"
    );
}

#[test]
fn test_build_loop_acc_value_with_return_and_mut_vars_builds_prod() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let sigma = Expr::const_(Name::from_string("PUnit"), vec![]);
    let acc_fvar = ctx.push_local("__do_acc".to_string(), sigma.clone());
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let state_fvar = ctx.push_local("state".to_string(), nat_ty.clone());

    ctx.do_loop_ctx = Some(DoLoopContext {
        sigma,
        acc_fvar,
        u_level: Level::zero(),
        mut_vars: vec![("state".to_string(), state_fvar, nat_ty.clone())],
        return_type: Some(nat_ty),
    });

    let acc_value = ctx
        .build_loop_acc_value()
        .expect("return and mutable loop accumulator");
    assert!(
        expr_contains_const(&acc_value, "Option.none"),
        "return-aware loop accumulator should include the Option.none component, got {acc_value:?}"
    );
    assert!(
        expr_contains_const(&acc_value, "Prod.mk"),
        "loop accumulator with mut vars should build a product payload, got {acc_value:?}"
    );
}

#[test]
fn test_is_loop_mut_var_reads_active_loop_bindings() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let sigma = Expr::const_(Name::from_string("PUnit"), vec![]);
    let acc_fvar = ctx.push_local("__do_acc".to_string(), sigma.clone());
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let counter_fvar = ctx.push_local("counter".to_string(), nat_ty.clone());

    ctx.do_loop_ctx = Some(DoLoopContext {
        sigma,
        acc_fvar,
        u_level: Level::zero(),
        mut_vars: vec![("counter".to_string(), counter_fvar, nat_ty)],
        return_type: None,
    });

    assert!(ctx.is_loop_mut_var("counter"));
    assert!(!ctx.is_loop_mut_var("missing"));
}

#[test]
fn test_polymorphic_three_mut_do_state_projects_reassigns_and_kernel_checks() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let type_0 = Expr::type_();
    let type_1 = Expr::sort(Level::succ(Level::succ(Level::zero())));

    let x = ctx.push_local("x".to_string(), nat_ty.clone());
    let y = ctx.push_local("y".to_string(), type_0.clone());
    let z = ctx.push_local("z".to_string(), type_1.clone());
    let state_types = vec![
        ("x".to_string(), nat_ty.clone()),
        ("y".to_string(), type_0.clone()),
        ("z".to_string(), type_1.clone()),
    ];
    let sigma = elab_do_prod::build_sigma_type(&ctx, &state_types)
        .expect("polymorphic do-state product type");
    let acc_fvar = ctx.push_local("__do_acc".to_string(), sigma.clone());
    ctx.do_loop_ctx = Some(DoLoopContext {
        sigma: sigma.clone(),
        acc_fvar,
        u_level: Level::succ(Level::succ(Level::zero())),
        mut_vars: vec![
            ("x".to_string(), x, nat_ty.clone()),
            ("y".to_string(), y, type_0.clone()),
            ("z".to_string(), z, type_1.clone()),
        ],
        return_type: None,
    });

    let packed = ctx
        .build_loop_acc_value()
        .expect("pack polymorphic do state");
    let packed_ty = ctx
        .infer_type(&packed)
        .expect("kernel checks packed polymorphic do state");
    assert!(ctx.is_def_eq(&packed_ty, &sigma));

    let mut_info = vec![
        ("x".to_string(), x, nat_ty.clone()),
        ("y".to_string(), y, type_0.clone()),
        ("z".to_string(), z, type_1.clone()),
    ];
    let projections = ctx
        .destructure_acc_from_expr(packed, &mut_info)
        .expect("project polymorphic do state");
    for ((_, _, expected_ty), (_, _, _, projection)) in mut_info.iter().zip(&projections) {
        let actual_ty = ctx
            .infer_type(projection)
            .expect("kernel checks exact do-state projection");
        assert!(ctx.is_def_eq(&actual_ty, expected_ty));
    }

    // Model a reassignment round: the active do context now points at fresh
    // values of the same three heterogeneous types. Repacking must retain the
    // original sigma type exactly.
    let x2 = ctx.push_local("x_reassigned".to_string(), nat_ty.clone());
    let y2 = ctx.push_local("y_reassigned".to_string(), type_0.clone());
    let z2 = ctx.push_local("z_reassigned".to_string(), type_1.clone());
    ctx.do_loop_ctx
        .as_mut()
        .expect("active do loop context")
        .mut_vars = vec![
        ("x".to_string(), x2, nat_ty),
        ("y".to_string(), y2, type_0),
        ("z".to_string(), z2, type_1),
    ];
    let reassigned = ctx
        .build_loop_acc_value()
        .expect("repack reassigned polymorphic do state");
    let reassigned_ty = ctx
        .infer_type(&reassigned)
        .expect("kernel checks reassigned polymorphic do state");
    assert!(ctx.is_def_eq(&reassigned_ty, &sigma));
}
