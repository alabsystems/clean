// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for ControlStack (elab_do_stack.rs).

use super::*;
use crate::infer::ElabCtx;
use clean_kernel::{Environment, ExprKind};
use std::collections::HashSet;

fn dummy_monad_info() -> DoMonadInfo {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let m = Expr::const_(Name::from_string("IO"), vec![]);
    let cached_punit = Expr::const_(Name::from_string("PUnit"), vec![u.clone()]);
    let cached_punit_unit = Expr::const_(Name::from_string("PUnit.unit"), vec![u.clone()]);
    DoMonadInfo {
        m,
        u,
        v,
        cached_punit,
        cached_punit_unit,
    }
}

#[test]
fn test_build_empty_stack() {
    let info = ControlInfo::pure();
    let stack = ControlStack::build(&info, None, None).expect("build empty stack");
    assert_eq!(stack.layers.len(), 1);
    assert!(!stack.has_transformers());
    assert!(
        stack.return_layer_idx.is_none(),
        "pure ControlStack should have no return_layer_idx"
    );
    assert!(
        stack.break_layer_idx.is_none(),
        "pure ControlStack should have no break_layer_idx"
    );
    assert!(
        stack.continue_layer_idx.is_none(),
        "pure ControlStack should have no continue_layer_idx"
    );
}

#[test]
fn test_build_break_only() {
    let info = ControlInfo {
        breaks: true,
        ..ControlInfo::pure()
    };
    let stack = ControlStack::build(&info, None, None).expect("build break stack");
    assert_eq!(stack.layers.len(), 2);
    assert!(stack.has_transformers());
    assert!(matches!(stack.layers[1], ControlStackLayer::Break));
    assert_eq!(stack.break_layer_idx, Some(1));
}

#[test]
fn test_build_full_stack() {
    let mut reassigns = HashSet::new();
    reassigns.insert("x".to_string());
    let info = ControlInfo {
        breaks: true,
        continues: true,
        returns_early: true,
        num_regular_exits: 1,
        reassigns,
    };
    let return_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let state_sigma = Expr::const_(Name::from_string("Nat"), vec![]);
    let stack =
        ControlStack::build(&info, Some(return_ty), Some(state_sigma)).expect("build full stack");

    // Base + EarlyReturn + State + Break + Continue = 5 layers
    assert_eq!(stack.layers.len(), 5);
    assert!(matches!(stack.layers[0], ControlStackLayer::Base));
    assert!(matches!(
        stack.layers[1],
        ControlStackLayer::EarlyReturn { .. }
    ));
    assert!(matches!(stack.layers[2], ControlStackLayer::State { .. }));
    assert!(matches!(stack.layers[3], ControlStackLayer::Break));
    assert!(matches!(stack.layers[4], ControlStackLayer::Continue));

    assert_eq!(stack.return_layer_idx, Some(1));
    assert_eq!(stack.state_layer_idx, Some(2));
    assert_eq!(stack.break_layer_idx, Some(3));
    assert_eq!(stack.continue_layer_idx, Some(4));
}

#[test]
fn test_compute_wrapped_monad_no_transformers() {
    let info = ControlInfo::pure();
    let stack = ControlStack::build(&info, None, None).expect("build empty stack");
    let mi = dummy_monad_info();
    let wrapped = stack.compute_wrapped_monad(&mi);
    // Should just be the base monad
    assert_eq!(format!("{wrapped:?}"), format!("{:?}", mi.m));
}

#[test]
fn test_compute_wrapped_monad_with_break() {
    let info = ControlInfo {
        breaks: true,
        ..ControlInfo::pure()
    };
    let stack = ControlStack::build(&info, None, None).expect("build break stack");
    let mi = dummy_monad_info();
    let wrapped = stack.compute_wrapped_monad(&mi);
    // Should be OptionT IO — an App(App(OptionT, IO))... but let's just
    // verify it's not the bare monad
    assert_ne!(format!("{wrapped:?}"), format!("{:?}", mi.m));
}

#[test]
fn test_sigma_type_single_var() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let sigma =
        build_sigma_type(&ctx, &[("x".to_string(), nat_ty.clone())]).expect("single state type");
    assert_eq!(format!("{sigma:?}"), format!("{nat_ty:?}"));
}

#[test]
fn test_sigma_type_multiple_vars() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let sigma = build_sigma_type(
        &ctx,
        &[("x".to_string(), nat_ty), ("y".to_string(), bool_ty)],
    )
    .expect("multi-state type");
    // Should be Prod Nat Bool (an App expression)
    let debug = format!("{sigma:?}");
    assert!(
        debug.contains("App"),
        "sigma should be a Prod App, got {debug}"
    );
}

#[test]
fn proposition_state_component_uses_type_zero_cumulativity() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let true_prop = Expr::const_(Name::from_string("True"), vec![]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let sigma = build_sigma_type(
        &ctx,
        &[("proof".to_string(), true_prop), ("n".to_string(), nat_ty)],
    )
    .expect("Prop is cumulative into Type 0 for product state");
    let ExprKind::App(head, _) = sigma.kind() else {
        panic!("expected applied Prod type, got {sigma:?}");
    };
    let ExprKind::App(prod, _) = head.kind() else {
        panic!("expected binary Prod type, got {head:?}");
    };
    let ExprKind::Const(name, levels) = prod.kind() else {
        panic!("expected Prod constant, got {prod:?}");
    };
    assert_eq!(name.to_string(), "Prod");
    assert_eq!(levels.as_slice(), &[Level::zero(), Level::zero()]);
    let _ = ctx
        .infer_type(&sigma)
        .expect("kernel accepts cumulative proposition component");
}

#[test]
fn test_unwrap_sequence_ordering() {
    let mut reassigns = HashSet::new();
    reassigns.insert("x".to_string());
    let info = ControlInfo {
        breaks: true,
        returns_early: true,
        reassigns,
        ..ControlInfo::pure()
    };
    let return_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let state_sigma = Expr::const_(Name::from_string("Nat"), vec![]);
    let stack =
        ControlStack::build(&info, Some(return_ty), Some(state_sigma)).expect("build unwrap stack");
    let mi = dummy_monad_info();
    let steps = stack.unwrap_sequence(&mi);

    // Unwrap order: outermost first → Break, State, EarlyReturn
    assert_eq!(steps.len(), 3);
    assert!(matches!(steps[0].kind, UnwrapKind::Break));
    assert!(matches!(steps[1].kind, UnwrapKind::State { .. }));
    assert!(matches!(steps[2].kind, UnwrapKind::EarlyReturn { .. }));
}

#[test]
fn test_build_sigma_value_empty_is_rejected() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let result = build_sigma_value(&ctx, &[]);
    assert!(
        matches!(result, Err(ElabError::InternalInvariant(_))),
        "empty product values require an explicit unit representation, got {result:?}"
    );
}

#[test]
fn test_build_sigma_value_single() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let val = Expr::const_(Name::from_string("myVal"), vec![]);
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let vars = vec![("x".to_string(), val.clone(), ty)];
    let result = build_sigma_value(&ctx, &vars).expect("single state value");
    // Single var: result should be the value directly
    match result.kind() {
        ExprKind::Const(n, _) => assert_eq!(n.to_string(), "myVal"),
        _ => panic!("expected myVal for single var, got {result:?}"),
    }
}

#[test]
fn test_build_sigma_value_multiple() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let v1 = Expr::const_(Name::from_string("val1"), vec![]);
    let v2 = Expr::const_(Name::from_string("val2"), vec![]);
    let t1 = Expr::const_(Name::from_string("Nat"), vec![]);
    let t2 = Expr::const_(Name::from_string("Bool"), vec![]);
    let vars = vec![("x".to_string(), v1, t1), ("y".to_string(), v2, t2)];
    let result = build_sigma_value(&ctx, &vars).expect("multi-state value");
    // Two vars: head should be Prod.mk (applied to type args and values)
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(n, _) => assert_eq!(
            n.to_string(),
            "Prod.mk",
            "expected Prod.mk head for multi-var sigma value"
        ),
        _ => panic!("expected Const(Prod.mk, _) for multi-var, got {head:?}"),
    }
    // Should have 4 args: α, β, val1, val2
    let args = result.get_app_args();
    assert_eq!(args.len(), 4, "Prod.mk should have 4 args (α, β, v1, v2)");
}

#[test]
fn test_destructure_sigma_single() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let tuple = Expr::const_(Name::from_string("myTuple"), vec![]);
    let vars = [(
        "x".to_string(),
        Expr::const_(Name::from_string("Nat"), vec![]),
    )];
    let result = destructure_sigma(&ctx, &vars, tuple).expect("single state projection");
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].0, "x");
    match result[0].1.kind() {
        ExprKind::Const(n, _) => assert_eq!(n.to_string(), "myTuple"),
        _ => panic!("single var should be the tuple itself"),
    }
}

#[test]
fn test_destructure_sigma_multiple() {
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    let tuple = Expr::const_(Name::from_string("myTuple"), vec![]);
    let vars = [
        (
            "x".to_string(),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
        (
            "y".to_string(),
            Expr::const_(Name::from_string("Bool"), vec![]),
        ),
    ];
    let result = destructure_sigma(&ctx, &vars, tuple).expect("multi-state projections");
    assert_eq!(result.len(), 2);
    assert_eq!(result[0].0, "x");
    assert_eq!(result[1].0, "y");
    // First projection should use Prod.fst
    let head0 = result[0].1.get_app_fn();
    match head0.kind() {
        ExprKind::Const(n, _) => {
            assert_eq!(n.to_string(), "Prod.fst", "expected Prod.fst for first var")
        }
        _ => panic!("expected Const(Prod.fst, _) for first var, got {head0:?}"),
    }
}

#[test]
fn heterogeneous_three_field_state_round_trips_with_exact_universes() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);

    // Three mutable-state fields in Type 0, Type 1, and Type 2.
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

    let sigma = build_sigma_type(&ctx, &state_types).expect("heterogeneous state type");
    let initial = build_sigma_value(
        &ctx,
        &[
            ("x".to_string(), Expr::fvar(x), nat_ty.clone()),
            ("y".to_string(), Expr::fvar(y), type_0.clone()),
            ("z".to_string(), Expr::fvar(z), type_1.clone()),
        ],
    )
    .expect("heterogeneous state value");
    let initial_ty = ctx
        .infer_type(&initial)
        .expect("kernel infers packed heterogeneous state");
    assert!(ctx.is_def_eq(&initial_ty, &sigma));

    // The outer right component contains Type 1/2 state, so its universe must
    // not collapse to zero. The inner product must carry levels 1 and 2.
    let ExprKind::App(outer_head, _) = sigma.kind() else {
        panic!("expected outer Prod application, got {sigma:?}");
    };
    let ExprKind::App(outer_const, _) = outer_head.kind() else {
        panic!("expected applied outer Prod, got {outer_head:?}");
    };
    let ExprKind::Const(name, outer_levels) = outer_const.kind() else {
        panic!("expected outer Prod constant, got {outer_const:?}");
    };
    assert_eq!(name.to_string(), "Prod");
    assert_eq!(outer_levels[0], Level::zero());
    assert_ne!(outer_levels[1], Level::zero());

    let projected =
        destructure_sigma(&ctx, &state_types, initial).expect("destructure heterogeneous state");
    for ((_, projection), (_, expected_ty)) in projected.iter().zip(&state_types) {
        let projection_ty = ctx
            .infer_type(projection)
            .expect("kernel infers exact product projection");
        assert!(ctx.is_def_eq(&projection_ty, expected_ty));
    }

    // Simulate reassignment of every field, repack the projections' exact
    // types, and ask the kernel to validate the full round trip.
    let reassigned = build_sigma_value(
        &ctx,
        &[
            (
                "x".to_string(),
                Expr::const_(Name::from_string("Nat.zero"), vec![]),
                nat_ty,
            ),
            (
                "y".to_string(),
                Expr::const_(Name::from_string("Nat"), vec![]),
                type_0,
            ),
            ("z".to_string(), Expr::type_(), type_1),
        ],
    )
    .expect("repack reassigned heterogeneous state");
    let reassigned_ty = ctx
        .infer_type(&reassigned)
        .expect("kernel checks reassigned heterogeneous state");
    assert!(ctx.is_def_eq(&reassigned_ty, &sigma));
}

#[test]
fn test_mk_option_t_fail() {
    let info = ControlInfo {
        breaks: true,
        ..ControlInfo::pure()
    };
    let stack = ControlStack::build(&info, None, None).expect("build break stack");
    let mi = dummy_monad_info();
    let alpha = Expr::const_(Name::from_string("Nat"), vec![]);
    let break_idx = stack.break_layer_idx.expect("break layer should exist");
    let fail_expr = stack.mk_option_t_fail(break_idx, alpha, &mi);
    let debug = format!("{fail_expr:?}");
    assert!(debug.contains("App"), "fail should be an App expression");
}
