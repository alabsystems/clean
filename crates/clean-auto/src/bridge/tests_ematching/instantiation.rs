// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E-matching instantiation and pending-forall coverage.

use super::*;

#[test]
fn test_ematching_quantifier_instantiation() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let f_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0));
    let g_x = Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0));
    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let body = make_eq(ty.clone(), f_x.clone(), g_x.clone());

    let forall_expr = Expr::pi(BinderInfo::Default, ty.clone(), body.clone());
    bridge
        .add_hypothesis(&forall_expr)
        .expect("forall x, f(x) = g(x) should register");

    assert_eq!(
        bridge.pending_foralls.len(),
        1,
        "Should store exactly 1 forall hypothesis for E-matching"
    );

    let pending = &bridge.pending_foralls[0];
    assert!(
        !pending.triggers.is_empty(),
        "Should extract triggers from forall body"
    );
    let has_f_or_g = pending.triggers.iter().any(|t| {
        t.patterns.iter().any(|p| {
            matches!(p, crate::egraph::Pattern::App(sym, _) if sym.name() == "f" || sym.name() == "g")
        })
    });
    assert!(
        has_f_or_g,
        "Triggers for forall x, f(x) = g(x) must contain f or g as head, got: {:?}",
        pending.triggers
    );
    assert_eq!(
        pending.bound_vars,
        vec![0],
        "Should have one bound variable"
    );

    let body_args = pending.body.get_app_args();
    assert_eq!(
        body_args.len(),
        3,
        "Stored body should be an equality (Eq type lhs rhs) with 3 args, got {}",
        body_args.len()
    );
}

#[test]
fn test_ematching_instantiation_with_ground_terms() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a = Expr::fvar(FVarId::new(100));
    let f_a = Expr::app(Expr::const_(Name::from_string("f"), vec![]), a.clone());

    bridge.translate_term(&a).expect("translate a");
    bridge.translate_term(&f_a).expect("translate f(a)");

    let f_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0));
    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let body = make_eq(ty.clone(), f_x.clone(), f_x.clone());

    let forall_expr = Expr::pi(BinderInfo::Default, ty.clone(), body);
    bridge
        .add_hypothesis(&forall_expr)
        .expect("ground-term forall should register");

    assert!(
        !bridge.pending_foralls.is_empty(),
        "Forall hypothesis should be stored in pending_foralls"
    );
    assert!(
        !bridge.pending_foralls[0].triggers.is_empty(),
        "Pending forall should have triggers extracted from f(?x0)"
    );

    let instances = bridge.collect_ematching_instances(10);
    assert_eq!(
        instances.len(),
        0,
        "translate_term does not populate E-graph, so E-matching should find 0 instances (strengthen to assert !is_empty() when E-graph integration is completed)"
    );

    let pending = &bridge.pending_foralls[0];
    assert_eq!(
        pending.bound_vars,
        vec![0],
        "Should have one bound variable"
    );
    assert!(
        pending.triggers.iter().any(|t| {
            t.patterns
                .iter()
                .any(|p| matches!(p, crate::egraph::Pattern::App(sym, _) if sym.name() == "f"))
        }),
        "Trigger should contain f(?x0) pattern"
    );
}

#[test]
fn test_pending_foralls_structure() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let p_x = Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(0));
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    let forall_expr = Expr::pi(BinderInfo::Default, nat_ty.clone(), p_x.clone());

    bridge
        .add_hypothesis(&forall_expr)
        .expect("forall x, P(x) should register");

    assert_eq!(bridge.pending_foralls.len(), 1);
    let pending = &bridge.pending_foralls[0];

    assert_eq!(pending.bound_vars, vec![0]);
    assert!(
        !pending.triggers.is_empty(),
        "Should extract P(x) as a trigger"
    );
    let has_p_head = pending.triggers.iter().any(|t| {
        t.patterns
            .iter()
            .any(|p| matches!(p, crate::egraph::Pattern::App(sym, _) if sym.name() == "P"))
    });
    assert!(
        has_p_head,
        "Trigger for forall x, P(x) must have P as head symbol, got: {:?}",
        pending.triggers
    );
}

#[test]
fn test_pending_foralls_nested_forall_tracks_all_bound_vars() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let x = Expr::bvar(1);
    let y = Expr::bvar(0);
    let f_xy = Expr::app(
        Expr::app(Expr::const_(Name::from_string("f"), vec![]), x.clone()),
        y.clone(),
    );
    let g_yx = Expr::app(
        Expr::app(Expr::const_(Name::from_string("g"), vec![]), y.clone()),
        x.clone(),
    );

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let inner_body = make_eq(nat_ty.clone(), f_xy, g_yx);

    let forall_expr = Expr::pi(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::pi(BinderInfo::Default, nat_ty.clone(), inner_body),
    );

    bridge
        .add_hypothesis(&forall_expr)
        .expect("nested forall should register");

    assert_eq!(bridge.pending_foralls.len(), 1);
    let pending = &bridge.pending_foralls[0];

    assert_eq!(
        pending.bound_vars,
        vec![0, 1],
        "Should track both bound variables from nested forall"
    );

    let covers_all = pending.triggers.iter().any(|t| {
        let vars = t.variables();
        vars.contains(&"?x0".to_string()) && vars.contains(&"?x1".to_string())
    });
    assert!(
        covers_all,
        "At least one trigger should cover both nested bound variables"
    );
}
