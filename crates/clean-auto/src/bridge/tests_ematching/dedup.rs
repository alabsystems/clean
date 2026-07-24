// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E-matching deduplication coverage.

use super::*;

#[test]
fn test_ematching_deduplication() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a = Expr::fvar(FVarId::new(100));
    let b = Expr::fvar(FVarId::new(101));

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a_eq_a = make_eq(ty.clone(), a.clone(), a.clone());
    let b_eq_b = make_eq(ty.clone(), b.clone(), b.clone());

    bridge
        .add_hypothesis(&a_eq_a)
        .expect("reflexive equality for a should register");
    bridge
        .add_hypothesis(&b_eq_b)
        .expect("reflexive equality for b should register");

    let f_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0));
    let body = make_eq(ty.clone(), f_x.clone(), f_x.clone());

    let forall_expr = Expr::pi(BinderInfo::Default, ty.clone(), body);
    bridge
        .add_hypothesis(&forall_expr)
        .expect("dedup forall should register");

    let instances1 = bridge.collect_ematching_instances(100);
    let count1 = instances1.len();
    let instances2 = bridge.collect_ematching_instances(100);

    assert!(
        !bridge.pending_foralls.is_empty(),
        "Forall hypothesis forall x, f(x) = f(x) should be stored in pending_foralls"
    );
    assert!(
        !bridge.pending_foralls[0].triggers.is_empty(),
        "Pending forall should have triggers extracted from f(?x0)"
    );
    assert_eq!(
        instances2.len(),
        0,
        "Second collection should return 0 new instances (all seen in round 1 which had {count1})"
    );
}

#[test]
fn test_ematching_dedup_same_instance_multiple_triggers() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a = Expr::fvar(FVarId::new(100));
    let f_a = Expr::app(Expr::const_(Name::from_string("f"), vec![]), a.clone());
    let g_f_a = Expr::app(Expr::const_(Name::from_string("g"), vec![]), f_a.clone());

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let eq1 = make_eq(ty.clone(), f_a.clone(), f_a.clone());
    let eq2 = make_eq(ty.clone(), g_f_a.clone(), g_f_a.clone());
    bridge
        .add_hypothesis(&eq1)
        .expect("f(a) reflexive equality should register");
    bridge
        .add_hypothesis(&eq2)
        .expect("g(f(a)) reflexive equality should register");

    let p_x_x = Expr::app(
        Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(0)),
        Expr::bvar(0),
    );

    let forall_expr = Expr::pi(BinderInfo::Default, ty.clone(), p_x_x);
    bridge
        .add_hypothesis(&forall_expr)
        .expect("P(x, x) forall should register");

    let instances = bridge.collect_ematching_instances(100);

    assert!(
        !bridge.pending_foralls.is_empty(),
        "forall x : A, P(x,x) should be stored as a pending forall"
    );
    assert!(
        !bridge
            .pending_foralls
            .last()
            .expect("pending forall should be present")
            .triggers
            .is_empty(),
        "Pending forall forall x, P(x,x) should have triggers"
    );
    assert_eq!(
        instances.len(),
        0,
        "E-matching should find 0 instances: P(x,x) trigger needs ground P(...) terms in E-graph, but only f(...) and g(...) were added"
    );

    let pending = bridge
        .pending_foralls
        .last()
        .expect("pending forall should still be present");
    assert_eq!(
        pending.bound_vars,
        vec![0],
        "P(x,x) forall should have bound_vars [0]"
    );
    let has_p_trigger = pending.triggers.iter().any(|t| {
        t.patterns
            .iter()
            .any(|p| matches!(p, crate::egraph::Pattern::App(sym, _) if sym.name() == "P"))
    });
    assert!(
        has_p_trigger,
        "Trigger for forall x, P(x,x) should contain P(?x0, ?x0) pattern, got: {:?}",
        pending.triggers
    );

    let instances2 = bridge.collect_ematching_instances(100);
    assert_eq!(
        instances2.len(),
        0,
        "Second E-matching round should also find 0 instances"
    );
}
