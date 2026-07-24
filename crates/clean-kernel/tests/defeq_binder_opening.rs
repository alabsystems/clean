// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};

#[test]
fn pi_defeq_opens_binder_for_cast_k_reduction() {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    let tc = TypeChecker::new(&env);

    let prop = Expr::prop();
    let level_one = Level::succ(Level::zero()); // Sort 1
    let sort_one = Expr::sort(level_one.clone());
    let eq_prop_const = Expr::const_(Name::from_string("Eq"), vec![level_one.clone()]);
    let eq_sort_one_const = Expr::const_(
        Name::from_string("Eq"),
        vec![Level::succ(level_one.clone())],
    );
    let cast_const = Expr::const_(Name::from_string("cast"), vec![level_one]);

    // h : Eq (Sort 1) Prop Prop
    let h_ty = Expr::app(
        Expr::app(Expr::app(eq_sort_one_const, sort_one), prop.clone()),
        prop.clone(),
    );

    // Under binders Pi (x : Prop), Pi (h : Eq (Sort 1) Prop Prop), ...
    // x = BVar(1), h = BVar(0)
    let cast_h_x = Expr::app(
        Expr::app(
            Expr::app(Expr::app(cast_const, prop.clone()), prop.clone()),
            Expr::bvar(0),
        ),
        Expr::bvar(1),
    );

    let lhs_body = Expr::app(
        Expr::app(Expr::app(eq_prop_const.clone(), prop.clone()), cast_h_x),
        Expr::bvar(1),
    );
    let rhs_body = Expr::app(
        Expr::app(Expr::app(eq_prop_const, prop.clone()), Expr::bvar(1)),
        Expr::bvar(1),
    );

    let lhs = Expr::pi(
        BinderInfo::Default,
        prop.clone(),
        Expr::pi(BinderInfo::Default, h_ty.clone(), lhs_body),
    );
    let rhs = Expr::pi(
        BinderInfo::Default,
        prop.clone(),
        Expr::pi(BinderInfo::Default, h_ty, rhs_body),
    );

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "Pi binder comparison should open binders so cast h x reduces to x under K"
    );
}

#[test]
fn init_heq_registers_eq_of_heq_as_theorem() {
    let mut env = Environment::new();
    env.init_heq().expect("init_heq");

    let eq_of_heq = env
        .get_const(&Name::from_string("eq_of_heq"))
        .expect("eq_of_heq should exist");

    assert!(
        eq_of_heq.value.is_some(),
        "eq_of_heq should be a theorem with a proof term"
    );
    assert!(
        !eq_of_heq.is_reducible,
        "eq_of_heq theorem should be non-reducible"
    );
}
