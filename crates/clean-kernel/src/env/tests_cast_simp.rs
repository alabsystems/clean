// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::test_helpers::{assert_axiom, assert_const, expr_contains_const, pi_domain_at};
use super::*;
use crate::expr::BinderInfo;

fn pi_body_after(expr: &Expr, binders: usize) -> Option<&Expr> {
    let mut current = expr;
    for _ in 0..binders {
        match &current.kind {
            ExprKind::Pi(_, _, body) => current = body.as_ref(),
            _ => return None,
        }
    }
    Some(current)
}

fn app2_const(name: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string(name), vec![]), lhs),
        rhs,
    )
}

fn assert_cast_simp_constants(env: &Environment) {
    for name in [
        "Rat.ofInt",
        "Nat.cast_eq_prop",
        "Nat.cast_le_prop",
        "Nat.cast_lt_prop",
        "Int.cast_eq_prop",
        "Int.cast_le_prop",
        "Int.cast_lt_prop",
        "Rat.ofInt_add",
        "Rat.ofInt_mul",
    ] {
        assert_const(env, name);
    }
    assert_axiom(env, "Nat.cast_eq_prop");
    assert_axiom(env, "Int.cast_eq_prop");
    assert_axiom(env, "Rat.ofInt_add");
    assert_axiom(env, "Rat.ofInt_mul");
}

fn assert_type_inference(env: &Environment, names: &[&str]) {
    use crate::tc::TypeChecker;

    let tc = TypeChecker::new(env);
    for name in names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist after init_cast_simp_lemmas"));
        let _ = tc
            .infer_type(&info.type_)
            .unwrap_or_else(|e| panic!("{name} type should infer cleanly: {e}"));
    }
}

fn assert_int_of_nat_add_orientation(env: &Environment) {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    let int_of_nat = Name::from_string("Int.ofNat");
    let info = env
        .get_const(&Name::from_string("Int.ofNat_add"))
        .expect("Int.ofNat_add should exist");
    let expected_body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                int.clone(),
            ),
            Expr::app(
                Expr::const_(int_of_nat.clone(), vec![]),
                app2_const("Nat.add", Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
        app2_const(
            "Int.add",
            Expr::app(Expr::const_(int_of_nat, vec![]), Expr::bvar(1)),
            Expr::app(
                Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                Expr::bvar(0),
            ),
        ),
    );

    assert_eq!(pi_domain_at(&info.type_, 0), Some(&nat));
    assert_eq!(pi_domain_at(&info.type_, 1), Some(&nat));
    assert_eq!(pi_body_after(&info.type_, 2), Some(&expected_body));
}

fn assert_rat_of_int_inventory(env: &Environment) {
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let rat_info = env
        .get_const(&Name::from_string("Rat.ofInt_add"))
        .expect("Rat.ofInt_add should exist");
    let rat_of_int = env
        .get_const(&Name::from_string("Rat.ofInt"))
        .expect("Rat.ofInt should exist");

    assert_eq!(pi_domain_at(&rat_info.type_, 0), Some(&int));
    assert_eq!(pi_domain_at(&rat_info.type_, 1), Some(&int));
    assert_eq!(
        pi_body_after(&rat_info.type_, 2)
            .map(|body| expr_contains_const(body, &Name::from_string("Rat.ofInt"))),
        Some(true)
    );
    assert_eq!(pi_domain_at(&rat_of_int.type_, 0), Some(&int));
    assert_eq!(rat_of_int.type_, Expr::pi(BinderInfo::Default, int, rat));
}

#[test]
fn test_init_cast_simp_lemmas_registers_expected_constants() {
    let mut env = Environment::new();
    env.init_cast_simp_lemmas().unwrap();
    assert_cast_simp_constants(&env);
}

#[test]
fn test_cast_simp_lemmas_type_check_and_int_of_nat_add_pushes_cast_outward() {
    let mut env = Environment::new();
    env.init_cast_simp_lemmas().unwrap();

    assert_type_inference(
        &env,
        &[
            "Rat.ofInt",
            "Nat.cast_eq_prop",
            "Nat.cast_le_prop",
            "Nat.cast_lt_prop",
            "Int.cast_eq_prop",
            "Int.cast_le_prop",
            "Int.cast_lt_prop",
            "Rat.ofInt_add",
            "Rat.ofInt_mul",
            "Int.ofNat_add",
            "Int.ofNat_mul",
        ],
    );
    assert_int_of_nat_add_orientation(&env);
    assert_rat_of_int_inventory(&env);
}

#[test]
fn test_cast_simp_lemmas_idempotent() {
    let mut env = Environment::new();
    env.init_cast_simp_lemmas().unwrap();
    env.init_cast_simp_lemmas().unwrap();
    env.init_cast_simp_lemmas().unwrap();

    for name in [
        "Rat.ofInt",
        "Nat.cast_eq_prop",
        "Int.cast_eq_prop",
        "Rat.ofInt_add",
    ] {
        assert_const(&env, name);
    }
}
