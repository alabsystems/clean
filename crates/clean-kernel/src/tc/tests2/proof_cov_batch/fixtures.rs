// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::env::Declaration;

pub(super) fn fixture_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

pub(super) fn fixture_env() -> Environment {
    let mut env = Environment::new();
    let t_type = fixture_const("T");
    let u_type = fixture_const("U");
    let alias_prop = fixture_const("AliasProp");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("T"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("fixture env: add T : Type");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("U"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("fixture env: add U : Type");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("t"),
        level_params: vec![],
        type_: t_type.clone(),
    })
    .expect("fixture env: add t : T");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, t_type, u_type),
    })
    .expect("fixture env: add f : T -> U");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("fixture env: add p : Prop");
    env.add_decl(Declaration::Definition {
        name: Name::from_string("AliasProp"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    })
    .expect("fixture env: add AliasProp := Prop");
    env.add_decl(Declaration::Definition {
        name: Name::from_string("id_alias"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, alias_prop.clone(), alias_prop.clone()),
        value: Expr::lam(BinderInfo::Default, alias_prop, Expr::bvar(0)),
        is_reducible: true,
    })
    .expect("fixture env: add id_alias : AliasProp -> AliasProp");

    env
}

pub(super) fn fixture_nat_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("fixture env: init Nat");
    env
}

pub(super) fn valid_lambda_expr() -> Expr {
    Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0))
}

pub(super) fn valid_lambda_type() -> Expr {
    Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop())
}

pub(super) fn valid_let_expr() -> Expr {
    Expr::let_named(
        Name::anon(),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
        false,
    )
}

pub(super) fn valid_ft_expr() -> Expr {
    Expr::app(fixture_const("f"), fixture_const("t"))
}

pub(super) fn valid_id_alias_expr() -> Expr {
    Expr::app(fixture_const("id_alias"), fixture_const("p"))
}

pub(super) fn alias_prop_type() -> Expr {
    fixture_const("AliasProp")
}

pub(super) fn u_type() -> Expr {
    fixture_const("U")
}

pub(super) fn nat_type() -> Expr {
    fixture_const("Nat")
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(super) fn invalid_type_mismatch_expr() -> Expr {
    Expr::app(fixture_const("f"), Expr::prop())
}

pub(super) fn invalid_not_a_function_expr() -> Expr {
    Expr::app(fixture_const("t"), fixture_const("t"))
}

fn nat_zero() -> Expr {
    fixture_const("Nat.zero")
}

fn nat_succ(expr: Expr) -> Expr {
    Expr::app(fixture_const("Nat.succ"), expr)
}

fn nat_rec_const() -> Expr {
    Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    )
}

fn nat_rec_motive() -> Expr {
    let nat = nat_type();
    Expr::lam(BinderInfo::Default, nat.clone(), nat)
}

fn nat_rec_succ_case() -> Expr {
    let nat = nat_type();
    Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat, nat_succ(Expr::bvar(0))),
    )
}

fn nat_rec_major() -> Expr {
    nat_succ(nat_zero())
}

pub(super) fn nat_rec_inferred_type() -> Expr {
    Expr::app(nat_rec_motive(), nat_rec_major())
}

pub(super) fn valid_nat_rec_expr() -> Expr {
    let motive = nat_rec_motive();
    let zero_case = nat_zero();
    let succ_case = nat_rec_succ_case();
    let major = nat_rec_major();

    Expr::app(
        Expr::app(
            Expr::app(Expr::app(nat_rec_const(), motive), zero_case),
            succ_case,
        ),
        major,
    )
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(super) fn invalid_nat_rec_zero_case_expr() -> Expr {
    let motive = nat_rec_motive();
    let succ_case = nat_rec_succ_case();
    let major = nat_rec_major();

    Expr::app(
        Expr::app(
            Expr::app(Expr::app(nat_rec_const(), motive), Expr::prop()),
            succ_case,
        ),
        major,
    )
}
