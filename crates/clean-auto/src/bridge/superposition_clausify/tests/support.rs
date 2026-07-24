// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helpers for `superposition_clausify` test families.

use super::super::*;
use clean_kernel::{Declaration, Level, MDataValue};

pub(super) fn mk_eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs,
        ),
        rhs,
    )
}

pub(super) fn wrap_mdata(expr: Expr) -> Expr {
    let metadata = vec![(Name::from_string("simp"), MDataValue::Bool(true))];
    Expr::mdata(metadata, expr)
}

pub(super) fn mk_nat_env_with_test_consts() -> (Environment, Expr, Expr, Expr) {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["testA", "testB"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat_ty.clone(),
        })
        .expect("add decl");
    }
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    (env, nat_ty, a, b)
}
