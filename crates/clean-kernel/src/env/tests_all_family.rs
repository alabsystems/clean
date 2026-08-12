// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the generic `C.All` family generator (rung P4,
//! `designs/2026-08-06-deep-induction-scheme-all.md`). Acceptance = the
//! generated declaration passes the full checked `add_inductive`.

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Register a `List`-shaped container: `MyList.{u} : Type u → Type u`.
fn add_mylist(env: &mut Environment) {
    let u = Name::from_string("u");
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));
    let list_at = |a: Expr| {
        Expr::app(
            Expr::const_(Name::from_string("MyList"), vec![Level::param(u.clone())]),
            a,
        )
    };
    let nil_ty = Expr::pi(BinderInfo::Implicit, sort_u.clone(), list_at(Expr::bvar(0)));
    let cons_ty = Expr::pi(
        BinderInfo::Implicit,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(
                BinderInfo::Default,
                list_at(Expr::bvar(1)),
                list_at(Expr::bvar(2)),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("MyList"),
            type_: Expr::pi(
                BinderInfo::Default,
                sort_u,
                Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(
                    Name::from_string("u"),
                )))),
            ),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyList.nil"),
                    type_: nil_ty,
                },
                Constructor {
                    name: Name::from_string("MyList.cons"),
                    type_: cons_ty,
                },
            ],
        }],
    })
    .expect("MyList registers");
}

#[test]
fn test_all_family_list_generates_and_kernel_checks() {
    let mut env = Environment::new();
    add_mylist(&mut env);
    let plan = env
        .all_family_decl(&Name::from_string("MyList"))
        .expect("MyList is in the v1 container class");
    assert!(!plan.reuse, "first generation is fresh");
    assert_eq!(plan.all_name.to_string(), "MyList.All");
    env.add_inductive(plan.decl.clone())
        .expect("the generated All family must pass the full kernel check");
    // Idempotence: regenerating against the registered family reuses.
    let again = env
        .all_family_decl(&Name::from_string("MyList"))
        .expect("regeneration succeeds");
    assert!(again.reuse, "byte-identical re-generation must reuse");
    // The family has the expected two ctors.
    let all = env
        .get_inductive(&Name::from_string("MyList.All"))
        .expect("MyList.All registered");
    assert_eq!(all.constructor_names.len(), 2, "nil + cons lifted");
}

#[test]
fn test_all_family_rejects_indexed_container() {
    let mut env = Environment::new();
    // An indexed Prop family is outside the v1 class. The ctor's CONSTANT
    // result index keeps registration from promoting the index to a param.
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("IdxP"),
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
                Expr::from_kind(ExprKind::Sort(Level::zero())),
            ),
            constructors: vec![Constructor {
                name: Name::from_string("IdxP.mk"),
                type_: Expr::app(
                    Expr::const_(Name::from_string("IdxP"), vec![]),
                    Expr::from_kind(ExprKind::Sort(Level::zero())),
                ),
            }],
        }],
    })
    .expect("IdxP registers");
    let err = env
        .all_family_decl(&Name::from_string("IdxP"))
        .expect_err("indexed container must decline");
    assert!(err.contains("indexed"), "reason names the gate: {err}");
}
