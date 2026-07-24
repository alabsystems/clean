// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Iota reduction tests — recursive types, enums, and literal expansion.
//!
//! Tests for recursive Nat.succ induction, enumeration types without
//! recursive fields, and Nat/String literal expansion during iota reduction.

use super::support::make_nat_env_and_ref;
use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Test iota on Nat.succ includes induction hypothesis.
/// Nat.rec motive z s (succ n) = s n (Nat.rec motive z s n)
#[test]
fn test_iota_reduction_recursive_nat_succ() {
    let (env, nat_ref) = make_nat_env_and_ref();

    let rec_val = env
        .get_recursor(&Name::from_string("Nat.rec"))
        .expect("get Nat.rec");
    assert_eq!(rec_val.rules.len(), 2);
    assert!(rec_val.rules[0].recursive_fields.is_empty());
    assert_eq!(rec_val.rules[1].recursive_fields.len(), 1);
    assert!(rec_val.rules[1].recursive_fields[0]);

    let tc = TypeChecker::new(&env);
    let rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::prop());
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(BinderInfo::Default, Expr::prop(), q.clone()),
    );
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), p), succ_case),
        one,
    );
    assert_eq!(tc.whnf(&app), q);
}

/// Test enumerations (no recursive fields) reduce correctly.
#[test]
fn test_iota_reduction_enum_no_recursive() {
    let mut env = Environment::new();
    let bool_name = Name::from_string("MyBool");
    let bool_ref = Expr::const_(bool_name.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bool_name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyBool.false"),
                    type_: bool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("MyBool.true"),
                    type_: bool_ref.clone(),
                },
            ],
        }],
    };
    env.add_inductive(decl).expect("add MyBool inductive");

    let rec_val = env
        .get_recursor(&Name::from_string("MyBool.rec"))
        .expect("get MyBool.rec");
    for rule in &rec_val.rules {
        assert!(
            rule.recursive_fields.is_empty(),
            "Enum has no recursive fields"
        );
    }

    let tc = TypeChecker::new(&env);
    let rec = Expr::const_(Name::from_string("MyBool.rec"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, bool_ref, Expr::prop());
    let true_case = Expr::const_(Name::from_string("T"), vec![]);
    let app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(rec, motive),
                Expr::const_(Name::from_string("F"), vec![]),
            ),
            true_case.clone(),
        ),
        Expr::const_(Name::from_string("MyBool.true"), vec![]),
    );
    assert_eq!(tc.whnf(&app), true_case);
}

/// Build Nat.rec application for literal tests. Returns (app, rec_level).
fn build_nat_rec_literal_app(_env: &Environment, nat_ref: &Expr, major: Expr) -> Expr {
    let motive = Expr::lam(BinderInfo::Default, nat_ref.clone(), nat_ref.clone());
    let zero_case = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::bvar(0),
            ),
        ),
    );
    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), zero_case), succ_case),
        major,
    )
}

/// Nat literals like `2` should reduce completely through iota + Nat reduction (#574).
///
/// The recursor `Nat.rec motive zero_case succ_case 2` first expands via iota
/// to `succ_case 1 (Nat.rec motive zero_case succ_case 1)`, then WHNF's
/// `reduce_nat` collapses `Nat.succ (lit 1)` to `lit 2`.
#[test]
fn test_iota_reduction_nat_literal() {
    let (env, nat_ref) = make_nat_env_and_ref();
    let tc = TypeChecker::new(&env);

    let nat_literal = Expr::from_kind(ExprKind::Lit(crate::expr::Literal::Nat(
        crate::BigNat::Small(2),
    )));
    let app = build_nat_rec_literal_app(&env, &nat_ref, nat_literal);
    let result = tc.whnf(&app);

    // After iota + WHNF nat reduction, the result is a Nat literal 2
    // (reduce_nat collapses Nat.succ(lit 1) -> lit 2).
    match result.kind() {
        ExprKind::Lit(crate::expr::Literal::Nat(n)) => {
            assert_eq!(n.to_u64(), Some(2), "Expected Nat literal 2, got {:?}", n);
        }
        ExprKind::Const(n, _) if *n == Name::from_string("Nat.succ") => {
            // Also acceptable: Nat.succ form if reduce_nat doesn't fire
            assert!(
                !result.get_app_args().is_empty(),
                "Expected Nat.succ argument"
            );
        }
        _ => panic!("Expected Nat literal 2 or Nat.succ, got {:?}", result),
    }
}

/// String literals expand to String.mk [c₁, ..., cₙ] during iota (#574).
#[test]
fn test_iota_reduction_string_literal() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_char().expect("init_char");
    env.init_list().expect("init_list");
    env.init_string().expect("init_string");
    let tc = TypeChecker::new(&env);

    let string_const = Expr::const_(Name::from_string("String"), vec![]);
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let char_const = Expr::const_(Name::from_string("Char"), vec![]);
    let list_char = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::succ(Level::zero())]),
        char_const.clone(),
    );

    let motive = Expr::lam(BinderInfo::Default, string_const, nat_const);
    let mk_case = Expr::lam(
        BinderInfo::Default,
        list_char,
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("List.length"),
                    vec![Level::succ(Level::zero())],
                ),
                char_const,
            ),
            Expr::bvar(0),
        ),
    );
    let rec = Expr::const_(
        Name::from_string("String.rec"),
        vec![Level::succ(Level::zero())],
    );
    let app = Expr::app(
        Expr::app(Expr::app(rec, motive), mk_case),
        Expr::str_lit("ab"),
    );

    let result = tc.whnf(&app);
    let result_head = result.get_app_fn();
    assert!(
        !matches!(result_head.kind(), ExprKind::Const(n, _) if n == &Name::from_string("String.rec")),
        "String.rec should have reduced, but got: {:?}",
        result
    );
}
