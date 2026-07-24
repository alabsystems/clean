// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Iota reduction tests — field boundary and args_before_major calculation.
//!
//! Tests verifying correct field extraction boundaries, args_before_major
//! arithmetic, indexed inductives, and param vs index handling.

use super::support::make_nat_env_named;
use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Kills mutants at line 761: replace < with ==, >, or <=.
/// Tests: if field_start < major_args.len()
#[test]
fn test_try_iota_reduction_field_boundary() {
    let (env, _nat, nat_ref) = make_nat_env_named();
    let tc = TypeChecker::new(&env);

    let rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::prop());
    let case_zero = Expr::type_();
    let case_succ = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
        ),
    );
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Nat.rec with zero should give case_zero
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec.clone(), motive.clone()), case_zero.clone()),
            case_succ.clone(),
        ),
        zero,
    );
    let result = tc.whnf(&app);
    assert_eq!(result, case_zero, "Nat.rec zero should give case_zero");

    // Nat.rec with succ(zero) must also reduce
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let app2 = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), case_zero), case_succ),
        succ_zero,
    );
    let result2 = tc.whnf(&app2);
    assert_ne!(
        app2, result2,
        "Nat.rec (succ zero) must reduce (field_start < major_args.len)"
    );
}

/// Kills mutant at line 716: replace + with - in args_before_major.
/// Uses Bool (0 params, 1 motive, 2 minors, 0 indices).
#[test]
fn test_try_iota_reduction_args_before_major() {
    let mut env = Environment::new();
    let bool_name = Name::from_string("Bool");
    let bool_ref = Expr::const_(bool_name.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bool_name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Bool.true"),
                    type_: bool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Bool.false"),
                    type_: bool_ref.clone(),
                },
            ],
        }],
    };
    env.add_inductive(decl).expect("add Bool inductive");
    let tc = TypeChecker::new(&env);

    let rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, bool_ref.clone(), Expr::prop());
    let case_true = Expr::type_();
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec, motive), case_true.clone()),
            Expr::prop(),
        ),
        Expr::const_(Name::from_string("Bool.true"), vec![]),
    );
    let result = tc.whnf(&app);
    assert_eq!(result, case_true, "Bool.rec true should give case_true");
}

/// Add Idx (indexed inductive with 1 non-fixed index) to an environment that already has Nat.
/// Idx : Nat → Type, Idx.mk : (n : Nat) → Idx (Nat.succ n)
/// The index is Nat.succ(n), NOT n itself, so fixedIndicesToParams won't promote it.
fn add_idx_inductive(env: &mut Environment, nat_ref: &Expr) -> Name {
    let idx_name = Name::from_string("Idx");
    let idx_type = Expr::pi(BinderInfo::Default, nat_ref.clone(), Expr::type_());
    // Idx.mk : (n : Nat) → Idx (Nat.succ n)
    let idx_mk_type = Expr::pi(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::app(
            Expr::const_(idx_name.clone(), vec![]),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::from_kind(ExprKind::BVar(0)),
            ),
        ),
    );
    let idx_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: idx_name.clone(),
            type_: idx_type,
            constructors: vec![Constructor {
                name: Name::from_string("Idx.mk"),
                type_: idx_mk_type,
            }],
        }],
    };
    env.add_inductive(idx_decl).expect("add Idx inductive");
    idx_name
}

/// Kills mutants at tc.rs:716 (+ to -) and tc.rs:761 (< boundary).
/// Uses Idx : Nat → Type with num_indices = 1 (non-fixed index, not promoted).
#[test]
fn test_iota_reduction_indexed_inductive() {
    let (mut env, _nat, nat_ref) = make_nat_env_named();
    let idx_name = add_idx_inductive(&mut env, &nat_ref);

    let idx_val = env.get_inductive(&idx_name).expect("get Idx inductive");
    assert_eq!(idx_val.num_indices, 1, "Idx should have 1 index");
    let rec_val = env
        .get_recursor(&Name::from_string("Idx.rec"))
        .expect("get Idx.rec");
    assert_eq!(rec_val.num_indices, 1, "Idx.rec should have 1 index");

    let tc = TypeChecker::new(&env);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    // Idx.mk zero : Idx (succ zero)
    let major = Expr::app(
        Expr::const_(Name::from_string("Idx.mk"), vec![]),
        zero.clone(),
    );
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );
    let rec = Expr::const_(Name::from_string("Idx.rec"), vec![Level::zero()]);
    let motive = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(idx_name.clone(), vec![]),
                Expr::from_kind(ExprKind::BVar(0)),
            ),
            Expr::prop(),
        ),
    );
    let minor = Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::type_());
    // Idx.rec motive minor (succ zero) (Idx.mk zero)
    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), minor), succ_zero),
        major,
    );
    let result = tc.whnf(&app);

    assert_ne!(app, result, "Idx.rec must reduce (kills line 716 mutant)");
    assert!(
        !matches!(&result.kind, ExprKind::Lam(..)),
        "Result should not be a lambda (kills line 761 mutants)"
    );
}

/// Add Vec (1 param, 1 index) to an environment that already has Nat.
fn add_vec_inductive(env: &mut Environment, nat_ref: &Expr) -> Name {
    let vec_name = Name::from_string("Vec");
    let u = Name::from_string("u");
    let vec_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::from_kind(ExprKind::Sort(Level::Param(u.clone()))),
        Expr::pi(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::from_kind(ExprKind::Sort(Level::Param(u.clone()))),
        ),
    );
    let vec_nil_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::from_kind(ExprKind::Sort(Level::Param(u.clone()))),
        Expr::app(
            Expr::app(
                Expr::const_(vec_name.clone(), vec![Level::Param(u.clone())]),
                Expr::from_kind(ExprKind::BVar(0)),
            ),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ),
    );
    let vec_decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: vec_name.clone(),
            type_: vec_type,
            constructors: vec![Constructor {
                name: Name::from_string("Vec.nil"),
                type_: vec_nil_type,
            }],
        }],
    };
    env.add_inductive(vec_decl).expect("add Vec inductive");
    vec_name
}

/// Tests param vs index: Vec has 1 param (α) and 1 index (n).
/// Kills args_before_major mutation (+ to -) with mixed param/index.
#[test]
fn test_iota_reduction_param_vs_index() {
    let (mut env, _nat, nat_ref) = make_nat_env_named();
    let vec_name = add_vec_inductive(&mut env, &nat_ref);

    let vec_val = env.get_inductive(&vec_name).expect("get Vec inductive");
    assert_eq!(vec_val.num_params, 1, "Vec should have 1 param");
    assert_eq!(vec_val.num_indices, 1, "Vec should have 1 index");

    let tc = TypeChecker::new(&env);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let alpha = Expr::type_();
    let nil = Expr::app(
        Expr::const_(Name::from_string("Vec.nil"), vec![Level::zero()]),
        alpha.clone(),
    );
    let rec = Expr::const_(
        Name::from_string("Vec.rec"),
        vec![Level::zero(), Level::zero()],
    );
    let motive = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(
                Expr::app(Expr::const_(vec_name, vec![Level::zero()]), alpha.clone()),
                Expr::from_kind(ExprKind::BVar(0)),
            ),
            Expr::prop(),
        ),
    );
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::app(rec, alpha), motive), Expr::type_()),
            zero,
        ),
        nil,
    );
    let result = tc.whnf(&app);
    assert_ne!(app, result, "Vec.rec nil must reduce (param+index test)");
}
