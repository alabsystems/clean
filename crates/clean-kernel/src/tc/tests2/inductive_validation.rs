// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for add_inductive validation pipeline (#2156).
//!
//! Regression tests for Phase 3 (parameter consistency check) and
//! acceptance tests for well-formed inductive declarations.

use super::*;

#[test]
fn test_ctor_param_mismatch_rejected() {
    // Pipeline regression test for #2156: wrong parameter domain is rejected.
    // Exercises full validation pipeline (infer_type may catch before check_ctor_params).
    //   MyList.nil : (A : Nat) → MyList A    -- wrong: domain Nat ≠ Type u
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};
    use crate::level::Level;

    let mut env = Environment::new();

    // First register Nat so the type checker can resolve it
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    let nat_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::pi(BinderInfo::Default, nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    };
    env.add_inductive(nat_decl)
        .expect("invariant: valid inductive declaration");

    let u = Name::from_string("u");
    let my_list = Name::from_string("MyList");

    // MyList : Type u → Type u   (Type u = Sort (u+1), provably nonzero [R1])
    let my_list_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
    );

    // Wrong constructor: first parameter domain is Nat instead of Type u
    // MyList.bad_nil : (A : Nat) → MyList A
    let bad_nil_type = Expr::pi(
        BinderInfo::Default,
        nat_ref.clone(), // Wrong: should be Type u, is Nat
        Expr::app(
            Expr::const_(my_list.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(0),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: my_list.clone(),
            type_: my_list_type,
            constructors: vec![Constructor {
                name: Name::from_string("MyList.bad_nil"),
                type_: bad_nil_type,
            }],
        }],
    };

    let result = env.add_inductive(decl);
    assert!(
        result.is_err(),
        "Constructor with wrong parameter type should be rejected"
    );
}

#[test]
fn test_ctor_param_match_accepted() {
    // Phase 3 of #2156: correct parameters should pass.
    //
    // inductive Pair (A : Type) (B : Type) : Type
    // | mk : A → B → Pair A B
    //
    // Constructor type: (A : Type) → (B : Type) → A → B → Pair A B
    // Parameters match the inductive's (A : Type) → (B : Type) → Type.
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};
    use crate::level::Level;

    let mut env = Environment::new();

    let pair = Name::from_string("Pair");

    // Pair : Type → Type → Type 1
    // (A : Type) → (B : Type) → Type 1
    let type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let pair_type = Expr::pi(
        BinderInfo::Default,
        type1.clone(), // A : Type
        Expr::pi(
            BinderInfo::Default,
            type1.clone(), // B : Type
            type1.clone(), // Type 1
        ),
    );

    // Pair.mk : (A : Type) → (B : Type) → A → B → Pair A B
    // BVar references (from innermost):
    //   BVar(0) = b : B
    //   BVar(1) = a : A
    //   BVar(2) = B : Type
    //   BVar(3) = A : Type
    let mk_type = Expr::pi(
        BinderInfo::Default,
        type1.clone(), // A : Type
        Expr::pi(
            BinderInfo::Default,
            type1.clone(), // B : Type
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // a : A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1), // b : B
                    Expr::app(
                        Expr::app(
                            Expr::const_(pair.clone(), vec![]),
                            Expr::bvar(3), // A
                        ),
                        Expr::bvar(2), // B
                    ),
                ),
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: pair.clone(),
            type_: pair_type,
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: mk_type,
            }],
        }],
    };

    env.add_inductive(decl)
        .expect("invariant: valid inductive declaration");

    // Verify it was registered correctly
    env.get_recursor(&Name::from_string("Pair.rec"))
        .expect("Pair.rec recursor should be registered");
    let pair_ind = env
        .get_inductive(&pair)
        .expect("invariant: valid inductive declaration");
    assert_eq!(pair_ind.num_params, 2);
}
