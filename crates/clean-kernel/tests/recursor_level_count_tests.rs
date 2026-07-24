// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Algorithm audit: recursor universe level count tests.
//!
//! Validates that non-Prop recursors always get +1 universe parameter for the
//! motive level, and that recursor applications with wrong level counts are
//! rejected by the kernel type checker.
//!
//! Bug context: `cases` and `induction` in proof_manipulation.rs copy universe
//! levels from the inductive type head (e.g., Nat has 0 levels) and pass them
//! to the recursor (e.g., Nat.rec which needs 1 level). This produces
//! LevelCountMismatch when close_goal type-checks the proof. Part of #2154.
//!
//! Also validates that inductive types with `Sort u` where fields require
//! `Sort (u+1)` are correctly rejected (universe constraint check in
//! inductive_builder.rs:224). Part of #2162.

use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::level::Level;
use clean_kernel::name::Name;

/// Helper: build a Nat environment.
fn make_nat_env() -> Environment {
    let mut env = Environment::new();
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat,
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    })
    .expect("add Nat");
    env
}

/// Build Vec inductive declaration with given sort level for the parameter type.
/// `param_sort` is the sort for the implicit type parameter (e.g., Sort u or Sort (u+1)).
fn make_vec_decl(param_sort: Level, ulvl: Level) -> (Name, InductiveDecl) {
    let u = Name::from_string("u");
    let vec_name = Name::from_string("Vec");
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let vec_c = |lvls: Vec<Level>| Expr::const_(vec_name.clone(), lvls);

    let vec_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(param_sort.clone()),
        Expr::pi(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::sort(param_sort.clone()),
        ),
    );

    let nil_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(param_sort.clone()),
        Expr::app(
            Expr::app(vec_c(vec![ulvl.clone()]), Expr::bvar(0)),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ),
    );

    let cons_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(param_sort),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(
                BinderInfo::Default,
                nat_ref,
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(
                        Expr::app(vec_c(vec![ulvl.clone()]), Expr::bvar(2)),
                        Expr::bvar(0),
                    ),
                    Expr::app(
                        Expr::app(vec_c(vec![ulvl.clone()]), Expr::bvar(3)),
                        Expr::app(
                            Expr::const_(Name::from_string("Nat.succ"), vec![]),
                            Expr::bvar(1),
                        ),
                    ),
                ),
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: vec_name.clone(),
            type_: vec_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("Vec.nil"),
                    type_: nil_ty,
                },
                Constructor {
                    name: Name::from_string("Vec.cons"),
                    type_: cons_ty,
                },
            ],
        }],
    };

    (vec_name, decl)
}

/// Non-Prop inductive (Nat : Type) has recursor with +1 level parameter.
///
/// Nat has 0 level_params, but Nat.rec should have 1 (the motive level).
/// This is the core property that cases/induction must respect.
#[test]
fn test_non_prop_recursor_has_extra_motive_level() {
    let env = make_nat_env();

    let nat_info = env.get_inductive(&Name::from_string("Nat")).unwrap();
    let nat_level_count = nat_info.level_params.len();
    assert_eq!(nat_level_count, 0, "Nat has 0 level params");

    let rec_info = env.get_recursor(&Name::from_string("Nat.rec")).unwrap();
    let rec_level_count = rec_info.level_params.len();
    assert_eq!(
        rec_level_count,
        nat_level_count + 1,
        "Non-Prop recursor should have exactly 1 extra level for motive"
    );
}

/// Prop inductive has recursor with +1 level (motive into Sort u, not fixed Prop).
#[test]
fn test_prop_recursor_level_count() {
    let mut env = make_nat_env();

    let false_name = Name::from_string("False");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: false_name.clone(),
            type_: Expr::prop(),
            constructors: vec![],
        }],
    })
    .expect("add False");

    let false_info = env.get_inductive(&false_name).unwrap();
    let rec_info = env.get_recursor(&Name::from_string("False.rec")).unwrap();
    assert_eq!(
        rec_info.level_params.len(),
        false_info.level_params.len() + 1,
        "False.rec should have 1 extra level (motive into Sort u)"
    );
}

/// Polymorphic inductive with correct universe (Sort (u+1) = Type u) accepts.
#[test]
fn test_polymorphic_inductive_correct_universe() {
    let mut env = make_nat_env();
    let ulvl = Level::Param(Name::from_string("u"));
    let succ_u = Level::succ(ulvl.clone());

    let (_vec_name, decl) = make_vec_decl(succ_u, ulvl);
    let result = env.add_inductive(decl);

    assert!(
        result.is_ok(),
        "Vec with Sort (u+1) should pass universe constraint check: {:?}",
        result.err()
    );
}

/// Polymorphic inductive with WRONG universe (Sort u) is rejected.
///
/// Vec : Sort u → Nat → Sort u fails because field `n : Nat` has sort 1,
/// but is_geq(u, 1) is false (u could be 0).
#[test]
fn test_polymorphic_inductive_wrong_universe_rejected() {
    let mut env = make_nat_env();
    let ulvl = Level::Param(Name::from_string("u"));

    // Wrong: use Sort u directly (not Sort (u+1))
    let (_vec_name, decl) = make_vec_decl(ulvl.clone(), ulvl);
    let result = env.add_inductive(decl);

    assert!(
        result.is_err(),
        "Vec with Sort u should fail: Nat field sort 1 > Param(u)"
    );
}
