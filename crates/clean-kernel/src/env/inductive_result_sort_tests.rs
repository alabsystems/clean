// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The result-sort helper against Lean's `check_inductive_types` loop.

use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{allows_large_elim, allows_large_elim_without_env, InductiveType};
use crate::level::Level;
use crate::Name;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn sort1() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

fn env_with(defs: &[(&str, Expr, Expr)]) -> Environment {
    let mut env = Environment::try_with_prelude().expect("prelude environment");
    for (name, type_, value) in defs {
        env.add_decl(Declaration::Definition {
            name: n(name),
            level_params: vec![],
            type_: type_.clone(),
            value: value.clone(),
            is_reducible: false,
        })
        .expect("definition admitted");
    }
    env
}

fn arity_env() -> Environment {
    env_with(&[
        ("MyProp", sort1(), Expr::prop()),
        (
            "MyArity",
            sort1(),
            Expr::pi(
                BinderInfo::Default,
                Expr::const_(n("Nat"), vec![]),
                Expr::prop(),
            ),
        ),
    ])
}

#[test]
fn test_result_sort_syntactic_telescope_is_read_without_reduction() {
    let env = Environment::default();
    let ty = Expr::pi(BinderInfo::Default, sort1(), Expr::prop());
    let sort = env.type_former_result_sort(&ty).expect("ends in a sort");
    assert_eq!(sort.level, Level::zero());
    assert_eq!(sort.arity, 1);
}

#[test]
fn test_result_sort_delta_codomain_is_found_up_to_whnf() {
    let env = arity_env();
    let sort = env
        .type_former_result_sort(&Expr::const_(n("MyProp"), vec![]))
        .expect("MyProp unfolds to Prop");
    assert_eq!(sort.level, Level::zero());
    assert_eq!(sort.arity, 0);
    assert_eq!(
        env.type_former_is_prop(&Expr::const_(n("MyProp"), vec![])),
        Some(true)
    );
}

#[test]
fn test_result_sort_counts_binders_a_definition_hides() {
    let env = arity_env();
    let ty = Expr::const_(n("MyArity"), vec![]);
    let sort = env.type_former_result_sort(&ty).expect("Nat → Prop");
    assert_eq!((sort.level, sort.arity), (Level::zero(), 1));
    let member = InductiveType {
        name: n("Hidden"),
        type_: ty,
        constructors: vec![],
    };
    let err = env
        .member_result_level(&member)
        .expect_err("a hidden binder is refused by the eliminator builders");
    assert!(err.to_string().contains("hides binders"), "{err}");
}

#[test]
fn test_result_sort_non_sort_codomain_is_none() {
    let env = arity_env();
    let ty = Expr::const_(n("Nat"), vec![]);
    assert!(env.type_former_result_sort(&ty).is_none());
    assert_eq!(env.type_former_is_prop(&ty), None);
    // No admission accepts such a family; the public analysis never grants
    // it a large eliminator.
    assert!(!allows_large_elim(&env, &ty, &[], 0, 1));
}

#[test]
fn test_large_elim_reads_the_level_not_the_head() {
    let env = arity_env();
    let my_prop = Expr::const_(n("MyProp"), vec![]);
    let two = [
        crate::inductive::Constructor {
            name: n("B.t"),
            type_: Expr::const_(n("B"), vec![]),
        },
        crate::inductive::Constructor {
            name: n("B.f"),
            type_: Expr::const_(n("B"), vec![]),
        },
    ];
    // Two constructors at a δ-Prop level: Prop-only (the hole answered `true`).
    assert!(!allows_large_elim(&env, &my_prop, &two, 0, 1));
    assert_eq!(
        allows_large_elim_without_env(&Level::zero(), 2, 1),
        Some(false)
    );
    assert_eq!(
        allows_large_elim_without_env(&Level::succ(Level::zero()), 2, 1),
        Some(true)
    );
}

/// The structural import tier counts a hidden index as Lean does, exactly,
/// once the definition is resident: `Hidden : MyArity` with
/// `MyArity := Nat → Prop` has one index, not "at least the syntactic
/// remainder".
#[test]
fn test_imported_arity_split_is_exact_up_to_whnf() {
    use crate::inductive::InductiveVal;
    let record = |name: &str, num_indices: u32| InductiveVal {
        name: n(name),
        level_params: vec![],
        type_: Expr::const_(n("MyArity"), vec![]),
        num_params: 0,
        num_indices,
        all_names: vec![n(name)],
        constructor_names: vec![],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: false,
        is_nested: false,
    };
    let mut env = arity_env();
    let refused = env.extend_inductives_structural(std::iter::once(record("HiddenTwo", 2)));
    assert!(
        refused
            .iter()
            .any(|(name, e)| name == &n("HiddenTwo") && e.to_string().contains("does not split")),
        "two indices where Lean counts one must be refused: {refused:?}"
    );
    assert!(env
        .extend_inductives_structural(std::iter::once(record("HiddenOne", 1)))
        .is_empty());
}
