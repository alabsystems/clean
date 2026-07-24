// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{BinderInfo, Expr, ExprKind, MDataValue, ZFCSetExpr};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::level::Level;
use clean_kernel::Name;

fn add_wave0_axioms(env: &mut Environment) {
    for name in ["myProp", "p", "q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        })
        .unwrap();
    }

    env.add_decl(Declaration::Definition {
        name: Name::from_string("id"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::sort(Level::zero()),
        ),
        value: Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::bvar(0),
        ),
        is_reducible: true,
    })
    .unwrap();
}

fn add_zfc_set_axiom(env: &mut Environment) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("ZFC.Set"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
}

fn add_wave0_pair_inductive(env: &mut Environment) {
    let pair = Name::from_string("Pair");
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::app(
                        Expr::app(Expr::const_(pair.clone(), vec![]), Expr::bvar(3)),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: pair.clone(),
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::type_(),
                Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
            ),
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: mk_type,
            }],
        }],
    })
    .unwrap();
}

pub(super) fn release_infer_env() -> Environment {
    let mut env = Environment::new();
    add_wave0_axioms(&mut env);
    add_wave0_pair_inductive(&mut env);
    env
}

pub(super) fn release_zfc_env() -> Environment {
    let mut env = release_infer_env();
    add_zfc_set_axiom(&mut env);
    env
}

fn pair_val() -> Expr {
    let prop = Expr::sort(Level::zero());
    let mk = Expr::const_(Name::from_string("Pair.mk"), vec![]);
    let p = Expr::const_(Name::from_string("p"), vec![]);
    let q = Expr::const_(Name::from_string("q"), vec![]);
    Expr::app(
        Expr::app(Expr::app(Expr::app(mk, prop.clone()), prop), p),
        q,
    )
}

fn wave0_base_cases(prop: &Expr, type0: &Expr) -> Vec<(&'static str, Expr)> {
    vec![
        ("prop", prop.clone()),
        ("type", type0.clone()),
        ("type1", Expr::sort(Level::succ(Level::succ(Level::zero())))),
        (
            "lam_identity",
            Expr::lam(BinderInfo::Default, prop.clone(), Expr::bvar(0)),
        ),
        (
            "lam_nested",
            Expr::lam(
                BinderInfo::Default,
                type0.clone(),
                Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
            ),
        ),
        (
            "pi_prop_to_prop",
            Expr::pi(BinderInfo::Default, prop.clone(), prop.clone()),
        ),
        (
            "pi_type_to_type",
            Expr::pi(BinderInfo::Default, type0.clone(), type0.clone()),
        ),
        (
            "let_simple",
            Expr::let_named(
                Name::anon(),
                type0.clone(),
                prop.clone(),
                Expr::bvar(0),
                false,
            ),
        ),
        (
            "let_dependent",
            Expr::let_named(
                Name::anon(),
                type0.clone(),
                prop.clone(),
                Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
                false,
            ),
        ),
        (
            "app_lambda",
            Expr::app(
                Expr::lam(BinderInfo::Default, type0.clone(), Expr::bvar(0)),
                prop.clone(),
            ),
        ),
        (
            "app_const",
            Expr::app(
                Expr::const_(Name::from_string("id"), vec![]),
                Expr::const_(Name::from_string("myProp"), vec![]),
            ),
        ),
    ]
}

fn wave0_terminal_cases(prop: &Expr, pair_v: &Expr) -> Vec<(&'static str, Expr)> {
    vec![
        ("nat_zero", Expr::nat_lit(0)),
        ("nat_forty_two", Expr::nat_lit(42)),
        ("string_literal", Expr::str_lit("clean")),
        (
            "const_axiom",
            Expr::const_(Name::from_string("myProp"), vec![]),
        ),
        (
            "const_definition",
            Expr::const_(Name::from_string("id"), vec![]),
        ),
        (
            "proj_fst",
            Expr::proj(Name::from_string("Pair"), 0, pair_v.clone()),
        ),
        (
            "proj_snd",
            Expr::proj(Name::from_string("Pair"), 1, pair_v.clone()),
        ),
        (
            "mdata_sort",
            Expr::mdata(
                vec![(Name::from_string("note"), MDataValue::Nat(0))],
                prop.clone(),
            ),
        ),
        (
            "mdata_lambda",
            Expr::mdata(
                vec![(
                    Name::from_string("tag"),
                    MDataValue::String("identity".into()),
                )],
                Expr::lam(BinderInfo::Default, prop.clone(), Expr::bvar(0)),
            ),
        ),
    ]
}

pub(super) fn wave0_corpus() -> Vec<(&'static str, Expr)> {
    let prop = Expr::sort(Level::zero());
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let pair_v = pair_val();
    let mut cases = wave0_base_cases(&prop, &type0);
    cases.extend(wave0_terminal_cases(&prop, &pair_v));
    cases
}

pub(super) fn cubical_interval() -> Expr {
    Expr::from_kind(ExprKind::CubicalInterval)
}

pub(super) fn cubical_i0() -> Expr {
    Expr::from_kind(ExprKind::CubicalI0)
}

pub(super) fn cubical_i1() -> Expr {
    Expr::from_kind(ExprKind::CubicalI1)
}

pub(super) fn cubical_constant_interval_family() -> Expr {
    Expr::lam(BinderInfo::Default, cubical_interval(), cubical_interval())
}

pub(super) fn cubical_constant_prop_path() -> Expr {
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Expr::prop().into(),
    })
}

fn zfc_set_ty() -> Expr {
    Expr::const_(Name::from_string("ZFC.Set"), vec![])
}

pub(super) fn zfc_empty_set() -> Expr {
    Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty))
}

pub(super) fn zfc_set_to_prop_pred() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        zfc_set_ty(),
        Expr::from_kind(ExprKind::ZFCMem {
            element: Expr::bvar(0).into(),
            set: zfc_empty_set().into(),
        }),
    )
}

pub(super) fn zfc_set_identity() -> Expr {
    Expr::lam(BinderInfo::Default, zfc_set_ty(), Expr::bvar(0))
}
