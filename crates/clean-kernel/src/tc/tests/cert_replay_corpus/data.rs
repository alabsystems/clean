// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Corpus data: environment builders + expression entries for Wave 0.

use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;

/// A single entry in the self-verification corpus.
pub(super) struct CorpusEntry {
    pub(super) name: &'static str,
    pub(super) expr: Expr,
    pub(super) env: Environment,
}

fn empty_env() -> Environment {
    Environment::new()
}

fn env_with_axioms() -> Environment {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("myProp"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("myType"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env
}

fn env_with_id_fn() -> Environment {
    let mut env = Environment::new();
    let id_type = Expr::arrow(Expr::prop(), Expr::prop());
    let id_value = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("id"),
        level_params: vec![],
        type_: id_type,
        value: id_value,
        is_reducible: true,
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("q"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env
}

fn env_with_binary_fn() -> Environment {
    let mut env = env_with_id_fn();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(Expr::prop(), Expr::arrow(Expr::prop(), Expr::prop())),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: Expr::arrow(Expr::prop(), Expr::prop()),
    })
    .unwrap();
    env
}

fn env_with_pair() -> Environment {
    let mut env = Environment::new();
    let pair = Name::from_string("Pair");
    let pair_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
    );
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
            type_: pair_type,
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: mk_type,
            }],
        }],
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env
}

fn env_with_univ_poly() -> Environment {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Alpha"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::sort(Level::param(Name::from_string("u"))),
    })
    .unwrap();
    env
}

// Each category builder returns a Vec<CorpusEntry> and is under 80 lines.

pub(super) fn sort_entries() -> Vec<CorpusEntry> {
    vec![
        CorpusEntry {
            name: "sort_prop",
            expr: Expr::prop(),
            env: empty_env(),
        },
        CorpusEntry {
            name: "sort_type0",
            expr: Expr::type_(),
            env: empty_env(),
        },
        CorpusEntry {
            name: "sort_type1",
            expr: Expr::sort(Level::succ(Level::succ(Level::zero()))),
            env: empty_env(),
        },
        CorpusEntry {
            name: "sort_type2",
            expr: Expr::sort(Level::succ(Level::succ(Level::succ(Level::zero())))),
            env: empty_env(),
        },
        CorpusEntry {
            name: "sort_max",
            expr: Expr::sort(Level::max(Level::zero(), Level::succ(Level::zero()))),
            env: empty_env(),
        },
    ]
}

pub(super) fn lambda_entries() -> Vec<CorpusEntry> {
    use crate::tc::tests::helpers::build_nested_lambda;
    vec![
        CorpusEntry {
            name: "lam_id_prop",
            expr: Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
            env: empty_env(),
        },
        CorpusEntry {
            name: "lam_id_type",
            expr: Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
            env: empty_env(),
        },
        CorpusEntry {
            name: "lam_poly_id",
            expr: Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "lam_const_k",
            expr: Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(1)),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "lam_const_fn",
            expr: Expr::lam(BinderInfo::Default, Expr::prop(), Expr::prop()),
            env: empty_env(),
        },
        CorpusEntry {
            name: "lam_nested_3",
            expr: Expr::lam(
                BinderInfo::Default,
                Expr::type_(),
                Expr::lam(
                    BinderInfo::Default,
                    Expr::type_(),
                    Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
                ),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "lam_nested_5",
            expr: build_nested_lambda(5),
            env: empty_env(),
        },
        CorpusEntry {
            name: "lam_nested_10",
            expr: build_nested_lambda(10),
            env: empty_env(),
        },
        CorpusEntry {
            name: "lam_church_zero",
            expr: Expr::lam(
                BinderInfo::Default,
                Expr::arrow(Expr::prop(), Expr::prop()),
                Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "lam_church_one",
            expr: Expr::lam(
                BinderInfo::Default,
                Expr::arrow(Expr::prop(), Expr::prop()),
                Expr::lam(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::app(Expr::bvar(1), Expr::bvar(0)),
                ),
            ),
            env: empty_env(),
        },
    ]
}

pub(super) fn pi_entries() -> Vec<CorpusEntry> {
    use crate::tc::tests::helpers::build_nested_pi;
    vec![
        CorpusEntry {
            name: "pi_prop_prop",
            expr: Expr::arrow(Expr::prop(), Expr::prop()),
            env: empty_env(),
        },
        CorpusEntry {
            name: "pi_type_prop",
            expr: Expr::arrow(Expr::type_(), Expr::prop()),
            env: empty_env(),
        },
        CorpusEntry {
            name: "pi_prop_type",
            expr: Expr::arrow(Expr::prop(), Expr::type_()),
            env: empty_env(),
        },
        CorpusEntry {
            name: "pi_type_type",
            expr: Expr::arrow(Expr::type_(), Expr::type_()),
            env: empty_env(),
        },
        CorpusEntry {
            name: "pi_dependent",
            expr: Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "pi_nested_3",
            expr: build_nested_pi(3),
            env: empty_env(),
        },
        CorpusEntry {
            name: "pi_nested_5",
            expr: build_nested_pi(5),
            env: empty_env(),
        },
    ]
}

pub(super) fn app_entries() -> Vec<CorpusEntry> {
    let id_env = env_with_id_fn();
    let bin_env = env_with_binary_fn();
    vec![
        CorpusEntry {
            name: "app_id_p",
            expr: Expr::app(Expr::const_str("id"), Expr::const_str("p")),
            env: id_env.clone(),
        },
        CorpusEntry {
            name: "app_id_q",
            expr: Expr::app(Expr::const_str("id"), Expr::const_str("q")),
            env: id_env,
        },
        CorpusEntry {
            name: "app_beta_redex",
            expr: Expr::app(
                Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
                Expr::prop(),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "app_binary",
            expr: Expr::app(
                Expr::app(Expr::const_str("f"), Expr::const_str("p")),
                Expr::const_str("q"),
            ),
            env: bin_env.clone(),
        },
        CorpusEntry {
            name: "app_composition",
            expr: Expr::app(
                Expr::const_str("g"),
                Expr::app(Expr::const_str("g"), Expr::const_str("p")),
            ),
            env: bin_env.clone(),
        },
        CorpusEntry {
            name: "app_nested",
            expr: Expr::app(
                Expr::const_str("id"),
                Expr::app(Expr::const_str("g"), Expr::const_str("p")),
            ),
            env: bin_env,
        },
        CorpusEntry {
            name: "app_nested_beta",
            expr: Expr::app(
                Expr::app(
                    Expr::lam(
                        BinderInfo::Default,
                        Expr::type_(),
                        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(1)),
                    ),
                    Expr::prop(),
                ),
                Expr::prop(),
            ),
            env: empty_env(),
        },
    ]
}

pub(super) fn let_entries() -> Vec<CorpusEntry> {
    use crate::tc::tests::helpers::build_nested_lets;
    vec![
        CorpusEntry {
            name: "let_simple",
            expr: Expr::let_named(
                Name::anon(),
                Expr::type_(),
                Expr::prop(),
                Expr::bvar(0),
                false,
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "let_unused_body",
            expr: Expr::let_named(
                Name::anon(),
                Expr::type_(),
                Expr::prop(),
                Expr::type_(),
                false,
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "let_dependent",
            expr: Expr::let_named(
                Name::anon(),
                Expr::sort(Level::succ(Level::zero())),
                Expr::prop(),
                Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
                false,
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "let_nested_2",
            expr: Expr::let_named(
                Name::anon(),
                Expr::type_(),
                Expr::prop(),
                Expr::let_named(
                    Name::anon(),
                    Expr::type_(),
                    Expr::prop(),
                    Expr::bvar(0),
                    false,
                ),
                false,
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "let_nested_3",
            expr: build_nested_lets(3),
            env: empty_env(),
        },
    ]
}

pub(super) fn lit_entries() -> Vec<CorpusEntry> {
    vec![
        CorpusEntry {
            name: "lit_nat_0",
            expr: Expr::nat_lit(0),
            env: empty_env(),
        },
        CorpusEntry {
            name: "lit_nat_42",
            expr: Expr::nat_lit(42),
            env: empty_env(),
        },
        CorpusEntry {
            name: "lit_nat_large",
            expr: Expr::nat_lit(1_000_000),
            env: empty_env(),
        },
        CorpusEntry {
            name: "lit_string",
            expr: Expr::str_lit("hello"),
            env: empty_env(),
        },
    ]
}

pub(super) fn const_entries() -> Vec<CorpusEntry> {
    let ax_env = env_with_axioms();
    let id_env = env_with_id_fn();
    let poly_env = env_with_univ_poly();
    vec![
        CorpusEntry {
            name: "const_prop_axiom",
            expr: Expr::const_str("myProp"),
            env: ax_env.clone(),
        },
        CorpusEntry {
            name: "const_type_axiom",
            expr: Expr::const_str("myType"),
            env: ax_env,
        },
        CorpusEntry {
            name: "const_definition",
            expr: Expr::const_str("id"),
            env: id_env,
        },
        CorpusEntry {
            name: "const_univ_poly_zero",
            expr: Expr::const_(Name::from_string("Alpha"), vec![Level::zero()]),
            env: poly_env.clone(),
        },
        CorpusEntry {
            name: "const_univ_poly_one",
            expr: Expr::const_(Name::from_string("Alpha"), vec![Level::succ(Level::zero())]),
            env: poly_env,
        },
    ]
}

pub(super) fn mdata_entries() -> Vec<CorpusEntry> {
    use crate::expr::MDataValue;
    vec![
        CorpusEntry {
            name: "mdata_prop",
            expr: Expr::mdata(
                vec![(Name::from_string("trace"), MDataValue::Bool(true))],
                Expr::prop(),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "mdata_lambda",
            expr: Expr::mdata(
                vec![(Name::from_string("tag"), MDataValue::String("test".into()))],
                Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "mdata_nested",
            expr: Expr::mdata(
                vec![(Name::from_string("outer"), MDataValue::Nat(1))],
                Expr::mdata(
                    vec![(Name::from_string("inner"), MDataValue::Nat(2))],
                    Expr::type_(),
                ),
            ),
            env: empty_env(),
        },
    ]
}

pub(super) fn proj_entries() -> Vec<CorpusEntry> {
    let env = env_with_pair();
    let pair_val = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_str("Pair.mk"), Expr::prop()),
                Expr::prop(),
            ),
            Expr::const_str("a"),
        ),
        Expr::const_str("b"),
    );
    vec![
        CorpusEntry {
            name: "proj_fst",
            expr: Expr::proj(Name::from_string("Pair"), 0, pair_val.clone()),
            env: env.clone(),
        },
        CorpusEntry {
            name: "proj_snd",
            expr: Expr::proj(Name::from_string("Pair"), 1, pair_val),
            env,
        },
    ]
}

pub(super) fn complex_entries() -> Vec<CorpusEntry> {
    vec![
        CorpusEntry {
            name: "complex_church_two",
            expr: Expr::lam(
                BinderInfo::Default,
                Expr::arrow(Expr::prop(), Expr::prop()),
                Expr::lam(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::app(Expr::bvar(1), Expr::app(Expr::bvar(1), Expr::bvar(0))),
                ),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "complex_bool_true",
            expr: Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(1)),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "complex_bool_false",
            expr: Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "complex_flip",
            expr: Expr::lam(
                BinderInfo::Default,
                Expr::arrow(Expr::prop(), Expr::arrow(Expr::prop(), Expr::prop())),
                Expr::lam(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::lam(
                        BinderInfo::Default,
                        Expr::prop(),
                        Expr::app(Expr::app(Expr::bvar(2), Expr::bvar(0)), Expr::bvar(1)),
                    ),
                ),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "complex_compose",
            expr: Expr::lam(
                BinderInfo::Default,
                Expr::arrow(Expr::prop(), Expr::prop()),
                Expr::lam(
                    BinderInfo::Default,
                    Expr::arrow(Expr::prop(), Expr::prop()),
                    Expr::lam(
                        BinderInfo::Default,
                        Expr::prop(),
                        Expr::app(Expr::bvar(2), Expr::app(Expr::bvar(1), Expr::bvar(0))),
                    ),
                ),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "complex_let_lambda",
            expr: Expr::let_named(
                Name::anon(),
                Expr::arrow(Expr::prop(), Expr::prop()),
                Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
                Expr::bvar(0),
                false,
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "complex_higher_order",
            expr: Expr::lam(
                BinderInfo::Default,
                Expr::arrow(Expr::arrow(Expr::prop(), Expr::prop()), Expr::prop()),
                Expr::app(
                    Expr::bvar(0),
                    Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
                ),
            ),
            env: empty_env(),
        },
        CorpusEntry {
            name: "complex_curried_type",
            expr: Expr::arrow(
                Expr::prop(),
                Expr::arrow(Expr::prop(), Expr::arrow(Expr::prop(), Expr::prop())),
            ),
            env: empty_env(),
        },
    ]
}

pub(super) fn binder_variant_entries() -> Vec<CorpusEntry> {
    vec![
        CorpusEntry {
            name: "binder_implicit",
            expr: Expr::lam(BinderInfo::Implicit, Expr::prop(), Expr::bvar(0)),
            env: empty_env(),
        },
        CorpusEntry {
            name: "binder_strict_implicit",
            expr: Expr::lam(BinderInfo::StrictImplicit, Expr::prop(), Expr::bvar(0)),
            env: empty_env(),
        },
        CorpusEntry {
            name: "binder_inst_implicit",
            expr: Expr::lam(BinderInfo::InstImplicit, Expr::prop(), Expr::bvar(0)),
            env: empty_env(),
        },
    ]
}

/// Build the complete corpus from all category builders.
pub(super) fn build_corpus() -> Vec<CorpusEntry> {
    let mut corpus = Vec::with_capacity(60);
    corpus.extend(sort_entries());
    corpus.extend(lambda_entries());
    corpus.extend(pi_entries());
    corpus.extend(app_entries());
    corpus.extend(let_entries());
    corpus.extend(lit_entries());
    corpus.extend(const_entries());
    corpus.extend(mdata_entries());
    corpus.extend(proj_entries());
    corpus.extend(complex_entries());
    corpus.extend(binder_variant_entries());
    corpus
}
