// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Wave 0 corpus integration test (#1891 AC3)
//!
//! Feeds the canonical Wave 0 expression corpus through `verify_batch`,
//! validating that the verify_api handles all expression categories from
//! the baseline established in #1890.

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{BinderInfo, Expr, MDataValue};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::verify_api::{verify_batch, verify_expr};

/// Build an environment with declarations for Const/App/Proj corpus entries.
fn wave0_env() -> Environment {
    let mut env = Environment::new();

    // Axioms: myProp, p, q : Prop
    for name in ["myProp", "p", "q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        })
        .unwrap();
    }

    // Definition: id : Prop → Prop := λ x. x
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

    // Inductive: Pair (A B : Type) with Pair.mk : A → B → Pair A B
    let pair = Name::from_string("Pair");
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(), // A
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(), // B
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1), // B
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

    env
}

/// Build Pair.mk Prop Prop p q for projection tests.
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

/// Build the Wave 0 canonical expression corpus (19 entries, 9 categories).
fn wave0_corpus() -> Vec<Expr> {
    let prop = Expr::sort(Level::zero());
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let pair_v = pair_val();

    vec![
        // Sort (3): Prop, Type, Type+1
        prop.clone(),
        type0.clone(),
        Expr::sort(Level::succ(Level::succ(Level::zero()))),
        // Lambda (2): identity, nested polymorphic
        Expr::lam(BinderInfo::Default, prop.clone(), Expr::bvar(0)),
        Expr::lam(
            BinderInfo::Default,
            type0.clone(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        ),
        // Pi (2): Prop→Prop, Type→Type
        Expr::pi(BinderInfo::Default, prop.clone(), prop.clone()),
        Expr::pi(BinderInfo::Default, type0.clone(), type0.clone()),
        // Let (2): simple, dependent
        Expr::let_named(
            Name::anon(),
            type0.clone(),
            prop.clone(),
            Expr::bvar(0),
            false,
        ),
        Expr::let_named(
            Name::anon(),
            type0.clone(),
            prop.clone(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
            false,
        ),
        // App (2): lambda-applied, const-applied
        Expr::app(
            Expr::lam(BinderInfo::Default, type0, Expr::bvar(0)),
            prop.clone(),
        ),
        Expr::app(
            Expr::const_(Name::from_string("id"), vec![]),
            Expr::const_(Name::from_string("myProp"), vec![]),
        ),
        // Literal (2): Nat 0, Nat 42
        Expr::nat_lit(0),
        Expr::nat_lit(42),
        // Const (2): axiom, definition
        Expr::const_(Name::from_string("myProp"), vec![]),
        Expr::const_(Name::from_string("id"), vec![]),
        // Proj (2): field 0, field 1
        Expr::proj(Name::from_string("Pair"), 0, pair_v.clone()),
        Expr::proj(Name::from_string("Pair"), 1, pair_v),
        // MData (2): wrapped sort, wrapped lambda
        Expr::mdata(
            vec![(Name::from_string("note"), MDataValue::Nat(0))],
            prop.clone(),
        ),
        Expr::mdata(
            vec![(
                Name::from_string("tag"),
                MDataValue::String("identity".into()),
            )],
            Expr::lam(BinderInfo::Default, prop, Expr::bvar(0)),
        ),
    ]
}

#[test]
fn test_wave0_corpus_through_verify_batch() {
    let env = wave0_env();
    let corpus = wave0_corpus();

    assert_eq!(corpus.len(), 19, "Wave 0 corpus should have 19 entries");

    let stats = verify_batch(&env, &corpus);

    assert_eq!(stats.total(), 19);
    assert_eq!(
        stats.passed(),
        19,
        "All Wave 0 corpus entries must pass, errors: {:?}",
        stats.errors()
    );
    assert_eq!(stats.failed(), 0);
    assert!(stats.errors().is_empty());
    assert!((stats.pass_rate() - 1.0).abs() < f64::EPSILON);

    // Micro coverage accounting: confirmed + skipped = passed
    assert_eq!(
        stats.micro_confirmed() + stats.micro_skipped(),
        stats.passed()
    );
    assert!(
        stats.micro_confirmed() > 0,
        "Some entries must be micro-confirmed"
    );
}

#[test]
fn test_wave0_individual_evidence() {
    let env = wave0_env();
    let corpus = wave0_corpus();

    for (i, expr) in corpus.iter().enumerate() {
        let evidence = verify_expr(&env, expr)
            .unwrap_or_else(|e| panic!("Wave 0 corpus entry {i} failed: {e}"));
        assert!(
            evidence.replay_match(),
            "Corpus entry {i}: replay_match must be true"
        );
    }
}
