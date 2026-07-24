// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Refutation-wrapping coverage for `ay_refutation::wrap_refutation_as_goal_proof(...)`.

#[cfg(feature = "ay-smt")]
use super::super::*;
#[cfg(feature = "ay-smt")]
use super::support::*;
#[cfg(feature = "ay-smt")]
use clean_kernel::env::Declaration;
#[cfg(feature = "ay-smt")]
use clean_kernel::name::Name;
#[cfg(feature = "ay-smt")]
use clean_kernel::{Environment, Expr, TypeChecker};

#[cfg(feature = "ay-smt")]
#[test]
fn test_wrap_refutation_as_goal_proof_abstracts_negated_goal_assumption() {
    let (env, p) = mk_prop_hyp_env(false);
    let neg_p = mk_negated(&p);
    let neg_fvar = clean_kernel::FVarId::new(123);
    let refutation = mk_absurd_false(
        &p,
        &Expr::const_(Name::from_string("hp"), vec![]),
        &Expr::fvar(neg_fvar),
    );

    let proof =
        ay_refutation::wrap_refutation_as_goal_proof(&p, &neg_p, refutation, Some(neg_fvar));
    assert_by_contradiction_head(&proof, "negated-goal abstraction");

    assert_inferred_type(&env, &proof, &p, "wrapped refutation should prove P");
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_wrap_refutation_as_goal_proof_lifts_hypothesis_only_contradiction() {
    let mut env = Environment::new();
    env.init_true_false().expect("init True/False");
    env.init_classical().expect("init Classical");
    for (name, ty) in [
        ("P", Expr::prop()),
        ("Q", Expr::prop()),
        ("hq", Expr::const_(Name::from_string("Q"), vec![])),
        (
            "hnq",
            Expr::app(
                Expr::const_(Name::from_string("Not"), vec![]),
                Expr::const_(Name::from_string("Q"), vec![]),
            ),
        ),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
        .expect("axiom declaration should succeed");
    }

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let neg_p = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p.clone());
    let refutation = mk_absurd_false(
        &q,
        &Expr::const_(Name::from_string("hq"), vec![]),
        &Expr::const_(Name::from_string("hnq"), vec![]),
    );

    let proof = ay_refutation::wrap_refutation_as_goal_proof(&p, &neg_p, refutation, None);
    assert_by_contradiction_head(&proof, "hypothesis-only contradiction");

    let inferred = TypeChecker::new(&env)
        .infer_type(&proof)
        .expect("wrapped ex falso proof should typecheck");
    assert_eq!(inferred, p, "wrapped contradiction should prove P");
}
