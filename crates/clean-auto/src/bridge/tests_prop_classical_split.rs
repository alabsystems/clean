// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused coverage for the remaining propositional fallbacks in #2442.

use super::super::*;
use crate::proof::ProofStep;
use clean_kernel::env::Declaration;
use ntest::timeout;

fn setup_prop_env() -> Environment {
    let mut env = Environment::new();
    for (name, type_) in [
        (
            "And",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
        (
            "Or",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
        (
            "Not",
            Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        ),
        ("False", Expr::prop()),
        ("P", Expr::prop()),
        ("Q", Expr::prop()),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .unwrap();
    }
    env
}

fn prop(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_and(left: &Expr, right: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), left.clone()),
        right.clone(),
    )
}

fn mk_not(expr: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), expr.clone())
}

fn mk_or(left: &Expr, right: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), left.clone()),
        right.clone(),
    )
}

#[test]
#[timeout(30000)]
fn test_not_of_contradictory_and_uses_temporary_assumption() {
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let p = prop("P");
    let goal = mk_not(&mk_and(&p, &mk_not(&p)));
    let goal_class = bridge.classify_prop(&goal);

    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("non-contradiction should reconstruct natively");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Not.assumption"));
    match proof.kind() {
        ExprKind::Lam(_, _, body) => {
            let head = body.get_app_fn();
            assert!(
                matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("absurd")),
                "temporary assumption path should derive False via absurd, got {head:?}"
            );
        }
        other => panic!("expected lambda proof for non-contradiction, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_or_classical_split_handles_negated_conjunction_shape() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let neg_and = mk_not(&mk_and(&p, &q));
    let goal = mk_or(&mk_not(&p), &mk_not(&q));

    bridge.prop_hypotheses.push((FVarId::new(600), neg_and));

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("De Morgan shape should use a classical split");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.classical_split"));
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Or.rec")),
        "classical split should build an Or.rec case split, got {head:?}"
    );
    let args = proof.get_app_args();
    let em = args
        .last()
        .expect("Or.rec proof should carry the Classical.em witness");
    let em_head = em.get_app_fn();
    assert!(
        matches!(em_head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Classical.em")),
        "last Or.rec argument should be Classical.em, got {em_head:?}"
    );
    let em_args = em.get_app_args();
    assert!(
        matches!(em_args.first().map(|arg| arg.kind()), Some(ExprKind::Const(name, _)) if *name == Name::from_string("P")),
        "the classical split should case-split on P, got {em_args:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_prove_non_contradiction_is_verified() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let goal = mk_not(&mk_and(&p, &mk_not(&p)));

    let result = bridge
        .prove(&goal)
        .expect("non-contradiction should solve")
        .verified()
        .expect("non-contradiction should reconstruct a proof");

    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "Not.assumption"),
        "prove() should use the temporary-assumption negation path, got {:?}",
        result.proof_step()
    );
}

#[test]
#[timeout(30000)]
fn test_prove_de_morgan_shape_is_verified() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let neg_and = mk_not(&mk_and(&p, &q));
    let goal = mk_or(&mk_not(&p), &mk_not(&q));

    bridge
        .add_hypothesis_with_fvar(&neg_and, Some(FVarId::new(601)))
        .expect("negated conjunction hypothesis should assert");

    let result = bridge
        .prove(&goal)
        .expect("De Morgan shape should solve")
        .verified()
        .expect("De Morgan shape should reconstruct a proof");

    assert!(
        matches!(result.proof_step(), ProofStep::Propositional(s) if s == "Or.classical_split"),
        "prove() should use the classical split path, got {:?}",
        result.proof_step()
    );
}
