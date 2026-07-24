// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for propositional proof reconstruction fallback paths (#302 self-audit).
//!
//! Covers the try_ex_falso fallback that fires after all match arms fail:
//! when a non-False goal has no direct strategy but contradictory hypotheses
//! Q + ¬Q exist, try_ex_falso builds `absurd Q ¬Q : target` via False.elim.

use super::super::*;
use crate::proof::ProofStep;
use clean_kernel::env::Declaration;
use ntest::timeout;

fn add_prop_axioms(env: &mut Environment) {
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
        ("True", Expr::prop()),
        ("False", Expr::prop()),
        (
            "Iff",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .unwrap();
    }
}

fn add_prop_constructors(env: &mut Environment) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("True.intro"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("True"), vec![]),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("False.elim"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Default,
                Expr::const_(Name::from_string("False"), vec![]),
                Expr::bvar(1),
            ),
        ),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("absurd"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::prop(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::app(
                            Expr::const_(Name::from_string("Not"), vec![]),
                            Expr::bvar(2),
                        ),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    })
    .unwrap();
}

fn add_prop_constants(env: &mut Environment) {
    for name in ["P", "Q", "R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();
    }
}

fn setup_prop_env() -> Environment {
    let mut env = Environment::new();
    add_prop_axioms(&mut env);
    add_prop_constructors(&mut env);
    add_prop_constants(&mut env);
    env
}

fn prop(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_not(a: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), a.clone())
}

#[test]
#[timeout(30000)]
fn test_ex_falso_fallback_from_contradiction() {
    // Coverage: try_ex_falso fallback at build_prop_proof_inner (after all match arms fail).
    // Goal P is an atom with no matching hypothesis and no structural strategy.
    // Contradictory hypotheses Q and ¬Q exist, so the fallback builds:
    //   absurd (fvar Q) (fvar ¬Q) : P  (via False.elim P (absurd ...))
    //
    // Code path: build_prop_proof_inner → match goal_class → _ (Atom) → Err →
    //   result.or_else(|_| try_ex_falso(goal_expr)) → try_absurd_from_hypotheses → Ok
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let not_q = mk_not(&q);

    bridge.prop_hypotheses.push((FVarId::new(400), q.clone()));
    bridge.prop_hypotheses.push((FVarId::new(401), not_q));

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_propositional_proof(&goal_class, &p);
    assert!(
        result.is_ok(),
        "ex_falso from Q + ¬Q contradiction should prove P: {:?}",
        result.err()
    );
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "absurd"));

    // Verify proof structure: absurd applied to (Q_type, P, fvar(Q), fvar(¬Q))
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("absurd")),
        "ex_falso proof should be headed by absurd, got {:?}",
        head.kind()
    );
}

#[test]
#[timeout(30000)]
fn test_ex_falso_fallback_with_false_hypothesis() {
    // Coverage: try_ex_falso fallback when a direct False hypothesis exists.
    // Goal P is an atom, hypothesis is False → try_ex_falso → False.elim P h_false.
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let false_expr = Expr::const_(Name::from_string("False"), vec![]);

    bridge.prop_hypotheses.push((FVarId::new(402), false_expr));

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_propositional_proof(&goal_class, &p);
    assert!(
        result.is_ok(),
        "ex_falso from False hypothesis should prove P: {:?}",
        result.err()
    );
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "False.elim"));

    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("False.elim")),
        "ex_falso with False hypothesis should use False.elim, got {:?}",
        head.kind()
    );
}

#[test]
#[timeout(30000)]
fn test_budget_exhaustion_returns_exact_error() {
    // Coverage: node budget guard at build_prop_proof_inner.
    // After setting budget to 0, the next call should immediately fail with
    // the budget exhaustion error (not the depth error).
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let p = prop("P");

    bridge.prop_reconstruction_budget.set(0);

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_prop_proof_inner(&goal_class, &p, 0);
    assert!(
        matches!(result, Err(BridgeError::ProofTraceFailed(ref msg))
            if msg == "propositional proof reconstruction node budget exhausted"),
        "budget guard should return the dedicated exhaustion error, got {:?}",
        result
    );
}
