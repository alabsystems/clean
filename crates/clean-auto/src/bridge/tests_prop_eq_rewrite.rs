// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Eq.mp/Eq.mpr propositional rewriting (#2442 Phase 2C).
//!
//! Covers the grind-style `closeGoalWithTrueEqFalse` pattern:
//! - Eq.mpr with True rhs (h: P = True → P via Eq.mpr h True.intro)
//! - Eq.mp with True lhs (h: True = P → P via Eq.mp h True.intro)
//! - Eq.mpr/Eq.mp with provable other side
//! - Or.elim with Eq assumptions

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

fn mk_or(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a.clone()),
        b.clone(),
    )
}

fn mk_eq_prop(ty: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    // @Eq.{u+1} ty lhs rhs — for Prop-level, u+1 = 1
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Eq"),
                    vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
                ),
                ty.clone(),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

#[test]
#[timeout(30000)]
fn test_eq_mpr_with_true_rhs() {
    // Grind-style pattern: h : Eq(Prop, P, True), goal: P
    // Proof: Eq.mpr h True.intro : P
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let true_expr = prop("True");
    let eq_p_true = mk_eq_prop(&Expr::prop(), &p, &true_expr);

    bridge.prop_hypotheses.push((FVarId::new(400), eq_p_true));

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_propositional_proof(&goal_class, &p);
    assert!(
        result.is_ok(),
        "Eq.mpr with True rhs should succeed: {:?}",
        result.err()
    );
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.mpr"));
    // Verify proof structure: Eq.mpr _ _ h True.intro
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Eq.mpr")),
        "proof should be headed by Eq.mpr, got {:?}",
        head.kind()
    );
}

#[test]
#[timeout(30000)]
fn test_eq_mp_with_true_lhs() {
    // h : Eq(Prop, True, P), goal: P
    // Proof: Eq.mp h True.intro : P
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let true_expr = prop("True");
    let eq_true_p = mk_eq_prop(&Expr::prop(), &true_expr, &p);

    bridge.prop_hypotheses.push((FVarId::new(401), eq_true_p));

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_propositional_proof(&goal_class, &p);
    assert!(
        result.is_ok(),
        "Eq.mp with True lhs should succeed: {:?}",
        result.err()
    );
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.mp"));
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Eq.mp")),
        "proof should be headed by Eq.mp, got {:?}",
        head.kind()
    );
}

#[test]
#[timeout(30000)]
fn test_eq_mpr_with_provable_rhs() {
    // h1 : Eq(Prop, P, Q), h2 : Q, goal: P
    // Proof: Eq.mpr h1 h2 : P
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let eq_pq = mk_eq_prop(&Expr::prop(), &p, &q);

    bridge.prop_hypotheses.push((FVarId::new(410), eq_pq));
    bridge.prop_hypotheses.push((FVarId::new(411), q.clone()));

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_propositional_proof(&goal_class, &p);
    assert!(
        result.is_ok(),
        "Eq.mpr with provable rhs should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.mpr"));
}

#[test]
#[timeout(30000)]
fn test_eq_mp_with_provable_lhs() {
    // h1 : Eq(Prop, P, Q), h2 : P, goal: Q
    // Proof: Eq.mp h1 h2 : Q
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let eq_pq = mk_eq_prop(&Expr::prop(), &p, &q);

    bridge.prop_hypotheses.push((FVarId::new(420), eq_pq));
    bridge.prop_hypotheses.push((FVarId::new(421), p.clone()));

    let goal_class = bridge.classify_prop(&q);
    let result = bridge.build_propositional_proof(&goal_class, &q);
    assert!(
        result.is_ok(),
        "Eq.mp with provable lhs should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.mp"));
}

#[test]
#[timeout(30000)]
fn test_eq_rewrite_no_applicable_hypothesis() {
    // No Eq hypothesis, no direct match → should fail
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let p = prop("P");

    let result = bridge.try_eq_rewrite(&p, 0);
    assert!(
        result.is_err(),
        "eq_rewrite with no Eq hypothesis should fail"
    );
}

#[test]
#[timeout(30000)]
fn test_or_elim_with_eq_assumption_true_rhs() {
    // Or.elim where one branch assumption is Eq(Prop, P, True) (#2442 Phase 2C).
    // h1 : Or(Eq(Prop, P, True), Q), h2 : Q → P, goal: P
    // Left branch:  assumption = Eq(Prop, P, True) → Eq.mpr (bvar 0) True.intro : P
    // Right branch: assumption = Q → modus ponens with h2
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let true_expr = prop("True");
    let eq_p_true = mk_eq_prop(&Expr::prop(), &p, &true_expr);
    let or_eq_q = mk_or(&eq_p_true, &q);
    let implies_qp = Expr::pi(BinderInfo::Default, q.clone(), p.clone());

    bridge.prop_hypotheses.push((FVarId::new(430), or_eq_q));
    bridge.prop_hypotheses.push((FVarId::new(431), implies_qp));

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_propositional_proof(&goal_class, &p);
    assert!(
        result.is_ok(),
        "Or.elim with Eq assumption (True rhs) should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}
