// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Iff (biconditional) decomposition in propositional proof reconstruction (#2442 Phase 2).
//!
//! Covers Iff.mp (forward), Iff.mpr (backward), and Or.elim branches with Iff assumptions.

use super::super::*;
use crate::proof::ProofStep;
use clean_kernel::env::Declaration;
use ntest::timeout;

fn prop(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_or(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a.clone()),
        b.clone(),
    )
}

fn mk_iff(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), a.clone()),
        b.clone(),
    )
}

fn add_iff_constructors(env: &mut Environment) {
    // Iff.mp : {a b : Prop} → (a ↔ b) → a → b
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Iff.mp"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::prop(),
                Expr::pi(
                    BinderInfo::Default,
                    mk_iff(&Expr::bvar(1), &Expr::bvar(0)),
                    Expr::pi(BinderInfo::Default, Expr::bvar(2), Expr::bvar(2)),
                ),
            ),
        ),
    })
    .unwrap();
    // Iff.mpr : {a b : Prop} → (a ↔ b) → b → a
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Iff.mpr"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::prop(),
                Expr::pi(
                    BinderInfo::Default,
                    mk_iff(&Expr::bvar(1), &Expr::bvar(0)),
                    Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(3)),
                ),
            ),
        ),
    })
    .unwrap();
}

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
            "Iff",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
        ("True", Expr::prop()),
        ("False", Expr::prop()),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .unwrap();
    }
    add_iff_constructors(&mut env);
    for name in ["P", "Q", "R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();
    }
    env
}

#[test]
#[timeout(30000)]
fn test_iff_mp_from_hypothesis() {
    // Top-level Iff.mp: h1 : Iff(P, Q), h2 : P, goal: Q
    // Iff.mp h1 h2 : Q
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let iff_pq = mk_iff(&p, &q);

    bridge.prop_hypotheses.push((FVarId::new(400), iff_pq));
    bridge.prop_hypotheses.push((FVarId::new(401), p.clone()));

    let goal_class = bridge.classify_prop(&q);
    let result = bridge.build_propositional_proof(&goal_class, &q);
    assert!(
        result.is_ok(),
        "Iff.mp should succeed with Iff(P,Q) + P hypothesis: {:?}",
        result.err()
    );
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Iff.mp"));
    // Verify proof structure: @Iff.mp P Q h1 h2
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Iff.mp")),
        "proof head should be Iff.mp, got {:?}",
        head.kind()
    );
    assert_eq!(proof.get_app_args().len(), 4, "Iff.mp takes 4 arguments");
}

#[test]
#[timeout(30000)]
fn test_iff_mpr_from_hypothesis() {
    // Top-level Iff.mpr: h1 : Iff(P, Q), h2 : Q, goal: P
    // Iff.mpr h1 h2 : P
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let iff_pq = mk_iff(&p, &q);

    bridge.prop_hypotheses.push((FVarId::new(410), iff_pq));
    bridge.prop_hypotheses.push((FVarId::new(411), q.clone()));

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_propositional_proof(&goal_class, &p);
    assert!(
        result.is_ok(),
        "Iff.mpr should succeed with Iff(P,Q) + Q hypothesis: {:?}",
        result.err()
    );
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Iff.mpr"));
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Iff.mpr")),
        "proof head should be Iff.mpr, got {:?}",
        head.kind()
    );
    assert_eq!(proof.get_app_args().len(), 4, "Iff.mpr takes 4 arguments");
}

#[test]
#[timeout(30000)]
fn test_or_elim_with_iff_assumption_forward() {
    // Or.elim where one branch has Iff assumption, using forward direction.
    // h1 : Or(Iff(P, Q), R), h2 : P, h3 : R → Q, goal: Q
    // Left branch:  assumption = Iff(P, Q), P provable via h2 → Iff.mp (bvar 0) h2
    // Right branch: assumption = R → assumption_modus_ponens with h3
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let r = prop("R");
    let iff_pq = mk_iff(&p, &q);
    let or_iff_r = mk_or(&iff_pq, &r);
    let implies_rq = Expr::pi(BinderInfo::Default, r.clone(), q.clone());

    bridge.prop_hypotheses.push((FVarId::new(420), or_iff_r));
    bridge.prop_hypotheses.push((FVarId::new(421), p.clone()));
    bridge.prop_hypotheses.push((FVarId::new(422), implies_rq));

    let goal_class = bridge.classify_prop(&q);
    let result = bridge.build_propositional_proof(&goal_class, &q);
    assert!(
        result.is_ok(),
        "Or.elim with Iff assumption (forward) should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}

#[test]
#[timeout(30000)]
fn test_or_elim_with_iff_assumption_backward() {
    // Or.elim where one branch has Iff assumption, using backward direction.
    // h1 : Or(Iff(P, Q), R), h2 : Q, h3 : R → P, goal: P
    // Left branch:  assumption = Iff(P, Q), Q provable via h2 → Iff.mpr (bvar 0) h2
    // Right branch: assumption = R → assumption_modus_ponens with h3
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let r = prop("R");
    let iff_pq = mk_iff(&p, &q);
    let or_iff_r = mk_or(&iff_pq, &r);
    let implies_rp = Expr::pi(BinderInfo::Default, r.clone(), p.clone());

    bridge.prop_hypotheses.push((FVarId::new(430), or_iff_r));
    bridge.prop_hypotheses.push((FVarId::new(431), q.clone()));
    bridge.prop_hypotheses.push((FVarId::new(432), implies_rp));

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_propositional_proof(&goal_class, &p);
    assert!(
        result.is_ok(),
        "Or.elim with Iff assumption (backward) should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}
