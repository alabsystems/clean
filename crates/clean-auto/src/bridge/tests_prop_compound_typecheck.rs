// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel type-check coverage for compound propositional reconstruction (#2442).

use super::super::*;
use crate::proof::ProofStep;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, LocalContext, TypeChecker};

fn setup_prop_env() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    env.init_and().unwrap();
    env.init_iff().unwrap();
    env.init_classical().unwrap();

    for name in ["P", "Q", "R"] {
        env.add_decl(clean_kernel::env::Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();
    }

    env
}

fn prop(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_and(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a.clone()),
        b.clone(),
    )
}

fn mk_or(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a.clone()),
        b.clone(),
    )
}

fn mk_not(a: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), a.clone())
}

fn mk_iff(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), a.clone()),
        b.clone(),
    )
}

fn assert_proof_type_checks(
    env: &Environment,
    ctx: LocalContext,
    proof: &Expr,
    goal: &Expr,
    msg: &str,
) {
    let tc = TypeChecker::with_context(env, ctx);
    tc.check_type(proof, goal)
        .unwrap_or_else(|e| panic!("{msg}: proof should check against goal {goal:?}: {e:?}"));
}

#[test]
fn test_and_intro_kernel_typecheck() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let goal = mk_and(&p, &q);
    let hp = FVarId::new(700);
    let hq = FVarId::new(701);

    bridge.prop_hypotheses.push((hp, p.clone()));
    bridge.prop_hypotheses.push((hq, q.clone()));

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("And(P, Q) should succeed via And.intro");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "And.intro"));

    let mut ctx = LocalContext::new();
    ctx.push_with_id(hp, Name::from_string("hp"), p, BinderInfo::Default);
    ctx.push_with_id(hq, Name::from_string("hq"), q, BinderInfo::Default);
    assert_proof_type_checks(&env, ctx, &proof, &goal, "And.intro");
}

#[test]
fn test_or_inl_kernel_typecheck() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let goal = mk_or(&p, &q);
    let hp = FVarId::new(710);

    bridge.prop_hypotheses.push((hp, p.clone()));

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("Or(P, Q) should succeed via Or.inl");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.inl"));

    let mut ctx = LocalContext::new();
    ctx.push_with_id(hp, Name::from_string("hp"), p, BinderInfo::Default);
    assert_proof_type_checks(&env, ctx, &proof, &goal, "Or.inl");
}

#[test]
fn test_or_inr_kernel_typecheck() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let goal = mk_or(&p, &q);
    let hq = FVarId::new(711);

    // Only Q available — must use Or.inr (right injection)
    bridge.prop_hypotheses.push((hq, q.clone()));

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("Or(P, Q) should succeed via Or.inr when only Q is available");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.inr"));

    let mut ctx = LocalContext::new();
    ctx.push_with_id(hq, Name::from_string("hq"), q, BinderInfo::Default);
    assert_proof_type_checks(&env, ctx, &proof, &goal, "Or.inr");
}

#[test]
fn test_implies_lam_kernel_typecheck() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let goal = Expr::pi(BinderInfo::Default, p.clone(), q.clone());
    let hq = FVarId::new(720);

    bridge.prop_hypotheses.push((hq, q.clone()));

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("P -> Q should succeed via Implies.lam when Q is already known");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Implies.lam"));

    let mut ctx = LocalContext::new();
    ctx.push_with_id(hq, Name::from_string("hq"), q, BinderInfo::Default);
    assert_proof_type_checks(&env, ctx, &proof, &goal, "Implies.lam");
}

#[test]
fn test_not_lam_absurd_kernel_typecheck() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let goal = mk_not(&p);
    let hnp = FVarId::new(730);

    bridge.prop_hypotheses.push((hnp, goal.clone()));

    let (step, proof) = bridge
        .build_not_proof(&p, 0)
        .expect("Not(P) should succeed via Not.lam_absurd");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Not.lam_absurd"));

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        hnp,
        Name::from_string("hnp"),
        goal.clone(),
        BinderInfo::Default,
    );
    assert_proof_type_checks(&env, ctx, &proof, &goal, "Not.lam_absurd");
}

#[test]
fn test_iff_intro_kernel_typecheck() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let goal = mk_iff(&p, &q);
    let hpq = FVarId::new(740);
    let hqp = FVarId::new(741);
    let p_implies_q = Expr::pi(BinderInfo::Default, p.clone(), q.clone());
    let q_implies_p = Expr::pi(BinderInfo::Default, q.clone(), p.clone());

    bridge.prop_hypotheses.push((hpq, p_implies_q.clone()));
    bridge.prop_hypotheses.push((hqp, q_implies_p.clone()));

    let goal_class = LogicalForm::Iff(p, q);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("Iff(P, Q) should succeed via Iff.intro");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Iff.intro"));

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        hpq,
        Name::from_string("hpq"),
        p_implies_q,
        BinderInfo::Default,
    );
    ctx.push_with_id(
        hqp,
        Name::from_string("hqp"),
        q_implies_p,
        BinderInfo::Default,
    );
    assert_proof_type_checks(&env, ctx, &proof, &goal, "Iff.intro");
}
