// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for theory-trail-guided hypothesis reconstruction (#2442).

use super::super::*;
use super::test_helpers::{make_eq, setup_env};
use crate::smt::ProofTrailEntry;
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Level, LocalContext, TypeChecker};
use ntest::timeout;

fn mk_and(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a.clone()),
        b.clone(),
    )
}

fn mk_not(expr: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), expr.clone())
}

fn mk_or(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a.clone()),
        b.clone(),
    )
}

fn expr_contains_bvar(expr: &Expr, target: u32) -> bool {
    fn zfc_contains_bvar(expr: &clean_kernel::expr::ZFCSetExpr, target: u32) -> bool {
        use clean_kernel::expr::ZFCSetExpr;

        match expr {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => false,
            ZFCSetExpr::Singleton(expr)
            | ZFCSetExpr::Union(expr)
            | ZFCSetExpr::PowerSet(expr)
            | ZFCSetExpr::Choice(expr) => expr_contains_bvar(expr, target),
            ZFCSetExpr::Pair(lhs, rhs) => {
                expr_contains_bvar(lhs, target) || expr_contains_bvar(rhs, target)
            }
            ZFCSetExpr::Separation { set, pred } | ZFCSetExpr::Replacement { set, func: pred } => {
                expr_contains_bvar(set, target) || expr_contains_bvar(pred, target)
            }
        }
    }

    match expr.kind() {
        ExprKind::BVar(idx) => *idx == target,
        ExprKind::App(func, arg) => {
            expr_contains_bvar(func, target) || expr_contains_bvar(arg, target)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_bvar(ty, target) || expr_contains_bvar(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_bvar(ty, target)
                || expr_contains_bvar(val, target)
                || expr_contains_bvar(body, target)
        }
        ExprKind::MData(_, inner) => expr_contains_bvar(inner, target),
        ExprKind::Proj(_, _, inner) => expr_contains_bvar(inner, target),
        ExprKind::Lit(_)
        | ExprKind::Const(_, _)
        | ExprKind::Sort(_)
        | ExprKind::FVar(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => false,
        ExprKind::Squash(inner) | ExprKind::CubicalPathLam { body: inner } => {
            expr_contains_bvar(inner, target)
        }
        ExprKind::CubicalPath { ty, left, right } => {
            expr_contains_bvar(ty, target)
                || expr_contains_bvar(left, target)
                || expr_contains_bvar(right, target)
        }
        ExprKind::CubicalPathApp { path, arg } => {
            expr_contains_bvar(path, target) || expr_contains_bvar(arg, target)
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            expr_contains_bvar(ty, target)
                || expr_contains_bvar(phi, target)
                || expr_contains_bvar(u, target)
                || expr_contains_bvar(base, target)
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            expr_contains_bvar(ty, target)
                || expr_contains_bvar(phi, target)
                || expr_contains_bvar(base, target)
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            expr_contains_bvar(ty, target)
                || expr_contains_bvar(r, target)
                || expr_contains_bvar(s, target)
                || expr_contains_bvar(base, target)
        }
        ExprKind::ZFCSet(inner) => zfc_contains_bvar(inner, target),
        ExprKind::ZFCMem { element, set } => {
            expr_contains_bvar(element, target) || expr_contains_bvar(set, target)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            expr_contains_bvar(domain, target) || expr_contains_bvar(pred, target)
        }
    }
}

fn assert_left_or_branch_rebuilds_shifted_eq_trans(proof: &Expr) {
    let args = proof.get_app_args();
    assert_eq!(args.len(), 6, "Or.elim proof should apply 6 arguments");

    match args[3].kind() {
        ExprKind::Lam(_, _, left_body) => match left_body.kind() {
            ExprKind::Lam(_, _, inner_body) => {
                let head = inner_body.get_app_fn();
                assert!(
                    matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("trans")),
                    "left branch should rebuild equality with Eq.trans under the nested implication, got {head:?}"
                );
                assert!(
                    expr_contains_bvar(inner_body, 1),
                    "left branch should shift the outer Or.elim assumption under the inner lambda"
                );
                assert!(
                    !expr_contains_bvar(inner_body, 0),
                    "left branch equality body should not capture the inner implication binder"
                );
            }
            other => panic!("expected nested implication lambda in left branch, got {other:?}"),
        },
        other => panic!("expected left Or.elim branch lambda, got {other:?}"),
    }
}

fn assert_right_or_branch_reuses_implication_assumption(proof: &Expr) {
    let args = proof.get_app_args();
    assert_eq!(args.len(), 6, "Or.elim proof should apply 6 arguments");

    match args[4].kind() {
        ExprKind::Lam(_, _, right_body) => {
            assert!(
                matches!(right_body.kind(), ExprKind::BVar(0)),
                "right branch should reuse the implication assumption directly"
            );
        }
        other => panic!("expected right Or.elim branch lambda, got {other:?}"),
    }
}

fn assert_theory_trail_steps(bridge: &SmtBridge<'_>) {
    assert!(
        !bridge.proof_trail().is_empty(),
        "expected a non-empty theory proof trail"
    );
    assert!(
        bridge
            .proof_trail()
            .iter()
            .any(|entry| matches!(entry, ProofTrailEntry::TheoryConflict { .. })),
        "expected equality theory conflict in proof trail"
    );
}

fn assert_guided_hypotheses(
    bridge: &SmtBridge<'_>,
    and_fvar: FVarId,
    neq_fvar: FVarId,
    noise_fvar: FVarId,
) {
    assert!(
        bridge.trail_hypothesis_hints.contains(&and_fvar),
        "trail hints should recover the parent And hypothesis FVarId"
    );
    assert!(
        bridge.trail_hypothesis_hints.contains(&neq_fvar),
        "trail hints should include the conflicting disequality hypothesis"
    );
    assert!(
        !bridge.trail_hypothesis_hints.contains(&noise_fvar),
        "trail hints should exclude unrelated hypotheses"
    );

    let guided_ids: Vec<_> = bridge
        .iter_guided_hypotheses()
        .map(|(fvar, _)| fvar)
        .collect();
    assert_eq!(
        guided_ids[0], and_fvar,
        "trail-related hypotheses should be preferred"
    );
    assert_eq!(
        guided_ids[1], neq_fvar,
        "trail-related hypotheses should stay ahead of noise"
    );
    assert_eq!(
        guided_ids[2], noise_fvar,
        "irrelevant hypotheses should remain as fallback"
    );
}

fn mk_eq_app(u: &Name, alpha_idx: u32, lhs_idx: u32, rhs_idx: u32) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::param(u.clone())]),
                Expr::bvar(alpha_idx),
            ),
            Expr::bvar(lhs_idx),
        ),
        Expr::bvar(rhs_idx),
    )
}

fn add_eq_symm(env: &mut Environment, u: &Name) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.symm"),
        level_params: vec![u.clone()],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(u.clone())),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::bvar(0),
                Expr::pi(
                    BinderInfo::Implicit,
                    Expr::bvar(1),
                    Expr::pi(
                        BinderInfo::Default,
                        mk_eq_app(u, 2, 1, 0),
                        mk_eq_app(u, 3, 1, 2),
                    ),
                ),
            ),
        ),
    })
    .unwrap();
}

fn add_eq_trans(env: &mut Environment, u: &Name) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.trans"),
        level_params: vec![u.clone()],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(u.clone())),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::bvar(0),
                Expr::pi(
                    BinderInfo::Implicit,
                    Expr::bvar(1),
                    Expr::pi(
                        BinderInfo::Implicit,
                        Expr::bvar(2),
                        Expr::pi(
                            BinderInfo::Default,
                            mk_eq_app(u, 3, 2, 1),
                            Expr::pi(
                                BinderInfo::Default,
                                mk_eq_app(u, 4, 2, 1),
                                mk_eq_app(u, 5, 4, 2),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    })
    .unwrap();
}

fn setup_guided_eq_env() -> Environment {
    let mut env = setup_env();
    let u = Name::from_string("u");
    add_eq_symm(&mut env, &u);
    add_eq_trans(&mut env, &u);
    env
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
#[timeout(30000)]
fn test_prove_reconstructs_equality_from_trail_guided_and_hypothesis() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    let noise_fvar = FVarId::new(900);
    let and_fvar = FVarId::new(901);
    let neq_fvar = FVarId::new(902);

    let noise_eq = make_eq(ty.clone(), a.clone(), a.clone());
    let eq_ab = make_eq(ty.clone(), a.clone(), b.clone());
    let eq_bc = make_eq(ty.clone(), b.clone(), c.clone());
    let eq_ac = make_eq(ty.clone(), a.clone(), c.clone());
    let neq_ac = mk_not(&eq_ac);

    bridge
        .add_hypothesis_with_fvar(&noise_eq, Some(noise_fvar))
        .expect("noise hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&mk_and(&eq_ab, &eq_bc), Some(and_fvar))
        .expect("conjunctive equality hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&neq_ac, Some(neq_fvar))
        .expect("negated equality hypothesis should assert");

    let result = bridge
        .prove(&eq_ac)
        .expect("conjunctive equality goal should solve");
    assert_theory_trail_steps(&bridge);
    assert_guided_hypotheses(&bridge, and_fvar, neq_fvar, noise_fvar);

    assert!(
        result.is_verified(),
        "trail-guided equality reconstruction should build a native proof, got {result:?}"
    );
    let proof_result = result
        .verified()
        .expect("verified equality proof should be available");
    let proof = proof_result.proof_term();
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("trans")),
        "conjunctive equality proof should build an Eq.trans chain, got {head:?}"
    );

    let step = proof_result.proof_step();
    assert!(
        matches!(step, ProofStep::Trans(_, _)),
        "conjunctive equality proof should report a transitivity step, got {step:?}"
    );
    let hyp_ids = super::collect_hypothesis_ids(step);
    assert_eq!(
        hyp_ids,
        vec![and_fvar, and_fvar],
        "the proof should use the parent conjunction hypothesis for both equality legs"
    );
    assert!(
        !hyp_ids.contains(&noise_fvar),
        "the proof should not use the unrelated noise hypothesis"
    );
}

#[test]
#[timeout(30000)]
fn test_builds_implication_body_from_conjunctive_equality_assumption() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    for term in [&a, &b, &c] {
        bridge
            .translate_term(term)
            .expect("equality terms should translate before reconstruction");
    }

    let eq_ab = make_eq(ty.clone(), a.clone(), b.clone());
    let eq_bc = make_eq(ty.clone(), b.clone(), c.clone());
    let eq_ac = make_eq(ty.clone(), a.clone(), c.clone());
    let premise = mk_and(&eq_ab, &eq_bc);
    let goal = Expr::pi(BinderInfo::Default, premise.clone(), eq_ac.clone());

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("implication should reconstruct equality from its assumption");

    assert!(
        matches!(&step, ProofStep::Propositional(s) if s == "Implies.assumption_eq"),
        "expected the implication equality-assumption strategy, got {step:?}"
    );
    match proof.kind() {
        ExprKind::Lam(_, _, body) => {
            let head = body.get_app_fn();
            assert!(
                matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("trans")),
                "implication body should build an Eq.trans chain, got {head:?}"
            );
        }
        other => panic!("expected lambda proof for implication goal, got {other:?}"),
    }
}

#[test]
fn test_guided_equality_multihop_reversed_leg_typechecks() {
    let env = setup_guided_eq_env();
    let mut bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let h_ab_id = FVarId::new(930);
    let h_cb_id = FVarId::new(931);
    let h_ab = make_eq(ty.clone(), a.clone(), b.clone());
    let h_cb = make_eq(ty.clone(), c.clone(), b.clone());
    let goal = make_eq(ty.clone(), a.clone(), c.clone());

    bridge
        .add_hypothesis_with_fvar(&h_ab, Some(h_ab_id))
        .expect("first guided equality should assert");
    bridge
        .add_hypothesis_with_fvar(&h_cb, Some(h_cb_id))
        .expect("reversed guided equality should assert");

    let lhs_term = bridge
        .translate_term(&a)
        .expect("lhs term should register before guided equality proof search");
    let rhs_term = bridge
        .translate_term(&c)
        .expect("rhs term should register before guided equality proof search");

    let (step, proof) = bridge
        .try_guided_hypothesis_equality_proof(lhs_term, rhs_term, &a, &c, &ty)
        .expect("guided equality proof search should succeed")
        .expect("guided equality proof should exist");

    assert!(
        matches!(step, ProofStep::Trans(_, _)),
        "guided multi-hop proof should record a transitivity step, got {step:?}"
    );

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_ab_id,
        Name::from_string("h_ab"),
        h_ab,
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_cb_id,
        Name::from_string("h_cb"),
        h_cb,
        BinderInfo::Default,
    );

    assert_proof_type_checks(
        &env,
        ctx,
        &proof,
        &goal,
        "guided equality multi-hop reversed leg",
    );
}

#[test]
#[timeout(30000)]
fn test_prove_reconstructs_equality_from_or_branch_assumption() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    let eq_ab = make_eq(ty.clone(), a.clone(), b.clone());
    let eq_bc = make_eq(ty.clone(), b.clone(), c.clone());
    let eq_ac = make_eq(ty.clone(), a.clone(), c.clone());
    let disj = mk_or(&mk_and(&eq_ab, &eq_bc), &eq_ac);

    bridge
        .add_hypothesis_with_fvar(&disj, Some(FVarId::new(903)))
        .expect("disjunctive equality hypothesis should assert");

    let result = bridge
        .prove(&eq_ac)
        .expect("equality goal from disjunctive hypothesis should solve");
    let proof_result = result
        .verified()
        .expect("Or branch equality should reconstruct a native proof");
    assert!(
        matches!(proof_result.proof_step(), ProofStep::Propositional(s) if s == "Or.elim"),
        "expected Or.elim proof reconstruction, got {:?}",
        proof_result.proof_step()
    );
}

#[test]
#[timeout(30000)]
fn test_or_branch_equality_assumption_shifts_under_nested_implication() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let r = Expr::const_(Name::from_string("R"), vec![]);

    for term in [&a, &b, &c] {
        bridge
            .translate_term(term)
            .expect("equality terms should translate before nested implication reconstruction");
    }

    let eq_ab = make_eq(ty.clone(), a.clone(), b.clone());
    let eq_bc = make_eq(ty.clone(), b.clone(), c.clone());
    let eq_ac = make_eq(ty.clone(), a.clone(), c.clone());
    let premise = mk_and(&eq_ab, &eq_bc);
    let goal = Expr::pi(BinderInfo::Default, r, eq_ac.clone());
    let disj = mk_or(&premise, &goal);

    bridge
        .add_hypothesis_with_fvar(&disj, Some(FVarId::new(904)))
        .expect("disjunction hypothesis should assert");

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("Or.elim should rebuild the implication with a shifted equality assumption");

    assert!(
        matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"),
        "expected Or.elim proof reconstruction, got {step:?}"
    );
    assert_left_or_branch_rebuilds_shifted_eq_trans(&proof);
    assert_right_or_branch_reuses_implication_assumption(&proof);
}
