// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Multi-hop Eq.trans coverage for propositional reconstruction (#2442).
//!
//! Keeps the new transitivity-chain coverage isolated from the in-progress
//! Phase 3B test files in the shared worktree.

use super::super::*;
use super::test_helpers::{make_eq, setup_env};
use crate::proof::ProofStep;
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Environment, Expr, ExprKind, FVarId, Level, LocalContext, TypeChecker,
};
use ntest::timeout;

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

fn setup_multihop_env() -> Environment {
    let mut env = setup_env();
    let u = Name::from_string("u");
    add_eq_symm(&mut env, &u);
    add_eq_trans(&mut env, &u);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("d"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .unwrap();
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
fn test_eq_trans_multi_hop_mixed_directions() {
    let env = setup_multihop_env();
    let mut bridge = SmtBridge::new(&env);
    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);

    bridge
        .add_hypothesis_with_fvar(
            &make_eq(ty_a.clone(), a.clone(), b.clone()),
            Some(FVarId::new(10)),
        )
        .expect("first equality should assert");
    bridge
        .add_hypothesis_with_fvar(
            &make_eq(ty_a.clone(), c.clone(), b.clone()),
            Some(FVarId::new(11)),
        )
        .expect("reversed middle equality should assert");
    bridge
        .add_hypothesis_with_fvar(
            &make_eq(ty_a.clone(), c.clone(), d.clone()),
            Some(FVarId::new(12)),
        )
        .expect("last equality should assert");

    let goal = make_eq(ty_a, a, d);
    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("Eq(A, a, d) should succeed via multi-hop Eq.trans");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.trans"));
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Eq.trans")),
        "multi-hop equality proof should still be rooted at Eq.trans, got {head:?}"
    );
}

#[test]
fn test_eq_trans_multi_hop_mixed_directions_typecheck() {
    let env = setup_multihop_env();
    let mut bridge = SmtBridge::new(&env);
    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);
    let h_ab_id = FVarId::new(640);
    let h_cb_id = FVarId::new(641);
    let h_cd_id = FVarId::new(642);
    let h_ab = make_eq(ty_a.clone(), a.clone(), b.clone());
    let h_cb = make_eq(ty_a.clone(), c.clone(), b.clone());
    let h_cd = make_eq(ty_a.clone(), c.clone(), d.clone());
    let goal = make_eq(ty_a, a, d);

    bridge
        .add_hypothesis_with_fvar(&h_ab, Some(h_ab_id))
        .expect("first equality should assert");
    bridge
        .add_hypothesis_with_fvar(&h_cb, Some(h_cb_id))
        .expect("reversed middle equality should assert");
    bridge
        .add_hypothesis_with_fvar(&h_cd, Some(h_cd_id))
        .expect("last equality should assert");

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("Eq(A, a, d) should succeed via multi-hop Eq.trans");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.trans"));

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
    ctx.push_with_id(
        h_cd_id,
        Name::from_string("h_cd"),
        h_cd,
        BinderInfo::Default,
    );
    assert_proof_type_checks(
        &env,
        ctx,
        &proof,
        &goal,
        "Eq.trans sub-goal multi-hop mixed directions",
    );
}
