// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel type-check coverage for Phase 3 propositional proof reconstruction (#2442).
//!
//! Mirrors the pattern from `tests_arith_typecheck.rs`: builds proof terms via
//! SmtBridge, then verifies them against the original goal using the kernel
//! TypeChecker. This provides stronger assurance than the structural checks in
//! `tests_prop_phase3.rs`.

use super::super::*;
use crate::proof::ProofStep;
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Level, LocalContext, TypeChecker};

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

/// Build an environment with Eq, Eq.refl, Eq.symm, Eq.trans, type A, and constants a/b/c.
fn add_eq_core(env: &mut Environment, u: &Name) {
    // Eq : {α : Sort u} → α → α → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![u.clone()],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(u.clone())),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
            ),
        ),
    })
    .unwrap();
}

fn add_eq_refl(env: &mut Environment, u: &Name) {
    // Eq.refl : ∀ {α : Sort u} (a : α), Eq α a a
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.refl"),
        level_params: vec![u.clone()],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(u.clone())),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), vec![Level::param(u.clone())]),
                            Expr::bvar(1),
                        ),
                        Expr::bvar(0),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    })
    .unwrap();
}

fn add_eq_symm(env: &mut Environment, u: &Name) {
    // Eq.symm : ∀ {α : Sort u} {a b : α}, Eq α a b → Eq α b a
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
    // Eq.trans : ∀ {α : Sort u} {a b c : α}, Eq α a b → Eq α b c → Eq α a c
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

fn add_test_constants(env: &mut Environment) {
    // A : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("A"), vec![]),
        })
        .unwrap();
    }
}

fn setup_eq_env() -> Environment {
    let mut env = Environment::new();
    let u = Name::from_string("u");

    add_eq_core(&mut env, &u);
    add_eq_refl(&mut env, &u);
    add_eq_symm(&mut env, &u);
    add_eq_trans(&mut env, &u);
    add_test_constants(&mut env);

    env
}

fn mk_eq(ty: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty.clone(),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
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

/// Eq.refl standalone: @Eq.refl A a type-checks against Eq A a a.
#[test]
fn test_eq_refl_standalone_kernel_typecheck() {
    let env = setup_eq_env();
    let bridge = SmtBridge::new(&env);
    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = mk_eq(&ty_a, &a, &a);

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("Eq(A, a, a) should succeed via Eq.refl");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.refl"));
    assert_proof_type_checks(
        &env,
        LocalContext::new(),
        &proof,
        &goal,
        "Eq.refl standalone",
    );
}

/// Forall + Eq.refl: fun (x : A) => @Eq.refl A x type-checks against
/// ∀ (x : A), Eq A x x.
///
/// This is the critical test for bvar handling in the Forall lambda wrapper:
/// the body proof's bvar(0) must correctly refer to the lambda-bound variable.
#[test]
fn test_forall_eq_refl_kernel_typecheck() {
    let env = setup_eq_env();
    let bridge = SmtBridge::new(&env);
    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let eq_body = mk_eq(&ty_a, &Expr::bvar(0), &Expr::bvar(0));
    let goal = Expr::pi(BinderInfo::Default, ty_a, eq_body);

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("∀ x : A, x = x should succeed via Forall.lam + Eq.refl");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Forall.lam"));
    assert_proof_type_checks(
        &env,
        LocalContext::new(),
        &proof,
        &goal,
        "Forall eq_refl body",
    );
}

/// Eq.symm sub-goal: a reversed equality hypothesis should type-check when the
/// sub-goal builder flips it to match the requested orientation.
#[test]
fn test_eq_symm_subgoal_kernel_typecheck() {
    let env = setup_eq_env();
    let mut bridge = SmtBridge::new(&env);
    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let hyp_id = FVarId::new(610);
    let hyp = mk_eq(&ty_a, &b, &a);
    let goal = mk_eq(&ty_a, &a, &b);

    bridge
        .add_hypothesis_with_fvar(&hyp, Some(hyp_id))
        .expect("reversed equality hypothesis should assert");

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("Eq(A, a, b) should succeed via Eq.symm");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.symm"));

    let mut ctx = LocalContext::new();
    ctx.push_with_id(hyp_id, Name::from_string("h_ba"), hyp, BinderInfo::Default);
    assert_proof_type_checks(&env, ctx, &proof, &goal, "Eq.symm sub-goal");
}

/// Eq.trans sub-goal: direct/direct chain (a=b, b=c ⊢ a=c) type-checks.
#[test]
fn test_eq_trans_subgoal_kernel_typecheck_direct_chain() {
    let env = setup_eq_env();
    let mut bridge = SmtBridge::new(&env);
    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let h_ab_id = FVarId::new(620);
    let h_bc_id = FVarId::new(621);
    let h_ab = mk_eq(&ty_a, &a, &b);
    let h_bc = mk_eq(&ty_a, &b, &c);
    let goal = mk_eq(&ty_a, &a, &c);

    bridge
        .add_hypothesis_with_fvar(&h_ab, Some(h_ab_id))
        .expect("first equality should assert");
    bridge
        .add_hypothesis_with_fvar(&h_bc, Some(h_bc_id))
        .expect("second equality should assert");

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("Eq(A, a, c) should succeed via Eq.trans direct chain");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.trans"));

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_ab_id,
        Name::from_string("h_ab"),
        h_ab,
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_bc_id,
        Name::from_string("h_bc"),
        h_bc,
        BinderInfo::Default,
    );
    assert_proof_type_checks(&env, ctx, &proof, &goal, "Eq.trans sub-goal direct chain");
}

/// Eq.trans sub-goal: symm/symm chain (b=a, c=b ⊢ a=c) type-checks after the
/// builder wraps both hypothesis references with Eq.symm.
#[test]
fn test_eq_trans_subgoal_kernel_typecheck_with_both_reversed() {
    let env = setup_eq_env();
    let mut bridge = SmtBridge::new(&env);
    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let h_ba_id = FVarId::new(630);
    let h_cb_id = FVarId::new(631);
    let h_ba = mk_eq(&ty_a, &b, &a);
    let h_cb = mk_eq(&ty_a, &c, &b);
    let goal = mk_eq(&ty_a, &a, &c);

    bridge
        .add_hypothesis_with_fvar(&h_ba, Some(h_ba_id))
        .expect("reversed first equality should assert");
    bridge
        .add_hypothesis_with_fvar(&h_cb, Some(h_cb_id))
        .expect("reversed second equality should assert");

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("Eq(A, a, c) should succeed via Eq.trans with both reversed");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.trans"));

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_ba_id,
        Name::from_string("h_ba"),
        h_ba,
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
        "Eq.trans sub-goal with both reversed",
    );
}

/// Eq.trans sub-goal: a mixed-direction one-step chain should still type-check
/// after the builder inserts the necessary symmetry wrapper on the first edge.
#[test]
fn test_eq_trans_subgoal_kernel_typecheck_with_reversed_first_edge() {
    let env = setup_eq_env();
    let mut bridge = SmtBridge::new(&env);
    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let h_ba_id = FVarId::new(611);
    let h_bc_id = FVarId::new(612);
    let h_ba = mk_eq(&ty_a, &b, &a);
    let h_bc = mk_eq(&ty_a, &b, &c);
    let goal = mk_eq(&ty_a, &a, &c);

    bridge
        .add_hypothesis_with_fvar(&h_ba, Some(h_ba_id))
        .expect("reversed first equality should assert");
    bridge
        .add_hypothesis_with_fvar(&h_bc, Some(h_bc_id))
        .expect("second equality should assert");

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("Eq(A, a, c) should succeed via Eq.trans with a reversed first edge");

    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.trans"));

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_ba_id,
        Name::from_string("h_ba"),
        h_ba,
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_bc_id,
        Name::from_string("h_bc"),
        h_bc,
        BinderInfo::Default,
    );
    assert_proof_type_checks(
        &env,
        ctx,
        &proof,
        &goal,
        "Eq.trans sub-goal with reversed first edge",
    );
}
