// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E2E tests for ThResolution and Or Alethe rule handlers.
//!
//! These tests verify that `ProofStep::Step { rule: ThResolution/Or }` steps
//! produce proof terms that type-check through the kernel, matching how ay
//! actually emits proofs (as opposed to boolean tautology rules it never emits).
//!
//! Part of #2432, #2427.

use super::{attempt_reconstruction, ReconstructionResult, VariableMapping};
use ay::Sort;
use ay_core::{Proof, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, ExprKind, FVarId, Level, LocalContext, TypeChecker,
};

/// Create a minimal environment with Eq, Nat, Not/absurd/False, and test axioms.
fn mk_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["testA", "testB"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat_ty.clone(),
        })
        .unwrap_or_else(|e| panic!("add {name}: {e:?}"));
    }
    env
}

/// Create an environment with Or, Classical.em, Eq, Int, absurd, and test axioms.
fn mk_env_with_classical() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_int().expect("init_int");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["testA", "testB", "testC"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .unwrap_or_else(|e| panic!("add {name}: {e:?}"));
    }
    env
}

/// Build `@Eq.{1} Nat testA testB`.
fn mk_eq_prop() -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let u1 = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![u1]), nat_ty),
            a,
        ),
        b,
    )
}

/// Build `Not (Eq Nat testA testB)`.
fn mk_neq_prop() -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), mk_eq_prop())
}

/// Build `@Eq.{1} Int x y` for named Int axioms.
fn mk_eq_int(x: &str, y: &str) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let x_expr = Expr::const_(Name::from_string(x), vec![]);
    let y_expr = Expr::const_(Name::from_string(y), vec![]);
    let u1 = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![u1]), int_ty),
            x_expr,
        ),
        y_expr,
    )
}

/// Replace sentinel FVarIds with normal ones and add to local context.
fn finalize_proof(
    result: &ReconstructionResult,
    proof_term: Expr,
    ctx: &mut LocalContext,
    neg_goal: &Expr,
) -> Expr {
    if let Some(sentinel_id) = result.negated_goal_fvar {
        let normal_neg_id = FVarId::new(20);
        let term = proof_term.subst_fvar(sentinel_id, &Expr::fvar(normal_neg_id));
        ctx.push_with_id(
            normal_neg_id,
            Name::from_string("h_neg"),
            neg_goal.clone(),
            BinderInfo::Default,
        );
        term
    } else {
        proof_term
    }
}

/// Assert that a proof term type-checks to False.
fn assert_type_checks_to_false(env: &Environment, ctx: LocalContext, proof: &Expr, msg: &str) {
    let tc = TypeChecker::with_context(env, ctx);
    let ty = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("{msg}: type-check failed: {e:?}"));
    assert!(
        matches!(ty.kind(), ExprKind::Const(n, _) if *n == Name::from_string("False")),
        "{msg}: expected type False, got {:?}",
        ty.kind(),
    );
}

/// Build ay proof: Assume(p), Assume(¬p), ThResolution([], [h1, h2]) → contradiction.
fn mk_unit_contradiction_th_res() -> (TermStore, VariableMapping, Proof, FVarId) {
    let eq_prop = mk_eq_prop();
    let h_eq_id = FVarId::new(10);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let p = terms.mk_var("p", Sort::Bool);
    map.register_var("p", eq_prop.clone(), Expr::prop());
    map.register_hypothesis("p", h_eq_id, Expr::fvar(h_eq_id), eq_prop);

    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(p, None);
    let h2 = proof.add_assume(not_p, None);
    proof.add_rule_step(
        ay_core::AletheRule::ThResolution,
        vec![],
        vec![h1, h2],
        vec![],
    );

    (terms, map, proof, h_eq_id)
}

/// E2E: ThResolution unit contradiction → kernel type-checks to False.
///
/// Part of #2432.
#[test]
fn test_e2e_th_resolution_unit_contradiction_type_checks() {
    let env = mk_env();
    let eq_prop = mk_eq_prop();
    let neq_prop = mk_neq_prop();
    let (terms, map, proof, h_eq_id) = mk_unit_contradiction_th_res();

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_eq_id,
        Name::from_string("h_eq"),
        eq_prop,
        BinderInfo::Default,
    );

    let result = attempt_reconstruction(&proof, &terms, &map, &neq_prop);
    assert!(
        result.stats.reconstructed_steps >= 3,
        "all 3 steps should reconstruct, got {} (error: {:?})",
        result.stats.reconstructed_steps,
        result.stats.error,
    );
    assert_eq!(result.stats.rule_attempts.get("th_resolution"), Some(&1));
    assert_eq!(result.stats.rule_successes.get("th_resolution"), Some(&1));

    let proof_term = result
        .proof_term
        .clone()
        .expect("should produce a proof term");
    let proof_term = finalize_proof(&result, proof_term, &mut ctx, &neq_prop);
    assert_type_checks_to_false(&env, ctx, &proof_term, "ThResolution unit contradiction");
}

/// E2E: Or rule (identity) + ThResolution → kernel type-checks to False.
///
/// Part of #2432, #2427.
#[test]
fn test_e2e_or_then_th_resolution_type_checks() {
    let env = mk_env();
    let eq_prop = mk_eq_prop();
    let neq_prop = mk_neq_prop();
    let h_eq_id = FVarId::new(10);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let p = terms.mk_var("p", Sort::Bool);
    map.register_var("p", eq_prop.clone(), Expr::prop());
    map.register_hypothesis("p", h_eq_id, Expr::fvar(h_eq_id), eq_prop.clone());
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    let s0 = proof.add_assume(p, None);
    let s1 = proof.add_rule_step(ay_core::AletheRule::Or, vec![p], vec![s0], vec![]);
    let s2 = proof.add_assume(not_p, None);
    proof.add_rule_step(
        ay_core::AletheRule::ThResolution,
        vec![],
        vec![s1, s2],
        vec![],
    );

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_eq_id,
        Name::from_string("h_eq"),
        eq_prop,
        BinderInfo::Default,
    );

    let result = attempt_reconstruction(&proof, &terms, &map, &neq_prop);
    assert!(
        result.stats.reconstructed_steps >= 4,
        "all 4 steps: {:?}",
        result.stats.error
    );
    assert_eq!(result.stats.rule_attempts.get("or"), Some(&1));
    assert_eq!(result.stats.rule_attempts.get("th_resolution"), Some(&1));

    let proof_term = result
        .proof_term
        .clone()
        .expect("should produce a proof term");
    let proof_term = finalize_proof(&result, proof_term, &mut ctx, &neq_prop);
    assert_type_checks_to_false(&env, ctx, &proof_term, "Or+ThResolution");
}

/// Build a 7-step EUF transitivity proof using ThResolution instead of Resolution.
fn mk_euf_transitivity_th_res(
    h_ab_id: FVarId,
    h_bc_id: FVarId,
    eq_ab: &Expr,
    eq_bc: &Expr,
) -> (TermStore, VariableMapping, Proof) {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_a = terms.mk_var("fvar_1", Sort::Int);
    let ay_b = terms.mk_var("fvar_2", Sort::Int);
    let ay_c = terms.mk_var("fvar_3", Sort::Int);

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var(
        "fvar_1",
        Expr::const_(Name::from_string("testA"), vec![]),
        int_ty.clone(),
    );
    map.register_var(
        "fvar_2",
        Expr::const_(Name::from_string("testB"), vec![]),
        int_ty.clone(),
    );
    map.register_var(
        "fvar_3",
        Expr::const_(Name::from_string("testC"), vec![]),
        int_ty,
    );

    let ay_eq_ab = terms.mk_eq(ay_a, ay_b);
    let ay_eq_bc = terms.mk_eq(ay_b, ay_c);
    let ay_eq_ac = terms.mk_eq(ay_a, ay_c);
    let ay_not_eq_ab = terms.mk_not(ay_eq_ab);
    let ay_not_eq_bc = terms.mk_not(ay_eq_bc);
    let ay_not_eq_ac = terms.mk_not(ay_eq_ac);

    map.register_hypothesis("h_ab", h_ab_id, Expr::fvar(h_ab_id), eq_ab.clone());
    map.register_hypothesis("h_bc", h_bc_id, Expr::fvar(h_bc_id), eq_bc.clone());

    let mut proof = Proof::new();
    let s0 = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![ay_not_eq_ab, ay_not_eq_bc, ay_eq_ac],
        TheoryLemmaKind::EufTransitive,
    );
    let s1 = proof.add_assume(ay_eq_ab, None);
    let s2 = proof.add_rule_step(
        ay_core::AletheRule::ThResolution,
        vec![ay_not_eq_bc, ay_eq_ac],
        vec![s0, s1],
        vec![],
    );
    let s3 = proof.add_assume(ay_eq_bc, None);
    let s4 = proof.add_rule_step(
        ay_core::AletheRule::ThResolution,
        vec![ay_eq_ac],
        vec![s2, s3],
        vec![],
    );
    let s5 = proof.add_assume(ay_not_eq_ac, None);
    proof.add_rule_step(
        ay_core::AletheRule::ThResolution,
        vec![],
        vec![s4, s5],
        vec![],
    );

    (terms, map, proof)
}

/// E2E: EUF transitivity via 3-step ThResolution chain → kernel type-checks to False.
///
/// Part of #2432.
#[test]
fn test_e2e_euf_transitivity_th_resolution_type_checks() {
    let env = mk_env_with_classical();
    let eq_ab = mk_eq_int("testA", "testB");
    let eq_bc = mk_eq_int("testB", "testC");
    let eq_ac = mk_eq_int("testA", "testC");
    let neq_ac = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_ac.clone(),
    );

    let h_ab_id = FVarId::new(1);
    let h_bc_id = FVarId::new(2);
    let (terms, map, proof) = mk_euf_transitivity_th_res(h_ab_id, h_bc_id, &eq_ab, &eq_bc);

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_ab_id,
        Name::from_string("h_ab"),
        eq_ab,
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_bc_id,
        Name::from_string("h_bc"),
        eq_bc,
        BinderInfo::Default,
    );

    let result = attempt_reconstruction(&proof, &terms, &map, &neq_ac);
    assert!(
        result.stats.reconstructed_steps >= 7,
        "all 7 steps: {:?}",
        result.stats.error
    );
    assert_eq!(result.stats.rule_attempts.get("th_resolution"), Some(&3));

    let proof_term = result
        .proof_term
        .clone()
        .expect("should produce proof term");
    let proof_term = finalize_proof(&result, proof_term, &mut ctx, &neq_ac);
    assert_type_checks_to_false(&env, ctx, &proof_term, "EUF via ThResolution");
}

/// Build `@Eq.{1} Nat testB testA` (reversed from mk_eq_prop).
fn mk_eq_prop_reversed() -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let u1 = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![u1]), nat_ty),
            Expr::const_(Name::from_string("testB"), vec![]),
        ),
        Expr::const_(Name::from_string("testA"), vec![]),
    )
}

/// Build a multi-pivot ThResolution proof: c1=[p,q], c2=[¬p,¬q], resolvent=[p,¬p].
/// The correct pivot is q (not p). Tests find_implicit_pivot disambiguation.
fn mk_multi_pivot_th_res() -> (TermStore, VariableMapping, Proof, Expr) {
    use super::expr_builders::{mk_not, mk_or};

    let p_prop = mk_eq_prop();
    let q_prop = mk_eq_prop_reversed();
    let not_p_prop = mk_not(&p_prop);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not(p);
    let not_q = terms.mk_not(q);
    let or_pq = terms.mk_or(vec![p, q]);
    let or_np_nq = terms.mk_or(vec![not_p, not_q]);

    map.register_var("p", p_prop.clone(), Expr::prop());
    map.register_var("q", q_prop.clone(), Expr::prop());

    let h1 = FVarId::new(10);
    let h2 = FVarId::new(11);
    map.register_hypothesis("h_or_pq", h1, Expr::fvar(h1), mk_or(&p_prop, &q_prop));
    map.register_hypothesis(
        "h_or_np_nq",
        h2,
        Expr::fvar(h2),
        mk_or(&not_p_prop, &mk_not(&q_prop)),
    );

    let mut proof = Proof::new();
    let s0 = proof.add_assume(or_pq, None);
    let s1 = proof.add_assume(or_np_nq, None);
    proof.add_rule_step(
        ay_core::AletheRule::ThResolution,
        vec![p, not_p],
        vec![s0, s1],
        vec![],
    );

    let neg_goal = mk_or(&p_prop, &not_p_prop);
    (terms, map, proof, neg_goal)
}

/// Regression test for R1 finding: multi-pivot disambiguation selects the correct
/// pivot based on the stated resolvent clause.
///
/// c1=[p,q], c2=[¬p,¬q] share two complementary pairs. Resolvent [p,¬p] requires
/// pivot=q, not p. The naive first-match strategy would pick p and fail.
///
/// Part of #2432, #2427.
#[test]
fn test_th_resolution_multi_pivot_selects_correct_pivot() {
    let (terms, map, proof, neg_goal) = mk_multi_pivot_th_res();

    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);

    // The th_resolution step itself should succeed (pivot disambiguation works).
    // The proof-level stats.error is NoContradiction because the resolvent [p,¬p]
    // has 2 literals — this is expected since [p,q] ∧ [¬p,¬q] is satisfiable.
    // We test resolution rule success, not empty-clause derivation.
    assert_eq!(result.stats.rule_attempts.get("th_resolution"), Some(&1));
    assert_eq!(result.stats.rule_successes.get("th_resolution"), Some(&1));
    assert!(result.proof_term.is_some(), "should produce a proof term");
    assert!(
        !result.derives_empty_clause,
        "partial proof should not claim empty clause"
    );
}
