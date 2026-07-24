// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused e2e coverage for EUF transitivity reconstruction and its
//! non-empty-clause fail-closed boundary.

use super::super::{attempt_reconstruction, VariableMapping};
use super::{assert_proof_type_checks_to_false, mk_env_with_classical, mk_eq_int};
use ay::Sort;
use ay_core::{Proof, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, LocalContext, TypeChecker};

/// Build ay terms, variable mappings, and a 7-step EUF transitivity proof.
///
/// Returns (terms, map, proof) where the proof derives False from:
///   TheoryLemma{¬(a=b), ¬(b=c), a=c} + Assume(a=b) + Assume(b=c) + Assume(¬(a=c))
///   resolved through 3 resolution steps to the empty clause when
///   `close_empty_clause` is `true`.
fn mk_euf_transitivity_ay_proof(
    h_ab_id: FVarId,
    h_bc_id: FVarId,
    eq_ab: &Expr,
    eq_bc: &Expr,
    close_empty_clause: bool,
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
    let s2 = proof.add_resolution(vec![ay_not_eq_bc, ay_eq_ac], ay_not_eq_ab, s0, s1);
    let s3 = proof.add_assume(ay_eq_bc, None);
    let s4 = proof.add_resolution(vec![ay_eq_ac], ay_not_eq_bc, s2, s3);
    if close_empty_clause {
        let s5 = proof.add_assume(ay_not_eq_ac, None);
        proof.add_resolution(vec![], ay_eq_ac, s4, s5);
    }

    (terms, map, proof)
}

fn mk_euf_transitivity_fixture() -> (Expr, Expr, Expr, FVarId, FVarId) {
    let eq_ab = mk_eq_int("testA", "testB");
    let eq_bc = mk_eq_int("testB", "testC");
    let neq_ac = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        mk_eq_int("testA", "testC"),
    );
    (eq_ab, eq_bc, neq_ac, FVarId::new(10), FVarId::new(11))
}

fn mk_euf_transitivity_context(
    h_ab_id: FVarId,
    h_bc_id: FVarId,
    eq_ab: Expr,
    eq_bc: Expr,
) -> LocalContext {
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
    ctx
}

/// E2E: EUF transitivity theory lemma + resolution chain → kernel type-checks to False.
///
/// Validates Classical.em case-splitting, BVar index arithmetic, Eq.trans chains,
/// find_hypothesis_by_prop matching, and multi-step resolution wiring.
///
/// Part of #2412.
#[test]
fn test_e2e_euf_transitivity_type_checks() {
    let env = mk_env_with_classical();
    let (eq_ab, eq_bc, neq_ac, h_ab_id, h_bc_id) = mk_euf_transitivity_fixture();
    let (terms, map, proof) = mk_euf_transitivity_ay_proof(h_ab_id, h_bc_id, &eq_ab, &eq_bc, true);
    let mut ctx = mk_euf_transitivity_context(h_ab_id, h_bc_id, eq_ab, eq_bc);

    let result = attempt_reconstruction(&proof, &terms, &map, &neq_ac);
    assert!(
        result.stats.reconstructed_steps >= 7,
        "all 7 steps should reconstruct, got {} (error: {:?})",
        result.stats.reconstructed_steps,
        result.stats.error,
    );
    let mut proof_term = result
        .proof_term
        .expect("EUF transitivity chain should produce a proof term");

    if let Some(sentinel_id) = result.negated_goal_fvar {
        let neg_id = FVarId::new(20);
        proof_term = proof_term.subst_fvar(sentinel_id, &Expr::fvar(neg_id));
        ctx.push_with_id(
            neg_id,
            Name::from_string("h_neg_goal"),
            neq_ac.clone(),
            BinderInfo::Default,
        );
    }

    assert_proof_type_checks_to_false(&env, ctx, &proof_term, "EUF transitivity + resolution e2e");
}

/// Regression: a successfully reconstructed EUF clause is not itself a refutation.
///
/// If the final proof step still carries a residual clause, the bridge must keep
/// the proof as partial instead of claiming the empty clause.
#[test]
fn test_euf_transitivity_partial_clause_stays_non_contradictory() {
    let env = mk_env_with_classical();
    let (eq_ab, eq_bc, neq_ac, h_ab_id, h_bc_id) = mk_euf_transitivity_fixture();
    let (terms, map, proof) = mk_euf_transitivity_ay_proof(h_ab_id, h_bc_id, &eq_ab, &eq_bc, false);
    let ctx = mk_euf_transitivity_context(h_ab_id, h_bc_id, eq_ab, eq_bc);

    let result = attempt_reconstruction(&proof, &terms, &map, &neq_ac);
    assert!(
        result.stats.reconstructed_steps >= 5,
        "EUF partial chain should still reconstruct its available steps, got {} (error: {:?})",
        result.stats.reconstructed_steps,
        result.stats.error,
    );
    assert!(
        result.proof_term.is_some(),
        "EUF partial chain should still return the reconstructed clause proof"
    );
    assert!(
        !result.derives_empty_clause,
        "EUF partial chain must not claim the empty clause without the final contradiction step"
    );
    assert_eq!(
        result.negated_goal_fvar, None,
        "partial EUF proof should not introduce a negated-goal witness"
    );
    assert!(
        result
            .stats
            .error
            .as_ref()
            .is_some_and(|message| message.contains("proof does not derive empty clause")),
        "EUF partial chain should fail closed with a NoContradiction marker: {:?}",
        result.stats.error
    );

    let proof_term = result
        .proof_term
        .expect("EUF partial chain should produce the residual clause proof");
    let ty = TypeChecker::with_context(&env, ctx)
        .infer_type(&proof_term)
        .unwrap_or_else(|e| panic!("EUF partial chain should type-check: {e:?}"));
    assert!(
        !matches!(ty.kind(), ExprKind::Const(n, _) if *n == Name::from_string("False")),
        "EUF partial chain should keep a residual clause type, not False: {:?}",
        ty.kind()
    );
}
