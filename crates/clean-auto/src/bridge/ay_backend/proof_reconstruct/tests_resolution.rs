// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for resolution proof reconstruction (#2392).

use super::resolution_build::ResolutionBuilder;
use super::resolution_plan::{ClausePlan, ResolutionPlan};
use super::tests_support::register_bool_hypothesis_var as register_bool_var;
use super::{attempt_reconstruction, ReconstructionContext, ReconstructionResult, VariableMapping};
use ay::Sort;
use ay_core::{Proof, ProofId, TermId, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, FVarId, LocalContext, TypeChecker};

fn mk_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");
    env
}

fn push_prop_var(ctx: &mut LocalContext, id: u64, name: &str) {
    ctx.push_with_id(
        FVarId::new(id),
        Name::from_string(name),
        Expr::prop(),
        BinderInfo::Default,
    );
}

fn finalize_open_resolution_proof(
    result: &ReconstructionResult,
    mut proof_term: Expr,
    ctx: &mut LocalContext,
    negated_goal: &Expr,
) -> Expr {
    for (idx, (sentinel_id, assumed_prop)) in result.compound_witness_fvars.iter().enumerate() {
        let normal_id = FVarId::new(100 + idx as u64);
        proof_term = proof_term.subst_fvar(*sentinel_id, &Expr::fvar(normal_id));
        let clause_name = format!("h_clause_{idx}");
        ctx.push_with_id(
            normal_id,
            Name::from_string(&clause_name),
            assumed_prop.clone(),
            BinderInfo::Default,
        );
    }

    if let Some(sentinel_id) = result.negated_goal_fvar {
        let normal_neg_id = FVarId::new(200);
        proof_term = proof_term.subst_fvar(sentinel_id, &Expr::fvar(normal_neg_id));
        ctx.push_with_id(
            normal_neg_id,
            Name::from_string("h_neg"),
            negated_goal.clone(),
            BinderInfo::Default,
        );
    }

    proof_term
}

fn assert_proof_type_checks_to_expected(
    env: &Environment,
    ctx: LocalContext,
    proof: &Expr,
    expected: &Expr,
    msg: &str,
) {
    let tc = TypeChecker::with_context(env, ctx);
    let ty = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("{msg}: type-check failed: {e:?}"));
    assert!(
        tc.is_def_eq(&ty, expected),
        "{msg}: expected inferred type {:?} to be def-eq to {:?}",
        ty.kind(),
        expected.kind(),
    );
}

fn finalize_and_assert_type_checks_to_or_ab(
    result: &ReconstructionResult,
    proof_term: Expr,
    negated_goal: &Expr,
    msg: &str,
) -> Expr {
    let env = mk_env();
    let mut ctx = LocalContext::new();
    push_prop_var(&mut ctx, 1, "p");
    push_prop_var(&mut ctx, 2, "a");
    push_prop_var(&mut ctx, 3, "b");
    let proof_term = finalize_open_resolution_proof(result, proof_term, &mut ctx, negated_goal);
    let expected = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Or"), vec![]),
            Expr::fvar(FVarId::new(2)),
        ),
        Expr::fvar(FVarId::new(3)),
    );
    assert_proof_type_checks_to_expected(&env, ctx, &proof_term, &expected, msg);
    proof_term
}

#[test]
fn test_resolution_unit_unit() {
    // {p} + {¬p} → {} (empty clause = False)
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(p, None);
    let h2 = proof.add_assume(not_p, None);
    proof.add_resolution(vec![], p, h1, h2);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.total_steps, 3);
    assert_eq!(result.stats.assume_steps, 2);
    assert_eq!(result.stats.resolution_steps, 1);
    assert!(
        result.stats.reconstructed_steps >= 3,
        "all 3 steps should be reconstructed, got {}",
        result.stats.reconstructed_steps,
    );
    let proof_term = result
        .proof_term
        .expect("resolution unit×unit should produce a proof term");
    let head = proof_term.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "absurd",
            "unit×unit resolution should produce absurd"
        ),
        _ => panic!("expected absurd, got {:?}", head),
    }
}

#[test]
fn test_resolution_unit_multi() {
    // {p} + {¬p, q} → {q}
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let q = register_bool_var(&mut terms, &mut map, "fvar_2", 2);
    let not_p = terms.mk_not(p);
    let c2_clause = terms.mk_or(vec![not_p, q]);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(p, None);
    let h2 = proof.add_assume(c2_clause, None);
    proof.add_resolution(vec![q], p, h1, h2);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.resolution_steps, 1);
    assert!(
        result.stats.reconstructed_steps >= 3,
        "all steps should be reconstructed, got {}",
        result.stats.reconstructed_steps,
    );
    let proof_term = result
        .proof_term
        .expect("resolution unit×multi should produce a proof term");
    let head = proof_term.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "Or.rec",
            "unit×multi resolution should produce Or.rec"
        ),
        _ => panic!("expected Or.rec, got {:?}", head),
    }
}

#[test]
fn test_resolution_multi_multi() {
    // {p, a} + {¬p, b} → {a, b}
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let a = register_bool_var(&mut terms, &mut map, "fvar_2", 2);
    let b = register_bool_var(&mut terms, &mut map, "fvar_3", 3);
    let not_p = terms.mk_not(p);

    let c1_clause = terms.mk_or(vec![p, a]);
    let c2_clause = terms.mk_or(vec![not_p, b]);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(c1_clause, None);
    let h2 = proof.add_assume(c2_clause, None);
    proof.add_resolution(vec![a, b], p, h1, h2);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.resolution_steps, 1);
    assert!(
        result.stats.reconstructed_steps >= 3,
        "all steps should be reconstructed, got {}",
        result.stats.reconstructed_steps,
    );
    let proof_term = result
        .proof_term
        .expect("resolution multi×multi should produce a proof term");
    let head = proof_term.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "Or.rec",
            "multi×multi resolution should produce Or.rec"
        ),
        _ => panic!("expected Or.rec, got {:?}", head),
    }
}

#[test]
fn test_resolution_negative_pivot() {
    // {¬p, a} + {p, b} → {a, b}  (pivot is ¬p)
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let a = register_bool_var(&mut terms, &mut map, "fvar_2", 2);
    let b = register_bool_var(&mut terms, &mut map, "fvar_3", 3);
    let not_p = terms.mk_not(p);

    let c1_clause = terms.mk_or(vec![not_p, a]);
    let c2_clause = terms.mk_or(vec![p, b]);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(c1_clause, None);
    let h2 = proof.add_assume(c2_clause, None);
    proof.add_resolution(vec![a, b], not_p, h1, h2);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.resolution_steps, 1);
    assert!(
        result.stats.reconstructed_steps >= 3,
        "all steps should be reconstructed (negative pivot), got {}",
        result.stats.reconstructed_steps,
    );
    let _ = result
        .proof_term
        .expect("resolution with negative pivot should produce a proof term");
}

#[test]
fn test_resolution_swapped_pivot_orientation() {
    // {¬p, a} + {p, b} → {a, b}, but ay may record the pivot as `p`.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let a = register_bool_var(&mut terms, &mut map, "fvar_2", 2);
    let b = register_bool_var(&mut terms, &mut map, "fvar_3", 3);
    let not_p = terms.mk_not(p);

    let c1_clause = terms.mk_or(vec![not_p, a]);
    let c2_clause = terms.mk_or(vec![p, b]);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(c1_clause, None);
    let h2 = proof.add_assume(c2_clause, None);
    proof.add_resolution(vec![a, b], p, h1, h2);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.resolution_steps, 1);
    assert!(
        result.stats.reconstructed_steps >= 3,
        "all steps should be reconstructed when pivot orientation is swapped, got {}",
        result.stats.reconstructed_steps,
    );
    let proof_term = result
        .proof_term
        .clone()
        .expect("resolution should accept the swapped pivot orientation");
    let proof_term = finalize_and_assert_type_checks_to_or_ab(
        &result,
        proof_term,
        &negated_goal,
        "swapped-orientation resolution",
    );
    let head = proof_term.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "Or.rec",
            "swapped-orientation resolution should still build Or.rec"
        ),
        _ => panic!("expected Or.rec, got {:?}", head),
    }
}

#[test]
fn test_resolution_deduplicated_resolvent_shared_literal() {
    // {p, a} + {¬p, a, b} → {a, b} after ay deduplicates the shared `a`.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let a = register_bool_var(&mut terms, &mut map, "fvar_2", 2);
    let b = register_bool_var(&mut terms, &mut map, "fvar_3", 3);
    let not_p = terms.mk_not(p);

    let c1_clause = terms.mk_or(vec![p, a]);
    let c2_clause = terms.mk_or(vec![not_p, a, b]);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(c1_clause, None);
    let h2 = proof.add_assume(c2_clause, None);
    proof.add_resolution(vec![a, b], p, h1, h2);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.resolution_steps, 1);
    assert!(
        result.stats.reconstructed_steps >= 3,
        "shared non-pivot literals should still reconstruct after deduplication, got {}",
        result.stats.reconstructed_steps,
    );
    let proof_term = result
        .proof_term
        .clone()
        .expect("resolution should reconstruct when the resolvent deduplicates shared literals");
    let proof_term = finalize_and_assert_type_checks_to_or_ab(
        &result,
        proof_term,
        &negated_goal,
        "deduplicated resolvent resolution",
    );
    let head = proof_term.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "Or.rec",
            "deduplicated resolvent should still produce Or.rec"
        ),
        _ => panic!("expected Or.rec, got {:?}", head),
    }
}

#[test]
fn test_resolution_chain() {
    // {p} + {¬p, q} → {q}, then {q} + {¬q} → {}
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let q = register_bool_var(&mut terms, &mut map, "fvar_2", 2);
    let not_p = terms.mk_not(p);
    let not_q = terms.mk_not(q);

    let c2_clause = terms.mk_or(vec![not_p, q]);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(p, None);
    let h2 = proof.add_assume(c2_clause, None);
    let h3 = proof.add_assume(not_q, None);
    let r1 = proof.add_resolution(vec![q], p, h1, h2);
    proof.add_resolution(vec![], q, r1, h3);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.total_steps, 5);
    assert_eq!(result.stats.assume_steps, 3);
    assert_eq!(result.stats.resolution_steps, 2);
    assert!(
        result.stats.reconstructed_steps >= 5,
        "all 5 steps should be reconstructed in chain, got {}",
        result.stats.reconstructed_steps,
    );
    let proof_term = result
        .proof_term
        .expect("resolution chain should produce a proof term");
    let head = proof_term.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "absurd",
            "final empty-clause resolution should produce absurd"
        ),
        _ => panic!("expected absurd at end of chain, got {:?}", head),
    }
}

#[test]
fn test_resolution_empty_resolvent() {
    // {p} + {¬p} → {} — target = False path
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(p, None);
    let h2 = proof.add_assume(not_p, None);
    proof.add_resolution(vec![], p, h1, h2);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    let proof_term = result
        .proof_term
        .expect("empty resolvent should produce a proof of False");
    let args = proof_term.get_app_args();
    assert_eq!(
        args.len(),
        4,
        "absurd should have 4 args, got {}",
        args.len()
    );
    let target_arg = &args[1];
    match target_arg.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "False",
            "target of empty-resolvent absurd should be False"
        ),
        _ => panic!("expected False as target, got {:?}", target_arg),
    }
}

// --- Tests moved from inline resolution.rs #[cfg(test)] block (#2508) ---

/// Build a minimal unit×unit `ResolutionPlan` for testing `mk_resolution_absurd`
/// through the builder. Both clauses have exactly one proposition so the build
/// path goes directly to absurd discharge without touching the Or.rec walker.
fn mk_absurd_test_plan(
    pivot: TermId,
    target: Expr,
    pivot_is_negation: bool,
    step_id: ProofId,
) -> ResolutionPlan {
    let dummy = Expr::prop();
    ResolutionPlan {
        left: ClausePlan {
            props: vec![dummy.clone()],
            suffixes: vec![dummy.clone()],
            pivot_idx: 0,
            to_resolvent: vec![None],
        },
        right: ClausePlan {
            props: vec![dummy.clone()],
            suffixes: vec![dummy],
            pivot_idx: 0,
            to_resolvent: vec![None],
        },
        resolvent_props: vec![],
        resolvent_suffixes: vec![],
        target,
        pivot,
        pivot_is_negation,
        step_id,
    }
}

/// Verify that mk_resolution_absurd returns an error (not an ill-typed
/// proof term) when the pivot proposition is missing from the term cache.
/// Regression test for #2414 (moved from resolution.rs inline tests, #2508).
#[test]
fn test_mk_resolution_absurd_cache_miss_returns_error() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);

    let var_map = VariableMapping::new();
    let ctx = ReconstructionContext::new(&terms, &var_map, 0);
    // term_cache is empty — pivot proposition NOT cached

    let proof_a = Expr::fvar(FVarId::new(1));
    let proof_b = Expr::fvar(FVarId::new(2));
    let target = Expr::const_(Name::from_string("False"), vec![]);

    // Positive pivot, cache miss → should be Err, not ill-typed Expr
    let plan = mk_absurd_test_plan(p, target.clone(), false, ProofId(42));
    let builder = ResolutionBuilder::new(&ctx, &plan);
    let result = builder.build(&proof_a, &proof_b);
    assert!(
        result.is_err(),
        "cache miss on positive pivot must return Err"
    );
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("42"),
        "error should report step_index 42, got: {}",
        err_msg
    );

    // Negated pivot (Not(p)), inner not cached → should be Err
    let plan = mk_absurd_test_plan(not_p, target, true, ProofId(7));
    let builder = ResolutionBuilder::new(&ctx, &plan);
    let result = builder.build(&proof_a, &proof_b);
    assert!(
        result.is_err(),
        "cache miss on negated pivot must return Err"
    );
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("7"),
        "error should report step_index 7, got: {}",
        err_msg
    );
}

/// Verify that mk_resolution_absurd succeeds when the pivot proposition
/// IS in the term cache (normal path).
/// Moved from resolution.rs inline tests (#2508).
#[test]
fn test_mk_resolution_absurd_cache_hit_succeeds() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);

    let var_map = VariableMapping::new();
    let mut ctx = ReconstructionContext::new(&terms, &var_map, 0);

    // Populate cache with the pivot proposition
    let p_prop = Expr::fvar(FVarId::new(100));
    ctx.term_cache.insert(p, p_prop);

    let proof_a = Expr::fvar(FVarId::new(1));
    let proof_b = Expr::fvar(FVarId::new(2));
    let target = Expr::const_(Name::from_string("False"), vec![]);

    // Positive pivot, cache hit → should succeed
    let plan = mk_absurd_test_plan(p, target.clone(), false, ProofId(0));
    let builder = ResolutionBuilder::new(&ctx, &plan);
    let result = builder.build(&proof_a, &proof_b);
    assert!(result.is_ok(), "cache hit on positive pivot must succeed");

    // Negated pivot: inner (p) is cached → should succeed
    let plan = mk_absurd_test_plan(not_p, target, true, ProofId(0));
    let builder = ResolutionBuilder::new(&ctx, &plan);
    let result = builder.build(&proof_a, &proof_b);
    assert!(
        result.is_ok(),
        "cache hit on negated pivot inner must succeed"
    );
}
