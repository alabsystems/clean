// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_reconstruct_assume_negated_goal_returns_proof_fvar() {
    // When the assumed proposition matches the negated goal, reconstruct_assume
    // must return a proof *term* (FVar) whose type is the proposition — not the
    // proposition itself (#2269 acceptance criterion 2).
    let mut terms = TermStore::new();
    // Use fvar_N naming so translate_var's fallback parsing succeeds.
    let p = terms.mk_var("fvar_10", Sort::Bool);

    // Build a proof that just assumes `p` (the negated goal).
    let mut proof = Proof::new();
    proof.add_assume(p, None);

    // The negated goal is the translated form of p: Expr::fvar(FVarId(10))
    let negated_goal_expr = Expr::fvar(FVarId::new(10));

    let map = VariableMapping::new();
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal_expr);

    // The proof_term should be an FVar (proof witness), NOT the proposition.
    let proof_term = result
        .proof_term
        .expect("single-assume proof should produce a term");
    match proof_term.kind() {
        ExprKind::FVar(id) => {
            assert_eq!(
                id.as_u64(),
                u64::MAX,
                "sentinel FVarId for negated goal proof"
            );
        }
        _ => panic!(
            "expected FVar proof term for negated goal, got {:?}",
            proof_term
        ),
    }

    // negated_goal_fvar should be set.
    let ng_fvar = result
        .negated_goal_fvar
        .expect("negated_goal_fvar should be set");
    assert_eq!(ng_fvar.as_u64(), u64::MAX);
}

#[test]
fn test_reconstruct_assume_hypothesis_preferred_over_negated_goal() {
    // When the assumed variable matches BOTH a registered hypothesis AND the
    // negated goal, the hypothesis proof should be returned (not the negated
    // goal FVar). Hypotheses are more specific.
    let mut terms = TermStore::new();
    let p = terms.mk_var("hyp_p", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(p, None);

    let hyp_fvar = FVarId::new(777);
    let hyp_expr = Expr::fvar(hyp_fvar);
    let prop_ty = Expr::prop();

    let mut map = VariableMapping::new();
    // Register in both maps: name_to_expr for translate_var, hypothesis_proofs
    // for the hypothesis lookup in reconstruct_assume.
    map.register_var("hyp_p", hyp_expr.clone(), prop_ty.clone());
    map.register_hypothesis("hyp_p", hyp_fvar, hyp_expr.clone(), prop_ty);

    // The negated goal matches the translated proposition (fvar_777).
    let negated_goal_expr = hyp_expr;

    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal_expr);

    let proof_term = result
        .proof_term
        .expect("should produce a term from hypothesis");
    // Should be the hypothesis FVar (777), not the negated goal sentinel.
    match proof_term.kind() {
        ExprKind::FVar(id) => {
            assert_eq!(
                id.as_u64(),
                777,
                "hypothesis FVar should be preferred over negated goal"
            );
        }
        _ => panic!("expected FVar(777) from hypothesis, got {:?}", proof_term),
    }

    // negated_goal_fvar should NOT be set since we used the hypothesis path.
    assert!(
        result.negated_goal_fvar.is_none(),
        "negated_goal_fvar should be None when hypothesis matches"
    );
}

// --- Regression: negated-goal Assume with Not-wrapped ay term (#302) ---

#[test]
fn test_reconstruct_assume_negated_goal_not_wrapped() {
    // Regression test for #302: in the real call chain, ay asserts `(not P)` so
    // the proof's Assume step references a `Not(P)` term. translate_term produces
    // `mk_not(P_expr)` = `App(Const("Not"), P_expr)`. The negated_goal parameter
    // must also be `mk_not(P_expr)` for the comparison to succeed. Previously the
    // caller passed the un-negated `P_expr`, causing negated-goal detection to miss.
    let mut terms = TermStore::new();
    let p = terms.mk_var("fvar_10", Sort::Bool);
    // Wrap in Not — this is what ay internally sees after asserting `(not P)`.
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    proof.add_assume(not_p, None);

    // The negated goal is the kernel-level `Not(P)`, matching what translate_term
    // produces for the Not-wrapped ay term.
    let p_expr = Expr::fvar(FVarId::new(10));
    let negated_goal_expr = mk_not(&p_expr);

    let map = VariableMapping::new();
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal_expr);

    let proof_term = result
        .proof_term
        .expect("Not-wrapped assume should produce a proof term");
    match proof_term.kind() {
        ExprKind::FVar(id) => {
            assert_eq!(
                id.as_u64(),
                u64::MAX,
                "sentinel FVarId for negated goal proof"
            );
        }
        _ => panic!(
            "expected FVar sentinel for negated goal, got {:?}",
            proof_term
        ),
    }

    let ng_fvar = result
        .negated_goal_fvar
        .expect("negated_goal_fvar should be set for Not-wrapped assume");
    assert_eq!(ng_fvar.as_u64(), u64::MAX);
}

#[test]
fn test_reconstruct_assume_negated_goal_mismatch_regression() {
    // Negative test: if we pass the un-negated proposition while the ay term
    // is Not-wrapped, the negated-goal detection should NOT fire. This documents
    // the pre-fix broken behavior so we can detect if it regresses.
    let mut terms = TermStore::new();
    let p = terms.mk_var("fvar_10", Sort::Bool);
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    proof.add_assume(not_p, None);

    // Pass the un-negated proposition — this was the bug.
    let un_negated_goal = Expr::fvar(FVarId::new(10));

    let map = VariableMapping::new();
    let result = attempt_reconstruction(&proof, &terms, &map, &un_negated_goal);

    // With the un-negated goal, the negated_goal_fvar should NOT be set because
    // the comparison `mk_not(P) == P` fails.
    assert!(
        result.negated_goal_fvar.is_none(),
        "negated_goal_fvar should be None when caller passes un-negated prop"
    );
}
