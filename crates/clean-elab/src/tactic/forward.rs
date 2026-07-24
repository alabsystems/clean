// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Forward reasoning tactics: `have` and `suffices`.
//!
//! - `have` introduces an intermediate lemma into the proof context
//! - `suffices` reduces a goal by providing a sufficient condition

use crate::unify::{MetaState, Unifier, UnifyResult};
use clean_kernel::{Expr, ExprKind, Name};

use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};

/// Introduce an auxiliary lemma.
///
/// The `have` tactic introduces an intermediate result into the proof.
/// Given `have h : T := proof`, it:
/// 1. Verifies that `proof` has type `T`
/// 2. Adds `h : T` to the local context
/// 3. Continues with the original goal
///
/// This is "forward reasoning" - proving a lemma and adding it as a hypothesis.
///
/// # Arguments
/// * `name` - Name for the new hypothesis
/// * `ty` - Type of the lemma to prove
/// * `proof` - Optional proof term. If None, creates a subgoal for the proof.
///
/// # Example
/// ```text
/// // Goal: P
/// have_("h", T, Some(proof_of_T))
/// // Now have h : T in context, still need to prove P
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `ty` is a well-typed expression in the current environment
/// REQUIRES: If `proof` is `Some(pf)`, then `pf` must have type unifiable with `ty`
/// ENSURES: On Ok with `Some(pf)`, original goal closed with let-binding proof
/// ENSURES: On Ok with `None`, original goal closed; 2 new goals pushed (lemma + continuation)
/// ENSURES: On Ok, new goal(s) have `h : ty` available in local context
/// ENSURES: On Err(TypeMismatch), proof type does not unify with `ty`; state unchanged
pub fn have_(state: &mut ProofState, name: &str, ty: Expr, proof: Option<Expr>) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    if let Some(pf) = proof {
        // Verify the proof has the expected type
        let proof_ty = state.infer_type(&goal, &pf)?;
        let ty_inst = state.metas.instantiate(&ty);
        let ctx = state.build_local_ctx(&goal);

        let unify_result = {
            let (metas, env) = state.metas_and_env();
            Unifier::with_env(metas, env, ctx).unify(&proof_ty, &ty_inst)
        };
        match unify_result {
            UnifyResult::Success => {
                // Proof is valid - add to context as a let-binding
                let fvar = state.fresh_fvar();

                let local_decl = LocalDecl {
                    fvar,
                    name: name.to_string(),
                    ty: ty.clone(),
                    value: Some(pf.clone()),
                };

                // Create new goal with extended context
                let mut new_ctx = goal.local_ctx.clone();
                new_ctx.push(local_decl);

                // Create a new metavariable for the continuation
                let new_meta_id = state.fresh_meta_in_context(goal.target.clone(), &new_ctx);
                let new_meta_expr =
                    Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id)));

                // The proof of the original goal is:
                // let h : T := proof in <continuation>
                let proof_term = Expr::let_named(
                    Name::from_string(name),
                    ty,
                    pf,
                    new_meta_expr.abstract_fvar(fvar),
                    false,
                );

                // Part of #2154 Tier 2 Wave 2: let-binding with meta, no lambdas.
                state.close_goal(&goal, proof_term)?;

                // Add the new goal
                let new_goal = Goal {
                    meta_id: new_meta_id,
                    target: goal.target.clone(),
                    local_ctx: new_ctx,
                    tag: None,
                };

                state.goals.push_front(new_goal);
                Ok(())
            }
            UnifyResult::Failure(msg) => Err(TacticError::TypeMismatch {
                expected: format!("{ty_inst:?}"),
                actual: msg,
            }),
            UnifyResult::Stuck => Err(TacticError::UnificationFailed(
                "unification stuck while checking have proof".to_string(),
            )),
        }
    } else {
        // No proof provided - create two goals:
        // 1. Prove T (the lemma)
        // 2. Continue original proof with h : T available

        let fvar = state.fresh_fvar();

        let local_decl = LocalDecl {
            fvar,
            name: name.to_string(),
            ty: ty.clone(),
            value: None,
        };

        // Extended context for continuation
        let mut new_ctx = goal.local_ctx.clone();
        new_ctx.push(local_decl);

        // Create metavariables for both goals
        // The lemma proposition may mention locals from the original goal
        // (for example `have h : P x`), so capture that exact scope explicitly.
        // The continuation alone receives the newly introduced `h` local.
        let lemma_meta_id = state.fresh_meta_in_context(ty.clone(), &goal.local_ctx);
        let cont_meta_id = state.fresh_meta_in_context(goal.target.clone(), &new_ctx);

        let lemma_meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(lemma_meta_id)));
        let cont_meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(cont_meta_id)));

        // The proof of the original goal is:
        // let h : T := <lemma_proof> in <continuation>
        let proof_term = Expr::let_named(
            Name::from_string(name),
            ty.clone(),
            lemma_meta_expr,
            cont_meta_expr.abstract_fvar(fvar),
            false,
        );

        // Part of #2154 Tier 2 Wave 2: let-binding with two metas, no lambdas.
        state.close_goal(&goal, proof_term)?;

        // Goal 1: prove the lemma T
        let lemma_goal = Goal {
            meta_id: lemma_meta_id,
            target: ty,
            local_ctx: goal.local_ctx.clone(),
            tag: None,
        };

        // Goal 2: prove the original target with h available
        let cont_goal = Goal {
            meta_id: cont_meta_id,
            target: goal.target.clone(),
            local_ctx: new_ctx,
            tag: None,
        };

        // Insert goals (lemma first, then continuation)
        state.goals.push_front(cont_goal);
        state.goals.push_front(lemma_goal);

        Ok(())
    }
}

/// Suffices tactic for backward reasoning.
///
/// The `suffices` tactic lets you prove a goal by showing that it follows from
/// a simpler statement. Given `suffices h : T by proof`, it:
/// 1. Creates a goal to prove T
/// 2. Creates a goal to prove (T → original_goal)
///
/// This is "backward reasoning" - reducing the goal to proving a sufficient condition.
///
/// # Arguments
/// * `_name` - Name for the sufficient condition hypothesis (unused in proof term)
/// * `ty` - Type representing the sufficient condition
/// * `proof_fn` - Optional proof that T implies the original goal
///
/// # Example
/// ```text
/// // Goal: P ∧ Q
/// suffices_("h", P, Some(proof_of_P_implies_PandQ))
/// // Now just need to prove P
/// ```
///
/// Without a proof function:
/// ```text
/// // Goal: Complex
/// suffices_("h", Simpler, None)
/// // Goal 1: Simpler
/// // Goal 2: Simpler → Complex
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `ty` is a well-typed Prop-valued expression
/// REQUIRES: If `proof_fn` is `Some(pf)`, then `pf` must have type `ty → goal.target`
/// ENSURES: On Ok with `Some(pf)`, original goal closed; 1 new goal for `ty`
/// ENSURES: On Ok with `None`, original goal closed; 2 new goals (sufficient + implication)
/// ENSURES: On Err(TypeMismatch), proof_fn type does not match `ty → goal.target`
pub fn suffices_(
    state: &mut ProofState,
    _name: &str,
    ty: Expr,
    proof_fn: Option<Expr>,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    if let Some(pf) = proof_fn {
        // Verify the proof function has type (ty → goal.target)
        let expected_fn_ty = Expr::arrow(ty.clone(), goal.target.clone());
        let proof_ty = state.infer_type(&goal, &pf)?;
        let expected_inst = state.metas.instantiate(&expected_fn_ty);
        let ctx = state.build_local_ctx(&goal);

        let unify_result = {
            let (metas, env) = state.metas_and_env();
            Unifier::with_env(metas, env, ctx).unify(&proof_ty, &expected_inst)
        };
        match unify_result {
            UnifyResult::Success => {
                // proof_fn is valid - now we just need to prove ty
                let sufficient_meta_id = state.fresh_meta(ty.clone());
                let sufficient_meta_expr = Expr::fvar(MetaState::to_fvar(sufficient_meta_id));

                // The proof of the original goal is: pf <proof_of_ty>
                let proof_term = Expr::app(pf, sufficient_meta_expr);

                // Part of #2154 Tier 2 Wave 2: app with meta arg, no lambdas.
                state.close_goal(&goal, proof_term)?;

                // Create a goal for proving ty
                let sufficient_goal = Goal {
                    meta_id: sufficient_meta_id,
                    target: ty,
                    local_ctx: goal.local_ctx.clone(),
                    tag: None,
                };

                state.goals.push_front(sufficient_goal);
                Ok(())
            }
            UnifyResult::Failure(msg) => Err(TacticError::TypeMismatch {
                expected: format!("{expected_inst:?}"),
                actual: msg,
            }),
            UnifyResult::Stuck => Err(TacticError::UnificationFailed(
                "unification stuck while checking suffices proof".to_string(),
            )),
        }
    } else {
        // No proof function provided - create two goals:
        // 1. Prove ty (the sufficient condition)
        // 2. Prove ty → original_goal (with h : ty available via intro)

        // Create metavariables for both goals
        let sufficient_meta_id = state.fresh_meta(ty.clone());
        let impl_meta_id = state.fresh_meta_in_context(
            Expr::arrow(ty.clone(), goal.target.clone()),
            &goal.local_ctx,
        );

        let sufficient_meta_expr =
            Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(sufficient_meta_id)));
        let impl_meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(impl_meta_id)));

        // The proof of the original goal is: <impl_proof> <proof_of_ty>
        let proof_term = Expr::app(impl_meta_expr, sufficient_meta_expr);

        // Part of #2154 Tier 2 Wave 2: app with two metas, no lambdas.
        state.close_goal(&goal, proof_term)?;

        // Goal 1: prove the sufficient condition
        let sufficient_goal = Goal {
            meta_id: sufficient_meta_id,
            target: ty.clone(),
            local_ctx: goal.local_ctx.clone(),
            tag: None,
        };

        // Goal 2: prove that sufficient condition implies original goal
        let impl_goal = Goal {
            meta_id: impl_meta_id,
            target: Expr::arrow(ty, goal.target),
            local_ctx: goal.local_ctx.clone(),
            tag: None,
        };

        // Insert goals (sufficient first, then implication)
        state.goals.push_front(impl_goal);
        state.goals.push_front(sufficient_goal);

        Ok(())
    }
}
