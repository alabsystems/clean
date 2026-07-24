// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conversion tactics
//!
//! Provides tactics for converting between equivalent forms.
//! Calc chain tactics are in calc.rs (split for file size, #2154).

use crate::unify::MetaState;
use clean_kernel::expr::ExprKind;
use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

use super::equality::match_equality;
use super::ring::make_eq;
use super::{Goal, ProofState, TacticError, TacticResult};

// ============================================================================
// convert: Prove goal by converting to equivalent form
// ============================================================================

/// The `convert` tactic proves the goal by finding a proof term that may not
/// exactly match, generating subgoals for mismatched parts.
///
/// Given goal `⊢ T` and term `h : T'`, `convert h` will:
/// 1. If T and T' are definitionally equal, close the goal
/// 2. Otherwise, create subgoals to prove T = T' or its components match
///
/// This is useful when you have a proof that's "almost right" but needs
/// some massaging.
pub fn convert(state: &mut ProofState, proof_term: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    // Type check the proof term (#2214: use goal's local context so FVars resolve)
    let proof_type = state.infer_type(&goal, &proof_term).map_err(|_| {
        TacticError::TypeCheckFailed("convert: cannot infer type of proof term".into())
    })?;

    // Check if types are definitionally equal
    if state.is_def_eq(&goal, &target, &proof_type) {
        // Part of #2154 Tier A: is_def_eq guard verified type match;
        // close_goal re-checks via infer_type + is_def_eq (redundant but safe).
        state.close_goal(&goal, proof_term)?;
        return Ok(());
    }

    // Types differ - try to decompose and create subgoals
    convert_with_subgoals(state, &goal, &target, &proof_type, &proof_term)
}

/// Create subgoals for type mismatch in convert.
///
/// Strategy 1: Both sides are equalities — decompose into component subgoals
/// and build a composite Eq.trans/Eq.symm proof.
/// Strategy 2: General type mismatch — create a single Eq.mpr subgoal.
///
/// Part of #2154 goal-decomposition pattern: both strategies now assign a
/// composite proof to the original goal's metavariable via `close_goal`.
///
/// # Contract
///
/// REQUIRES: `goal` is a valid goal from the current proof state
/// REQUIRES: `target` is the WHNF-instantiated goal target type
/// REQUIRES: `proof_type` is the inferred type of `proof_term`
/// REQUIRES: `target` and `proof_type` are NOT definitionally equal (checked by caller)
/// ENSURES: On Ok, the original goal is closed with a composite proof term
/// ENSURES: On Ok, 1-2 new subgoals are pushed for the user to solve
/// ENSURES: For equality decomposition, subgoals cover mismatched LHS/RHS components
/// ENSURES: For general mismatch, a single `target = proof_type` subgoal is created
fn convert_with_subgoals(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    proof_type: &Expr,
    proof_term: &Expr,
) -> TacticResult {
    // Strategy 1: If both are equalities, decompose
    if let (Ok((t_ty, t_lhs, t_rhs, t_levels)), Ok((p_ty, p_lhs, p_rhs, _p_levels))) =
        (match_equality(target), match_equality(proof_type))
    {
        // Check type compatibility (#2214: use goal's local context)
        if !state.is_def_eq(goal, &t_ty, &p_ty) {
            return Err(TacticError::TypeMismatch {
                expected: "matching equality types".into(),
                actual: "incompatible equality types".into(),
            });
        }

        let lhs_match = state.is_def_eq(goal, &t_lhs, &p_lhs);
        let rhs_match = state.is_def_eq(goal, &t_rhs, &p_rhs);

        if lhs_match && rhs_match {
            // Part of #2154 Tier A: is_def_eq decomposition verified all
            // components match; close_goal re-checks the composed proof.
            state.close_goal(goal, proof_term.clone())?;
            return Ok(());
        }

        // Build composite proof referencing subgoal metas.
        // proof_term : @Eq p_ty p_lhs p_rhs
        // Goal:        @Eq t_ty t_lhs t_rhs  (where t_ty =def p_ty)
        //
        // Chain: t_lhs →[meta_lhs] p_lhs →[proof_term] p_rhs →[Eq.symm meta_rhs] t_rhs
        let trans_name = Name::from_string("Eq.trans");
        let symm_name = Name::from_string("Eq.symm");

        match (lhs_match, rhs_match) {
            (true, true) => unreachable!("both sides match — handled by early return above"),
            (false, true) => {
                // Only LHS differs: subgoal is t_lhs = p_lhs
                // @Eq.trans t_ty t_lhs p_lhs p_rhs meta_lhs proof_term
                //   : t_lhs = p_rhs ≡ t_lhs = t_rhs (since t_rhs =def p_rhs)
                let subgoal_target = make_eq(&t_ty, &t_lhs, &p_lhs, &t_levels);
                let meta_id = state.fresh_meta(subgoal_target.clone());
                let meta_expr = Expr::fvar(MetaState::to_fvar(meta_id));

                let mut proof = Expr::const_(trans_name, t_levels.clone());
                proof = Expr::app(proof, t_ty);
                proof = Expr::app(proof, t_lhs);
                proof = Expr::app(proof, p_lhs);
                proof = Expr::app(proof, p_rhs);
                proof = Expr::app(proof, meta_expr);
                proof = Expr::app(proof, proof_term.clone());

                state.close_goal(goal, proof)?;

                state.goals.push_front(Goal {
                    meta_id,
                    target: subgoal_target,
                    local_ctx: goal.local_ctx.clone(),
                    tag: None,
                });
            }
            (true, false) => {
                // Only RHS differs: subgoal is t_rhs = p_rhs
                // @Eq.symm t_ty t_rhs p_rhs meta_rhs : p_rhs = t_rhs
                // @Eq.trans t_ty p_lhs p_rhs t_rhs proof_term symm
                //   : p_lhs = t_rhs ≡ t_lhs = t_rhs (since t_lhs =def p_lhs)
                let subgoal_target = make_eq(&t_ty, &t_rhs, &p_rhs, &t_levels);
                let meta_id = state.fresh_meta(subgoal_target.clone());
                let meta_expr = Expr::fvar(MetaState::to_fvar(meta_id));

                let mut symm_proof = Expr::const_(symm_name, t_levels.clone());
                symm_proof = Expr::app(symm_proof, t_ty.clone());
                symm_proof = Expr::app(symm_proof, t_rhs.clone());
                symm_proof = Expr::app(symm_proof, p_rhs.clone());
                symm_proof = Expr::app(symm_proof, meta_expr);

                let mut proof = Expr::const_(trans_name, t_levels);
                proof = Expr::app(proof, t_ty);
                proof = Expr::app(proof, p_lhs);
                proof = Expr::app(proof, p_rhs);
                proof = Expr::app(proof, t_rhs);
                proof = Expr::app(proof, proof_term.clone());
                proof = Expr::app(proof, symm_proof);

                state.close_goal(goal, proof)?;

                state.goals.push_front(Goal {
                    meta_id,
                    target: subgoal_target,
                    local_ctx: goal.local_ctx.clone(),
                    tag: None,
                });
            }
            (false, false) => {
                // Both differ: subgoals are t_lhs = p_lhs, t_rhs = p_rhs
                // inner = @Eq.trans t_ty p_lhs p_rhs t_rhs proof_term (Eq.symm meta_rhs)
                //       : p_lhs = t_rhs
                // proof = @Eq.trans t_ty t_lhs p_lhs t_rhs meta_lhs inner
                //       : t_lhs = t_rhs
                let lhs_subgoal = make_eq(&t_ty, &t_lhs, &p_lhs, &t_levels);
                let rhs_subgoal = make_eq(&t_ty, &t_rhs, &p_rhs, &t_levels);
                let meta_lhs = state.fresh_meta(lhs_subgoal.clone());
                let meta_rhs = state.fresh_meta(rhs_subgoal.clone());
                let meta_lhs_expr = Expr::fvar(MetaState::to_fvar(meta_lhs));
                let meta_rhs_expr = Expr::fvar(MetaState::to_fvar(meta_rhs));

                // Eq.symm(t_ty, t_rhs, p_rhs, meta_rhs) : p_rhs = t_rhs
                let mut symm_proof = Expr::const_(symm_name, t_levels.clone());
                symm_proof = Expr::app(symm_proof, t_ty.clone());
                symm_proof = Expr::app(symm_proof, t_rhs.clone());
                symm_proof = Expr::app(symm_proof, p_rhs.clone());
                symm_proof = Expr::app(symm_proof, meta_rhs_expr);

                // inner = Eq.trans(t_ty, p_lhs, p_rhs, t_rhs, proof_term, symm)
                let mut inner = Expr::const_(trans_name.clone(), t_levels.clone());
                inner = Expr::app(inner, t_ty.clone());
                inner = Expr::app(inner, p_lhs.clone());
                inner = Expr::app(inner, p_rhs);
                inner = Expr::app(inner, t_rhs.clone());
                inner = Expr::app(inner, proof_term.clone());
                inner = Expr::app(inner, symm_proof);

                // proof = Eq.trans(t_ty, t_lhs, p_lhs, t_rhs, meta_lhs, inner)
                let mut proof = Expr::const_(trans_name, t_levels);
                proof = Expr::app(proof, t_ty);
                proof = Expr::app(proof, t_lhs);
                proof = Expr::app(proof, p_lhs);
                proof = Expr::app(proof, t_rhs);
                proof = Expr::app(proof, meta_lhs_expr);
                proof = Expr::app(proof, inner);

                state.close_goal(goal, proof)?;

                // Push subgoals (LHS first so it's current)
                state.goals.push_front(Goal {
                    meta_id: meta_rhs,
                    target: rhs_subgoal,
                    local_ctx: goal.local_ctx.clone(),
                    tag: None,
                });
                state.goals.push_front(Goal {
                    meta_id: meta_lhs,
                    target: lhs_subgoal,
                    local_ctx: goal.local_ctx.clone(),
                    tag: None,
                });
            }
        }

        return Ok(());
    }

    // Strategy 2: Create a single goal to prove type equality,
    // then use Eq.mpr to cast proof_term from proof_type to target.
    //
    // Compute the universe level from the target's sort:
    //   target : Sort u → eq uses @Eq.{succ u}, Eq.mpr uses .{u}
    //   Prop case: u = 0 → @Eq.{1} Prop, Eq.mpr.{0}
    //   Type case: u = 1 → @Eq.{2} Type, Eq.mpr.{1}
    let sort_level = state
        .infer_type(goal, target)
        .ok()
        .and_then(|ty| match ty.kind() {
            ExprKind::Sort(level) => Some(level.clone()),
            _ => None,
        })
        .ok_or_else(|| {
            TacticError::TypeCheckFailed(
                "convert: cannot infer universe level of target type".into(),
            )
        })?;

    let eq_level = Level::succ(sort_level.clone());
    let sort_expr = Expr::sort(sort_level.clone());

    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![eq_level]),
                sort_expr,
            ),
            target.clone(),
        ),
        proof_type.clone(),
    );

    let eq_meta_id = state.fresh_meta(eq_goal.clone());
    let eq_meta_expr = Expr::fvar(MetaState::to_fvar(eq_meta_id));

    // Eq.mpr.{u} expects @Eq.{succ u}
    let eq_mpr = Expr::const_(Name::from_string("Eq.mpr"), vec![sort_level]);
    let proof = Expr::app(
        Expr::app(
            Expr::app(Expr::app(eq_mpr, target.clone()), proof_type.clone()),
            eq_meta_expr,
        ),
        proof_term.clone(),
    );

    // Part of #2154: type-check Eq.mpr proof before accepting
    state.close_goal(goal, proof)?;

    state.goals.push_front(Goal {
        meta_id: eq_meta_id,
        target: eq_goal,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    });

    Ok(())
}

/// `convert` using a named hypothesis from context
pub fn convert_hyp(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;

    // Find hypothesis
    let decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;

    let proof_term = Expr::fvar(decl.fvar);

    convert(state, proof_term)
}
