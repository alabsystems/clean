// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural equality tactics: symm, trans, calc_trans.
//!
//! Tactics that manipulate equalities structurally (symmetry, transitivity)
//! without rewriting subexpressions.
//! Substitution tactics (subst, subst_vars) are in subst.rs (#307 split).

use clean_kernel::{Expr, Name};

use super::super::{Goal, ProofState, TacticError, TacticResult};
use super::expr_utils::match_equality;
use crate::unify::MetaState;

/// Symmetry tactic for equality goals.
///
/// For a goal `a = b`, reduces the goal to `b = a` using `Eq.symm`.
/// Requires `Eq.symm` to be present in the environment (via `env.init_eq()`).
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: Current goal target WHNF-reduces to `@Eq α a b`
/// REQUIRES: `Eq.symm` exists in the environment
/// ENSURES: On Ok, original goal closed with `Eq.symm` proof
/// ENSURES: On Ok, new goal `b = a` pushed with same local context
/// ENSURES: On Err(GoalMismatch), goal is not an equality; state unchanged
pub fn symm(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.whnf(&goal, &goal.target);

    let (eq_ty, lhs, rhs, levels) = match_equality(&target)
        .map_err(|_| TacticError::GoalMismatch("symm: goal is not an equality".to_string()))?;

    let symm_name = Name::from_string("Eq.symm");
    if state.env.get_const(&symm_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Eq.symm".to_string(),
        });
    }

    let eq_ty = state.metas.instantiate(&eq_ty);
    let lhs = state.metas.instantiate(&lhs);
    let rhs = state.metas.instantiate(&rhs);

    // Build the swapped goal: b = a
    let swapped_target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), levels.clone()),
                eq_ty.clone(),
            ),
            rhs.clone(),
        ),
        lhs.clone(),
    );
    let swapped_meta_id = state.fresh_meta(swapped_target.clone());
    let swapped_meta = Expr::fvar(MetaState::to_fvar(swapped_meta_id));

    // Eq.symm {α := eq_ty} {a := rhs} {b := lhs} ?m : lhs = rhs
    let mut proof = Expr::const_(symm_name, levels);
    proof = Expr::app(proof, eq_ty);
    proof = Expr::app(proof, rhs);
    proof = Expr::app(proof, lhs);
    proof = Expr::app(proof, swapped_meta.clone());

    // Part of #2154: type-check Eq.symm proof before accepting
    state.close_goal(&goal, proof)?;

    let new_goal = Goal {
        meta_id: swapped_meta_id,
        target: swapped_target,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };
    state.goals.push_front(new_goal);

    Ok(())
}

/// The `trans` tactic applies transitivity to an equality goal.
///
/// Given a goal `a = c`, the tactic splits it into two subgoals:
/// - `a = middle` (first goal to prove)
/// - `middle = c` (second goal to prove)
///
/// The proof is constructed using `Eq.trans`.
///
/// # Example
/// ```text
/// Goal: x = z
/// trans y
/// Goal 1: x = y
/// Goal 2: y = z
/// ```
///
/// When both subgoals are solved, the proof is `Eq.trans ?1 ?2`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: Current goal target WHNF-reduces to `@Eq α a c`
/// REQUIRES: `Eq.trans` exists in the environment
/// REQUIRES: `middle` is well-typed and has type `α`
/// ENSURES: On Ok, original goal closed with `Eq.trans` proof
/// ENSURES: On Ok, two new goals pushed: `a = middle` (first) and `middle = c`
/// ENSURES: On Err(GoalMismatch), goal is not an equality; state unchanged
pub fn trans(state: &mut ProofState, middle: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.whnf(&goal, &goal.target);

    // Match goal as equality a = c
    let (eq_ty, lhs, rhs, levels) = match_equality(&target)
        .map_err(|_| TacticError::GoalMismatch("trans: goal is not an equality".to_string()))?;

    // Check that Eq.trans exists
    let trans_name = Name::from_string("Eq.trans");
    if state.env.get_const(&trans_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Eq.trans".to_string(),
        });
    }

    let eq_ty = state.metas.instantiate(&eq_ty);
    let lhs = state.metas.instantiate(&lhs);
    let rhs = state.metas.instantiate(&rhs);
    let middle = state.metas.instantiate(&middle);

    // Build the first subgoal: a = middle
    let goal1_target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), levels.clone()),
                eq_ty.clone(),
            ),
            lhs.clone(),
        ),
        middle.clone(),
    );
    let goal1_meta_id = state.fresh_meta(goal1_target.clone());
    let goal1_meta = Expr::fvar(MetaState::to_fvar(goal1_meta_id));

    // Build the second subgoal: middle = c
    let goal2_target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), levels.clone()),
                eq_ty.clone(),
            ),
            middle.clone(),
        ),
        rhs.clone(),
    );
    let goal2_meta_id = state.fresh_meta(goal2_target.clone());
    let goal2_meta = Expr::fvar(MetaState::to_fvar(goal2_meta_id));

    // Build proof: Eq.trans {α} {a} {middle} {c} ?goal1 ?goal2
    // Eq.trans : ∀ {α : Sort u} {a b c : α}, Eq a b → Eq b c → Eq a c
    let mut proof = Expr::const_(trans_name, levels);
    proof = Expr::app(proof, eq_ty); // {α}
    proof = Expr::app(proof, lhs); // {a}
    proof = Expr::app(proof, middle); // {b}
    proof = Expr::app(proof, rhs); // {c}
    proof = Expr::app(proof, goal1_meta); // h1: a = middle
    proof = Expr::app(proof, goal2_meta); // h2: middle = c

    // Part of #2154: type-check Eq.trans proof before accepting
    state.close_goal(&goal, proof)?;

    // Add both goals (goal1 first, then goal2)
    let new_goal1 = Goal {
        meta_id: goal1_meta_id,
        target: goal1_target,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };
    let new_goal2 = Goal {
        meta_id: goal2_meta_id,
        target: goal2_target,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };

    // Insert goals: goal1 is first (current), goal2 comes after
    state.goals.push_front(new_goal2);
    state.goals.push_front(new_goal1);

    Ok(())
}

/// The `calc_trans` tactic applies transitivity using two existing equality hypotheses.
///
/// Given hypotheses `h1: a = b` and `h2: b = c` in the context, this tactic
/// produces a proof of `a = c` by applying `Eq.trans h1 h2`.
///
/// This is useful when building calculation chains manually.
///
/// # Example
/// ```text
/// h1 : x = y
/// h2 : y = z
/// Goal: x = z
/// calc_trans "h1" "h2"
/// -- Goal solved with proof Eq.trans h1 h2
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `h1_name` and `h2_name` are equality hypotheses in the local context
/// REQUIRES: `Eq.trans` exists in the environment
/// REQUIRES: RHS of h1 is def-eq to LHS of h2 (transitivity chain)
/// REQUIRES: LHS of h1 matches goal LHS, RHS of h2 matches goal RHS
/// ENSURES: On Ok, the current goal is closed with `Eq.trans h1 h2`
/// ENSURES: On Err(GoalMismatch), chain does not connect; state unchanged
pub fn calc_trans(state: &mut ProofState, h1_name: &str, h2_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.whnf(&goal, &goal.target);

    // Match goal as equality a = c
    let (goal_ty, goal_lhs, goal_rhs, goal_levels) = match_equality(&target).map_err(|_| {
        TacticError::GoalMismatch("calc_trans: goal is not an equality".to_string())
    })?;

    // Check that Eq.trans exists
    let trans_name = Name::from_string("Eq.trans");
    if state.env.get_const(&trans_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Eq.trans".to_string(),
        });
    }

    // Find h1 in context
    let h1_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == h1_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(h1_name.to_string()))?;

    // Find h2 in context
    let h2_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == h2_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(h2_name.to_string()))?;

    // Match h1 as equality a = b
    let h1_ty = state.whnf(&goal, &h1_decl.ty);
    let (_h1_eq_ty, h1_lhs, h1_rhs, _h1_levels) = match_equality(&h1_ty)
        .map_err(|_| TacticError::GoalMismatch(format!("{h1_name} is not an equality")))?;

    // Match h2 as equality b' = c
    let h2_ty = state.whnf(&goal, &h2_decl.ty);
    let (_h2_eq_ty, h2_lhs, h2_rhs, _h2_levels) = match_equality(&h2_ty)
        .map_err(|_| TacticError::GoalMismatch(format!("{h2_name} is not an equality")))?;

    // Check that h1's RHS equals h2's LHS (the "middle" term)
    if !state.is_def_eq(&goal, &h1_rhs, &h2_lhs) {
        return Err(TacticError::GoalMismatch(format!(
            "calc_trans: RHS of {h1_name} does not match LHS of {h2_name} (transitivity chain broken)"
        )));
    }

    // Check that h1's LHS equals goal's LHS
    if !state.is_def_eq(&goal, &h1_lhs, &goal_lhs) {
        return Err(TacticError::GoalMismatch(format!(
            "calc_trans: LHS of {h1_name} does not match goal LHS"
        )));
    }

    // Check that h2's RHS equals goal's RHS
    if !state.is_def_eq(&goal, &h2_rhs, &goal_rhs) {
        return Err(TacticError::GoalMismatch(format!(
            "calc_trans: RHS of {h2_name} does not match goal RHS"
        )));
    }

    // Build proof: Eq.trans {α} {a} {b} {c} h1 h2
    let mut proof = Expr::const_(trans_name, goal_levels);
    proof = Expr::app(proof, state.metas.instantiate(&goal_ty)); // {α}
    proof = Expr::app(proof, state.metas.instantiate(&h1_lhs)); // {a}
    proof = Expr::app(proof, state.metas.instantiate(&h1_rhs)); // {b}
    proof = Expr::app(proof, state.metas.instantiate(&h2_rhs)); // {c}
    proof = Expr::app(proof, Expr::fvar(h1_decl.fvar)); // h1
    proof = Expr::app(proof, Expr::fvar(h2_decl.fvar)); // h2

    // Part of #2154: type-check Eq.trans proof before accepting
    state.close_goal(&goal, proof)
}
