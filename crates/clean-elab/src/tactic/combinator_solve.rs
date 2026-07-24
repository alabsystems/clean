// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Depth-limited hypothesis search used by `solve_by_elim`.

use clean_kernel::{Expr, ExprKind};

use super::core::{Goal, ProofState, TacticError, TacticResult};
use super::proof_term::{apply, assumption};
use crate::stack_safe;

/// Solve the goal by iteratively applying hypotheses from the context.
///
/// This tactic searches for a proof by:
/// 1. Trying `assumption` (if the goal is directly in the context)
/// 2. Trying to apply each hypothesis and recursively solving subgoals
///
/// Uses depth-limited search to prevent infinite loops.
///
/// REQUIRES: `state.goals` is non-empty; `max_depth > 0` for meaningful search
///
/// ENSURES: on Ok, all goals are closed using only local hypotheses and
/// function application to depth <= `max_depth`; on Err, state is unchanged
/// (every recursive branch restores meta scopes on failure)
pub fn solve_by_elim(state: &mut ProofState, max_depth: usize) -> TacticResult {
    solve_by_elim_aux(state, max_depth, 0)
}

fn solve_by_elim_aux(
    state: &mut ProofState,
    max_depth: usize,
    current_depth: usize,
) -> TacticResult {
    stack_safe(|| {
        if current_depth > max_depth {
            return Err(TacticError::DepthExceeded {
                tactic: "solve_by_elim".into(),
                max_depth,
            });
        }

        if state.goals.is_empty() {
            return Ok(());
        }

        let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

        let saved_goals = state.goals.clone();
        state.metas_mut().push_scope();
        if assumption(state).is_ok() {
            if state.goals.is_empty() {
                state.metas_mut().commit();
                return Ok(());
            }
            if solve_by_elim_aux(state, max_depth, current_depth).is_ok() {
                state.metas_mut().commit();
                return Ok(());
            }
            state.invalidate_tc_cache();
            state.goals = saved_goals;
            state.metas_mut().pop_scope();
        } else {
            state.metas_mut().pop_scope();
        }

        for decl in &goal.local_ctx {
            let hyp_ty = state.metas.instantiate(&decl.ty);
            if is_applicable_hyp(&hyp_ty) || could_match_goal(state, &goal, &hyp_ty) {
                let saved_goals = state.goals.clone();
                state.metas_mut().push_scope();
                let hyp_expr = Expr::fvar(decl.fvar);

                if apply(state, hyp_expr).is_ok()
                    && solve_all_goals(state, max_depth, current_depth + 1).is_ok()
                {
                    state.metas_mut().commit();
                    return Ok(());
                }

                state.invalidate_tc_cache();
                state.goals = saved_goals;
                state.metas_mut().pop_scope();
            }
        }

        Err(TacticError::HypothesisNotFound(
            "solve_by_elim: no applicable hypothesis found".into(),
        ))
    })
}

fn is_applicable_hyp(ty: &Expr) -> bool {
    matches!(ty.kind(), ExprKind::Pi(_, _, _))
}

fn could_match_goal(state: &ProofState, goal: &Goal, hyp_ty: &Expr) -> bool {
    let target = state.metas.instantiate(&goal.target);
    state.is_def_eq(goal, hyp_ty, &target)
}

fn solve_all_goals(state: &mut ProofState, max_depth: usize, current_depth: usize) -> TacticResult {
    while !state.goals.is_empty() {
        solve_by_elim_aux(state, max_depth, current_depth)?;
    }
    Ok(())
}
