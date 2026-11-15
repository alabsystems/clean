// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retain equations when case analysis generalizes compound family indices.
//!
//! Generalization alone asks for every constructor branch, including branches
//! incompatible with the original index. Revert the major and its dependents,
//! generalize with an equation, and carry that equation through the motive.
//! The existing equation solver then specializes or closes each branch.

use std::collections::HashSet;

use clean_kernel::{Expr, ExprKind, FVarId};
use clean_parser::SurfaceName;

use super::core::{Goal, ProofState, TacticError, TacticResult};

fn compound_indices(
    state: &ProofState,
    goal: &Goal,
    major: FVarId,
) -> Result<Vec<Expr>, TacticError> {
    let decl = goal
        .local_ctx
        .iter()
        .find(|d| d.fvar == major)
        .ok_or_else(|| TacticError::HypothesisNotFound(format!("{major:?}")))?;
    let ty = state.whnf(goal, &decl.ty);
    let ExprKind::Const(name, _) = ty.get_app_fn().kind() else {
        return Ok(Vec::new());
    };
    // These have dedicated equation-elimination paths already.
    if name == &clean_kernel::Name::from_string("Eq")
        || name == &clean_kernel::Name::from_string("HEq")
    {
        return Ok(Vec::new());
    }
    let Some(ind) = state.env.get_inductive(name) else {
        return Ok(Vec::new());
    };
    let indices = super::indexed_family::applied_index_args(ind, &ty).ok_or_else(|| {
        TacticError::GoalMismatch("cases: incomplete indexed family application".into())
    })?;
    Ok(indices
        .into_iter()
        .filter(|e| !matches!(e.kind(), ExprKind::FVar(_)))
        .collect())
}

/// `None` leaves the historical local-index/non-indexed route unchanged.
/// A failed generalized elimination rolls back all its proof-state changes.
pub(crate) fn try_cases(state: &mut ProofState, major: FVarId) -> Option<TacticResult> {
    let goal = state.current_goal()?.clone();
    let indices = match compound_indices(state, &goal, major) {
        Ok(indices) if indices.is_empty() => return None,
        Ok(indices) => indices,
        Err(error) => return Some(Err(error)),
    };
    Some(super::cases_unify_eqs::attempt(state, |state| {
        cases_with_equations(state, major, indices)
    }))
}

fn cases_with_equations(
    state: &mut ProofState,
    mut major: FVarId,
    mut indices: Vec<Expr>,
) -> TacticResult {
    let tag = state
        .current_goal()
        .ok_or(TacticError::NoGoals)?
        .tag
        .clone();
    let mut equations = 0;
    while let Some(term) = indices.first().cloned() {
        let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let mut selected: HashSet<_> =
            super::major_dependents::dependents_of(state, &goal, &[major])
                .into_iter()
                .collect();
        selected.insert(major);
        let ordered: Vec<_> = goal
            .local_ctx
            .iter()
            .filter(|d| selected.contains(&d.fvar))
            .map(|d| d.fvar)
            .collect();
        let names = super::major_dependents::revert_fvars(state, &ordered)?;
        let ctx = &state.current_goal().ok_or(TacticError::NoGoals)?.local_ctx;
        let index_name = super::pattern::util::generate_fresh_hyp_name(
            ctx,
            &SurfaceName::generated_path("cases_index"),
        );
        let eq_name = super::pattern::util::generate_fresh_hyp_name(
            ctx,
            &SurfaceName::generated_path("cases_index_eq"),
        );
        super::generalize::generalize_eq(state, term, &index_name, &eq_name)?;
        let equation = state
            .current_goal()
            .and_then(|g| g.local_ctx.last())
            .map(|d| d.fvar)
            .ok_or(TacticError::NoGoals)?;
        let old_major = major;
        for (old, name) in ordered.iter().zip(names.iter().rev()) {
            super::target_equation::intro_shadowing(state, name)?;
            if *old == old_major {
                major = state
                    .current_goal()
                    .and_then(|g| g.local_ctx.last())
                    .map(|d| d.fvar)
                    .ok_or(TacticError::NoGoals)?;
            }
        }
        super::major_dependents::revert_fvars(state, &[equation])?;
        equations += 1;
        let next = compound_indices(
            state,
            state.current_goal().ok_or(TacticError::NoGoals)?,
            major,
        )?;
        if next.len() >= indices.len() {
            return Err(TacticError::GoalMismatch(
                "cases: index generalization did not remove a compound index".into(),
            ));
        }
        indices = next;
    }
    state.current_goal_mut().ok_or(TacticError::NoGoals)?.tag = tag;
    let existing: HashSet<_> = state.goals.iter().map(|g| g.meta_id).collect();
    super::proof_manipulation::cases_fvar(state, major)?;
    let branches: Vec<_> = state
        .goals
        .iter()
        .filter(|g| !existing.contains(&g.meta_id))
        .map(|g| g.meta_id)
        .collect();
    for branch in branches {
        let Some(index) = state.goals.iter().position(|g| g.meta_id == branch) else {
            continue;
        };
        state
            .focus_goal(index, |state| {
                let tag = state
                    .current_goal()
                    .ok_or(TacticError::NoGoals)?
                    .tag
                    .clone();
                if super::cases_unify_eqs::unify_index_eqs(state, equations)? {
                    state.current_goal_mut().ok_or(TacticError::NoGoals)?.tag = tag;
                }
                Ok(())
            })
            .ok_or(TacticError::NoGoals)??;
    }
    Ok(())
}
