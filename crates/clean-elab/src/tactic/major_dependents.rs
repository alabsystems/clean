// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hypotheses that mention an eliminated variable: ledger class (80) for
//! `cases`, gap G22 for `induction`.
//!
//! Lean never leaves such a hypothesis about the old variable. Its `cases`
//! (`Lean.MVarId.cases` → `MVarId.induction`, and the tactic's
//! `generalizeTargetsEq` + `unifyEqs?`) reverts every local whose type
//! depends on the major premise, eliminates, and re-introduces them after the
//! constructor's fields under their own names; `induction` generalizes them
//! into the motive (`generalizeVars`, `getFVarSetToGeneralize`), so the
//! induction hypothesis carries them as premises. Pinned Lean 4.8.0, after
//! `cases p` with `h : p.isLeaf = true` before `k`, which does not mention
//! `p`, prints `q, k, a✝, h : (P.leaf a✝).isLeaf = true`.
//!
//! Clean removed the major from each case's context and kept `h` unchanged,
//! naming a variable that no longer existed (`h : b = true` against the goal
//! `false = true`).
//!
//! The revert here keeps the reverted goal's binder scope, as a case goal
//! does (`ProofState::fresh_case_meta`): the eliminator's field binders sit
//! UNDER the reverted locals' binders, so they must not be handed a reverted
//! local's id, which `close_fvars`' id-to-depth arithmetic would resolve to
//! that local.

use std::collections::HashSet;

use clean_kernel::{Expr, ExprKind, FVarId};
use clean_parser::SurfaceName;

use super::core::{Goal, LocalDecl, ProofState, TacticError};
use super::hypothesis::collect_fvars;
use crate::unify::{MetaId, MetaState};

/// A declaration's dependencies when abstracting a telescope. A marked
/// `have` is opaque, so only its type participates; a genuine let's value
/// also participates. This is Lean's `findLocalDeclDependsOn` with
/// `generalizeNondepLet = true`, not its backward forbidden-set query.
pub(crate) fn generalizing_depends_on(
    state: &ProofState,
    decl: &LocalDecl,
    roots: &HashSet<FVarId>,
) -> bool {
    let mentions = |expr: &Expr| {
        collect_fvars(&state.metas.instantiate(expr))
            .iter()
            .any(|fvar| roots.contains(fvar))
    };
    mentions(&decl.ty) || (!decl.is_have() && decl.value.as_ref().is_some_and(mentions))
}

/// The locals of `goal` that depend on `roots` when abstracting a telescope,
/// directly or through another such local, in context order. `roots`
/// themselves are not included.
pub(crate) fn dependents_of(state: &ProofState, goal: &Goal, roots: &[FVarId]) -> Vec<FVarId> {
    let mut reached: HashSet<FVarId> = roots.iter().copied().collect();
    let mut out = Vec::new();
    for decl in &goal.local_ctx {
        if reached.contains(&decl.fvar) {
            continue;
        }
        if generalizing_depends_on(state, decl, &reached) {
            reached.insert(decl.fvar);
            out.push(decl.fvar);
        }
    }
    out
}

/// The locals the major premise `major` depends on, transitively, with
/// `major` itself: Lean's `mkGeneralizationForbiddenSet`. Generalizing one of
/// them would revert the major premise with it.
pub(crate) fn forbidden_for(goal: &Goal, major: FVarId) -> HashSet<FVarId> {
    let mut forbidden = HashSet::from([major]);
    let mut todo = vec![major];
    while let Some(fvar) = todo.pop() {
        let Some(decl) = goal.local_ctx.iter().find(|d| d.fvar == fvar) else {
            continue;
        };
        let mut mentioned = collect_fvars(&decl.ty);
        if let Some(value) = &decl.value {
            mentioned.extend(collect_fvars(value));
        }
        for dep in mentioned {
            if forbidden.insert(dep) {
                todo.push(dep);
            }
        }
    }
    forbidden
}

/// Revert `fvars` — a set closed under dependency — from the current goal as
/// leading `∀` and let binders of its target, in context order, and return their
/// names in REVERT order (the last in context first), the order
/// [`reintroduce`] and the `generalizing` re-introduction take.
///
/// A local definition retains its type and value in a let binder.
///
/// ENSURES: on `Ok`, the new main goal's context is the old one without
///   `fvars`, its tag and case binders are the old goal's, and the old goal
///   is closed by the new goal's metavariable applied to ordinary hypotheses.
pub(crate) fn revert_fvars(
    state: &mut ProofState,
    fvars: &[FVarId],
) -> Result<Vec<SurfaceName>, TacticError> {
    if fvars.is_empty() {
        return Ok(Vec::new());
    }
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let wanted: HashSet<FVarId> = fvars.iter().copied().collect();
    let reverted: Vec<_> = goal
        .local_ctx
        .iter()
        .filter(|d| wanted.contains(&d.fvar))
        .cloned()
        .collect();
    if reverted.len() != wanted.len() {
        return Err(TacticError::HypothesisNotFound(
            "revert: a dependent hypothesis is not in the current goal".to_string(),
        ));
    }
    let new_ctx: Vec<_> = goal
        .local_ctx
        .iter()
        .filter(|d| !wanted.contains(&d.fvar))
        .cloned()
        .collect();
    let target = state.metas.instantiate(&goal.target);
    let mut new_target = target;
    for decl in reverted.iter().rev() {
        let ty = state.metas.instantiate(&decl.ty);
        let body = new_target.abstract_fvar(decl.fvar);
        // A marked `have` is opaque, matching Lean's nondep local: it
        // generalizes as a hypothesis even though Clean retains its proof.
        new_target = match &decl.value {
            Some(value) if !decl.is_have() => Expr::let_named(
                decl.name.name().clone(),
                ty,
                state.metas.instantiate(value),
                body,
                false,
            ),
            _ => Expr::pi(decl.binder_info, ty, body),
        };
    }
    let new_meta_id: MetaId = state.fresh_case_meta(new_target.clone(), &goal, &new_ctx);
    let mut proof = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id)));
    for decl in &reverted {
        // A let is already defined inside the new goal's type, so it is not
        // a function argument. Only ordinary hypotheses are applied here.
        if decl.value.is_none() || decl.is_have() {
            proof = Expr::app(proof, Expr::fvar(decl.fvar));
        }
    }
    state.close_goal(&goal, proof)?;
    state.goals.push_front(Goal {
        meta_id: new_meta_id,
        target: new_target,
        local_ctx: new_ctx,
        case_binders: goal.case_binders.clone(),
        tag: goal.tag.clone(),
    });
    Ok(reverted.iter().rev().map(|d| d.name.clone()).collect())
}

/// Re-introduce `names` (given in revert order) at the front of every goal
/// whose metavariable is in `case_metas`, keeping each goal's tag and case
/// binders: Lean's per-case `introNP` of the reverted locals.
pub(crate) fn reintroduce(
    state: &mut ProofState,
    case_metas: &[MetaId],
    names: &[SurfaceName],
) -> Result<(), TacticError> {
    if names.is_empty() {
        return Ok(());
    }
    for meta in case_metas {
        let Some(index) = state.goals.iter().position(|g| g.meta_id == *meta) else {
            continue;
        };
        let tag = state.goals.get(index).and_then(|g| g.tag.clone());
        let outcome = state.focus_goal(index, |st| {
            for name in names.iter().rev() {
                super::target_equation::intro_shadowing(st, name)?;
            }
            Ok(())
        });
        match outcome {
            Some(result) => result?,
            None => {
                return Err(TacticError::InvalidTarget {
                    tactic: "cases".into(),
                    detail: "re-introduction: goal index out of range".into(),
                })
            }
        }
        if let Some(goal) = state.goals.get_mut(index) {
            goal.tag = tag;
        }
    }
    Ok(())
}

/// What `induction x generalizing ys` reverts before it eliminates, Lean
/// 4.8's `generalizeVars`: every local that mentions `x` (generalized
/// automatically, gap G22) together with `ys` and their dependents, reverted
/// together in CONTEXT order, so each induction hypothesis quantifies over
/// them in that order. Returns the reverted names in revert order.
///
/// Lean's two refusals are kept: a `generalizing` variable `x`'s own type
/// depends on ("variable cannot be generalized because target depends on
/// it") and one that is already generalized ("unnecessary 'generalizing'
/// argument, variable '…' is generalized automatically").
pub(crate) fn generalize_for_induction(
    state: &mut ProofState,
    major_name: &SurfaceName,
    user: &[SurfaceName],
) -> Result<Vec<SurfaceName>, TacticError> {
    let named = |decl: &LocalDecl, name: &SurfaceName| {
        crate::tactic::pattern::names::hypothesis_named(&decl.name, name)
    };
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let Some(major) = goal
        .local_ctx
        .iter()
        .rev()
        .find(|d| named(d, major_name))
        .map(|d| d.fvar)
    else {
        // The eliminator reports the unknown target itself.
        return Ok(Vec::new());
    };
    let forbidden = forbidden_for(&goal, major);
    let mut set: HashSet<FVarId> = dependents_of(state, &goal, &[major]).into_iter().collect();
    for name in user {
        let decl = goal
            .local_ctx
            .iter()
            .rev()
            .find(|d| named(d, name))
            .ok_or_else(|| {
                TacticError::HypothesisNotFound(format!(
                    "induction … generalizing: '{name}' is not a hypothesis in the current goal"
                ))
            })?;
        if forbidden.contains(&decl.fvar) {
            return Err(TacticError::GoalMismatch(format!(
                "variable cannot be generalized because target depends on it: {name}"
            )));
        }
        if !set.insert(decl.fvar) {
            return Err(TacticError::GoalMismatch(format!(
                "unnecessary 'generalizing' argument, variable '{name}' is generalized \
                 automatically"
            )));
        }
    }
    let roots: Vec<FVarId> = set.iter().copied().collect();
    set.extend(dependents_of(state, &goal, &roots));
    let ordered: Vec<FVarId> = goal
        .local_ctx
        .iter()
        .filter(|d| set.contains(&d.fvar))
        .map(|d| d.fvar)
        .collect();
    revert_fvars(state, &ordered)
}
