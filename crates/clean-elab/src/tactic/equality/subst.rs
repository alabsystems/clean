// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Substitution tactics: subst, subst_vars.
//!
//! These tactics eliminate equality hypotheses by substituting free variables.
//! Split from structural.rs for file size (#307).

use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, Name};

use super::super::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::expr_utils::match_equality;
use crate::unify::MetaState;

/// All data needed to perform a substitution: target FVar, replacement, and equality info.
struct SubstInfo {
    fvar_id: FVarId,
    replacement: Expr,
    fvar_is_lhs: bool,
    hyp_fvar: FVarId,
    eq_type: Expr,
    eq_level_u: Level,
}

/// Whether `id` occurs free in `expr` (a specific-FVar occurrence check).
fn fvar_occurs_in(expr: &Expr, id: FVarId) -> bool {
    match expr.kind() {
        ExprKind::FVar(fid) => *fid == id,
        ExprKind::App(f, a) => fvar_occurs_in(f, id) || fvar_occurs_in(a, id),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            fvar_occurs_in(ty, id) || fvar_occurs_in(body, id)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            fvar_occurs_in(ty, id) || fvar_occurs_in(val, id) || fvar_occurs_in(body, id)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            fvar_occurs_in(inner, id)
        }
        _ => false,
    }
}

/// Whether `id` occurs in any OTHER hypothesis's type (excluding the equality
/// hypothesis `hyp_name` being substituted, and the variable's own decl).
///
/// A `subst` that eliminates variable `id` only abstracts `id` out of the GOAL
/// target (via the `Eq.ndrec` motive). Any surviving hypothesis whose type still
/// references `id` would keep its real (un-rewritten) declared type in the kernel
/// proof term, so plugging it back in (`exact h`) mismatches. Therefore a
/// dependent variable must NOT be the one eliminated when a cleaner side exists.
fn fvar_in_other_hyps(goal: &Goal, id: FVarId, hyp_name: &str) -> bool {
    goal.local_ctx
        .iter()
        .any(|d| d.name != hyp_name && d.fvar != id && fvar_occurs_in(&d.ty, id))
}

/// Determine which side of an equality is a free variable in the local context,
/// preferring the side that can be soundly eliminated.
///
/// Returns `(fvar_id, replacement, fvar_is_lhs)`.
///
/// # Direction selection
///
/// `subst` on `h : lhs = rhs` eliminates one side's local variable, abstracting it
/// out of the goal via the `Eq.ndrec` motive. Because that motive covers only the
/// GOAL (not other hypotheses), the eliminated variable must not appear in any
/// OTHER surviving hypothesis — otherwise that hypothesis keeps its real,
/// un-rewritten type in the kernel proof term and a later `exact h`/reference to it
/// mismatches (a `fvar mismatch`). So when both sides are context fvars, prefer the
/// side that does NOT occur in other hypotheses (Lean's `subst` reverts such
/// dependents; picking the clean side is the sound subset we support here). When
/// both sides are equally (in)dependent, fall back to eliminating the LHS, matching
/// the historical direction. If only one side is a context fvar, that side is used.
fn find_subst_fvar(
    goal: &Goal,
    hyp_name: &str,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<(FVarId, Expr, bool), TacticError> {
    let lhs_fvar = match lhs.kind() {
        ExprKind::FVar(id) if goal.local_ctx.iter().any(|d| d.fvar == *id) => Some(*id),
        _ => None,
    };
    let rhs_fvar = match rhs.kind() {
        ExprKind::FVar(id) if goal.local_ctx.iter().any(|d| d.fvar == *id) => Some(*id),
        _ => None,
    };

    match (lhs_fvar, rhs_fvar) {
        (Some(l), Some(r)) => {
            // Both sides are context variables. Prefer eliminating the side that is
            // NOT referenced by other hypotheses (the sound direction). If the LHS
            // is clean, or neither is clean (fall back to historical LHS-first), use
            // the LHS; otherwise use the RHS.
            let lhs_dependent = fvar_in_other_hyps(goal, l, hyp_name);
            let rhs_dependent = fvar_in_other_hyps(goal, r, hyp_name);
            if lhs_dependent && !rhs_dependent {
                Ok((r, lhs.clone(), false))
            } else {
                Ok((l, rhs.clone(), true))
            }
        }
        (Some(l), None) => Ok((l, rhs.clone(), true)),
        (None, Some(r)) => Ok((r, lhs.clone(), false)),
        (None, None) => Err(TacticError::GoalMismatch(
            "subst: neither side of the equality is a free variable in the context".to_string(),
        )),
    }
}

/// Build the `Eq.ndrec` proof term for substitution.
///
/// Constructs `@Eq.ndrec.{0,u} α e (fun z => P(z)) ?minor x (Eq.symm h | h)`.
/// Direction: `h:x=e` uses `Eq.symm`; `h:e=x` uses `h` directly.
fn build_eq_ndrec_proof(goal: &Goal, info: &SubstInfo, minor: Expr) -> Expr {
    let motive = Expr::lam(
        BinderInfo::Default,
        info.eq_type.clone(),
        goal.target.abstract_fvar(info.fvar_id),
    );
    let var_expr = Expr::fvar(info.fvar_id);
    let h_expr = Expr::fvar(info.hyp_fvar);

    let eq_proof = if info.fvar_is_lhs {
        let mut symm = Expr::const_(Name::from_string("Eq.symm"), vec![info.eq_level_u.clone()]);
        symm = Expr::app(symm, info.eq_type.clone());
        symm = Expr::app(symm, var_expr.clone());
        symm = Expr::app(symm, info.replacement.clone());
        Expr::app(symm, h_expr)
    } else {
        h_expr
    };

    let mut proof = Expr::const_(
        Name::from_string("Eq.ndrec"),
        vec![Level::zero(), info.eq_level_u.clone()],
    );
    proof = Expr::app(proof, info.eq_type.clone());
    proof = Expr::app(proof, info.replacement.clone());
    proof = Expr::app(proof, motive);
    proof = Expr::app(proof, minor);
    proof = Expr::app(proof, var_expr);
    Expr::app(proof, eq_proof)
}

/// The `subst` tactic substitutes an equality hypothesis into the goal and context.
///
/// Given a hypothesis `h : x = e` where `x` is a free variable, this tactic:
/// 1. Replaces all occurrences of `x` with `e` in the goal
/// 2. Replaces all occurrences of `x` with `e` in other hypotheses
/// 3. Removes the hypothesis `h` from the context
/// 4. Removes `x` from the context (since it's been substituted away)
///
/// The equality can be in either direction:
/// - `h : x = e` - substitutes `x` with `e`
/// - `h : e = x` - substitutes `x` with `e`
///
/// # Errors
/// - `HypothesisNotFound` if the hypothesis doesn't exist
/// - `GoalMismatch` if the hypothesis is not an equality
/// - `Other` if neither side of the equality is a free variable in the context
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` names an equality hypothesis in the local context
/// REQUIRES: One side of the equality is an FVar present in the local context
/// ENSURES: On Ok, original goal closed with `Eq.ndrec` proof (type-checked)
/// ENSURES: On Ok, new goal has `x` and `h` removed from context, `x` replaced by `e`
/// ENSURES: On Ok, all hypothesis types are updated with the substitution
/// ENSURES: On Err(GoalMismatch), neither side is a context FVar; state unchanged
pub fn subst(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let hyp_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    let hyp_ty = state.whnf(&goal, &hyp_decl.ty);
    let (eq_type, lhs, rhs, eq_levels) = match_equality(&hyp_ty)
        .map_err(|_| TacticError::GoalMismatch(format!("subst: {hyp_name} is not an equality")))?;

    let (fvar_id, replacement, fvar_is_lhs) = find_subst_fvar(&goal, hyp_name, &lhs, &rhs)?;
    let eq_level_u = eq_levels.into_iter().next().unwrap_or(Level::zero());

    let info = SubstInfo {
        fvar_id,
        replacement,
        fvar_is_lhs,
        hyp_fvar: hyp_decl.fvar,
        eq_type,
        eq_level_u,
    };

    let new_target = goal.target.subst_fvar(info.fvar_id, &info.replacement);

    let new_ctx: Vec<LocalDecl> = goal
        .local_ctx
        .iter()
        .filter(|d| d.name != hyp_name && d.fvar != info.fvar_id)
        .map(|d| LocalDecl {
            fvar: d.fvar,
            name: d.name.clone(),
            ty: d.ty.subst_fvar(info.fvar_id, &info.replacement),
            value: d
                .value
                .as_ref()
                .map(|v| v.subst_fvar(info.fvar_id, &info.replacement)),
        })
        .collect();

    let new_meta_id = state.fresh_meta_in_context(new_target.clone(), &new_ctx);
    let new_meta_expr = Expr::fvar(MetaState::to_fvar(new_meta_id));

    let proof = build_eq_ndrec_proof(&goal, &info, new_meta_expr);

    state.close_goal(&goal, proof)?;

    state.goals.push_front(Goal {
        meta_id: new_meta_id,
        target: new_target,
        local_ctx: new_ctx,
        tag: None,
    });

    Ok(())
}

/// The `subst_vars` tactic repeatedly applies `subst` to all equality hypotheses.
///
/// This finds all hypotheses of the form `h : x = e` or `h : e = x` where `x` is
/// a free variable and applies `subst` to eliminate them one by one.
///
/// # Example
/// ```text
/// x : Nat, y : Nat
/// h1 : x = 5
/// h2 : y = x + 1
/// goal : x + y = 11
///
/// subst_vars
///
/// goal : 5 + 6 = 11  (after substituting x=5, then y=6)
/// ```
pub fn subst_vars(state: &mut ProofState) -> TacticResult {
    let max_iterations = 100;
    for _ in 0..max_iterations {
        let goal = match state.current_goal() {
            Some(g) => g.clone(),
            None => return Ok(()),
        };

        let mut found = None;
        for decl in &goal.local_ctx {
            let hyp_ty = state.whnf(&goal, &decl.ty);
            if let Ok((_eq_type, lhs, rhs, _levels)) = match_equality(&hyp_ty) {
                let is_fvar_in_ctx = |e: &Expr| -> bool {
                    if let ExprKind::FVar(id) = e.kind() {
                        goal.local_ctx.iter().any(|d| d.fvar == *id)
                    } else {
                        false
                    }
                };

                if is_fvar_in_ctx(&lhs) || is_fvar_in_ctx(&rhs) {
                    found = Some(decl.name.clone());
                    break;
                }
            }
        }

        match found {
            Some(hyp_name) => {
                subst(state, &hyp_name)?;
            }
            None => return Ok(()),
        }
    }

    Ok(())
}
