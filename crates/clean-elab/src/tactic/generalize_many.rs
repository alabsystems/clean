// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generalizing several terms at once, each with its equation pending —
//! Lean 4.8's `MVarId.generalize` on an array of `GeneralizeArg`s
//! (`Lean/Meta/Tactic/Generalize.lean`, `generalizeCore`), as `rcases h₁ :
//! e₁, h₂ : e₂ with …` uses it.
//!
//! `generalizeCore` builds the telescope in two passes. `go` abstracts the
//! terms out of the TARGET only, innermost (last) first: `∀ x₁, (∀ x₂, T[e₂ :=
//! x₂])[e₁ := x₁]`. `go'` then adds the equations `hᵢ : eᵢ = xᵢ`, each built
//! from the ORIGINAL `eᵢ` (`arg.expr`). So no equation is ever rewritten by
//! another target's abstraction: with `rcases ha : n, hb : look n with ⟨m, w⟩`
//! Lean has `hb : look n = w`, never `look m = w`. Generalizing one term at a
//! time instead — each later call abstracting the earlier equations already
//! pending in the target — rewrote them, and accepted `have : look m = w :=
//! hb`, which pinned Lean refuses.

use clean_kernel::{BinderInfo, Expr, ExprKind};
use clean_parser::SurfaceName;

use super::core::{Goal, ProofState, TacticError, TacticResult};
use super::equality::abstract_over;
use super::proof_term::intro;
use crate::unify::MetaState;

/// Generalize `terms` in the current goal to fresh variables named
/// `var_names` (one each, same order), leaving `eᵢ = xᵢ → … →
/// target[eᵢ := xᵢ]` — an equation for each term whose `with_eq` is set, in
/// order — with only the variables introduced.
///
/// Every equation states the ORIGINAL term (`generalizeCore`'s `go'`). A
/// variable whose type mentions an earlier generalized term would need a
/// heterogeneous equation (Lean's `mkEqHEq`); that case is refused.
///
/// SOUNDNESS: the original goal is closed by the new goal's metavariable
/// applied to the terms and their `Eq.refl` proofs, which the kernel
/// re-checks with the rest of the proof term; nothing is assumed.
///
/// REQUIRES: `terms`, `var_names` and `with_eq` have one entry per term, and
/// the goal list is non-empty.
/// ENSURES: on Ok the original goal is closed and the front goal is the
/// generalized one, with `x₁ … xₖ` introduced in order.
pub(crate) fn generalize_eqs_pending(
    state: &mut ProofState,
    terms: &[Expr],
    var_names: &[SurfaceName],
    with_eq: &[bool],
) -> TacticResult {
    if terms.len() != var_names.len() || terms.len() != with_eq.len() {
        return Err(TacticError::InvalidTarget {
            tactic: "generalize".into(),
            detail: "one variable name per generalized term is required".into(),
        });
    }
    if terms.is_empty() {
        return Ok(());
    }
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let terms: Vec<Expr> = terms.iter().map(|t| state.metas.instantiate(t)).collect();
    let mut types = Vec::with_capacity(terms.len());
    for term in &terms {
        types.push(state.metas.instantiate(&state.infer_type(&goal, term)?));
    }

    // `go`: `∀ x₁ : τ₁, abstract(∀ x₂ : τ₂, abstract(… T …, e₂), e₁)`. Each
    // step's body is closed, so `abstract_over` binds exactly its own term.
    let mut telescope = state.metas.instantiate(&goal.target);
    for (term, ty) in terms.iter().zip(&types).rev() {
        telescope = Expr::pi(
            BinderInfo::Default,
            ty.clone(),
            abstract_over(&telescope, term),
        );
    }
    // Peel the `k` variable binders back off: their (possibly abstracted)
    // types and the body under them.
    let mut binder_types = Vec::with_capacity(terms.len());
    let mut body = telescope;
    for _ in 0..terms.len() {
        let ExprKind::Pi(_, ty, inner) = body.kind() else {
            return Err(TacticError::InvalidTarget {
                tactic: "generalize".into(),
                detail: "the generalized telescope lost a binder".into(),
            });
        };
        binder_types.push(ty.as_ref().clone());
        body = inner.as_ref().clone();
    }
    if binder_types.iter().any(Expr::has_loose_bvars) {
        return Err(TacticError::InvalidTarget {
            tactic: "generalize".into(),
            detail: "a generalized term's type mentions another generalized term; its \
                     equation would be heterogeneous (`HEq`), which is not supported"
                .into(),
        });
    }

    // `go'`: the equations, under all `k` variables, in order. The equation
    // of term `i` sits under `k + m` binders, `m` the equations before it, and
    // `xᵢ` was bound under `i`, so `xᵢ` is `bvar(k + m - i - 1)`.
    let count = terms.len();
    let mut equations = Vec::with_capacity(count);
    let mut refls = Vec::with_capacity(count);
    for (index, ((term, ty), _)) in terms
        .iter()
        .zip(&types)
        .zip(with_eq)
        .enumerate()
        .filter(|(_, (_, wanted))| **wanted)
    {
        let var = Expr::bvar(u32_index(count + equations.len() - index - 1)?);
        let (eq_const, eq_refl_const) = super::generalize::eq_constants(state, &goal, ty)?;
        equations.push(Expr::app(
            Expr::app(Expr::app(eq_const, ty.clone()), term.clone()),
            var,
        ));
        refls.push(Expr::app(
            Expr::app(eq_refl_const, ty.clone()),
            term.clone(),
        ));
    }
    // The body's variables now sit `k` equations further out.
    let mut new_target = body.lift(u32_index(equations.len())?);
    for equation in equations.into_iter().rev() {
        new_target = Expr::pi(BinderInfo::Default, equation, new_target);
    }
    for ty in binder_types.into_iter().rev() {
        new_target = Expr::pi(BinderInfo::Default, ty, new_target);
    }

    // Under the parent's scope, so the intros below never reuse the id of a
    // variable an elimination above this goal bound (see `generalize`).
    let new_meta_id = state.fresh_case_meta(new_target.clone(), &goal, &goal.local_ctx);
    let mut proof = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id)));
    for term in &terms {
        proof = Expr::app(proof, term.clone());
    }
    for refl in refls {
        proof = Expr::app(proof, refl);
    }
    state.close_goal(&goal, proof)?;
    state.goals.push_front(Goal {
        meta_id: new_meta_id,
        target: new_target,
        local_ctx: goal.local_ctx.clone(),
        case_binders: goal.case_binders.clone(),
        tag: None,
    });
    for name in var_names {
        intro(state, name)?;
    }
    Ok(())
}

/// A binder index as the kernel's `u32`.
fn u32_index(index: usize) -> Result<u32, TacticError> {
    u32::try_from(index).map_err(|_| TacticError::InvalidTarget {
        tactic: "generalize".into(),
        detail: "too many generalized terms".into(),
    })
}
