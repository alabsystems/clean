// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A helper as its binding site describes it, and its closure over the locals
//! it captures (`super` module docs).

use std::collections::{HashMap, HashSet};

use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Name};
use clean_parser::{Span, SurfaceBinder, SurfaceExpr};

use super::rewrite::ascribe_closed;
use crate::infer::ElabCtx;
use crate::unify::MetaState;

/// Whether a helper's binding refers to itself (Lean's `isNonRecursive`,
/// per clique).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::infer) enum HelperRecursion {
    /// The value never mentions the helper.
    NonRecursive,
    /// The value calls the helper.
    Recursive,
}

/// One `where` / `let rec` helper, as its binding site describes it to
/// [`ElabCtx::let_rec_lifted_value`].
#[derive(Debug)]
pub(in crate::infer) struct HelperSite<'s> {
    /// The name the helper lifts to.
    pub(in crate::infer) aux: &'s Name,
    /// Where the helper was written: its binder's region, or, for a binder
    /// the parser does not place (a term-level `let rec`), its value's
    /// ([`helper_site_span`]).
    pub(in crate::infer) span: Span,
    /// Whether its value calls it.
    pub(in crate::infer) recursion: HelperRecursion,
    /// The names its type gives its leading own parameters, outermost first
    /// ([`helper_own_params`]); `None` when it gives none (an equation-form
    /// helper's matched argument has no name).
    pub(in crate::infer) own_params: Option<Vec<(Name, BinderInfo)>>,
}

/// Where a helper was written: its binder's source region when the parser
/// placed it, else its value's.
pub(in crate::infer) fn helper_site_span(binder: &SurfaceBinder, val: &SurfaceExpr) -> Span {
    if binder.span == Span::dummy() {
        val.span()
    } else {
        binder.span
    }
}

/// The names and binder infos of surface binders, outermost first.
fn surface_param_names(binders: &[SurfaceBinder]) -> Vec<(Name, BinderInfo)> {
    binders
        .iter()
        .map(|b| {
            (
                b.name.name().clone(),
                crate::infer::convert_binder_info(b.info),
            )
        })
        .collect()
}

/// The names a helper's TYPE gives its own leading parameters, outermost
/// first — Lean binds a named argument by the binder names of the function's
/// type (`ElabAppArgs`). With a written type, its leading `∀` binders (an
/// arrow names nothing); with none, the leading `fun` parameters of the value
/// the type is inferred from. `None` when it names none.
pub(in crate::infer) fn helper_own_params(
    binder: &SurfaceBinder,
    val: &SurfaceExpr,
) -> Option<Vec<(Name, BinderInfo)>> {
    let mut params = Vec::new();
    match binder.ty.as_deref() {
        Some(ty) => {
            let mut cur = ty;
            while let SurfaceExpr::Pi(_, bs, body) = cur {
                params.extend(surface_param_names(bs));
                cur = body;
            }
        }
        None => {
            let mut cur = match val {
                SurfaceExpr::Ascription(_, inner, _) => inner.as_ref(),
                other => other,
            };
            while let SurfaceExpr::Lambda(_, bs, body) = cur {
                params.extend(surface_param_names(bs));
                cur = body;
            }
        }
    }
    (!params.is_empty()).then_some(params)
}

impl ElabCtx<'_> {
    /// The closed form of a helper: [`ascribe_closed`] of its type and value
    /// abstracted over the locals it captures, applied to them, and those
    /// locals (outermost first) with the binder info each gets. `None` when
    /// it cannot be closed.
    pub(super) fn close_let_rec_helper(
        &self,
        helper_ty: &Expr,
        helper_val: &Expr,
    ) -> Option<(Expr, Vec<(FVarId, BinderInfo)>)> {
        let mut ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(helper_ty));
        let mut val = self
            .metas
            .instantiate_levels(&self.metas.instantiate(helper_val));
        for (fvar, use_term) in &self.let_rec_lift.uses {
            ty = ty.subst_fvar(*fvar, use_term);
            val = val.subst_fvar(*fvar, use_term);
        }

        // The captured locals: free variables of the type and value, closed
        // under the types of the locals found (`mkClosureForAux`).
        let position: HashMap<FVarId, usize> = self
            .locals
            .iter()
            .enumerate()
            .map(|(i, (_, fvar, _))| (*fvar, i))
            .collect();
        let mut captured: HashSet<FVarId> = HashSet::new();
        // `ty` and `val` outlive the walk, so the addresses it records are
        // never reused for another node while it runs.
        let mut pending: Vec<FVarId> = Vec::new();
        let mut seen: HashSet<usize> = HashSet::new();
        free_fvars_shared(&ty, &mut pending, &mut seen);
        free_fvars_shared(&val, &mut pending, &mut seen);
        while let Some(fvar) = pending.pop() {
            if MetaState::from_fvar(fvar).is_some() {
                // An unassigned metavariable: the helper is not finished.
                return None;
            }
            if !captured.insert(fvar) {
                continue;
            }
            let index = *position.get(&fvar)?;
            let local_ty = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&self.locals[index].2));
            // A fresh address set: `local_ty` is dropped after this round,
            // and a later one may reuse its addresses.
            free_fvars_shared(&local_ty, &mut pending, &mut HashSet::new());
        }
        // A captured local whose binder info is unknown cannot be given the
        // one Lean's closure gives it, so the helper stays inline.
        if captured
            .iter()
            .any(|fvar| self.let_rec_lift.unknown_binders.contains(fvar))
        {
            return None;
        }
        let mut order: Vec<(usize, FVarId)> = captured
            .iter()
            .map(|fvar| (position[fvar], *fvar))
            .collect();
        order.sort_unstable();

        let mut closed_ty = ty;
        let mut closed_val = val;
        let mut infos: Vec<(FVarId, BinderInfo)> = Vec::with_capacity(order.len());
        for (index, fvar) in order.iter().rev() {
            let local_ty = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&self.locals[*index].2));
            let info = match self.let_rec_lift.binder_infos.get(fvar) {
                Some(info) => *info,
                None if self.auto_implicits.iter().any(|(_, f, _)| f == fvar) => {
                    BinderInfo::Implicit
                }
                None => BinderInfo::Default,
            };
            closed_ty = Expr::pi(info, local_ty.clone(), closed_ty.abstract_fvar(*fvar));
            closed_val = Expr::lam(info, local_ty, closed_val.abstract_fvar(*fvar));
            infos.push((*fvar, info));
        }
        infos.reverse();
        if closed_ty.has_fvar_quick() || closed_val.has_fvar_quick() {
            return None;
        }
        Some((
            Expr::apps(
                ascribe_closed(closed_ty, closed_val),
                order.into_iter().map(|(_, fvar)| Expr::fvar(fvar)),
            ),
            infos,
        ))
    }
}

/// Push the free variables of `e` (metavariables, which are free variables
/// too, included) onto `out`, visiting each shared subterm once — `seen`
/// holds the addresses visited — and no subterm without one.
///
/// A sibling helper's value holds each earlier helper it calls in closed,
/// lifted form, shared rather than copied: as a TREE the value of the `k`-th
/// helper of a chain whose helpers each call the one before twice holds
/// `2^k` copies of the first, though as a DAG it is linear. A walk that
/// visits every path (the tactic layer's `collect_fvars`) took 7.45 s at
/// depth 24 and more than 60 s at depth 32 (release, measured 2026-10-08);
/// the closed parts it walked have no free variable at all.
fn free_fvars_shared(e: &Expr, out: &mut Vec<FVarId>, seen: &mut HashSet<usize>) {
    if !e.has_fvar_quick() || !seen.insert(e as *const Expr as usize) {
        return;
    }
    crate::stack_safe(|| match e.kind() {
        ExprKind::FVar(id) => out.push(*id),
        ExprKind::App(f, a) => {
            free_fvars_shared(f, out, seen);
            free_fvars_shared(a, out, seen);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            free_fvars_shared(ty, out, seen);
            free_fvars_shared(body, out, seen);
        }
        ExprKind::Let(_, ty, value, body, _) => {
            free_fvars_shared(ty, out, seen);
            free_fvars_shared(value, out, seen);
            free_fvars_shared(body, out, seen);
        }
        ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => {
            free_fvars_shared(inner, out, seen);
        }
        // Every other form is walked whole (none occurs in a lifted helper).
        _ => out.extend(crate::tactic::hypothesis::collect_fvars(e)),
    });
}
