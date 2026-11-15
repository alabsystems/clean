// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Drop the section `variable`s a declaration did not use, from its
//! ELABORATED type and value.
//!
//! When the surface scan of [`crate::section_var_selection`] cannot see every
//! identifier of a declaration (a `by` block, a `do` block, a quotation …),
//! the declaration is elaborated with EVERY section variable prepended — the
//! context Lean elaborates a definition in — and this module then applies
//! Lean's own rule to the result. The same request is armed, over a superset
//! of Lean's choice rather than every variable, for a theorem whose header
//! scans but whose instance rule the surface cannot decide (an `outParam` the
//! header fills through a section instance —
//! `section_var_selection::header_selection`), and for a definition whose scan
//! is complete but activated an instance variable it does not name
//! (`section_var_selection::used_selection`):
//!
//! * for a `def` / `abbrev` / `instance`, `Meta.removeUnused`
//!   (`Lean/Meta/CollectFVars.lean:53`, reached from `withUsed` /
//!   `removeUnusedVars` in `Lean/Elab/MutualDef.lean:593-609`): a variable is
//!   kept exactly when the elaborated header or value mentions it, or the type
//!   of a kept variable does;
//! * for a `theorem` whose HEADER could not be scanned or decided,
//!   `withHeaderSecVars` (`MutualDef.lean:454-490`) over the elaborated type:
//!   header occurrences, `include`d variables, their dependencies, then
//!   instance-implicits whose type mentions only kept variables. A variable
//!   the proof uses is never dropped: Lean would have refused such a proof,
//!   and dropping the binder here would leave a dangling bound variable.
//!
//! Measured motivation (2026-09-12, Mathlib source): `abbrev
//! Function.Injective.preorder` has a `by` field, so it was registered with the
//! unused `ι` and `π` of `Order/Basic.lean`'s `variable {ι α β : Type*}
//! {π : ι → Type*}`, and every use of it (`Function.Injective.partialOrder`)
//! left `unsolved metavariables ?[22, 25]`.
//!
//! The pruning is SELF-VERIFYING: a binder is removed only when nothing left
//! under it still refers to it (`has_loose_bvar(0)`), so the result is always a
//! closed, well-scoped term — and the kernel re-checks the declaration as
//! registered.

use clean_kernel::{BinderData, BinderInfo, Expr, ExprKind, Level, Name};
use clean_parser::SurfaceName;

use super::ElabCtx;

/// Which Lean rule decides what survives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PruneRule {
    /// `def` / `abbrev` / `instance`: Lean's `removeUnused`.
    Used,
    /// A `theorem`: Lean's `withHeaderSecVars`.
    Header {
        /// Per prepended section variable: named by an `include`.
        forced: Vec<bool>,
    },
}

/// A request to prune the leading section binders of one declaration's
/// elaborated telescope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SectionPruneRequest {
    /// The names of the prepended section binders, in order — the prefix the
    /// declaration's surface binders must start with. A telescope whose
    /// binders do not start with these names is not the one the request was
    /// made for, and is left alone.
    pub(crate) section_names: Vec<SurfaceName>,
    /// The rule to apply.
    pub(crate) rule: PruneRule,
}

/// What a pruning did: the declaration it ran on and, per prepended section
/// binder, whether it was kept.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SectionPruneOutcome {
    /// The (qualified) name of the declaration whose telescope was pruned.
    pub(crate) decl: Name,
    /// Per prepended section binder, in order: kept.
    pub(crate) kept: Vec<bool>,
}

/// Peel `n` leading binders — `Π` when `pi`, else `λ`: `(binder, domain)` per
/// binder, then the body under all of them. `None` when there are fewer.
fn peel(expr: &Expr, n: usize, pi: bool) -> Option<(Vec<(BinderData, Expr)>, Expr)> {
    let mut binders = Vec::with_capacity(n);
    let mut cur = expr.clone();
    for _ in 0..n {
        let next = match (cur.kind(), pi) {
            (ExprKind::Pi(bd, dom, body), true) | (ExprKind::Lam(bd, dom, body), false) => {
                binders.push((*bd, (**dom).clone()));
                (**body).clone()
            }
            _ => return None,
        };
        cur = next;
    }
    Some((binders, cur))
}

/// Re-wrap `body` in `binders` (outermost first).
fn wrap(binders: &[(BinderData, Expr)], body: Expr, pi: bool) -> Expr {
    binders.iter().rev().fold(body, |acc, (bd, dom)| {
        if pi {
            Expr::pi(*bd, dom.clone(), acc)
        } else {
            Expr::lam(*bd, dom.clone(), acc)
        }
    })
}

/// Does section binder `owner`'s domain mention section binder `target`?
/// `doms[owner]` sits under binders `0..owner`, where binder `target` is
/// `BVar(owner - 1 - target)`.
fn domain_mentions(doms: &[(BinderData, Expr)], owner: usize, target: usize) -> bool {
    target < owner
        && u32::try_from(owner - 1 - target).is_ok_and(|idx| doms[owner].1.has_loose_bvar(idx))
}

/// The section binders `withHeaderSecVars` keeps, read off the elaborated
/// type: `doms[i]` is section binder `i`'s domain and `rest` everything under
/// all `doms.len()` of them, where binder `j` is `BVar(len - 1 - j)`.
fn header_keep(doms: &[(BinderData, Expr)], rest: &Expr, forced: &[bool]) -> Vec<bool> {
    let k = doms.len();
    let mut keep: Vec<bool> = (0..k)
        .map(|j| {
            forced.get(j).copied().unwrap_or(false)
                || u32::try_from(k - 1 - j).is_ok_and(|idx| rest.has_loose_bvar(idx))
        })
        .collect();
    // Dependency closure (`addDependencies`): a domain mentions only binders
    // to its left, so one right-to-left sweep reaches the fixpoint.
    for i in (0..k).rev() {
        if keep[i] {
            for (j, kept) in keep.iter_mut().enumerate().take(i) {
                if domain_mentions(doms, i, j) {
                    *kept = true;
                }
            }
        }
    }
    // Instance-implicits whose type mentions only kept variables, in
    // declaration order (`MutualDef.lean:479-486`; `.all` holds vacuously for
    // a type that mentions none).
    for i in 0..k {
        if !keep[i]
            && doms[i].0.info == BinderInfo::InstImplicit
            && (0..i).all(|j| keep[j] || !domain_mentions(doms, i, j))
        {
            keep[i] = true;
        }
    }
    keep
}

/// Prune section binders `offset .. offset + k` of an elaborated declaration's
/// type (`Π`-telescope) and value (`λ`-telescope) by `rule`, keeping the
/// `offset` binders outside them (the autos belonging to the captured
/// section context) untouched. Returns the pruned pair and, per section binder,
/// whether it was kept.
///
/// `None` — keep everything — when either term does not start with
/// `offset + k` binders of the expected shape, or still carries a free
/// variable or metavariable, whose eventual solution the pruning cannot see.
pub(crate) fn prune_section_binders(
    ty: &Expr,
    val: &Expr,
    offset: usize,
    k: usize,
    rule: &PruneRule,
) -> Option<(Expr, Expr, Vec<bool>)> {
    if k == 0 || ty.has_fvar_quick() || val.has_fvar_quick() {
        return None;
    }
    let (ty_outer, ty_inner) = peel(ty, offset, true)?;
    let (val_outer, val_inner) = peel(val, offset, false)?;
    let (ty_doms, ty_rest) = peel(&ty_inner, k, true)?;
    let (val_doms, val_rest) = peel(&val_inner, k, false)?;
    let marked = match rule {
        PruneRule::Used => vec![false; k],
        PruneRule::Header { forced } => header_keep(&ty_doms, &ty_rest, forced),
    };
    // Rebuild inside-out: at step `j`, `cur_ty`/`cur_val` are everything
    // under section binder `j`, where `BVar(0)` is binder `j` itself.
    let placeholder = Expr::sort(Level::Zero);
    let mut cur_ty = ty_rest;
    let mut cur_val = val_rest;
    let mut kept = vec![false; k];
    for j in (0..k).rev() {
        if marked[j] || cur_ty.has_loose_bvar(0) || cur_val.has_loose_bvar(0) {
            kept[j] = true;
            cur_ty = Expr::pi(ty_doms[j].0, ty_doms[j].1.clone(), cur_ty);
            cur_val = Expr::lam(val_doms[j].0, val_doms[j].1.clone(), cur_val);
        } else {
            // Nothing under binder `j` mentions it: instantiating its variable
            // inserts nothing and only renumbers the variables bound outside it.
            cur_ty = cur_ty.instantiate(&placeholder);
            cur_val = cur_val.instantiate(&placeholder);
        }
    }
    Some((
        wrap(&ty_outer, cur_ty, true),
        wrap(&val_outer, cur_val, false),
        kept,
    ))
}

/// Type-only counterpart: an axiom has no value that can retain a section
/// local. Every removed binder is unused in the final type below it.
fn prune_section_type(
    ty: &Expr,
    offset: usize,
    k: usize,
    rule: &PruneRule,
) -> Option<(Expr, Vec<bool>)> {
    if k == 0 || ty.has_fvar_quick() {
        return None;
    }
    let (outer, inner) = peel(ty, offset, true)?;
    let (domains, mut body) = peel(&inner, k, true)?;
    let marked = match rule {
        PruneRule::Used => vec![false; k],
        PruneRule::Header { forced } => header_keep(&domains, &body, forced),
    };
    let mut kept = vec![false; k];
    for j in (0..k).rev() {
        if marked[j] || body.has_loose_bvar(0) {
            kept[j] = true;
            body = Expr::pi(domains[j].0, domains[j].1.clone(), body);
        } else {
            body = body.instantiate(&Expr::prop());
        }
    }
    Some((wrap(&outer, body, true), kept))
}

impl ElabCtx<'_> {
    /// Arm the pruning of the next telescope whose surface binders start with
    /// `request.section_names` (see the module doc).
    pub(crate) fn set_section_prune_request(&mut self, request: SectionPruneRequest) {
        self.section_prune = Some(request);
        self.section_prune_outcome = None;
    }

    /// What the armed pruning did, if it ran; disarms it either way.
    pub(crate) fn take_section_prune_outcome(&mut self) -> Option<SectionPruneOutcome> {
        self.section_prune = None;
        self.section_prune_outcome.take()
    }

    /// An axiom closes only its type; the used-variable rule reads no value.
    pub(super) fn prune_armed_section_type<'n>(
        &mut self,
        decl: &Name,
        binder_names: impl IntoIterator<Item = &'n SurfaceName>,
        offset: usize,
        ty: Expr,
    ) -> Expr {
        let names: Vec<_> = binder_names.into_iter().collect();
        if !self.section_prune.as_ref().is_some_and(|request| {
            names.len() >= request.section_names.len()
                && request
                    .section_names
                    .iter()
                    .zip(&names)
                    .all(|(a, b)| a == *b)
        }) {
            return ty;
        }
        let Some(request) = self.section_prune.take() else {
            return ty;
        };
        match prune_section_type(&ty, offset, request.section_names.len(), &request.rule) {
            Some((ty, kept)) => {
                self.section_prune_outcome = Some(SectionPruneOutcome {
                    decl: decl.clone(),
                    kept,
                });
                ty
            }
            None => ty,
        }
    }

    /// Apply the armed pruning to declaration `decl`, whose elaborated `ty` /
    /// `val` telescope is `offset` auto-bound implicits followed by the
    /// binders named `binder_names`. A telescope that does not start with the
    /// requested section binders is returned unchanged and leaves the request
    /// armed.
    pub(super) fn prune_armed_section_binders<'n>(
        &mut self,
        decl: &Name,
        binder_names: impl IntoIterator<Item = &'n SurfaceName>,
        offset: usize,
        ty: Expr,
        val: Expr,
    ) -> (Expr, Expr) {
        let names: Vec<&SurfaceName> = binder_names.into_iter().collect();
        let for_this_telescope = self.section_prune.as_ref().is_some_and(|request| {
            names.len() >= request.section_names.len()
                && request
                    .section_names
                    .iter()
                    .zip(&names)
                    .all(|(want, have)| want == *have)
        });
        if !for_this_telescope {
            return (ty, val);
        }
        let Some(request) = self.section_prune.take() else {
            return (ty, val);
        };
        // A value that still names its own constant (a recursive call the
        // elaborator left as a constant) applies it at the UNPRUNED telescope;
        // pruning would make that call ill-typed, so keep everything.
        if val.collect_constants().contains(decl) || ty.collect_constants().contains(decl) {
            return (ty, val);
        }
        let k = request.section_names.len();
        match prune_section_binders(&ty, &val, offset, k, &request.rule) {
            Some((pruned_ty, pruned_val, kept)) => {
                // A universe parameter only a dropped binder mentioned leaves
                // the registered level list with it: every declaration kind
                // closes through `finalize_level_params`, which keeps only the
                // parameters that occur in the final terms.
                self.section_prune_outcome = Some(SectionPruneOutcome {
                    decl: decl.clone(),
                    kept,
                });
                (pruned_ty, pruned_val)
            }
            None => (ty, val),
        }
    }
}

#[cfg(test)]
#[path = "section_prune_tests.rs"]
mod tests;
