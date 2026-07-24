// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ExprFolderOpt: sharing-preserving expression folder.
//!
//! Returns `Option<Expr>` where `None` means "unchanged — reuse existing Arc."
//! Eliminates ~775 lines of duplicated `_opt` traversal boilerplate in `subst.rs`.
//!
//! Design: designs/2026-03-01-1980-expr-folder-opt.md
//! Issue: #1980

use super::stack_safe;
use crate::expr::{ek, Expr, ExprKind, FVarId, LevelVec, Literal, ZFCSetExpr};
use crate::level::Level;
use crate::name::Name;
use std::sync::Arc;

/// Merge 2 optional children. Returns None when both unchanged.
fn merge2(
    old_a: &Arc<Expr>,
    old_b: &Arc<Expr>,
    new_a: Option<Expr>,
    new_b: Option<Expr>,
    make: impl FnOnce(Arc<Expr>, Arc<Expr>) -> ExprKind,
) -> Option<Expr> {
    match (&new_a, &new_b) {
        (None, None) => None,
        _ => Some(ek(make(
            new_a.map_or_else(|| old_a.clone(), Arc::new),
            new_b.map_or_else(|| old_b.clone(), Arc::new),
        ))),
    }
}

/// Merge 3 optional children. Returns None when all unchanged.
fn merge3(
    old_a: &Arc<Expr>,
    old_b: &Arc<Expr>,
    old_c: &Arc<Expr>,
    new_a: Option<Expr>,
    new_b: Option<Expr>,
    new_c: Option<Expr>,
    make: impl FnOnce(Arc<Expr>, Arc<Expr>, Arc<Expr>) -> ExprKind,
) -> Option<Expr> {
    match (&new_a, &new_b, &new_c) {
        (None, None, None) => None,
        _ => Some(ek(make(
            new_a.map_or_else(|| old_a.clone(), Arc::new),
            new_b.map_or_else(|| old_b.clone(), Arc::new),
            new_c.map_or_else(|| old_c.clone(), Arc::new),
        ))),
    }
}

/// Merge 4 optional children. Returns None when all unchanged.
///
/// 9 parameters is necessary: 4 old refs, 4 new options, 1 constructor.
/// Splitting into a struct would add indirection for no benefit since this
/// is only called from the CubicalHComp arm.
fn merge4(
    old_a: &Arc<Expr>,
    old_b: &Arc<Expr>,
    old_c: &Arc<Expr>,
    old_d: &Arc<Expr>,
    new_a: Option<Expr>,
    new_b: Option<Expr>,
    new_c: Option<Expr>,
    new_d: Option<Expr>,
    make: impl FnOnce(Arc<Expr>, Arc<Expr>, Arc<Expr>, Arc<Expr>) -> ExprKind,
) -> Option<Expr> {
    match (&new_a, &new_b, &new_c, &new_d) {
        (None, None, None, None) => None,
        _ => Some(ek(make(
            new_a.map_or_else(|| old_a.clone(), Arc::new),
            new_b.map_or_else(|| old_b.clone(), Arc::new),
            new_c.map_or_else(|| old_c.clone(), Arc::new),
            new_d.map_or_else(|| old_d.clone(), Arc::new),
        ))),
    }
}

/// Sharing-preserving expression folder.
///
/// Returns `Option<Expr>` where `None` means "unchanged — reuse existing Arc."
/// This avoids allocating new nodes when subtrees are unmodified, which is
/// critical for kernel hot-path operations like `instantiate` and `lift`.
///
/// Lean 4 equivalent: the `replace_fn` pattern in `instantiate.cpp`.
///
/// # Performance contract
///
/// - `should_descend` is called once per node. Returning `false` avoids
///   traversing the entire subtree. Use for O(1) metadata guards
///   (e.g., `loose_bvar_range()` check).
/// - When all children return `None`, the parent returns `None` — zero
///   allocations for unchanged subtrees.
/// - Arc sharing is preserved: unchanged children keep their original Arc.
pub trait ExprFolderOpt {
    /// O(1) metadata guard. If false, `fold_expr_opt` returns `None` without
    /// examining children. Default: always descend.
    fn should_descend(&self, _expr: &Expr) -> bool {
        true
    }

    fn fold_bvar_opt(&mut self, _idx: u32) -> Option<Expr> {
        None
    }
    fn fold_fvar_opt(&mut self, _id: FVarId) -> Option<Expr> {
        None
    }
    fn fold_sort_opt(&mut self, _level: &Level) -> Option<Expr> {
        None
    }
    fn fold_const_opt(&mut self, _name: &Name, _levels: &LevelVec) -> Option<Expr> {
        None
    }
    fn fold_lit_opt(&mut self, _lit: &Literal) -> Option<Expr> {
        None
    }

    /// Called when recursing into a binder body (Lam, Pi, Let, CubicalPathLam,
    /// ZFCComprehension pred, ZFCSetExpr::Separation pred,
    /// ZFCSetExpr::Replacement func).
    ///
    /// Override to adjust depth counters before/after the recursive call.
    /// Default delegates to `fold_expr_opt`.
    fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
        self.fold_expr_opt(expr)
    }

    /// Main dispatch — rarely overridden.
    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if !self.should_descend(expr) {
            return None;
        }
        stack_safe(|| self.fold_expr_opt_inner(expr))
    }

    /// Inner dispatch called within stack_safe.
    ///
    /// Under Kani, only handles the core ExprKind variants constructed in
    /// harnesses. Under production, delegates to `fold_expr_opt_inner_full`.
    fn fold_expr_opt_inner(&mut self, expr: &Expr) -> Option<Expr> {
        #[cfg(kani)]
        {
            self.fold_expr_opt_inner_core(expr)
        }
        #[cfg(not(kani))]
        {
            self.fold_expr_opt_inner_full(expr)
        }
    }

    /// Kani-only: handles 7 core ExprKind variants used in harnesses.
    /// Eliminates recursive fold calls for Let/MData/Proj/Squash/Cubical/ZFC,
    /// reducing CBMC per-node branching from 20+ to 7.
    #[cfg(kani)]
    fn fold_expr_opt_inner_core(&mut self, expr: &Expr) -> Option<Expr> {
        match expr.kind() {
            ExprKind::BVar(idx) => self.fold_bvar_opt(*idx),
            ExprKind::FVar(id) => self.fold_fvar_opt(*id),
            ExprKind::Sort(level) => self.fold_sort_opt(level),
            ExprKind::Const(name, levels) => self.fold_const_opt(name, levels),
            ExprKind::Lit(lit) => self.fold_lit_opt(lit),
            ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => None,
            ExprKind::App(f, a) => {
                let nf = self.fold_expr_opt(f);
                let na = self.fold_expr_opt(a);
                merge2(f, a, nf, na, ExprKind::App)
            }
            ExprKind::Lam(bi, ty, body) => {
                let nty = self.fold_expr_opt(ty);
                let nbody = self.fold_binder_body_opt(body);
                merge2(ty, body, nty, nbody, |t, b| ExprKind::Lam(*bi, t, b))
            }
            ExprKind::Pi(bi, ty, body) => {
                let nty = self.fold_expr_opt(ty);
                let nbody = self.fold_binder_body_opt(body);
                merge2(ty, body, nty, nbody, |t, b| ExprKind::Pi(*bi, t, b))
            }
            _ => unreachable!("Kani harnesses only construct BVar/FVar/Sort/Const/Lit/App/Lam/Pi"),
        }
    }

    /// Production: full dispatch over all ExprKind variants.
    #[cfg(not(kani))]
    fn fold_expr_opt_inner_full(&mut self, expr: &Expr) -> Option<Expr> {
        match expr.kind() {
            ExprKind::BVar(idx) => self.fold_bvar_opt(*idx),
            ExprKind::FVar(id) => self.fold_fvar_opt(*id),
            ExprKind::Sort(level) => self.fold_sort_opt(level),
            ExprKind::Const(name, levels) => self.fold_const_opt(name, levels),
            ExprKind::Lit(lit) => self.fold_lit_opt(lit),
            ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => None,

            ExprKind::App(f, a) => {
                let nf = self.fold_expr_opt(f);
                let na = self.fold_expr_opt(a);
                merge2(f, a, nf, na, ExprKind::App)
            }
            ExprKind::Lam(bi, ty, body) => {
                let nty = self.fold_expr_opt(ty);
                let nbody = self.fold_binder_body_opt(body);
                merge2(ty, body, nty, nbody, |t, b| ExprKind::Lam(*bi, t, b))
            }
            ExprKind::Pi(bi, ty, body) => {
                let nty = self.fold_expr_opt(ty);
                let nbody = self.fold_binder_body_opt(body);
                merge2(ty, body, nty, nbody, |t, b| ExprKind::Pi(*bi, t, b))
            }
            ExprKind::Let(name, ty, val, body, non_dep) => {
                let nty = self.fold_expr_opt(ty);
                let nv = self.fold_expr_opt(val);
                let nbody = self.fold_binder_body_opt(body);
                merge3(ty, val, body, nty, nv, nbody, |t, v, b| {
                    ExprKind::Let(name.clone(), t, v, b, *non_dep)
                })
            }

            ExprKind::Proj(name, idx, inner) => self
                .fold_expr_opt(inner)
                .map(|ni| ek(ExprKind::Proj(name.clone(), *idx, Arc::new(ni)))),
            ExprKind::MData(meta, inner) => self
                .fold_expr_opt(inner)
                .map(|ni| ek(ExprKind::MData(meta.clone(), Arc::new(ni)))),
            ExprKind::Squash(inner) => self
                .fold_expr_opt(inner)
                .map(|ni| ek(ExprKind::Squash(Arc::new(ni)))),

            // Cubical extensions — delegated to separate method for function size
            ExprKind::CubicalPath { .. }
            | ExprKind::CubicalPathLam { .. }
            | ExprKind::CubicalPathApp { .. }
            | ExprKind::CubicalHComp { .. }
            | ExprKind::CubicalTransp { .. }
            | ExprKind::CubicalCoe { .. }
            // ZFC extensions
            | ExprKind::ZFCSet(_)
            | ExprKind::ZFCMem { .. }
            | ExprKind::ZFCComprehension { .. } => self.fold_expr_opt_extensions(expr),
        }
    }

    /// Cubical extension variants. Separated from fold_expr_opt_inner
    /// to stay under the function size limit.
    fn fold_expr_opt_extensions(&mut self, expr: &Expr) -> Option<Expr> {
        match expr.kind() {
            ExprKind::CubicalPath { ty, left, right } => {
                let nty = self.fold_expr_opt(ty);
                let nl = self.fold_expr_opt(left);
                let nr = self.fold_expr_opt(right);
                merge3(ty, left, right, nty, nl, nr, |t, l, r| {
                    ExprKind::CubicalPath {
                        ty: t,
                        left: l,
                        right: r,
                    }
                })
            }
            ExprKind::CubicalPathLam { body } => self
                .fold_binder_body_opt(body)
                .map(|nb| ek(ExprKind::CubicalPathLam { body: Arc::new(nb) })),
            ExprKind::CubicalPathApp { path, arg } => {
                let np = self.fold_expr_opt(path);
                let na = self.fold_expr_opt(arg);
                merge2(path, arg, np, na, |p, a| ExprKind::CubicalPathApp {
                    path: p,
                    arg: a,
                })
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                let nty = self.fold_expr_opt(ty);
                let nphi = self.fold_expr_opt(phi);
                let nu = self.fold_expr_opt(u);
                let nb = self.fold_expr_opt(base);
                merge4(ty, phi, u, base, nty, nphi, nu, nb, |t, p, u, b| {
                    ExprKind::CubicalHComp {
                        ty: t,
                        phi: p,
                        u,
                        base: b,
                    }
                })
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                let nty = self.fold_expr_opt(ty);
                let nphi = self.fold_expr_opt(phi);
                let nb = self.fold_expr_opt(base);
                merge3(ty, phi, base, nty, nphi, nb, |t, p, b| {
                    ExprKind::CubicalTransp {
                        ty: t,
                        phi: p,
                        base: b,
                    }
                })
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                let nty = self.fold_expr_opt(ty);
                let nr = self.fold_expr_opt(r);
                let ns = self.fold_expr_opt(s);
                let nb = self.fold_expr_opt(base);
                merge4(ty, r, s, base, nty, nr, ns, nb, |t, r, s, b| {
                    ExprKind::CubicalCoe {
                        ty: t,
                        r,
                        s,
                        base: b,
                    }
                })
            }
            // ZFC variants — explicit delegation (no wildcard per P1-705)
            ExprKind::ZFCSet(_) | ExprKind::ZFCMem { .. } | ExprKind::ZFCComprehension { .. } => {
                self.fold_expr_opt_zfc(expr)
            }
            _ => unreachable!("fold_expr_opt_extensions: only Cubical/ZFC variants expected"),
        }
    }

    /// ZFC extension variants. Only reachable from fold_expr_opt_extensions.
    /// Exhaustive variant checking lives in fold_expr_opt_inner.
    fn fold_expr_opt_zfc(&mut self, expr: &Expr) -> Option<Expr> {
        match expr.kind() {
            ExprKind::ZFCSet(set_expr) => self
                .fold_zfc_set_expr_opt(set_expr)
                .map(|ns| ek(ExprKind::ZFCSet(ns))),
            ExprKind::ZFCMem { element, set } => {
                let ne = self.fold_expr_opt(element);
                let ns = self.fold_expr_opt(set);
                merge2(element, set, ne, ns, |e, s| ExprKind::ZFCMem {
                    element: e,
                    set: s,
                })
            }
            ExprKind::ZFCComprehension { domain, pred } => {
                let nd = self.fold_expr_opt(domain);
                let np = self.fold_binder_body_opt(pred);
                merge2(domain, pred, nd, np, |d, p| ExprKind::ZFCComprehension {
                    domain: d,
                    pred: p,
                })
            }
            _ => unreachable!("fold_expr_opt_zfc: only ZFC variants expected"),
        }
    }

    /// Fold over a ZFC set expression. Default recurses into child Exprs.
    /// Returns None when all children unchanged.
    fn fold_zfc_set_expr_opt(&mut self, set_expr: &ZFCSetExpr) -> Option<ZFCSetExpr> {
        match set_expr {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => None,
            ZFCSetExpr::Singleton(e) => self
                .fold_expr_opt(e)
                .map(|ne| ZFCSetExpr::Singleton(Arc::new(ne))),
            ZFCSetExpr::Pair(a, b) => {
                let na = self.fold_expr_opt(a);
                let nb = self.fold_expr_opt(b);
                match (&na, &nb) {
                    (None, None) => None,
                    _ => Some(ZFCSetExpr::Pair(
                        na.map_or_else(|| a.clone(), Arc::new),
                        nb.map_or_else(|| b.clone(), Arc::new),
                    )),
                }
            }
            ZFCSetExpr::Union(e) => self
                .fold_expr_opt(e)
                .map(|ne| ZFCSetExpr::Union(Arc::new(ne))),
            ZFCSetExpr::PowerSet(e) => self
                .fold_expr_opt(e)
                .map(|ne| ZFCSetExpr::PowerSet(Arc::new(ne))),
            ZFCSetExpr::Separation { set, pred } => {
                let ns = self.fold_expr_opt(set);
                let np = self.fold_binder_body_opt(pred);
                match (&ns, &np) {
                    (None, None) => None,
                    _ => Some(ZFCSetExpr::Separation {
                        set: ns.map_or_else(|| set.clone(), Arc::new),
                        pred: np.map_or_else(|| pred.clone(), Arc::new),
                    }),
                }
            }
            ZFCSetExpr::Replacement { set, func } => {
                let ns = self.fold_expr_opt(set);
                let nf = self.fold_binder_body_opt(func);
                match (&ns, &nf) {
                    (None, None) => None,
                    _ => Some(ZFCSetExpr::Replacement {
                        set: ns.map_or_else(|| set.clone(), Arc::new),
                        func: nf.map_or_else(|| func.clone(), Arc::new),
                    }),
                }
            }
            ZFCSetExpr::Choice(e) => self
                .fold_expr_opt(e)
                .map(|ne| ZFCSetExpr::Choice(Arc::new(ne))),
        }
    }
}
