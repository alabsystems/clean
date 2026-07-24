// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ExprFolder, ExprVisitor, and ExprFolderOpt traits for eliminating duplicated traversals.
//!
//! 17 files across the codebase independently implement full `match expr.kind()`
//! traversals over all ExprKind variants. These traits factor out the structural
//! recursion so implementors only override leaf-level behavior.
//!
//! - `ExprFolder`: transforms an Expr tree (returns a new Expr)
//! - `ExprVisitor`: queries an Expr tree (returns an accumulated result)
//! - `ExprFolderOpt`: sharing-preserving folder (returns `Option<Expr>`, `None` = unchanged)
//!
//! Design: designs/2026-02-27-expr-visitor-trait.md (Phase 1+2)
//!         designs/2026-03-01-1980-expr-folder-opt.md (Phase 3)
//! Issues: #1824, #1980

use super::stack_safe;
use crate::expr::{BinderData, Expr, ExprKind, FVarId, LevelVec, Literal, MDataMap, ZFCSetExpr};
use crate::level::Level;
use crate::name::Name;
use std::sync::Arc;

/// Transform an Expr tree bottom-up.
///
/// Override leaf methods to customize behavior; the default `fold_expr`
/// implementation handles structural recursion over all ExprKind variants
/// (including Cubical and ZFC extensions).
///
/// # Example
///
/// ```text
/// struct IdentityFolder;
/// impl ExprFolder for IdentityFolder {}
/// // fold_expr returns the input unchanged
/// ```
pub trait ExprFolder {
    // ════════════════════════════════════════════════════════════════════
    // Leaf methods — override these for custom behavior
    // ════════════════════════════════════════════════════════════════════

    fn fold_bvar(&mut self, idx: u32) -> Expr {
        Expr::bvar(idx)
    }

    fn fold_fvar(&mut self, id: FVarId) -> Expr {
        Expr::fvar(id)
    }

    fn fold_sort(&mut self, level: &Level) -> Expr {
        Expr::sort(level.clone())
    }

    fn fold_const(&mut self, name: &Name, levels: &LevelVec) -> Expr {
        Expr::const_(name.clone(), levels.clone())
    }

    fn fold_lit(&mut self, lit: &Literal) -> Expr {
        Expr::from_kind(ExprKind::Lit(lit.clone()))
    }

    fn fold_sprop(&mut self) -> Expr {
        Expr::from_kind(ExprKind::SProp)
    }

    fn fold_cubical_interval(&mut self) -> Expr {
        Expr::from_kind(ExprKind::CubicalInterval)
    }

    fn fold_cubical_i0(&mut self) -> Expr {
        Expr::from_kind(ExprKind::CubicalI0)
    }

    fn fold_cubical_i1(&mut self) -> Expr {
        Expr::from_kind(ExprKind::CubicalI1)
    }

    // ════════════════════════════════════════════════════════════════════
    // Structural methods — override to intercept specific node types
    // ════════════════════════════════════════════════════════════════════

    fn fold_app(&mut self, f: &Expr, a: &Expr) -> Expr {
        Expr::app(self.fold_expr(f), self.fold_expr(a))
    }

    fn fold_lam(&mut self, bd: BinderData, ty: &Expr, body: &Expr) -> Expr {
        Expr::lam(bd, self.fold_expr(ty), self.fold_binder_body(body))
    }

    fn fold_pi(&mut self, bd: BinderData, ty: &Expr, body: &Expr) -> Expr {
        Expr::pi(bd, self.fold_expr(ty), self.fold_binder_body(body))
    }

    fn fold_let(&mut self, name: &Name, ty: &Expr, val: &Expr, body: &Expr, non_dep: bool) -> Expr {
        Expr::let_named(
            name.clone(),
            self.fold_expr(ty),
            self.fold_expr(val),
            self.fold_binder_body(body),
            non_dep,
        )
    }

    fn fold_proj(&mut self, struct_name: &Name, idx: u32, inner: &Expr) -> Expr {
        Expr::proj(struct_name.clone(), idx, self.fold_expr(inner))
    }

    fn fold_mdata(&mut self, metadata: &MDataMap, inner: &Expr) -> Expr {
        Expr::mdata(metadata.clone(), self.fold_expr(inner))
    }

    /// Called when recursing into a binder body (Lam, Pi, Let, CubicalPathLam,
    /// ZFCComprehension pred, ZFCSetExpr::Separation pred, ZFCSetExpr::Replacement func).
    /// Override to track binder depth. Default delegates to fold_expr.
    fn fold_binder_body(&mut self, expr: &Expr) -> Expr {
        self.fold_expr(expr)
    }

    // ════════════════════════════════════════════════════════════════════
    // Main dispatch — rarely overridden
    // ════════════════════════════════════════════════════════════════════

    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        stack_safe(|| match expr.kind() {
            ExprKind::BVar(idx) => self.fold_bvar(*idx),
            ExprKind::FVar(id) => self.fold_fvar(*id),
            ExprKind::Sort(level) => self.fold_sort(level),
            ExprKind::Const(name, levels) => self.fold_const(name, levels),
            ExprKind::Lit(lit) => self.fold_lit(lit),
            ExprKind::SProp => self.fold_sprop(),
            ExprKind::CubicalInterval => self.fold_cubical_interval(),
            ExprKind::CubicalI0 => self.fold_cubical_i0(),
            ExprKind::CubicalI1 => self.fold_cubical_i1(),
            ExprKind::App(f, a) => self.fold_app(f, a),
            ExprKind::Lam(bd, ty, body) => self.fold_lam(*bd, ty, body),
            ExprKind::Pi(bd, ty, body) => self.fold_pi(*bd, ty, body),
            ExprKind::Let(name, ty, val, body, non_dep) => {
                self.fold_let(name, ty, val, body, *non_dep)
            }
            ExprKind::Proj(name, idx, inner) => self.fold_proj(name, *idx, inner),
            ExprKind::MData(metadata, inner) => self.fold_mdata(metadata, inner),
            ExprKind::Squash(inner) => {
                Expr::from_kind(ExprKind::Squash(Arc::new(self.fold_expr(inner))))
            }
            ExprKind::CubicalPath { ty, left, right } => Expr::from_kind(ExprKind::CubicalPath {
                ty: Arc::new(self.fold_expr(ty)),
                left: Arc::new(self.fold_expr(left)),
                right: Arc::new(self.fold_expr(right)),
            }),
            ExprKind::CubicalPathLam { body } => Expr::from_kind(ExprKind::CubicalPathLam {
                body: Arc::new(self.fold_binder_body(body)),
            }),
            ExprKind::CubicalPathApp { path, arg } => Expr::from_kind(ExprKind::CubicalPathApp {
                path: Arc::new(self.fold_expr(path)),
                arg: Arc::new(self.fold_expr(arg)),
            }),
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                Expr::from_kind(ExprKind::CubicalHComp {
                    ty: Arc::new(self.fold_expr(ty)),
                    phi: Arc::new(self.fold_expr(phi)),
                    u: Arc::new(self.fold_expr(u)),
                    base: Arc::new(self.fold_expr(base)),
                })
            }
            ExprKind::CubicalTransp { ty, phi, base } => Expr::from_kind(ExprKind::CubicalTransp {
                ty: Arc::new(self.fold_expr(ty)),
                phi: Arc::new(self.fold_expr(phi)),
                base: Arc::new(self.fold_expr(base)),
            }),
            ExprKind::CubicalCoe { ty, r, s, base } => Expr::from_kind(ExprKind::CubicalCoe {
                ty: Arc::new(self.fold_expr(ty)),
                r: Arc::new(self.fold_expr(r)),
                s: Arc::new(self.fold_expr(s)),
                base: Arc::new(self.fold_expr(base)),
            }),
            ExprKind::ZFCSet(set_expr) => {
                Expr::from_kind(ExprKind::ZFCSet(self.fold_zfc_set_expr(set_expr)))
            }
            ExprKind::ZFCMem { element, set } => Expr::from_kind(ExprKind::ZFCMem {
                element: Arc::new(self.fold_expr(element)),
                set: Arc::new(self.fold_expr(set)),
            }),
            ExprKind::ZFCComprehension { domain, pred } => {
                Expr::from_kind(ExprKind::ZFCComprehension {
                    domain: Arc::new(self.fold_expr(domain)),
                    pred: Arc::new(self.fold_binder_body(pred)),
                })
            }
        })
    }

    /// Fold over a ZFC set expression. Default recurses into child Exprs.
    fn fold_zfc_set_expr(&mut self, set_expr: &ZFCSetExpr) -> ZFCSetExpr {
        match set_expr {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => set_expr.clone(),
            ZFCSetExpr::Singleton(e) => ZFCSetExpr::Singleton(Arc::new(self.fold_expr(e))),
            ZFCSetExpr::Pair(a, b) => {
                ZFCSetExpr::Pair(Arc::new(self.fold_expr(a)), Arc::new(self.fold_expr(b)))
            }
            ZFCSetExpr::Union(e) => ZFCSetExpr::Union(Arc::new(self.fold_expr(e))),
            ZFCSetExpr::PowerSet(e) => ZFCSetExpr::PowerSet(Arc::new(self.fold_expr(e))),
            ZFCSetExpr::Separation { set, pred } => ZFCSetExpr::Separation {
                set: Arc::new(self.fold_expr(set)),
                pred: Arc::new(self.fold_binder_body(pred)),
            },
            ZFCSetExpr::Replacement { set, func } => ZFCSetExpr::Replacement {
                set: Arc::new(self.fold_expr(set)),
                func: Arc::new(self.fold_binder_body(func)),
            },
            ZFCSetExpr::Choice(e) => ZFCSetExpr::Choice(Arc::new(self.fold_expr(e))),
        }
    }
}

/// Query an Expr tree without transformation.
///
/// `Result` is the accumulated query result. `combine` merges results from
/// child nodes. Override leaf methods to inject values at specific node types.
///
/// # Example
///
/// ```text
/// struct FreeVarCollector { fvars: Vec<FVarId> }
/// impl ExprVisitor for FreeVarCollector {
///     type Result = ();
///     fn combine(&self, _a: (), _b: ()) {}
///     fn visit_fvar(&mut self, id: FVarId) {
///         self.fvars.push(id);
///     }
/// }
/// ```
pub trait ExprVisitor {
    type Result: Default;

    /// Merge results from two child sub-expressions.
    fn combine(&self, a: Self::Result, b: Self::Result) -> Self::Result;

    // ════════════════════════════════════════════════════════════════════
    // Leaf methods — override for custom behavior
    // ════════════════════════════════════════════════════════════════════

    fn visit_bvar(&mut self, _idx: u32) -> Self::Result {
        Self::Result::default()
    }

    fn visit_fvar(&mut self, _id: FVarId) -> Self::Result {
        Self::Result::default()
    }

    fn visit_sort(&mut self, _level: &Level) -> Self::Result {
        Self::Result::default()
    }

    fn visit_const(&mut self, _name: &Name, _levels: &LevelVec) -> Self::Result {
        Self::Result::default()
    }

    fn visit_lit(&mut self, _lit: &Literal) -> Self::Result {
        Self::Result::default()
    }

    /// Called when visiting a binder body. Override to track binder depth.
    /// Default delegates to visit_expr.
    fn visit_binder_body(&mut self, expr: &Expr) -> Self::Result {
        self.visit_expr(expr)
    }

    // ════════════════════════════════════════════════════════════════════
    // Main dispatch — rarely overridden
    // ════════════════════════════════════════════════════════════════════

    fn visit_expr(&mut self, expr: &Expr) -> Self::Result {
        stack_safe(|| match expr.kind() {
            ExprKind::BVar(idx) => self.visit_bvar(*idx),
            ExprKind::FVar(id) => self.visit_fvar(*id),
            ExprKind::Sort(level) => self.visit_sort(level),
            ExprKind::Const(name, levels) => self.visit_const(name, levels),
            ExprKind::Lit(lit) => self.visit_lit(lit),
            ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => Self::Result::default(),

            ExprKind::App(f, a) => {
                let rf = self.visit_expr(f);
                let ra = self.visit_expr(a);
                self.combine(rf, ra)
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                let rt = self.visit_expr(ty);
                let rb = self.visit_binder_body(body);
                self.combine(rt, rb)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                let rt = self.visit_expr(ty);
                let rv = self.visit_expr(val);
                let rb = self.visit_binder_body(body);
                self.combine(rt, self.combine(rv, rb))
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                self.visit_expr(inner)
            }
            ExprKind::CubicalPath { ty, left, right } => {
                let rt = self.visit_expr(ty);
                let rl = self.visit_expr(left);
                let rr = self.visit_expr(right);
                self.combine(rt, self.combine(rl, rr))
            }
            ExprKind::CubicalPathLam { body } => self.visit_binder_body(body),
            ExprKind::CubicalPathApp { path, arg } => {
                let rp = self.visit_expr(path);
                let ra = self.visit_expr(arg);
                self.combine(rp, ra)
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                let rt = self.visit_expr(ty);
                let rp = self.visit_expr(phi);
                let ru = self.visit_expr(u);
                let rb = self.visit_expr(base);
                self.combine(rt, self.combine(rp, self.combine(ru, rb)))
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                let rt = self.visit_expr(ty);
                let rp = self.visit_expr(phi);
                let rb = self.visit_expr(base);
                self.combine(rt, self.combine(rp, rb))
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                let rt = self.visit_expr(ty);
                let rr = self.visit_expr(r);
                let rs = self.visit_expr(s);
                let rb = self.visit_expr(base);
                self.combine(rt, self.combine(rr, self.combine(rs, rb)))
            }
            ExprKind::ZFCSet(set_expr) => self.visit_zfc_set_expr(set_expr),
            ExprKind::ZFCMem { element, set } => {
                let re = self.visit_expr(element);
                let rs = self.visit_expr(set);
                self.combine(re, rs)
            }
            ExprKind::ZFCComprehension { domain, pred } => {
                let rd = self.visit_expr(domain);
                let rp = self.visit_binder_body(pred);
                self.combine(rd, rp)
            }
        })
    }

    /// Visit a ZFC set expression. Default recurses into child Exprs.
    fn visit_zfc_set_expr(&mut self, set_expr: &ZFCSetExpr) -> Self::Result {
        match set_expr {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => Self::Result::default(),
            ZFCSetExpr::Singleton(e)
            | ZFCSetExpr::Union(e)
            | ZFCSetExpr::PowerSet(e)
            | ZFCSetExpr::Choice(e) => self.visit_expr(e),
            ZFCSetExpr::Pair(a, b) => {
                let ra = self.visit_expr(a);
                let rb = self.visit_expr(b);
                self.combine(ra, rb)
            }
            ZFCSetExpr::Separation { set, pred } | ZFCSetExpr::Replacement { set, func: pred } => {
                let rs = self.visit_expr(set);
                let rp = self.visit_binder_body(pred);
                self.combine(rs, rp)
            }
        }
    }
}

#[path = "visitor_opt.rs"]
mod opt;
pub use opt::ExprFolderOpt;

#[cfg(test)]
#[path = "visitor_tests.rs"]
mod tests;
