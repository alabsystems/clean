// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FVar abstraction in expressions.
//!
//! Converts FVar occurrences to BVar at a given depth, adjusting existing BVar
//! indices above the depth. Used by the certificate rebinding traversal.

use std::sync::Arc;

use crate::expr::{stack_safe, Expr, ExprKind, FVarId};
use crate::tc::local_context::checked_add_u32;

/// Abstract FVar occurrences in an expression, converting them to BVar(depth).
/// Stack-safe wrapper for deeply nested expressions.
pub(crate) fn abstract_fvar_in_expr(e: Expr, fvar_id: FVarId, depth: u32) -> Expr {
    stack_safe(|| abstract_fvar_in_expr_impl(e, fvar_id, depth))
}

fn abstract_fvar_in_expr_impl(e: Expr, fvar_id: FVarId, depth: u32) -> Expr {
    // O(1) metadata guard: skip subtrees with no FVars and no loose BVars at or above depth.
    // Matches the guard in expr/subst.rs Abstractor::should_descend.
    if !e.has_fvar_quick() && depth >= e.loose_bvar_range() {
        return e;
    }
    match &e.kind {
        ExprKind::FVar(id) if *id == fvar_id => Expr::from_kind(ExprKind::BVar(depth)),
        ExprKind::BVar(idx) => {
            // Shift BVars at or above target depth (Lean 4 parity: abstract shifts free bvars)
            if *idx >= depth {
                Expr::from_kind(ExprKind::BVar(checked_add_u32(
                    *idx,
                    1,
                    "abstract_fvar bvar shift",
                )))
            } else {
                e
            }
        }
        ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Const(_, _) | ExprKind::Lit(_) => e,
        ExprKind::App(f, a) => Expr::from_kind(ExprKind::App(
            Arc::new(abstract_fvar_in_expr(f.as_ref().clone(), fvar_id, depth)),
            Arc::new(abstract_fvar_in_expr(a.as_ref().clone(), fvar_id, depth)),
        )),
        ExprKind::Lam(bi, ty, body) => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            Expr::from_kind(ExprKind::Lam(
                *bi,
                Arc::new(abstract_fvar_in_expr(ty.as_ref().clone(), fvar_id, depth)),
                Arc::new(abstract_fvar_in_expr(body.as_ref().clone(), fvar_id, d1)),
            ))
        }
        ExprKind::Pi(bi, ty, body) => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            Expr::from_kind(ExprKind::Pi(
                *bi,
                Arc::new(abstract_fvar_in_expr(ty.as_ref().clone(), fvar_id, depth)),
                Arc::new(abstract_fvar_in_expr(body.as_ref().clone(), fvar_id, d1)),
            ))
        }
        ExprKind::Let(let_name, ty, val, body, let_nondep) => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            Expr::from_kind(ExprKind::Let(
                let_name.clone(),
                Arc::new(abstract_fvar_in_expr(ty.as_ref().clone(), fvar_id, depth)),
                Arc::new(abstract_fvar_in_expr(val.as_ref().clone(), fvar_id, depth)),
                Arc::new(abstract_fvar_in_expr(body.as_ref().clone(), fvar_id, d1)),
                *let_nondep,
            ))
        }
        ExprKind::Proj(name, idx, inner) => Expr::from_kind(ExprKind::Proj(
            name.clone(),
            *idx,
            Arc::new(abstract_fvar_in_expr(
                inner.as_ref().clone(),
                fvar_id,
                depth,
            )),
        )),
        ExprKind::MData(meta, inner) => Expr::from_kind(ExprKind::MData(
            meta.clone(),
            Arc::new(abstract_fvar_in_expr(
                inner.as_ref().clone(),
                fvar_id,
                depth,
            )),
        )),
        // Mode-specific extensions delegated to separate function
        _ => abstract_fvar_mode_specific(e, fvar_id, depth),
    }
}

/// Mode-specific FVar abstraction: Cubical, ZFC, and Impredicative expression kinds.
fn abstract_fvar_mode_specific(e: Expr, fvar_id: FVarId, depth: u32) -> Expr {
    match &e.kind {
        ExprKind::CubicalInterval | ExprKind::CubicalI0 | ExprKind::CubicalI1 => e,
        ExprKind::CubicalPath { ty, left, right } => Expr::from_kind(ExprKind::CubicalPath {
            ty: Arc::new(abstract_fvar_in_expr(ty.as_ref().clone(), fvar_id, depth)),
            left: Arc::new(abstract_fvar_in_expr(left.as_ref().clone(), fvar_id, depth)),
            right: Arc::new(abstract_fvar_in_expr(
                right.as_ref().clone(),
                fvar_id,
                depth,
            )),
        }),
        ExprKind::CubicalPathLam { body } => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            Expr::from_kind(ExprKind::CubicalPathLam {
                body: Arc::new(abstract_fvar_in_expr(body.as_ref().clone(), fvar_id, d1)),
            })
        }
        ExprKind::CubicalPathApp { path, arg } => Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(abstract_fvar_in_expr(path.as_ref().clone(), fvar_id, depth)),
            arg: Arc::new(abstract_fvar_in_expr(arg.as_ref().clone(), fvar_id, depth)),
        }),
        ExprKind::CubicalHComp { ty, phi, u, base } => Expr::from_kind(ExprKind::CubicalHComp {
            ty: Arc::new(abstract_fvar_in_expr(ty.as_ref().clone(), fvar_id, depth)),
            phi: Arc::new(abstract_fvar_in_expr(phi.as_ref().clone(), fvar_id, depth)),
            u: Arc::new(abstract_fvar_in_expr(u.as_ref().clone(), fvar_id, depth)),
            base: Arc::new(abstract_fvar_in_expr(base.as_ref().clone(), fvar_id, depth)),
        }),
        ExprKind::CubicalTransp { ty, phi, base } => Expr::from_kind(ExprKind::CubicalTransp {
            ty: Arc::new(abstract_fvar_in_expr(ty.as_ref().clone(), fvar_id, depth)),
            phi: Arc::new(abstract_fvar_in_expr(phi.as_ref().clone(), fvar_id, depth)),
            base: Arc::new(abstract_fvar_in_expr(base.as_ref().clone(), fvar_id, depth)),
        }),
        ExprKind::CubicalCoe { ty, r, s, base } => Expr::from_kind(ExprKind::CubicalCoe {
            ty: Arc::new(abstract_fvar_in_expr(ty.as_ref().clone(), fvar_id, depth)),
            r: Arc::new(abstract_fvar_in_expr(r.as_ref().clone(), fvar_id, depth)),
            s: Arc::new(abstract_fvar_in_expr(s.as_ref().clone(), fvar_id, depth)),
            base: Arc::new(abstract_fvar_in_expr(base.as_ref().clone(), fvar_id, depth)),
        }),
        ExprKind::ZFCSet(set_expr) => {
            let new_set = set_expr.abstract_fvar_at(fvar_id, depth);
            if new_set == *set_expr {
                e
            } else {
                Expr::from_kind(ExprKind::ZFCSet(new_set))
            }
        }
        ExprKind::ZFCMem { element, set } => Expr::from_kind(ExprKind::ZFCMem {
            element: Arc::new(abstract_fvar_in_expr(
                element.as_ref().clone(),
                fvar_id,
                depth,
            )),
            set: Arc::new(abstract_fvar_in_expr(set.as_ref().clone(), fvar_id, depth)),
        }),
        ExprKind::ZFCComprehension { domain, pred } => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            Expr::from_kind(ExprKind::ZFCComprehension {
                domain: Arc::new(abstract_fvar_in_expr(
                    domain.as_ref().clone(),
                    fvar_id,
                    depth,
                )),
                pred: Arc::new(abstract_fvar_in_expr(pred.as_ref().clone(), fvar_id, d1)),
            })
        }
        ExprKind::SProp => e,
        ExprKind::Squash(inner) => Expr::from_kind(ExprKind::Squash(Arc::new(
            abstract_fvar_in_expr(inner.as_ref().clone(), fvar_id, depth),
        ))),
        // Core CIC cases handled by abstract_fvar_in_expr_impl
        _ => unreachable!("core CIC case should be handled by abstract_fvar_in_expr_impl"),
    }
}
