// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Iterative drop for deeply nested expressions.
//!
//! Expressions with saturated depth (>= 255) use a worklist-based iterative
//! teardown to avoid stack overflow in recursive Drop. This matches Lean 4's
//! approach in `runtime/object.cpp:394-408`.

use super::{Expr, ExprKind, ExprMeta, ZFCSetExpr};
use std::sync::Arc;

/// If the cached depth saturates, the true depth may be far larger than 255.
/// Use iterative teardown in that case to avoid recursive Drop stack overflow.
const ITERATIVE_DROP_DEPTH_THRESHOLD: u8 = ExprMeta::MAX_DEPTH as u8;

// Gate iterative Drop with #[cfg(not(kani))]: the iterative worklist matches all
// 20+ ExprKind variants, causing CBMC to generate prohibitive verification
// conditions. Under Kani, we use a replace-and-forget strategy instead (see below).
#[cfg(not(kani))]
impl Drop for Expr {
    fn drop(&mut self) {
        if self.meta().approx_depth() < ITERATIVE_DROP_DEPTH_THRESHOLD {
            // Shallow expressions are cheap to drop recursively.
            return;
        }

        // Depth saturation means the actual tree can be much deeper than 255.
        // Move out the original kind and iteratively drain it to avoid stack growth.
        let kind = std::mem::replace(&mut self.kind, ExprKind::BVar(0));
        iterative_drop_kind(kind);
    }
}

// Kani Drop: REVERTED (was added in iter 2144, reverted in iter 2145).
//
// The unconditional mem::replace on ExprKind (20+ variants) forces CBMC to model
// reading ALL variant layouts from memory on every Expr drop — even for trivial
// BVar/FVar/Sort leaves where the default compiler-generated drop is a no-op.
// This added ~10x overhead to leaf-only harnesses (e.g., verify_inst_lift_identity
// passed in 31s without this Drop, timed out at 300s with it).
//
// For compound expressions (App, Lam, etc.) where recursive Arc<Expr> drops cause
// CBMC path explosion, use explicit leak() in the harness instead. All compound
// harnesses already leak their values; the remaining timeouts are from the visitor's
// ExprKind match (fold_expr_opt_inner), not from drops.
//
// The Level Kani Drop (level.rs) is kept because Level has only 5 variants (vs 20+
// for ExprKind) and prevents CBMC from recursing through Arc<Level> in Succ/Max/IMax.

/// Iteratively drop an `Expr` without consuming O(depth) stack frames.
///
/// `Expr::drop` automatically switches to iterative teardown when cached depth
/// saturates (>= 255). This helper is still available for explicit deep-tree
/// cleanup paths and test coverage.
///
/// Use this for cleanup paths that may release very deep expression trees.
///
/// Reference: Lean 4 uses a similar worklist approach in `runtime/object.cpp:394-408`.
pub fn iterative_drop(mut expr: Expr) {
    let kind = std::mem::replace(&mut expr.kind, ExprKind::BVar(0));
    std::mem::forget(expr); // Prevent recursive drop of the (now-leaf) Expr.
    iterative_drop_kind(kind);
}

/// Iteratively drain an expression kind by processing `Arc<Expr>` children using
/// a worklist instead of recursive drop.
fn iterative_drop_kind(kind: ExprKind) {
    let mut worklist: Vec<Arc<Expr>> = Vec::new();
    collect_arc_children(kind, &mut worklist);

    // Iteratively process the worklist.
    while let Some(arc) = worklist.pop() {
        // Try to take unique ownership of the Arc's inner Expr.
        // If refcount == 1, we own it and must drop it ourselves (iteratively).
        // If refcount > 1, Arc::drop just decrements — no recursion risk.
        match Arc::try_unwrap(arc) {
            Ok(mut inner) => {
                let inner_kind = std::mem::replace(&mut inner.kind, ExprKind::BVar(0));
                std::mem::forget(inner);
                collect_arc_children(inner_kind, &mut worklist);
            }
            Err(_shared_arc) => {
                // Arc has other owners; dropping it just decrements refcount.
            }
        }
    }
}

/// Extract all `Arc<Expr>` children from an `ExprKind` variant into the worklist.
///
/// The `ExprKind` value is consumed (moved), preventing its default drop from firing.
/// Non-Arc fields (Name, Level, u32, etc.) are dropped normally here.
fn collect_arc_children(kind: ExprKind, worklist: &mut Vec<Arc<Expr>>) {
    match kind {
        // Leaf variants: no Arc<Expr> children.
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => {}

        // Single-child variants.
        ExprKind::Proj(_, _, e)
        | ExprKind::MData(_, e)
        | ExprKind::Squash(e)
        | ExprKind::CubicalPathLam { body: e } => {
            worklist.push(e);
        }

        // Two-child variants.
        ExprKind::App(f, a) => {
            worklist.push(f);
            worklist.push(a);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            worklist.push(ty);
            worklist.push(body);
        }
        ExprKind::CubicalPathApp { path, arg } => {
            worklist.push(path);
            worklist.push(arg);
        }
        ExprKind::ZFCMem { element, set } => {
            worklist.push(element);
            worklist.push(set);
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            worklist.push(domain);
            worklist.push(pred);
        }

        // Three-child variants.
        ExprKind::Let(_, ty, val, body, _) => {
            worklist.push(ty);
            worklist.push(val);
            worklist.push(body);
        }
        ExprKind::CubicalPath { ty, left, right } => {
            worklist.push(ty);
            worklist.push(left);
            worklist.push(right);
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            worklist.push(ty);
            worklist.push(phi);
            worklist.push(base);
        }
        // Four-child variant.
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            worklist.push(ty);
            worklist.push(phi);
            worklist.push(u);
            worklist.push(base);
        }
        // Four-child variant (generalized coercion).
        ExprKind::CubicalCoe { ty, r, s, base } => {
            worklist.push(ty);
            worklist.push(r);
            worklist.push(s);
            worklist.push(base);
        }

        // ZFCSet: delegate to sub-expression children.
        ExprKind::ZFCSet(set_expr) => {
            collect_zfc_set_children(set_expr, worklist);
        }
    }
}

/// Extract `Arc<Expr>` children from a `ZFCSetExpr`.
fn collect_zfc_set_children(set_expr: ZFCSetExpr, worklist: &mut Vec<Arc<Expr>>) {
    match set_expr {
        ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
        ZFCSetExpr::Singleton(e)
        | ZFCSetExpr::Union(e)
        | ZFCSetExpr::PowerSet(e)
        | ZFCSetExpr::Choice(e) => {
            worklist.push(e);
        }
        ZFCSetExpr::Pair(a, b) => {
            worklist.push(a);
            worklist.push(b);
        }
        ZFCSetExpr::Separation { set, pred } => {
            worklist.push(set);
            worklist.push(pred);
        }
        ZFCSetExpr::Replacement { set, func } => {
            worklist.push(set);
            worklist.push(func);
        }
    }
}
