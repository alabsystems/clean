// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! BVar-to-metavariable conversion for simp pattern matching.
//!
//! Extracted from `simp/expr.rs` for file size enforcement (#307).
//! Converts bound variables in lemma patterns to fresh metavariables
//! for unification-based matching, and substitutes matched BVars back.

use std::sync::Arc;

use clean_kernel::{Expr, ExprKind, FVarId};

use crate::stack_safe;
use crate::unify::MetaState;

/// Convert bound variables in a pattern to fresh metavariables.
///
/// `scope` is the local-variable scope recorded on each minted meta: the
/// matcher unifies the pattern against a GOAL subterm, so a pattern variable
/// must be allowed to bind a term mentioning the goal's own locals
/// (`Nat.mul ?n 1` against `a * 1` binds `?n := a`, a goal FVar). Passing the
/// goal's locals here keeps the unifier's scope discipline intact: metas still
/// cannot capture binder-opened temporaries or anything outside the goal (B102).
///
/// Returns the transformed expression and a mapping from BVar indices to MetaIds.
///
/// # Contract
///
/// REQUIRES: `pattern` is a well-formed expression (valid BVar indices)
/// ENSURES: All top-level BVars in `pattern` are replaced by fresh metavariables
/// ENSURES: Inner BVars bound by Lam/Pi/Let binders are preserved unchanged
/// ENSURES: Returned map keys correspond to adjusted BVar indices (0-based from top)
pub(crate) fn convert_bvars_to_metas(
    pattern: &Expr,
    metas: &mut MetaState,
    scope: &[(String, FVarId, Expr)],
) -> (Expr, hashbrown::HashMap<u32, Expr>) {
    let mut bvar_to_meta = hashbrown::HashMap::new();
    let result = convert_bvars_to_metas_aux(pattern, metas, scope, &mut bvar_to_meta, 0);
    (result, bvar_to_meta)
}

fn convert_bvars_to_metas_aux(
    expr: &Expr,
    metas: &mut MetaState,
    scope: &[(String, FVarId, Expr)],
    bvar_to_meta: &mut hashbrown::HashMap<u32, Expr>,
    depth: u32,
) -> Expr {
    stack_safe(|| match expr.kind() {
        ExprKind::BVar(idx) => {
            // Only convert top-level BVars (not ones bound by inner lambdas).
            // BVars with idx >= depth are pattern variables.
            if *idx >= depth {
                let adjusted_idx = *idx - depth;
                if let Some(meta_expr) = bvar_to_meta.get(&adjusted_idx) {
                    return meta_expr.clone();
                }
                // Create a fresh metavariable for this BVar.
                // Use Type as a placeholder type (simp lemmas typically have type params).
                // The scope is the GOAL's locals (see `convert_bvars_to_metas`):
                // wide enough to bind goal subterms, still closed to
                // binder-opened temporaries.
                let meta_id = metas.fresh_with_locals(Expr::type_(), scope.to_vec());
                let meta_expr = Expr::fvar(MetaState::to_fvar(meta_id));
                bvar_to_meta.insert(adjusted_idx, meta_expr.clone());
                meta_expr
            } else {
                expr.clone()
            }
        }
        ExprKind::App(f, a) => {
            let f_conv = convert_bvars_to_metas_aux(f, metas, scope, bvar_to_meta, depth);
            let a_conv = convert_bvars_to_metas_aux(a, metas, scope, bvar_to_meta, depth);
            Expr::app(f_conv, a_conv)
        }
        ExprKind::Lam(bi, ty, body) => {
            let ty_conv = convert_bvars_to_metas_aux(ty, metas, scope, bvar_to_meta, depth);
            let body_conv = convert_bvars_to_metas_aux(body, metas, scope, bvar_to_meta, depth + 1);
            Expr::lam(*bi, ty_conv, body_conv)
        }
        ExprKind::Pi(bi, ty, body) => {
            let ty_conv = convert_bvars_to_metas_aux(ty, metas, scope, bvar_to_meta, depth);
            let body_conv = convert_bvars_to_metas_aux(body, metas, scope, bvar_to_meta, depth + 1);
            Expr::pi(*bi, ty_conv, body_conv)
        }
        ExprKind::Let(name, ty, val, body, non_dep) => {
            let ty_conv = convert_bvars_to_metas_aux(ty, metas, scope, bvar_to_meta, depth);
            let val_conv = convert_bvars_to_metas_aux(val, metas, scope, bvar_to_meta, depth);
            let body_conv = convert_bvars_to_metas_aux(body, metas, scope, bvar_to_meta, depth + 1);
            Expr::let_named(name.clone(), ty_conv, val_conv, body_conv, *non_dep)
        }
        ExprKind::Proj(name, idx, e) => {
            let e_conv = convert_bvars_to_metas_aux(e, metas, scope, bvar_to_meta, depth);
            Expr::proj(name.clone(), *idx, e_conv)
        }
        ExprKind::MData(mdata, e) => {
            let e_conv = convert_bvars_to_metas_aux(e, metas, scope, bvar_to_meta, depth);
            Expr::mdata(mdata.clone(), e_conv)
        }
        ExprKind::Squash(e) => {
            let e_conv = convert_bvars_to_metas_aux(e, metas, scope, bvar_to_meta, depth);
            Expr::from_kind(ExprKind::Squash(Arc::new(e_conv)))
        }
        _ => expr.clone(),
    })
}

/// Substitute BVars in an expression using a mapping to metavariable expressions.
///
/// REQUIRES: `bvar_to_meta` uses the adjusted top-level indexing from `convert_bvars_to_metas`
/// ENSURES: Only mapped top-level BVars are replaced; inner bound BVars are preserved
pub(crate) fn substitute_bvars_with_metas(
    expr: &Expr,
    bvar_to_meta: &hashbrown::HashMap<u32, Expr>,
) -> Expr {
    substitute_bvars_with_metas_aux(expr, bvar_to_meta, 0)
}

fn substitute_bvars_with_metas_aux(
    expr: &Expr,
    bvar_to_meta: &hashbrown::HashMap<u32, Expr>,
    depth: u32,
) -> Expr {
    stack_safe(|| match expr.kind() {
        ExprKind::BVar(idx) => {
            if *idx >= depth {
                let adjusted_idx = *idx - depth;
                if let Some(meta_expr) = bvar_to_meta.get(&adjusted_idx) {
                    return meta_expr.clone();
                }
            }
            expr.clone()
        }
        ExprKind::App(f, a) => {
            let f_sub = substitute_bvars_with_metas_aux(f, bvar_to_meta, depth);
            let a_sub = substitute_bvars_with_metas_aux(a, bvar_to_meta, depth);
            Expr::app(f_sub, a_sub)
        }
        ExprKind::Lam(bi, ty, body) => {
            let ty_sub = substitute_bvars_with_metas_aux(ty, bvar_to_meta, depth);
            let body_sub = substitute_bvars_with_metas_aux(body, bvar_to_meta, depth + 1);
            Expr::lam(*bi, ty_sub, body_sub)
        }
        ExprKind::Pi(bi, ty, body) => {
            let ty_sub = substitute_bvars_with_metas_aux(ty, bvar_to_meta, depth);
            let body_sub = substitute_bvars_with_metas_aux(body, bvar_to_meta, depth + 1);
            Expr::pi(*bi, ty_sub, body_sub)
        }
        ExprKind::Let(name, ty, val, body, non_dep) => {
            let ty_sub = substitute_bvars_with_metas_aux(ty, bvar_to_meta, depth);
            let val_sub = substitute_bvars_with_metas_aux(val, bvar_to_meta, depth);
            let body_sub = substitute_bvars_with_metas_aux(body, bvar_to_meta, depth + 1);
            Expr::let_named(name.clone(), ty_sub, val_sub, body_sub, *non_dep)
        }
        ExprKind::Proj(name, idx, e) => {
            let e_sub = substitute_bvars_with_metas_aux(e, bvar_to_meta, depth);
            Expr::proj(name.clone(), *idx, e_sub)
        }
        ExprKind::MData(mdata, e) => {
            let e_sub = substitute_bvars_with_metas_aux(e, bvar_to_meta, depth);
            Expr::mdata(mdata.clone(), e_sub)
        }
        ExprKind::Squash(e) => {
            let e_sub = substitute_bvars_with_metas_aux(e, bvar_to_meta, depth);
            Expr::from_kind(ExprKind::Squash(Arc::new(e_sub)))
        }
        _ => expr.clone(),
    })
}
