// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression-level operations for universe polymorphism.
//!
//! Provides recursive traversal of `Expr` trees to:
//! - Substitute universe levels in Sort/Const nodes
//! - Collect universe-level parameters from expressions
//! - Collect universe constraints from expression pairs
//! - Infer universe levels for omitted parameters
//! - Auto-level definitions by discovering universe params

use std::collections::HashMap;

use clean_kernel::{Expr, ExprKind, Level, Name};

use super::{apply_subst_to_level, UniverseInferCtx, UniversePolyError};
use crate::stack_safe;

// ═══════════════════════════════════════════════════════════════════════════
// Level substitution in expressions
// ═══════════════════════════════════════════════════════════════════════════

/// Substitute universe levels throughout an expression.
///
/// Walks the expression tree and applies the substitution map to every
/// `Sort(level)` and `Const(name, levels)` node.
pub(crate) fn substitute_levels_in_expr(expr: &Expr, solutions: &HashMap<Name, Level>) -> Expr {
    if solutions.is_empty() {
        return expr.clone();
    }
    stack_safe(|| substitute_levels_in_expr_impl(expr, solutions))
}

/// Recursive implementation of level substitution.
fn substitute_levels_in_expr_impl(expr: &Expr, solutions: &HashMap<Name, Level>) -> Expr {
    match expr.kind() {
        ExprKind::Sort(level) => {
            let new_level = apply_subst_to_level(level, solutions);
            Expr::sort(new_level)
        }
        ExprKind::Const(name, levels) => {
            let new_levels: Vec<Level> = levels
                .iter()
                .map(|l| apply_subst_to_level(l, solutions))
                .collect();
            Expr::const_(name.clone(), new_levels)
        }
        ExprKind::App(f, a) => {
            let new_f = stack_safe(|| substitute_levels_in_expr_impl(f, solutions));
            let new_a = stack_safe(|| substitute_levels_in_expr_impl(a, solutions));
            Expr::app(new_f, new_a)
        }
        ExprKind::Lam(binder, ty, body) => {
            let new_ty = stack_safe(|| substitute_levels_in_expr_impl(ty, solutions));
            let new_body = stack_safe(|| substitute_levels_in_expr_impl(body, solutions));
            Expr::lam(binder.info, new_ty, new_body)
        }
        ExprKind::Pi(binder, ty, body) => {
            let new_ty = stack_safe(|| substitute_levels_in_expr_impl(ty, solutions));
            let new_body = stack_safe(|| substitute_levels_in_expr_impl(body, solutions));
            Expr::pi(binder.info, new_ty, new_body)
        }
        ExprKind::Let(name, ty, val, body, non_dep) => {
            let new_ty = stack_safe(|| substitute_levels_in_expr_impl(ty, solutions));
            let new_val = stack_safe(|| substitute_levels_in_expr_impl(val, solutions));
            let new_body = stack_safe(|| substitute_levels_in_expr_impl(body, solutions));
            Expr::let_named(name.clone(), new_ty, new_val, new_body, *non_dep)
        }
        ExprKind::Proj(name, idx, inner) => {
            let new_inner = stack_safe(|| substitute_levels_in_expr_impl(inner, solutions));
            Expr::proj(name.clone(), *idx, new_inner)
        }
        ExprKind::MData(md, inner) => {
            let new_inner = stack_safe(|| substitute_levels_in_expr_impl(inner, solutions));
            Expr::mdata(md.clone(), new_inner)
        }
        // BVar, FVar, Lit contain no universe levels.
        _ => expr.clone(),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Universe parameter collection from expressions
// ═══════════════════════════════════════════════════════════════════════════

/// Collect all universe-level parameter names from an expression.
///
/// Walks Sort and Const nodes, delegates to `Level::collect_params` for
/// deduplication.
pub(crate) fn collect_level_params_from_expr(expr: &Expr, params: &mut Vec<Name>) {
    stack_safe(|| collect_level_params_from_expr_impl(expr, params));
}

fn collect_level_params_from_expr_impl(expr: &Expr, params: &mut Vec<Name>) {
    match expr.kind() {
        ExprKind::Sort(level) => {
            level.collect_params(params);
        }
        ExprKind::Const(_, levels) => {
            for level in levels.iter() {
                level.collect_params(params);
            }
        }
        ExprKind::App(f, a) => {
            stack_safe(|| collect_level_params_from_expr_impl(f, params));
            stack_safe(|| collect_level_params_from_expr_impl(a, params));
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            stack_safe(|| collect_level_params_from_expr_impl(ty, params));
            stack_safe(|| collect_level_params_from_expr_impl(body, params));
        }
        ExprKind::Let(_, ty, val, body, _) => {
            stack_safe(|| collect_level_params_from_expr_impl(ty, params));
            stack_safe(|| collect_level_params_from_expr_impl(val, params));
            stack_safe(|| collect_level_params_from_expr_impl(body, params));
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            stack_safe(|| collect_level_params_from_expr_impl(inner, params));
        }
        _ => {}
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Constraint collection from expression pairs
// ═══════════════════════════════════════════════════════════════════════════

/// Collect universe equality constraints from two expressions that should
/// be definitionally equal.
///
/// Walks both expressions in lockstep and generates `Eq` constraints for
/// corresponding universe levels in Sort/Const nodes.
pub(crate) fn collect_constraints_from_expr(lhs: &Expr, rhs: &Expr, ctx: &mut UniverseInferCtx) {
    stack_safe(|| collect_constraints_impl(lhs, rhs, ctx));
}

fn collect_constraints_impl(lhs: &Expr, rhs: &Expr, ctx: &mut UniverseInferCtx) {
    match (lhs.kind(), rhs.kind()) {
        (ExprKind::Sort(l1), ExprKind::Sort(l2)) => {
            ctx.add_eq(l1.clone(), l2.clone());
        }
        (ExprKind::Const(_, ls1), ExprKind::Const(_, ls2)) => {
            for (l1, l2) in ls1.iter().zip(ls2.iter()) {
                ctx.add_eq(l1.clone(), l2.clone());
            }
        }
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            stack_safe(|| collect_constraints_impl(f1, f2, ctx));
            stack_safe(|| collect_constraints_impl(a1, a2, ctx));
        }
        (ExprKind::Lam(_, ty1, b1), ExprKind::Lam(_, ty2, b2))
        | (ExprKind::Pi(_, ty1, b1), ExprKind::Pi(_, ty2, b2)) => {
            stack_safe(|| collect_constraints_impl(ty1, ty2, ctx));
            stack_safe(|| collect_constraints_impl(b1, b2, ctx));
        }
        (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => {
            stack_safe(|| collect_constraints_impl(ty1, ty2, ctx));
            stack_safe(|| collect_constraints_impl(v1, v2, ctx));
            stack_safe(|| collect_constraints_impl(b1, b2, ctx));
        }
        _ => {}
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Universe inference and auto-leveling
// ═══════════════════════════════════════════════════════════════════════════

/// Result of auto-leveling a definition.
#[derive(Debug, Clone)]
pub(crate) struct AutoLevelResult {
    /// The universe parameters for the definition (declared + discovered).
    pub(crate) universe_params: Vec<Name>,
    /// The (possibly updated) type expression with levels resolved.
    pub(crate) type_expr: Expr,
    /// The (possibly updated) value expression with levels resolved.
    pub(crate) value_expr: Option<Expr>,
}

/// Infer universe levels for a type/value pair.
///
/// Creates a fresh `UniverseInferCtx`, collects constraints from the
/// type and optional value, solves them, and returns the solution map.
pub(crate) fn infer_universe_levels(
    type_expr: &Expr,
    value_expr: Option<&Expr>,
    declared_params: &[Name],
) -> Result<HashMap<Name, Level>, UniversePolyError> {
    let mut ctx = UniverseInferCtx::new(declared_params.to_vec());

    // If there is a value, collect constraints between type and value.
    if let Some(val) = value_expr {
        collect_constraints_from_expr(type_expr, val, &mut ctx);
    }

    ctx.solve()
}

/// Auto-level a definition by discovering universe parameters.
///
/// Collects all universe parameter names from the type and value expressions,
/// merges with any explicitly declared parameters, and returns the combined
/// set along with the (unchanged) expressions.
///
/// This does NOT solve constraints or substitute — it only discovers
/// parameters. Use `infer_universe_levels` for constraint solving.
pub(crate) fn auto_level_definition(
    type_expr: &Expr,
    value_expr: Option<&Expr>,
    declared_params: &[Name],
) -> Result<AutoLevelResult, UniversePolyError> {
    let mut all_params: Vec<Name> = declared_params.to_vec();

    // Collect parameters from type.
    collect_level_params_from_expr(type_expr, &mut all_params);

    // Collect parameters from value (if present).
    if let Some(val) = value_expr {
        collect_level_params_from_expr(val, &mut all_params);
    }

    // Deduplicate while preserving order (declared params first).
    let mut seen = std::collections::HashSet::new();
    all_params.retain(|p| seen.insert(p.clone()));

    Ok(AutoLevelResult {
        universe_params: all_params,
        type_expr: type_expr.clone(),
        value_expr: value_expr.cloned(),
    })
}
