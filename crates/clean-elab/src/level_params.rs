// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe-level parameter collection.
//!
//! This is the SOLE surviving piece of the former `universe_poly` /
//! `universe_poly_ext` / `universe_poly_ext2` / `universe_constraint_ext`
//! family — four parallel universe-constraint solvers that arrived with the
//! initial lean5 port and never acquired a production caller. U2 rung 3's
//! fence 9 requires that exactly one level solver exist and that the losers be
//! deleted rather than left dormant, so they were removed (2026-08-13); see
//! `designs/2026-08-08-u2-universe-polymorphism-ladder.md`.
//!
//! The single level solver is `unify::level_solve::solve_level_eq`, reached
//! through the two thin `unify_levels` entry points.
//!
//! What was salvaged is this walk, which has two live call sites in
//! `infer/instance.rs` and is not a solver at all: it collects the level
//! parameter names occurring in an expression, delegating deduplication to
//! `Level::collect_params`.

use clean_kernel::{Expr, ExprKind, Name};

use crate::stack_safe;

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

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Level};

    fn p(n: &str) -> Level {
        Level::Param(Name::from_string(n))
    }

    /// The walk finds params under a `Sort`, and dedups.
    #[test]
    fn test_collect_finds_sort_params_deduped() {
        let e = Expr::app(Expr::sort(p("u")), Expr::sort(Level::max(p("u"), p("v"))));
        let mut got = Vec::new();
        collect_level_params_from_expr(&e, &mut got);
        let mut names: Vec<String> = got.iter().map(ToString::to_string).collect();
        names.sort();
        assert_eq!(
            names,
            vec!["u".to_string(), "v".to_string()],
            "both params must be found once each; `u` occurs twice (bare Sort and \
             inside the max) and must be deduped"
        );
    }

    /// Params carried by a `Const`'s level arguments are found too.
    ///
    /// This is the case the live call sites in `infer/instance.rs` care about:
    /// an instance's expression mentions its levels through constant
    /// applications, not only through bare sorts.
    #[test]
    fn test_collect_finds_const_level_args() {
        let e = Expr::app(
            Expr::const_(Name::from_string("F"), vec![p("w")]),
            Expr::sort(Level::zero()),
        );
        let mut got = Vec::new();
        collect_level_params_from_expr(&e, &mut got);
        assert_eq!(
            got.iter().map(ToString::to_string).collect::<Vec<_>>(),
            vec!["w".to_string()],
            "a Const's level arguments must be walked"
        );
    }

    /// A level-free expression contributes nothing.
    #[test]
    fn test_collect_on_level_free_expr_is_empty() {
        let mut got = Vec::new();
        collect_level_params_from_expr(&Expr::bvar(0), &mut got);
        assert!(got.is_empty(), "a bvar carries no level params");
    }

    /// BINDERS: the walk descends into both the binder type and the body.
    ///
    /// This is the arm the live callers actually depend on. `infer/instance.rs`
    /// walks `inst.type_`, and an instance type is a Pi TELESCOPE — if this arm
    /// were dropped, the params of every instance type would be silently
    /// missed. Ported from the deleted `universe_poly_tests.rs`
    /// `test_collect_params_from_nested_pi`, which was the only test covering
    /// it; an earlier revision of this module dropped it on the mistaken
    /// rationale that `Expr::pi` could not be called conveniently. It takes
    /// `impl Into<BinderData>`, so `BinderInfo::Default` works directly.
    #[test]
    fn test_collect_descends_into_nested_pi_binders() {
        let e = Expr::pi(
            BinderInfo::Default,
            Expr::sort(p("u")),
            Expr::pi(
                BinderInfo::Default,
                Expr::sort(p("v")),
                Expr::sort(Level::max(p("u"), p("w"))),
            ),
        );
        let mut got = Vec::new();
        collect_level_params_from_expr(&e, &mut got);
        let mut names: Vec<String> = got.iter().map(ToString::to_string).collect();
        names.sort();
        assert_eq!(
            names,
            vec!["u".to_string(), "v".to_string(), "w".to_string()],
            "params must be collected from nested binder TYPES and the innermost body"
        );
    }

    /// `Let` descends into all three of type, value, and body.
    ///
    /// Never covered before or after the salvage; added because dropping any
    /// one of the three recursions leaves the other tests green.
    #[test]
    fn test_collect_descends_into_let_type_value_and_body() {
        let e = Expr::let_named(
            Name::from_string("x"),
            Expr::sort(p("t")),
            Expr::sort(p("val")),
            Expr::sort(p("body")),
            false,
        );
        let mut got = Vec::new();
        collect_level_params_from_expr(&e, &mut got);
        let mut names: Vec<String> = got.iter().map(ToString::to_string).collect();
        names.sort();
        assert_eq!(
            names,
            vec!["body".to_string(), "t".to_string(), "val".to_string()],
            "a Let must be walked through its type, its value, AND its body"
        );
    }

    /// `MData` is transparent to the walk.
    ///
    /// Metadata wrappers are common on elaborated terms, and a walk that
    /// stopped at one would silently lose every param beneath it.
    #[test]
    fn test_collect_sees_through_mdata() {
        let inner = Expr::sort(p("u"));
        let e = Expr::mdata(clean_kernel::MDataMap::default(), inner);
        let mut got = Vec::new();
        collect_level_params_from_expr(&e, &mut got);
        assert_eq!(
            got.iter().map(ToString::to_string).collect::<Vec<_>>(),
            vec!["u".to_string()],
            "MData must be transparent, not a wall"
        );
    }
}
