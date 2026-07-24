// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Goal matching and relation expression builders for `calc` chains.
//!
//! Split from calc_trans.rs for file size.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

use super::arith_push_neg::{match_iff, match_le, match_lt};
use super::calc::CalcRel;
use super::calc_trans::rel_const_name;
use super::equality::match_equality;

fn match_named_comparison(
    expr: &Expr,
    expected_head: &str,
) -> Option<(Expr, Expr, Expr, Vec<Level>)> {
    let args = expr.get_app_args();
    if args.len() < 4 {
        return None;
    }

    match expr.get_app_fn().kind() {
        ExprKind::Const(name, levels) if name.to_string().contains(expected_head) => Some((
            args[args.len() - 4].clone(),
            args[args.len() - 2].clone(),
            args[args.len() - 1].clone(),
            levels.to_vec(),
        )),
        _ => None,
    }
}

/// Build a fully-applied relation expression for a calc relation.
///
/// REQUIRES: `lhs` and `rhs` inhabit `ty` for equality/order relations, or are
/// propositions for `Iff`.
/// ENSURES: Returns the kernel-level relation expression for `rel`.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn make_rel_expr(
    rel: CalcRel,
    ty: &Expr,
    inst: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    levels: &[Level],
) -> Expr {
    match rel {
        CalcRel::Eq => Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), levels.to_vec()),
                    ty.clone(),
                ),
                lhs.clone(),
            ),
            rhs.clone(),
        ),
        CalcRel::Iff => Expr::app(
            Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), lhs.clone()),
            rhs.clone(),
        ),
        CalcRel::Ne => {
            // Ne α a b = @Ne.{u} α a b (same shape as Eq)
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Ne"), levels.to_vec()),
                        ty.clone(),
                    ),
                    lhs.clone(),
                ),
                rhs.clone(),
            )
        }
        CalcRel::Le | CalcRel::Lt | CalcRel::Ge | CalcRel::Gt => super::tc_app::mk_tc_rel(
            Expr::const_(Name::from_string(rel_const_name(rel)), levels.to_vec()),
            ty.clone(),
            inst.clone(),
            lhs.clone(),
            rhs.clone(),
        ),
    }
}

/// Match an expression as a supported calc relation goal.
///
/// REQUIRES: `expr` is a well-formed goal target expression.
/// ENSURES: Returns relation metadata for `Eq`, `Ne`, `LE.le`, `LT.lt`,
/// `GE.ge`, `GT.gt`, or `Iff`.
/// ENSURES: Returns `None` for unsupported goal heads.
#[must_use]
pub(crate) fn match_goal_rel(expr: &Expr) -> Option<(CalcRel, Expr, Expr, Expr, Vec<Level>)> {
    if let Ok((ty, lhs, rhs, levels)) = match_equality(expr) {
        return Some((CalcRel::Eq, ty, lhs, rhs, levels));
    }

    // Ne has the same arity as Eq: @Ne.{u} α a b
    if let Some((ty, lhs, rhs, levels)) = match_ne(expr) {
        return Some((CalcRel::Ne, ty, lhs, rhs, levels));
    }

    if let Some((ty, lhs, rhs)) = match_le(expr) {
        let (_, _, _, levels) = match_named_comparison(expr, "LE.le")?;
        return Some((CalcRel::Le, ty, lhs, rhs, levels));
    }

    if let Some((ty, lhs, rhs)) = match_lt(expr) {
        let (_, _, _, levels) = match_named_comparison(expr, "LT.lt")?;
        return Some((CalcRel::Lt, ty, lhs, rhs, levels));
    }

    if let Some((ty, lhs, rhs, levels)) = match_named_comparison(expr, "GE.ge") {
        return Some((CalcRel::Ge, ty, lhs, rhs, levels));
    }

    if let Some((ty, lhs, rhs, levels)) = match_named_comparison(expr, "GT.gt") {
        return Some((CalcRel::Gt, ty, lhs, rhs, levels));
    }

    if let Some((lhs, rhs)) = match_iff(expr) {
        return Some((CalcRel::Iff, Expr::prop(), lhs, rhs, vec![]));
    }

    None
}

/// Match `@Ne.{u} α a b` expressions.
///
/// Ne has the same 3-argument application shape as Eq: type, lhs, rhs.
#[must_use]
fn match_ne(expr: &Expr) -> Option<(Expr, Expr, Expr, Vec<Level>)> {
    let args = expr.get_app_args();
    if args.len() < 3 {
        return None;
    }
    match expr.get_app_fn().kind() {
        ExprKind::Const(name, levels) if name.to_string() == "Ne" => Some((
            args[args.len() - 3].clone(),
            args[args.len() - 2].clone(),
            args[args.len() - 1].clone(),
            levels.to_vec(),
        )),
        _ => None,
    }
}
