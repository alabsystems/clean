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
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
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

/// Decompose `e` into `(rel, lhs, rhs)` exactly the way Lean's
/// `Lean.Elab.Term.getCalcRelation?` does — strip the last two arguments of the
/// application, whatever the head is.
///
/// Lean's `calc` is relation-AGNOSTIC: a step's type only has to be an
/// application carrying at least two arguments, and its last two arguments are
/// the endpoints (`Lean/Elab/Calc.lean`, "it assumes the last two arguments are
/// explicit"). [`match_goal_rel`] above recognizes only the seven relations
/// Clean ships dedicated transitivity lemmas for; using it as the *gate* on a
/// calc step rejects every other relation (`List.Sublist`, `List.Perm`,
/// `Dvd.dvd`, a user's own inductive relation, …) before any transitivity
/// machinery is reached. This function is that gate's Lean-faithful
/// replacement.
///
/// It only DECOMPOSES — it asserts nothing about `rel` being a genuine
/// relation. Every proof term built from the result is still checked by
/// `infer_type` here and re-checked by the kernel via `add_decl` /
/// `close_goal`, so admitting a non-relation head can only produce a loud
/// failure downstream, never an over-accept.
///
/// REQUIRES: none.
/// ENSURES: Returns `Some((rel, lhs, rhs))` iff `e` is an application of at
/// least two arguments, where `rel` is `e` with its last two arguments removed.
#[must_use]
pub(crate) fn get_calc_relation(e: &Expr) -> Option<(Expr, Expr, Expr)> {
    let ExprKind::App(fn_and_lhs, rhs) = e.kind() else {
        return None;
    };
    let ExprKind::App(rel, lhs) = fn_and_lhs.kind() else {
        return None;
    };
    Some((
        rel.as_ref().clone(),
        lhs.as_ref().clone(),
        rhs.as_ref().clone(),
    ))
}

/// Endpoint decomposition for one calc step.
///
/// Tries the dedicated seven-relation matcher first, so the existing
/// per-relation lemma routing and its endpoint conventions are bit-for-bit
/// unchanged for `Eq`/`Ne`/`LE.le`/`LT.lt`/`GE.ge`/`GT.gt`/`Iff`, then falls
/// back to Lean's generic last-two-arguments rule for everything else.
///
/// REQUIRES: none.
/// ENSURES: Returns `Some((lhs, rhs))` whenever [`match_goal_rel`] or
/// [`get_calc_relation`] decomposes `e`; the two agree on the endpoints for
/// every relation the former recognizes.
#[must_use]
pub(crate) fn calc_endpoints(e: &Expr) -> Option<(Expr, Expr)> {
    if let Some((_, _, lhs, rhs, _)) = match_goal_rel(e) {
        return Some((lhs, rhs));
    }
    let (_, lhs, rhs) = get_calc_relation(e)?;
    Some((lhs, rhs))
}

/// The head constant of a calc step's relation, if it has one.
///
/// For `@List.Sublist α l₁ l₂` this is `List.Sublist`; for a bare user relation
/// `MyR a b` it is `MyR`. Used to find the relation's own transitivity lemma
/// (`<R>.trans`) — which is exactly the term Lean's own `Trans` instances are
/// built from (`instance : Trans (@Sublist α) Sublist Sublist := ⟨Sublist.trans⟩`).
///
/// REQUIRES: none.
/// ENSURES: Returns `Some(name)` iff `e` decomposes via [`get_calc_relation`]
/// and the resulting relation's head is a constant.
#[must_use]
pub(crate) fn calc_relation_head(e: &Expr) -> Option<Name> {
    let (rel, _, _) = get_calc_relation(e)?;
    match rel.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    }
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
