// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-carry helpers for focused `conv` rewrites.

use clean_kernel::expr::ExprKind;
use clean_kernel::tc::whnf_proof::{CongrArgArgs, EqProofBuilder};
use clean_kernel::{BinderInfo, Expr, Level};

use super::conv::ConvPosition;
use super::equality::abstract_over;
use super::simp::mk_eq_trans_expr;
use super::{Goal, ProofState, TacticError};
use crate::stack_safe;

struct CongrArgProofInputs<'a> {
    alpha: &'a Expr,
    beta: &'a Expr,
    a1: &'a Expr,
    a2: &'a Expr,
    motive: Expr,
    h: Expr,
    source_detail: &'static str,
    target_detail: &'static str,
}

pub(crate) struct ConvRewriteProofInputs<'a> {
    pub target: &'a Expr,
    pub path: &'a [ConvPosition],
    pub focus_before: &'a Expr,
    pub focus_after: &'a Expr,
    pub from: &'a Expr,
    pub to: &'a Expr,
    pub from_ty: &'a Expr,
    pub leaf_eq_proof: Expr,
}

/// Shift BVar(i) -> BVar(i+1) for i >= depth.
///
/// Delegates to the kernel's `Expr::lift_from` which uses `ExprFolderOpt`
/// for sharing-preserving traversal with O(1) metadata guards. Part of #2092.
fn shift_bvars_for_new_binder(expr: &Expr, depth: u32) -> Expr {
    expr.lift_from(depth, 1)
}

fn abstract_over_eq_arg(
    expr: &Expr,
    arg_idx: usize,
    rest: &[ConvPosition],
    depth: u32,
) -> Option<Expr> {
    stack_safe(|| {
        let args = expr.get_app_args();
        if args.len() <= arg_idx {
            return None;
        }

        let mut rebuilt = shift_bvars_for_new_binder(expr.get_app_fn(), depth);
        for (idx, arg) in args.into_iter().enumerate() {
            let new_arg = if idx == arg_idx {
                abstract_over_conv_path_at_depth(arg, rest, depth)?
            } else {
                shift_bvars_for_new_binder(arg, depth)
            };
            rebuilt = Expr::app(rebuilt, new_arg);
        }
        Some(rebuilt)
    })
}

pub(crate) fn abstract_over_conv_path(expr: &Expr, path: &[ConvPosition]) -> Option<Expr> {
    abstract_over_conv_path_at_depth(expr, path, 0)
}

fn abstract_over_conv_path_at_depth(
    expr: &Expr,
    path: &[ConvPosition],
    depth: u32,
) -> Option<Expr> {
    stack_safe(|| {
        if path.is_empty() {
            return Some(Expr::bvar(depth));
        }

        let (head, rest) = (&path[0], &path[1..]);
        match (head, expr.kind()) {
            (ConvPosition::Root, _) => abstract_over_conv_path_at_depth(expr, rest, depth),
            (ConvPosition::AppFn, ExprKind::App(f, a)) => Some(Expr::app(
                abstract_over_conv_path_at_depth(f, rest, depth)?,
                shift_bvars_for_new_binder(a, depth),
            )),
            (ConvPosition::AppArg, ExprKind::App(f, a)) => Some(Expr::app(
                shift_bvars_for_new_binder(f, depth),
                abstract_over_conv_path_at_depth(a, rest, depth)?,
            )),
            (ConvPosition::EqLhs, _) => abstract_over_eq_arg(expr, 1, rest, depth),
            (ConvPosition::EqRhs, _) => abstract_over_eq_arg(expr, 2, rest, depth),
            (ConvPosition::BinderBody, ExprKind::Lam(bi, ty, body)) => Some(Expr::lam(
                *bi,
                shift_bvars_for_new_binder(ty, depth),
                abstract_over_conv_path_at_depth(body, rest, depth + 1)?,
            )),
            (ConvPosition::BinderBody, ExprKind::Pi(bi, ty, body)) => Some(Expr::pi(
                *bi,
                shift_bvars_for_new_binder(ty, depth),
                abstract_over_conv_path_at_depth(body, rest, depth + 1)?,
            )),
            (ConvPosition::BinderType, ExprKind::Lam(bi, ty, body)) => Some(Expr::lam(
                *bi,
                abstract_over_conv_path_at_depth(ty, rest, depth)?,
                shift_bvars_for_new_binder(body, depth + 1),
            )),
            (ConvPosition::BinderType, ExprKind::Pi(bi, ty, body)) => Some(Expr::pi(
                *bi,
                abstract_over_conv_path_at_depth(ty, rest, depth)?,
                shift_bvars_for_new_binder(body, depth + 1),
            )),
            (ConvPosition::LetValue, ExprKind::Let(name, ty, val, body, non_dep)) => {
                Some(Expr::let_named(
                    name.clone(),
                    shift_bvars_for_new_binder(ty, depth),
                    abstract_over_conv_path_at_depth(val, rest, depth)?,
                    shift_bvars_for_new_binder(body, depth + 1),
                    *non_dep,
                ))
            }
            (ConvPosition::LetType, ExprKind::Let(name, ty, val, body, non_dep)) => {
                Some(Expr::let_named(
                    name.clone(),
                    abstract_over_conv_path_at_depth(ty, rest, depth)?,
                    shift_bvars_for_new_binder(val, depth),
                    shift_bvars_for_new_binder(body, depth + 1),
                    *non_dep,
                ))
            }
            (ConvPosition::LetBody, ExprKind::Let(name, ty, val, body, non_dep)) => {
                Some(Expr::let_named(
                    name.clone(),
                    shift_bvars_for_new_binder(ty, depth),
                    shift_bvars_for_new_binder(val, depth),
                    abstract_over_conv_path_at_depth(body, rest, depth + 1)?,
                    *non_dep,
                ))
            }
            _ => None,
        }
    })
}

pub(crate) fn infer_sort_level(
    state: &ProofState,
    goal: &Goal,
    ty: &Expr,
    detail: &'static str,
) -> Result<Level, TacticError> {
    state
        .infer_type(goal, ty)
        .ok()
        .and_then(|sort| match sort.kind() {
            ExprKind::Sort(level) => Some(level.clone()),
            _ => None,
        })
        .ok_or_else(|| TacticError::TypeCheckFailed(detail.into()))
}

fn mk_congr_arg_proof(
    state: &ProofState,
    goal: &Goal,
    inputs: CongrArgProofInputs<'_>,
) -> Result<Expr, TacticError> {
    Ok(EqProofBuilder::mk_congr_arg(CongrArgArgs {
        u: infer_sort_level(state, goal, inputs.alpha, inputs.source_detail)?,
        v: infer_sort_level(state, goal, inputs.beta, inputs.target_detail)?,
        alpha: inputs.alpha.clone(),
        beta: inputs.beta.clone(),
        a1: inputs.a1.clone(),
        a2: inputs.a2.clone(),
        f: Expr::lam(BinderInfo::Default, inputs.alpha.clone(), inputs.motive),
        h: inputs.h,
    }))
}

pub(crate) fn build_conv_rewrite_eq_proof(
    state: &ProofState,
    goal: &Goal,
    inputs: ConvRewriteProofInputs<'_>,
) -> Result<Option<Expr>, TacticError> {
    let focus_eq_proof =
        if inputs.focus_before == inputs.from && inputs.focus_after != inputs.focus_before {
            inputs.leaf_eq_proof
        } else {
            let focus_ty = state.infer_type(goal, inputs.focus_before)?;
            mk_congr_arg_proof(
                state,
                goal,
                CongrArgProofInputs {
                    alpha: inputs.from_ty,
                    beta: &focus_ty,
                    a1: inputs.from,
                    a2: inputs.to,
                    motive: abstract_over(inputs.focus_before, inputs.from),
                    h: inputs.leaf_eq_proof,
                    source_detail: "conv_rw: cannot infer source equality universe",
                    target_detail: "conv_rw: cannot infer focused expression universe",
                },
            )?
        };

    if inputs.path.is_empty() {
        return Ok(Some(focus_eq_proof));
    }

    let Some(motive) = abstract_over_conv_path(inputs.target, inputs.path) else {
        return Ok(None);
    };
    let focus_ty = state.infer_type(goal, inputs.focus_before)?;
    let target_ty = state.infer_type(goal, inputs.target)?;
    Ok(Some(mk_congr_arg_proof(
        state,
        goal,
        CongrArgProofInputs {
            alpha: &focus_ty,
            beta: &target_ty,
            a1: inputs.focus_before,
            a2: inputs.focus_after,
            motive,
            h: focus_eq_proof,
            source_detail: "conv_rw: cannot infer focused expression universe",
            target_detail: "conv_rw: cannot infer focused target universe",
        },
    )?))
}

pub(crate) fn chain_conv_focus_eq_proofs(
    state: &ProofState,
    goal: &Goal,
    first: &Expr,
    second: &Expr,
) -> Result<Expr, TacticError> {
    mk_eq_trans_expr(state, goal, first, second).ok_or_else(|| {
        TacticError::TypeCheckFailed(
            "conv_rw: failed to compose focused rewrite witnesses with Eq.trans".into(),
        )
    })
}

pub(crate) fn lift_focus_eq_through_path(
    state: &ProofState,
    goal: &Goal,
    target: &Expr,
    path: &[ConvPosition],
    focus_before: &Expr,
    focus_after: &Expr,
    focus_eq_proof: Expr,
) -> Result<Option<Expr>, TacticError> {
    if path.is_empty() {
        return Ok(Some(focus_eq_proof));
    }

    let Some(motive) = abstract_over_conv_path(target, path) else {
        return Ok(None);
    };
    let focus_ty = state.infer_type(goal, focus_before)?;
    let target_ty = state.infer_type(goal, target)?;
    Ok(Some(mk_congr_arg_proof(
        state,
        goal,
        CongrArgProofInputs {
            alpha: &focus_ty,
            beta: &target_ty,
            a1: focus_before,
            a2: focus_after,
            motive,
            h: focus_eq_proof,
            source_detail: "conv_rw: cannot infer focused expression universe",
            target_detail: "conv_rw: cannot infer focused target universe",
        },
    )?))
}
