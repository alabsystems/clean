// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reduce a registered match compiler application by its actual definition.
//! The temporary alternatives are opaque locals: reduction must select one
//! before its original branch is installed. This mirrors Lean's
//! `reduceMatcher?`, without recognizing names or introducing an evaluator.

use clean_kernel::{Expr, ExprKind};

use super::{
    binder::open_binder, budget::SimpBudget, match_target::successor_from_addition,
    reduce::beta_reduce,
};
use crate::tactic::core::{Goal, ProofState};
use crate::tactic::op_projection::reduce_op_projection_head_instances;

pub(super) fn reduce_matcher_app(
    state: &ProofState,
    goal: &Goal,
    expression: &Expr,
    budget: &SimpBudget,
) -> Option<Expr> {
    let ExprKind::Const(name, levels) = expression.get_app_fn().kind() else {
        return None;
    };
    let info = state.env().get_matcher_info(name)?;
    let arity = info.arity()?;
    let arguments = expression.get_app_args();
    if arguments.len() < arity || info.alt_num_params.is_empty() || !budget.charge_attempt() {
        return None;
    }
    let declaration = state.env().get_const(name)?;
    if declaration.level_params.len() != levels.len() {
        return None;
    }
    let prefix_len = info.num_params as usize + 1 + info.num_discrs as usize;
    let prefix = Expr::apps(
        expression.get_app_fn().clone(),
        arguments[..prefix_len].iter().map(|a| (*a).clone()),
    );
    let mut telescope = state.infer_type_strict(goal, &prefix).ok()?;
    let mut scope = goal.clone();
    let mut alternatives = Vec::with_capacity(info.alt_num_params.len());
    for _ in &info.alt_num_params {
        if !budget.tick() {
            return None;
        }
        telescope = state.whnf(&scope, &telescope);
        let ExprKind::Pi(_, domain, body) = telescope.kind() else {
            return None;
        };
        let opened = open_binder(&scope, domain, body);
        alternatives.push(opened.fvar);
        telescope = opened.body;
        scope = opened.goal;
    }
    let body = declaration
        .value
        .as_ref()?
        .instantiate_level_params_direct(&declaration.level_params, levels);
    // Lean's reduceRec exposes one constructor of a positive Nat offset.
    // Preserve parameters, motive and alternatives. Only the probe sees the
    // checked successor view of a discriminant; final checks use the original.
    let discr_start = info.num_params as usize + 1;
    let discriminants = arguments[discr_start..prefix_len].iter().map(|discr| {
        successor_from_addition(
            state,
            goal,
            discr,
            budget,
            reduce_op_projection_head_instances,
        )
        .unwrap_or_else(|| (*discr).clone())
    });
    let probe = Expr::apps(
        body,
        arguments[..discr_start]
            .iter()
            .map(|a| (*a).clone())
            .chain(discriminants)
            .chain(alternatives.iter().copied().map(Expr::fvar)),
    );
    if !budget.admit(&probe, format_args!("preparing matcher {name}"))
        || !budget.admit_before_zeta(&probe, format_args!("preparing matcher {name}"))
    {
        return None;
    }
    // Selection must not unfold arbitrary semireducible discriminant
    // definitions merely because the kernel can. Reuse the existing bounded
    // reducible+instances WHNF; unsupported matcher auxiliaries stay stuck.
    let selected = state.whnf_instances(&scope, &probe);
    let ExprKind::FVar(selected_id) = selected.get_app_fn().kind() else {
        return None;
    };
    let selected_index = alternatives.iter().position(|id| id == selected_id)?;
    let fields = selected.get_app_args();
    if fields.len() != info.alt_num_params[selected_index] as usize {
        return None;
    }
    let result = beta_reduce(&Expr::apps(
        arguments[prefix_len + selected_index].clone(),
        fields.iter().map(|field| (*field).clone()).chain(
            arguments[arity..]
                .iter()
                .map(|argument| (*argument).clone()),
        ),
    ));
    if !budget.admit(&result, format_args!("reducing matcher {name}")) {
        return None;
    }
    // Full checking in the original context rejects a leaked placeholder or
    // an ill-typed branch. Definitional equality checks the actual body, so
    // even forged metadata cannot grant a rewrite the kernel does not admit.
    let original_type = state.infer_type_strict(goal, expression).ok()?;
    state
        .check_type_strict(goal, &result, &original_type)
        .ok()?;
    state.is_def_eq(goal, expression, &result).then_some(result)
}
