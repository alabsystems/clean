// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic entry points for field normalization.
//!
//! Uses the pure normalization from `field.rs` and integrates with `ProofState`.
//! Split from `field.rs` per 500-line limit (#307).

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::field::{expr_to_signed_int, field_normalize, is_div_head, is_inv_head, is_pow_head};
use super::field_denom::{clear_field_denominators, field_exprs_equal, field_has_denominator};
use super::{
    assumption, field_simp, match_equality, rfl, ring, ring_nf, Goal, ProofState, TacticError,
    TacticResult,
};
use crate::stack_safe;

fn app_head_name(expr: &Expr) -> Option<String> {
    match expr.strip_mdata().get_app_fn().strip_mdata().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn has_top_level_division(expr: &Expr) -> bool {
    app_head_name(expr).is_some_and(|name| is_div_head(&name))
}

fn collect_denominator_exprs(expr: &Expr, denoms: &mut Vec<Expr>) {
    stack_safe(|| {
        let expr = expr.strip_mdata();
        match expr.kind() {
            ExprKind::App(_, _) => {
                let args = expr.get_app_args();
                if let Some(name) = app_head_name(expr) {
                    if is_div_head(&name) && args.len() >= 2 {
                        let numer = (*args[args.len() - 2]).clone();
                        let denom = (*args[args.len() - 1]).clone();
                        denoms.push(denom.clone());
                        collect_denominator_exprs(&numer, denoms);
                        collect_denominator_exprs(&denom, denoms);
                        return;
                    }
                    if is_inv_head(&name) && !args.is_empty() {
                        let inner = (*args[args.len() - 1]).clone();
                        denoms.push(inner.clone());
                        collect_denominator_exprs(&inner, denoms);
                        return;
                    }
                    if is_pow_head(&name) && args.len() >= 2 {
                        let base = (*args[args.len() - 2]).clone();
                        let exp = (*args[args.len() - 1]).clone();
                        if matches!(expr_to_signed_int(&exp), Some(n) if n < 0) {
                            denoms.push(base.clone());
                        }
                        collect_denominator_exprs(&base, denoms);
                        collect_denominator_exprs(&exp, denoms);
                        return;
                    }
                }
                for arg in args {
                    collect_denominator_exprs(arg, denoms);
                }
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                collect_denominator_exprs(ty, denoms);
                collect_denominator_exprs(body, denoms);
            }
            ExprKind::Let(_, ty, value, body, _) => {
                collect_denominator_exprs(ty, denoms);
                collect_denominator_exprs(value, denoms);
                collect_denominator_exprs(body, denoms);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                collect_denominator_exprs(inner, denoms);
            }
            _ => {}
        }
    })
}

fn best_effort_zero_expr(state: &mut ProofState, goal: &Goal, ty: &Expr) -> Option<Expr> {
    for decl in &goal.local_ctx {
        if decl.name != "zero" {
            continue;
        }
        let decl_ty = state.metas().instantiate(&decl.ty);
        if state.is_def_eq(goal, &decl_ty, ty) {
            return Some(Expr::fvar(decl.fvar));
        }
    }

    let mut candidate_names = Vec::new();
    if let ExprKind::Const(name, _) = ty.strip_mdata().get_app_fn().strip_mdata().kind() {
        candidate_names.push(format!("{}.zero", name));
    }
    candidate_names.extend(
        ["zero", "Nat.zero", "Int.zero", "Rat.zero", "Real.zero"]
            .into_iter()
            .map(str::to_string),
    );

    candidate_names
        .into_iter()
        .find(|candidate| {
            state
                .env()
                .get_const(&Name::from_string(candidate))
                .is_some()
        })
        .map(|candidate| state.mk_const_str(&candidate))
}

fn make_nonzero_goal(state: &mut ProofState, goal: &Goal, ty: &Expr, denom: Expr) -> Option<Goal> {
    let zero = best_effort_zero_expr(state, goal, ty)?;
    let level = match state.infer_type(goal, ty).ok()?.kind() {
        ExprKind::Sort(level) => level.clone(),
        _ => return None,
    };

    let ne_target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Ne"), vec![level]),
                ty.clone(),
            ),
            denom,
        ),
        zero,
    );
    let meta_id = state.fresh_meta_in_context(ne_target.clone(), &goal.local_ctx);

    Some(Goal {
        meta_id,
        target: ne_target,
        local_ctx: goal.local_ctx.clone(),
        tag: Some("field_simp:ne_zero".to_string()),
    })
}

fn push_best_effort_nonzero_goals(state: &mut ProofState, goal: &Goal, ty: &Expr, exprs: &[&Expr]) {
    let mut denoms = Vec::new();
    for expr in exprs {
        collect_denominator_exprs(expr, &mut denoms);
    }

    let mut unique_denoms = Vec::new();
    for denom in denoms {
        if !unique_denoms.iter().any(|seen: &Expr| seen == &denom) {
            unique_denoms.push(denom);
        }
    }

    for denom in unique_denoms {
        if let Some(side_goal) = make_nonzero_goal(state, goal, ty, denom) {
            state.goals.push_back(side_goal);
        }
    }
}

fn try_discharge_field_side_goals(state: &mut ProofState) {
    while let Some(goal) = state.current_goal() {
        if goal.tag.as_deref() != Some("field_simp:ne_zero") {
            break;
        }
        if assumption(state).is_err() {
            break;
        }
    }
}

/// Best-effort field normalization tactic.
///
/// This first reuses `field_simp` for the top-level rewrite shapes it already
/// knows how to justify. When that path does not apply, it falls back to pure
/// symbolic normalization plus denominator tracking.
///
/// # Algorithm
/// 1. If no field operations (Div/Inv), delegate to `ring`.
/// 2. If top-level division, try `field_simp` (proof-carrying).
/// 3. Check symbolic equality after clearing denominators.
/// 4. Push nonzero side goals for each denominator.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On Ok, the main goal is closed or simplified.
/// ENSURES: Side goals for `≠ 0` may remain open.
pub(crate) fn field_normalize_tactic(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas().instantiate(&goal.target);

    let (ty, lhs, rhs, _levels) = match_equality(&target)
        .map_err(|_| TacticError::GoalMismatch("field: goal must be an equality".to_string()))?;

    let lhs_norm = field_normalize(&lhs);
    let rhs_norm = field_normalize(&rhs);

    if !field_has_denominator(&lhs_norm) && !field_has_denominator(&rhs_norm) {
        return ring(state);
    }

    // Try proof-carrying field_simp for top-level division shapes
    if has_top_level_division(&lhs) || has_top_level_division(&rhs) {
        let snapshot = state.clone();
        if field_simp(state).is_ok() {
            let _ = ring_nf(state).or_else(|_| ring(state));
            try_discharge_field_side_goals(state);
            return Ok(());
        }
        *state = snapshot;
    }

    // Fall back to symbolic equality check
    if field_exprs_equal(&lhs_norm, &rhs_norm) {
        if rfl(state).is_ok() || ring_nf(state).is_ok() || ring(state).is_ok() {
            push_best_effort_nonzero_goals(state, &goal, &ty, &[&lhs, &rhs]);
            try_discharge_field_side_goals(state);
            return Ok(());
        }

        return Err(TacticError::ArithmeticFailed {
            tactic: "field".to_string(),
            reason: format!(
                "symbolic field normalization matched, but no proof-producing rewrite is \
                 available for this goal shape\n  LHS: {lhs_norm:?}\n  RHS: {rhs_norm:?}"
            ),
        });
    }

    let (lhs_cleared, rhs_cleared) = clear_field_denominators(&lhs_norm, &rhs_norm);
    Err(TacticError::ArithmeticFailed {
        tactic: "field".to_string(),
        reason: format!(
            "normalized forms differ after clearing denominators\n  LHS: {lhs_norm:?}\n  RHS: \
             {rhs_norm:?}\n  Cleared LHS: {lhs_cleared:?}\n  Cleared RHS: {rhs_cleared:?}"
        ),
    })
}
