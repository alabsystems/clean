// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic-mode `match` lowering for phase 3D elab registrations.

use std::collections::HashSet;
use std::sync::Arc;

use super::registry::{CompoundTacticEntry, RefinePendingGoal, RefinePendingLocal};
use super::{LocalDecl, TacticError};
use crate::unify::MetaState;
use clean_kernel::{Environment, Expr, ExprKind, Name};
use clean_parser::{
    Span, SurfaceArg, SurfaceExpr, SurfaceLit, SurfaceMatchArm, SurfacePattern, SurfaceTactic,
    TacticMatchArm,
};

/// `match discrs with | pat => tacs | ...` — tactic-mode pattern matching.
///
/// Lowers tactic `match` to term `match` with one hole per arm, then routes the
/// resulting subgoals through synthetic `case` tactics.
///
/// Fixes #1848: previously ran first arm unconditionally.
pub(crate) fn compound_match() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "match".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Match(span, discrs, arms) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "match".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };

            if arms.is_empty() {
                return if ps.goals.is_empty() {
                    Ok(())
                } else {
                    Err(TacticError::InvalidTarget {
                        tactic: "match".into(),
                        detail: "no arms provided".into(),
                    })
                };
            }

            let discr_exprs: Vec<Expr> = discrs
                .iter()
                .map(|d| eval.elaborate(d))
                .collect::<Result<_, _>>()?;
            let existing_metas: HashSet<_> = eval.metas().iter().map(|(id, _)| id).collect();
            let case_order = match discr_exprs.as_slice() {
                [discr] => planned_case_order(ps.env(), &eval.infer_type(discr)?, arms),
                _ => (0..arms.len()).collect(),
            };
            let match_expr = build_tactic_match_expr(*span, discrs, arms);
            let refined = eval.elaborate_refine(ps, &match_expr)?;
            let pending_goals = if refined.pending_goals.len() == case_order.len() {
                refined.pending_goals.clone()
            } else {
                let current_goal = ps.current_goal().ok_or(TacticError::NoGoals)?;
                recover_pending_goals_from_new_metas(
                    eval.metas(),
                    &current_goal.target,
                    &current_goal.local_ctx,
                    &existing_metas,
                )
            };

            if pending_goals.len() != case_order.len() {
                return Err(TacticError::InvalidTarget {
                    tactic: "match".into(),
                    detail: format!(
                        "match elaborated to {} pending goal(s) for {} tactic arm(s)",
                        pending_goals.len(),
                        case_order.len()
                    ),
                });
            }

            let tags: Vec<Option<String>> = (0..pending_goals.len())
                .map(|idx| Some(format!("match_{}", idx + 1)))
                .collect();
            super::term_close::refine_elaborated_from_pending_with_tags(
                ps,
                refined.term,
                eval.metas(),
                &pending_goals,
                &tags,
            )?;

            for (idx, arm_idx) in case_order.into_iter().enumerate() {
                let case_tactic = SurfaceTactic::Case(
                    arms[arm_idx].span,
                    format!("match_{}", idx + 1),
                    Vec::new(),
                    arms[arm_idx].tactics.clone(),
                );
                eval.eval(ps, &case_tactic)?;
            }

            Ok(())
        }),
    }
}

fn recover_pending_goals_from_new_metas(
    metas: &MetaState,
    goal_target: &Expr,
    goal_locals: &[LocalDecl],
    existing: &HashSet<crate::unify::MetaId>,
) -> Vec<RefinePendingGoal> {
    let goal_target = metas.instantiate_levels(&metas.instantiate(goal_target));
    let goal_fvars: HashSet<_> = goal_locals.iter().map(|decl| decl.fvar).collect();
    let mut recovered = metas
        .iter()
        .filter(|(meta_id, meta)| {
            !existing.contains(meta_id)
                && meta.assignment.is_none()
                && metas.instantiate_levels(&metas.instantiate(&meta.ty)) == goal_target
        })
        .map(|(meta_id, meta)| RefinePendingGoal {
            meta_id,
            locals: meta
                .locals
                .iter()
                .filter(|(_, fvar, _)| !goal_fvars.contains(fvar))
                .map(|(name, fvar, ty)| RefinePendingLocal {
                    name: name.clone(),
                    fvar: *fvar,
                    ty: metas.instantiate_levels(&metas.instantiate(ty)),
                })
                .collect(),
            // The `match` tactic supplies its own `match_N` tags via the
            // `_with_tags` slice, which overrides this; recovered goals carry no
            // synthetic-hole name.
            tag: None,
        })
        .collect::<Vec<_>>();
    recovered.sort_by_key(|goal| goal.meta_id.as_u64());
    recovered
}

fn build_tactic_match_expr(
    span: Span,
    discrs: &[SurfaceExpr],
    arms: &[TacticMatchArm],
) -> SurfaceExpr {
    // RIGHT-nested tuple fold — `a, b, c` packs as `Prod.mk a (Prod.mk b c)` —
    // matching the right-nested tuple PATTERNS the arm parser produces
    // (`(p, q, r)` → `Prod.mk p (Prod.mk q r)`), and the term-mode `match_body`
    // scrutinee fold. The previous LEFT fold only agreed for exactly two
    // discriminants (brick B05, docs/plans/GAP_SWEEP_2026-07-09.md).
    let scrutinee = discrs
        .iter()
        .cloned()
        .rev()
        .reduce(|acc, expr| {
            let pair_span = expr.span().merge(acc.span());
            SurfaceExpr::App(
                pair_span,
                Box::new(SurfaceExpr::Ident(pair_span, "Prod.mk".to_string())),
                vec![SurfaceArg::positional(expr), SurfaceArg::positional(acc)],
            )
        })
        .expect("tactic match requires at least one discriminant");
    let arms = arms
        .iter()
        .map(|arm| SurfaceMatchArm {
            span: arm.span,
            pattern: arm.pattern.clone(),
            body: SurfaceExpr::Hole(arm.span),
        })
        .collect();
    SurfaceExpr::Match(span, None, Box::new(scrutinee), arms)
}

fn planned_case_order(env: &Environment, discr_ty: &Expr, arms: &[TacticMatchArm]) -> Vec<usize> {
    type_name_of(discr_ty)
        .and_then(|type_name| ctor_order_case_plan(env, &type_name, arms))
        .unwrap_or_else(|| (0..arms.len()).collect())
}

fn type_name_of(expr: &Expr) -> Option<String> {
    match &**expr.get_app_fn() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn ctor_order_case_plan(
    env: &Environment,
    type_name: &str,
    arms: &[TacticMatchArm],
) -> Option<Vec<usize>> {
    let ctor_order = &env
        .get_inductive(&Name::from_string(type_name))?
        .constructor_names;
    let mut specific = Vec::new();
    let mut wildcard = None;

    for (idx, arm) in arms.iter().enumerate() {
        match &arm.pattern {
            SurfacePattern::Wildcard => {
                if wildcard.is_some() || idx + 1 != arms.len() {
                    return None;
                }
                wildcard = Some(idx);
            }
            _ => {
                let full_ctor = top_level_ctor_target_name(env, type_name, &arm.pattern)?;
                if specific.iter().any(|(name, _)| name == &full_ctor) {
                    return None;
                }
                specific.push((full_ctor, idx));
            }
        }
    }

    let mut ordered = Vec::with_capacity(ctor_order.len());
    for ctor_name in ctor_order {
        let ctor_name = ctor_name.to_string();
        if let Some((_, idx)) = specific.iter().find(|(name, _)| name == &ctor_name) {
            ordered.push(*idx);
            continue;
        }
        if let Some(idx) = wildcard {
            ordered.push(idx);
            continue;
        }
        return None;
    }

    if specific
        .iter()
        .any(|(name, _)| !ctor_order.iter().any(|ctor| ctor.to_string() == *name))
    {
        return None;
    }

    let mut unique = Vec::new();
    for idx in ordered {
        if !unique.contains(&idx) {
            unique.push(idx);
        }
    }
    Some(unique)
}

fn top_level_ctor_target_name(
    env: &Environment,
    type_name: &str,
    pattern: &SurfacePattern,
) -> Option<String> {
    match pattern {
        SurfacePattern::Ctor(ctor_name, _) => Some(if ctor_name.contains('.') {
            ctor_name.clone()
        } else {
            format!("{type_name}.{ctor_name}")
        }),
        SurfacePattern::Lit(SurfaceLit::Nat(0)) => Some(format!("{type_name}.zero")),
        SurfacePattern::Lit(SurfaceLit::Nat(_)) | SurfacePattern::NumeralAdd(_, _) => {
            Some(format!("{type_name}.succ"))
        }
        SurfacePattern::Var(name) => {
            let full_ctor = if name.contains('.') {
                name.clone()
            } else {
                format!("{type_name}.{name}")
            };
            env.get_constructor(&Name::from_string(&full_ctor))
                .filter(|info| info.num_fields == 0)
                .map(|_| full_ctor)
        }
        SurfacePattern::As(_, inner) => top_level_ctor_target_name(env, type_name, inner),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
