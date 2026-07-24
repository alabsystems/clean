// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use super::proof_carry::infer_sort_level;
use super::{match_equality, Goal, ProofState, TacticError, TacticResult};
use crate::unify::MetaState;

fn mk_eq_expr(eq_level: Level, ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![eq_level]), ty),
            lhs,
        ),
        rhs,
    )
}

fn mk_apply_fun_injective_goal(
    state: &ProofState,
    goal: &Goal,
    func: &Expr,
    domain_ty: &Expr,
    codomain_ty: &Expr,
) -> Result<Expr, TacticError> {
    let domain_level = infer_sort_level(
        state,
        goal,
        domain_ty,
        "apply_fun_goal: cannot infer injectivity domain universe",
    )?;
    let codomain_level = infer_sort_level(
        state,
        goal,
        codomain_ty,
        "apply_fun_goal: cannot infer injectivity codomain universe",
    )?;

    if let Some(function_injective) = state
        .env()
        .get_const(&Name::from_string("Function.Injective"))
    {
        if function_injective.value.is_some() && function_injective.is_reducible {
            return Ok(Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Function.Injective"),
                            vec![domain_level.clone(), codomain_level.clone()],
                        ),
                        domain_ty.clone(),
                    ),
                    codomain_ty.clone(),
                ),
                func.clone(),
            ));
        }
    }

    let a1 = Expr::bvar(1);
    let a2 = Expr::bvar(0);
    let fa1_eq_fa2 = mk_eq_expr(
        codomain_level,
        codomain_ty.clone(),
        Expr::app(func.clone(), a1.clone()),
        Expr::app(func.clone(), a2.clone()),
    );
    let a1_eq_a2 = mk_eq_expr(domain_level, domain_ty.clone(), a1, a2);

    Ok(Expr::pi(
        BinderInfo::StrictImplicit,
        domain_ty.clone(),
        Expr::pi(
            BinderInfo::StrictImplicit,
            domain_ty.clone(),
            Expr::pi(BinderInfo::Default, fa1_eq_fa2, a1_eq_a2.lift(1)),
        ),
    ))
}

pub(super) fn apply_fun_goal(state: &mut ProofState, func: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);
    let func_ty = state.whnf(&goal, &state.infer_type(&goal, &func)?);
    if let ExprKind::Pi(_, _, codomain) = func_ty.kind() {
        if codomain.has_loose_bvars() {
            return Err(TacticError::GoalMismatch(
                "apply_fun_goal: dependent functions are not supported".into(),
            ));
        }
    }

    let (domain_ty, lhs, rhs, _levels) = match_equality(&target)
        .map_err(|_| TacticError::GoalMismatch("goal must be an equality".into()))?;

    let new_lhs = Expr::app(func.clone(), lhs.clone());
    let new_rhs = Expr::app(func.clone(), rhs.clone());
    let result_ty = state.infer_type(&goal, &new_lhs)?;
    let rhs_result_ty = state.infer_type(&goal, &new_rhs)?;
    if !state.is_def_eq(&goal, &result_ty, &rhs_result_ty) {
        return Err(TacticError::TypeMismatch {
            expected: format!("{result_ty:?}"),
            actual: format!("{rhs_result_ty:?}"),
        });
    }
    let result_level = infer_sort_level(
        state,
        &goal,
        &result_ty,
        "apply_fun_goal: cannot infer equality target universe",
    )?;
    let new_target = mk_eq_expr(result_level, result_ty.clone(), new_lhs, new_rhs);
    let injective_goal = mk_apply_fun_injective_goal(state, &goal, &func, &domain_ty, &result_ty)?;

    let new_eq_meta_id = state.fresh_meta(new_target.clone());
    let inj_meta_id = state.fresh_meta(injective_goal.clone());
    let new_eq_meta = Expr::fvar(MetaState::to_fvar(new_eq_meta_id));
    let inj_meta = Expr::fvar(MetaState::to_fvar(inj_meta_id));
    let old_goal_proof = Expr::app(Expr::app(Expr::app(inj_meta, lhs), rhs), new_eq_meta);

    let local_ctx = goal.local_ctx.clone();
    let tag = goal.tag.clone();
    state.close_goal(&goal, old_goal_proof)?;
    state.goals.push_front(Goal {
        meta_id: inj_meta_id,
        target: injective_goal,
        local_ctx: local_ctx.clone(),
        tag: tag.clone(),
    });
    state.goals.push_front(Goal {
        meta_id: new_eq_meta_id,
        target: new_target,
        local_ctx,
        tag,
    });

    Ok(())
}
