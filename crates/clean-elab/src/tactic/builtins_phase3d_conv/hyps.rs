// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hypothesis-path orchestration for the compound `conv` handler.
//!
//! Separated from registration/dispatch to reduce churn on the hot
//! `builtins_phase3d_conv` module. Part of #2547.

use crate::tactic::conv_proof::{infer_sort_level, lift_focus_eq_through_path};
use crate::tactic::{Goal, ProofState, TacticError};
use clean_kernel::{Expr, Name};
use clean_parser::SurfaceTactic;

fn build_hyp_cast_expr(
    ps: &ProofState,
    goal: &Goal,
    old_ty: &Expr,
    new_ty: &Expr,
    eq_proof: Expr,
    hyp_fvar: clean_kernel::FVarId,
) -> Result<Expr, TacticError> {
    let alpha = ps.infer_type(goal, old_ty)?;
    let sort_level = infer_sort_level(
        ps,
        goal,
        &alpha,
        "conv at: cannot infer Eq.subst universe for hypothesis cast",
    )?;
    let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![sort_level]);
    let cast = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(eq_subst, alpha.clone()),
                    Expr::lam(clean_kernel::BinderInfo::Default, alpha, Expr::bvar(0)),
                ),
                old_ty.clone(),
            ),
            new_ty.clone(),
        ),
        eq_proof,
    );
    Ok(Expr::app(cast, Expr::fvar(hyp_fvar)))
}

/// Run conv body on each named hypothesis.
///
/// Part of #2511: reconstructs the full hypothesis type when conv
/// navigation was used in the body and replaces the local declaration
/// through the proof-carrying local-ops API.
pub(super) fn eval_conv_hyps(
    eval: &mut dyn crate::tactic::registry::TacticEval,
    ps: &mut ProofState,
    names: &[String],
    tacs: &[SurfaceTactic],
) -> Result<(), TacticError> {
    for name in names {
        let (old_hyp_ty, local_ctx, hyp_fvar, goal_meta_id, goal_tag) = {
            let goal = ps.current_goal().ok_or(TacticError::NoGoals)?;
            let decl = goal
                .local_ctx
                .iter()
                .find(|d| d.name == *name)
                .ok_or_else(|| TacticError::HypothesisNotFound(format!("conv at: '{name}'")))?;
            (
                decl.ty.clone(),
                goal.local_ctx.clone(),
                decl.fvar,
                goal.meta_id,
                goal.tag.clone(),
            )
        };

        let mut conv_ps =
            crate::tactic::builtins_phase3d_elab::create_sub_proof_state(ps, old_hyp_ty.clone());

        super::run_conv_body(eval, &mut conv_ps, tacs)?;

        ps.merge_meta_state(&conv_ps);
        let Some(conv_goal) = conv_ps.current_goal() else {
            continue;
        };

        let new_focus = conv_goal.target.clone();
        let new_hyp_ty = super::reconstruct_conv_target(&conv_ps, &new_focus);

        match ps.replace_local_decl_def_eq(hyp_fvar, new_hyp_ty.clone()) {
            Ok(()) => continue,
            Err(TacticError::GoalMismatch(_)) => {}
            Err(err) => return Err(err),
        }

        let nav_path = conv_ps
            .conv_nav
            .as_ref()
            .map(|(_, path)| path.clone())
            .unwrap_or_default();
        let focus_witness = super::require_conv_focus_witness(
            &conv_ps,
            "conv at: body changed the hypothesis without recording a focus equality witness",
        )?;

        let infer_goal = Goal {
            meta_id: goal_meta_id,
            target: old_hyp_ty.clone(),
            local_ctx: local_ctx.clone(),
            tag: goal_tag.clone(),
        };
        let hyp_ty_eq_proof = lift_focus_eq_through_path(
            ps,
            &infer_goal,
            &old_hyp_ty,
            &nav_path,
            &focus_witness.before,
            &focus_witness.after,
            focus_witness.eq_proof,
        )?
        .ok_or_else(|| TacticError::InvalidTarget {
            tactic: "conv at".into(),
            detail: "conv at: proof carry failed to rebuild the navigation path".into(),
        })?;

        let hyp_cast = build_hyp_cast_expr(
            ps,
            &infer_goal,
            &old_hyp_ty,
            &new_hyp_ty,
            hyp_ty_eq_proof,
            hyp_fvar,
        )?;
        ps.replace_local_decl_with_cast(hyp_fvar, new_hyp_ty, hyp_cast)?;
    }
    Ok(())
}
