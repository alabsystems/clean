// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Goal-path orchestration for the compound `conv` handler.
//!
//! Separated from registration/dispatch to reduce churn on the hot
//! `builtins_phase3d_conv` module. Part of #2547.

use crate::tactic::conv_proof::lift_focus_eq_through_path;
use crate::tactic::{Goal, ProofState, TacticError};
use clean_parser::SurfaceTactic;

/// Run conv body on the current goal target with proof-producing boundary.
///
/// Part of #2519: produces an explicit equality proof (`old_target = new_target`)
/// from the conv body execution instead of using `replace_target_with_trusted_fallback`.
///
/// Architecture (modeled on Lean 4 `convert`/`convTarget`):
/// 1. Save the old target before running the conv body.
/// 2. Run the body in a sub-proof-state (which may navigate + rewrite).
/// 3. Reconstruct the new target from navigation path + rewritten focus.
/// 4. Lift the focused equality witness produced by the nested body through the
///    saved navigation path.
/// 5. Call `replace_target_eq` with the real proof — no `trustedArith`.
///
/// Falls back to `replace_target_def_eq` when the old and new targets are
/// definitionally equal (the free path that needs no proof).
///
/// The same focused-witness boundary is used for `conv at h`.
pub(super) fn eval_conv_goal(
    eval: &mut dyn crate::tactic::registry::TacticEval,
    ps: &mut ProofState,
    tacs: &[SurfaceTactic],
) -> Result<(), TacticError> {
    // Clone all data from the current goal upfront to release the borrow on `ps`.
    let (old_target, local_ctx, goal_meta_id, goal_tag) = {
        let goal = ps.current_goal().ok_or(TacticError::NoGoals)?;
        (
            goal.target.clone(),
            goal.local_ctx.clone(),
            goal.meta_id,
            goal.tag.clone(),
        )
    };

    let mut conv_ps =
        crate::tactic::builtins_phase3d_elab::create_sub_proof_state(ps, old_target.clone());

    super::run_conv_body(eval, &mut conv_ps, tacs)?;

    ps.merge_meta_state(&conv_ps);

    // Reconstruct the goal for type inference (needs the OLD target). Shared by
    // both the multi-focus congr tree and the single-focus path.
    let infer_goal = Goal {
        meta_id: goal_meta_id,
        target: old_target.clone(),
        local_ctx: local_ctx.clone(),
        tag: goal_tag.clone(),
    };

    // Multi-focus `conv => congr` path (#2477 Phase 4): recombine per-focus
    // equalities into one kernel-checked whole-application proof. If an outer
    // single-focus navigation path is also active (e.g. `arg -2; congr` focused
    // the equality's LHS first), lift the recombined congr proof through that
    // path so the candidate proves the WHOLE-target equality.
    if let Some(crate::tactic::core::ConvNav::Congr {
        original,
        head,
        args,
    }) = conv_ps.conv_focus_tree.as_ref()
    {
        // The sub-application equality `original = new_app` from the congr fold.
        let new_app = crate::tactic::conv_congr_recombine::rebuild_app(args, head);
        let outer_path = conv_ps
            .conv_nav
            .as_ref()
            .map(|(_, path)| path.clone())
            .unwrap_or_default();
        // The new WHOLE target: replace the focused sub-app in `old_target`.
        let new_target = if outer_path.is_empty() {
            new_app.clone()
        } else {
            crate::tactic::conv::ConvState::replace_at_position(&old_target, &outer_path, &new_app)
                .unwrap_or_else(|| new_app.clone())
        };

        match ps.replace_target_def_eq(new_target.clone()) {
            Ok(()) => return Ok(()),
            Err(TacticError::GoalMismatch(_)) => { /* need real proof */ }
            Err(e) => return Err(e),
        }

        let Some(congr_proof) = crate::tactic::conv_congr_recombine::recombine_foci(
            ps,
            &infer_goal,
            original,
            head,
            args,
        )?
        else {
            // No focus changed: defer to def-eq (already attempted) or unchanged.
            return Ok(());
        };

        // Lift the sub-application equality through the outer navigation path.
        let whole_eq_proof = lift_focus_eq_through_path(
            ps,
            &infer_goal,
            &old_target,
            &outer_path,
            original,
            &new_app,
            congr_proof,
        )?
        .ok_or_else(|| TacticError::InvalidTarget {
            tactic: "conv".into(),
            detail: "conv congr: failed to lift the recombined proof through the navigation path"
                .into(),
        })?;
        return ps.replace_target_eq(new_target, whole_eq_proof);
    }

    let Some(conv_goal) = conv_ps.current_goal() else {
        return Ok(());
    };

    // Reconstruct the new whole-target from navigation path + rewritten focus.
    let new_focus = conv_goal.target.clone();
    let new_target = super::reconstruct_conv_target(&conv_ps, &new_focus);

    // Fast path: definitional equality needs no proof.
    match ps.replace_target_def_eq(new_target.clone()) {
        Ok(()) => return Ok(()),
        Err(TacticError::GoalMismatch(_)) => { /* need real proof — fall through */ }
        Err(e) => return Err(e),
    }

    let nav_path = conv_ps
        .conv_nav
        .as_ref()
        .map(|(_, path)| path.clone())
        .unwrap_or_default();
    let focus_witness = super::require_conv_focus_witness(
        &conv_ps,
        "conv goal proof carry: conv body changed the target without recording a focus equality witness",
    )?;

    let target_eq_proof = lift_focus_eq_through_path(
        ps,
        &infer_goal,
        &old_target,
        &nav_path,
        &focus_witness.before,
        &focus_witness.after,
        focus_witness.eq_proof,
    )?
    .ok_or_else(|| TacticError::InvalidTarget {
        tactic: "conv".into(),
        detail: "conv goal proof carry: failed to rebuild the navigation path".into(),
    })?;

    ps.replace_target_eq(new_target, target_eq_proof)
}
