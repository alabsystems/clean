// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended conv navigation commands (#3082)
//!
//! Split from `conv.rs` per the 500-line limit (#307).
//! Provides:
//! - `conv_ext` - Enter a binder body, introducing the bound variable
//! - `conv_congr` - Enter all arguments of an application simultaneously
//! - `conv_change` - Replace the focused expression with a definitionally equal one
//! - `eval_conv` - Programmatic entry point for conv tactic mode

use clean_kernel::expr::ExprKind;
use clean_kernel::Expr;

use super::conv::ConvState;
use super::core::{ConvFocus, ConvNav};
use super::{Goal, LocalDecl, ProofState, TacticError, TacticResult};

/// Enter a binder body in conv mode, introducing the bound variable into scope.
///
/// In Lean 4, `ext x` inside a `conv` block enters a lambda/forall binder body,
/// introducing the bound variable as a free variable `x` in the local context.
/// This allows rewriting within the binder body while the variable is in scope.
///
/// REQUIRES: current goal target is a Lam or Pi expression
///
/// ENSURES: on Ok, the goal target is the binder body with BVar(0) replaced by
/// a fresh FVar named `var_name`, and the local context has a new binding for
/// `var_name` with the binder's domain type
///
/// ENSURES: on Err, proof state is unchanged
pub fn conv_ext(state: &mut ProofState, var_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    let (binder_ty, body) = match target.kind() {
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            ((**ty).clone(), (**body).clone())
        }
        _ => {
            return Err(TacticError::InvalidTarget {
                tactic: "conv ext".into(),
                detail: "goal is not a lambda or forall expression".into(),
            });
        }
    };

    // Create a fresh free variable for the bound variable
    let fvar_id = state.fresh_fvar();
    let fvar = Expr::fvar(fvar_id);

    // Substitute BVar(0) with the fresh FVar in the body
    let opened_body = body.instantiate(&fvar);

    // Add the new variable to the local context
    let mut new_local_ctx = goal.local_ctx.clone();
    new_local_ctx.push(LocalDecl {
        name: var_name.to_string(),
        fvar: fvar_id,
        ty: binder_ty,
        value: None,
    });

    // Binder navigation is scratch-state focus bookkeeping, not a proof that
    // the original metavariable changed type or acquired a new local.  Mint a
    // new scratch metavariable with the exact opened context rather than
    // widening and retargeting the existing obligation in place.
    let goal = state.pop_current_goal()?;
    let scratch_meta_id = state.fresh_meta_in_context(opened_body.clone(), &new_local_ctx);
    state.goals.push_front(Goal {
        meta_id: scratch_meta_id,
        target: opened_body,
        local_ctx: new_local_ctx,
        tag: goal.tag,
    });

    Ok(())
}

/// Open all components of the focused application in conv mode (`conv => congr`).
///
/// In Lean 4, `congr` inside a `conv` block opens the components of the focused
/// application so each can be independently rewritten, with the per-component
/// equalities glued back together by `congr`/`congrArg`/`congrFun`. Clean now
/// implements the full N-ary form: `conv => congr` on `f a1 .. an` builds a
/// FOCUS TREE (`ConvNav::Congr`, one `ConvFocus` per head + argument) on
/// `ps.conv_focus_tree`. Subsequent `arg i` selects a sub-focus, a rewrite
/// mutates only that focus's `after`/`eq_proof`, and the reconstruction
/// boundary recombines the per-focus equalities into ONE proof of the
/// whole-application equality via the left-fold in `conv_congr_recombine`.
///
/// SOUNDNESS: the tree only RECORDS per-focus equalities. The assembled
/// candidate proof is handed to `replace_target_eq`, which kernel-type-checks
/// it against `@Eq T old_target new_target` before any goal mutation (INV-4).
/// Untouched foci use `Eq.refl` (INV-5). Foci are consumed in SOURCE order and
/// the left-fold mirrors the kernel `App` nesting exactly (INV-1/INV-2), so no
/// argument is dropped or mis-positioned.
///
/// Each focus's `before` is captured here from the decomposed application
/// (`get_app_fn`/`get_app_args`, SOURCE order) with its kernel type cached via
/// `infer_type` (INV-3). Nesting is supported: `congr` ON a selected sub-focus
/// replaces that focus's leaf with its own children (recursion in the fold).
///
/// REQUIRES: current goal target is an application (ExprKind::App).
///
/// ENSURES: on Ok, `ps.conv_focus_tree` holds the opened focus tree and the
/// focus cursor is reset; the goal target is unchanged (selection happens via
/// `arg i`).
///
/// ENSURES: on Err(GoalMismatch), the goal is not an application; the proof
/// state is unchanged.
pub fn conv_congr(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    if !matches!(target.kind(), ExprKind::App(_, _)) {
        return Err(TacticError::GoalMismatch(
            "conv congr: goal is not an application".to_string(),
        ));
    }

    // If we are already inside a congr'd focus (cursor selected), nesting:
    // decompose the SELECTED focus into its own children (a sub-tree) and
    // descend the cursor into the last child.
    if let (Some(cursor), Some(ConvNav::Congr { .. })) = (
        state.conv_congr_cursor.clone(),
        state.conv_focus_tree.as_ref(),
    ) {
        // The current goal target is the selected focus's working expression.
        return open_nested_congr(state, &goal, &target, &cursor);
    }

    let (head, args) = decompose_app(state, &goal, &target)?;

    // Default the cursor to the LAST argument and narrow the goal target to it.
    // This preserves the proven single-focus behaviour of `congr; rw` (descend
    // into the last argument) AND of nested `congr; congr; rw` — a following
    // `arg i` simply re-selects a different focus for the multi-focus form.
    let last_cursor = if args.is_empty() { 0 } else { args.len() };
    let working = args
        .last()
        .map(|f| f.after.clone())
        .unwrap_or_else(|| head.after.clone());

    state.conv_focus_tree = Some(ConvNav::Congr {
        original: target,
        head,
        args,
    });
    state.conv_congr_cursor = Some(vec![last_cursor]);
    if let Some(g) = state.current_goal_mut() {
        g.target = working;
    }
    // The single-focus witness from any prior navigation is not valid in the
    // multi-focus tree; the tree carries per-focus equalities instead.
    state.conv_focus_witness = None;
    Ok(())
}

/// Decompose an application into a head focus + one focus per argument (SOURCE
/// order), caching each component's kernel type via `infer_type` (INV-3).
fn decompose_app(
    state: &ProofState,
    goal: &Goal,
    app: &Expr,
) -> Result<(ConvFocus, Vec<ConvFocus>), TacticError> {
    let head_expr = app.get_app_fn().clone();
    let arg_exprs: Vec<Expr> = app.get_app_args().into_iter().cloned().collect();
    let head_ty = state.infer_type(goal, &head_expr)?;
    let head = ConvFocus::leaf(head_expr, head_ty);
    let mut args = Vec::with_capacity(arg_exprs.len());
    for a in arg_exprs {
        let a_ty = state.infer_type(goal, &a)?;
        args.push(ConvFocus::leaf(a, a_ty));
    }
    Ok((head, args))
}

/// Decompose the focus at `cursor` into children (`[head, a1..an]`) and descend
/// the cursor into the last child (matching the default single-focus descent).
fn open_nested_congr(
    state: &mut ProofState,
    goal: &Goal,
    selected_focus_expr: &Expr,
    cursor: &[usize],
) -> TacticResult {
    if !matches!(selected_focus_expr.kind(), ExprKind::App(_, _)) {
        return Err(TacticError::GoalMismatch(
            "conv congr: selected focus is not an application".to_string(),
        ));
    }
    let (child_head, child_args) = decompose_app(state, goal, selected_focus_expr)?;
    let mut children = Vec::with_capacity(child_args.len() + 1);
    let last_child = if child_args.is_empty() {
        0
    } else {
        child_args.len()
    };
    let working = child_args
        .last()
        .map(|f| f.after.clone())
        .unwrap_or_else(|| child_head.after.clone());
    children.push(child_head);
    children.extend(child_args);

    let tree = state
        .conv_focus_tree
        .as_mut()
        .ok_or_else(|| TacticError::GoalMismatch("conv congr: no active focus tree".to_string()))?;
    let slot = tree
        .focus_at_path_mut(cursor)
        .ok_or_else(|| TacticError::GoalMismatch("conv congr: focus cursor out of range".into()))?;
    slot.children = children;
    slot.eq_proof = None;

    let mut new_cursor = cursor.to_vec();
    new_cursor.push(last_child);
    state.conv_congr_cursor = Some(new_cursor);
    if let Some(g) = state.current_goal_mut() {
        g.target = working;
    }
    Ok(())
}

/// Select a sibling sub-focus inside an active congr'd conv body (`arg i` after
/// `congr`). Maps the surface index `i` to a child slot at the CURRENT cursor
/// level (`0` = head; `i >= 1` = `args[i-1]`; negative counts from the end of
/// the argument list), REPLACING the last cursor component, then narrows the
/// conv goal target to that focus's working expression so a following `rw`
/// rewrites the right sub-expression.
///
/// Returns `Ok(true)` when a tree was active and a focus was selected;
/// `Ok(false)` when no congr tree is active (caller falls back to the proven
/// single-focus `conv_nav`).
pub(crate) fn conv_congr_select(state: &mut ProofState, i: i64) -> Result<bool, TacticError> {
    let Some(ConvNav::Congr { .. }) = state.conv_focus_tree.as_ref() else {
        return Ok(false);
    };

    // The parent path is the cursor minus its last component (the level whose
    // children `arg i` selects among). Default to top level if no cursor yet.
    let parent_path: Vec<usize> = match state.conv_congr_cursor.as_ref() {
        Some(c) if !c.is_empty() => c[..c.len() - 1].to_vec(),
        _ => Vec::new(),
    };

    let n_args = state
        .conv_focus_tree
        .as_ref()
        .and_then(|t| t.arg_count_at(&parent_path))
        .ok_or_else(|| {
            TacticError::GoalMismatch("conv congr: cannot resolve focus level".to_string())
        })?;

    // Resolve the surface index to a component (0 = head, 1..=n_args = args).
    let comp: usize = if i == 0 {
        0
    } else if i > 0 {
        let idx = i as usize;
        if idx > n_args {
            return Err(TacticError::GoalMismatch(format!(
                "conv congr: arg {i} out of range (application has {n_args} arguments)"
            )));
        }
        idx
    } else {
        let from_end = (-i) as usize;
        if from_end > n_args {
            return Err(TacticError::GoalMismatch(format!(
                "conv congr: arg {i} out of range (application has {n_args} arguments)"
            )));
        }
        n_args - from_end + 1
    };

    let mut new_cursor = parent_path;
    new_cursor.push(comp);

    let working = {
        let tree = state.conv_focus_tree.as_ref().ok_or_else(|| {
            TacticError::GoalMismatch("conv congr: no active focus tree".to_string())
        })?;
        tree.focus_at_path(&new_cursor)
            .ok_or_else(|| {
                TacticError::GoalMismatch("conv congr: focus cursor out of range".to_string())
            })?
            .after
            .clone()
    };

    state.conv_congr_cursor = Some(new_cursor);
    if let Some(g) = state.current_goal_mut() {
        g.target = working;
    }
    Ok(true)
}

/// Replace the focused expression with a definitionally equal one in conv mode.
///
/// This is the conv-specific `change` command. Inside a `conv` block, after
/// navigating to a subexpression, `conv_change` replaces the focused expression
/// with a new expression that must be definitionally equal.
///
/// REQUIRES: `new_focus` is definitionally equal to the current focus (goal target)
///
/// ENSURES: on Ok, the goal target is replaced with `new_focus`
///
/// ENSURES: on Err, proof state is unchanged if the expressions are not def-eq
pub fn conv_change(state: &mut ProofState, new_focus: Expr) -> TacticResult {
    state.replace_target_def_eq(new_focus)
}

/// Entry point for conv tactic mode.
///
/// `eval_conv` orchestrates the conv tactic block: it saves the current goal,
/// runs the provided body function (which can use `conv_ext`, `conv_lhs`,
/// `conv_rhs`, `conv_rw`, `conv_congr`, `conv_change`, etc.), and then
/// propagates the modified subexpression back to the full goal.
///
/// This is the programmatic API for conv mode. The parser-driven compound
/// handler `Conv` (in `builtins_phase3d_conv.rs`) uses `eval_conv_goal`
/// internally, which has the same architecture but integrates with the
/// `SurfaceTactic` dispatch.
///
/// REQUIRES: `state.goals` is non-empty
///
/// ENSURES: on Ok, the goal target reflects changes made by `body` within
/// the conv block, with proper proof reconstruction
///
/// ENSURES: on Err, the goal target is unchanged
///
/// # Example
/// ```text
/// eval_conv(&mut state, |ps| {
///     conv_lhs_nav(ps)?;   // focus on LHS
///     conv_rw(ps, vec![], "h", false)?;  // rewrite at focus
///     Ok(())
/// })
/// ```
pub fn eval_conv<F>(state: &mut ProofState, body: F) -> TacticResult
where
    F: FnOnce(&mut ProofState) -> TacticResult,
{
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let old_target = state.metas.instantiate(&goal.target);

    // Create a sub-proof-state for the conv body
    let mut conv_ps = state.clone_with_fresh_goal_target(old_target.clone());

    // Execute the body
    body(&mut conv_ps)?;

    // Merge metavariable state
    state.merge_meta_state(&conv_ps);

    // Multi-focus `conv => congr` path (#2477 Phase 4): recombine per-focus
    // equalities into one kernel-checked whole-application proof, lifted through
    // any outer single-focus navigation path. Mirrors `eval_conv_goal`.
    if let Some(ConvNav::Congr {
        original,
        head,
        args,
    }) = conv_ps.conv_focus_tree.as_ref()
    {
        let new_app = super::conv_congr_recombine::rebuild_app(args, head);
        let outer_path = conv_ps
            .conv_nav
            .as_ref()
            .map(|(_, path)| path.clone())
            .unwrap_or_default();
        let new_target = if outer_path.is_empty() {
            new_app.clone()
        } else {
            ConvState::replace_at_position(&old_target, &outer_path, &new_app)
                .unwrap_or_else(|| new_app.clone())
        };
        match state.replace_target_def_eq(new_target.clone()) {
            Ok(()) => return Ok(()),
            Err(TacticError::GoalMismatch(_)) => {}
            Err(e) => return Err(e),
        }
        let infer_goal = Goal {
            meta_id: goal.meta_id,
            target: old_target.clone(),
            local_ctx: goal.local_ctx.clone(),
            tag: goal.tag.clone(),
        };
        let Some(congr_proof) =
            super::conv_congr_recombine::recombine_foci(state, &infer_goal, original, head, args)?
        else {
            return Ok(());
        };
        let whole_eq_proof = super::conv_proof::lift_focus_eq_through_path(
            state,
            &infer_goal,
            &old_target,
            &outer_path,
            original,
            &new_app,
            congr_proof,
        )?
        .ok_or_else(|| TacticError::InvalidTarget {
            tactic: "eval_conv".into(),
            detail: "conv congr: failed to lift the recombined proof through the path".into(),
        })?;
        return state.replace_target_eq(new_target, whole_eq_proof);
    }

    let Some(conv_goal) = conv_ps.current_goal() else {
        return Ok(());
    };

    // Reconstruct the new target from navigation + rewrite
    let new_focus = conv_goal.target.clone();
    let new_target = if let Some((ref original, ref path)) = conv_ps.conv_nav {
        if !path.is_empty() {
            ConvState::replace_at_position(original, path, &new_focus)
                .unwrap_or_else(|| new_focus.clone())
        } else {
            new_focus.clone()
        }
    } else {
        new_focus
    };

    // Try definitional equality first (free path)
    match state.replace_target_def_eq(new_target.clone()) {
        Ok(()) => Ok(()),
        Err(TacticError::GoalMismatch(_)) => {
            // Non-def-eq change: check for conv_focus_witness to lift
            if let Some(ref witness) = conv_ps.conv_focus_witness {
                let nav_path = conv_ps
                    .conv_nav
                    .as_ref()
                    .map(|(_, path)| path.clone())
                    .unwrap_or_default();

                let infer_goal = Goal {
                    meta_id: goal.meta_id,
                    target: old_target.clone(),
                    local_ctx: goal.local_ctx.clone(),
                    tag: goal.tag,
                };

                let target_eq_proof = super::conv_proof::lift_focus_eq_through_path(
                    state,
                    &infer_goal,
                    &old_target,
                    &nav_path,
                    &witness.before,
                    &witness.after,
                    witness.eq_proof.clone(),
                )?
                .ok_or_else(|| TacticError::InvalidTarget {
                    tactic: "eval_conv".into(),
                    detail: "failed to lift conv proof through navigation path".into(),
                })?;

                state.replace_target_eq(new_target, target_eq_proof)
            } else {
                Err(TacticError::GoalMismatch(
                    "eval_conv: conv body changed the target without producing a proof".to_string(),
                ))
            }
        }
        Err(e) => Err(e),
    }
}
