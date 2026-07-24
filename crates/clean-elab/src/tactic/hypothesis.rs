// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hypothesis manipulation tactics
//!
//! This module provides tactics for manipulating hypotheses in the local context:
//! - `clear` - Remove a hypothesis
//! - `rename` - Rename a hypothesis
//! - `duplicate` - Duplicate a hypothesis with a new name
//! - `specialize` - Specialize a universally quantified hypothesis
//! - `clear_all_unused` - Clear all hypotheses not used in the goal
//! - `rename_all` - Rename multiple hypotheses at once
//! - `apply_fun` - Apply a function to both sides of an equality hypothesis
//! - `apply_fun_goal` - Apply a function to both sides of an equality goal
//! - `clear_except` - Clear all hypotheses except specified ones
//! - `replace` - Replace a hypothesis with a new one (creates proof obligation)
//! - `replace_hyp` - Replace a hypothesis with a new one (with explicit proof)

mod apply_fun_goal_impl;
mod proof_carry;

use std::collections::HashSet;

use clean_kernel::name::Name;
use clean_kernel::tc::whnf_proof::{CongrArgArgs, EqProofBuilder};
use clean_kernel::{Expr, ExprKind, ExprVisitor, FVarId};

use super::{match_equality, Goal, LocalDecl, ProofState, TacticError, TacticResult};
use crate::unify::MetaState;
use proof_carry::{infer_sort_level, replace_local_hyp_with_proof};

// ============================================================================
// Clear Tactic
// ============================================================================

/// Removes a hypothesis from the local context.
///
/// # Arguments
/// * `state` - The proof state
/// * `hyp_name` - Name of the hypothesis to remove
pub fn clear(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    let goal = state.current_goal_mut().ok_or(TacticError::NoGoals)?;

    let idx = goal
        .local_ctx
        .iter()
        .position(|decl| decl.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;

    goal.local_ctx.remove(idx);
    Ok(())
}

// ============================================================================
// Rename Tactic
// ============================================================================

/// Rename a hypothesis in the local context.
///
/// # Arguments
/// * `state` - The proof state
/// * `old_name` - Current name of the hypothesis
/// * `new_name` - New name to assign
pub fn rename(state: &mut ProofState, old_name: &str, new_name: &str) -> TacticResult {
    let goal = state.current_goal_mut().ok_or(TacticError::NoGoals)?;

    let decl = goal
        .local_ctx
        .iter_mut()
        .find(|d| d.name == old_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(old_name.to_string()))?;

    decl.name = new_name.to_string();
    Ok(())
}

// ============================================================================
// Duplicate Tactic
// ============================================================================

/// Duplicate a hypothesis in the local context with a new name.
///
/// # Arguments
/// * `state` - The proof state
/// * `hyp_name` - Name of the hypothesis to duplicate
/// * `new_name` - Name for the duplicate
pub fn duplicate(state: &mut ProofState, hyp_name: &str, new_name: &str) -> TacticResult {
    let goal = state.current_goal_mut().ok_or(TacticError::NoGoals)?;

    let decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    let new_decl = LocalDecl {
        name: new_name.to_string(),
        fvar: decl.fvar, // Share the same fvar (both refer to same value)
        ty: decl.ty,
        value: decl.value,
    };

    goal.local_ctx.push(new_decl);
    Ok(())
}

// ============================================================================
// Specialize Tactic
// ============================================================================

/// Specialize a hypothesis by applying it to an argument.
///
/// Given a hypothesis `h : ∀ x : A, P x` and a term `a : A`, this replaces
/// `h` with `h : P a` using the shared local-ops insertion boundary.
///
/// # Arguments
/// * `state` - The proof state
/// * `hyp_name` - Name of the hypothesis to specialize (must have Pi type)
/// * `arg` - The argument to apply
///
/// # Example
/// If you have `h : ∀ n : Nat, n + 0 = n` and call `specialize(state, "h", Expr::nat_lit(5))`,
/// then `h` becomes `h : 5 + 0 = 5`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` names a hypothesis in the local context
/// REQUIRES: The hypothesis has Pi type (after WHNF)
/// REQUIRES: `arg` has type matching the Pi domain (checked via `is_def_eq`)
/// ENSURES: On Ok, a new local `h : codomain[arg/x]` is introduced (shadowing the
///   old `h`) whose proof is the application `(old_h arg)`, recorded as a
///   `let`-binding in the proof term so the closed term is well-formed.
/// ENSURES: On Err(HypothesisNotFound), `hyp_name` is not in the local context;
///   state unchanged
/// ENSURES: On Err(TypeMismatch), `arg` type does not match domain; state unchanged
/// ENSURES: On Err(GoalMismatch), hypothesis is not universally quantified;
///   state unchanged
/// ENSURES: Never panics — a missing hypothesis, a non-∀/non-function `h`, or an
///   ill-typed application returns a `TacticError`.
pub fn specialize(state: &mut ProofState, hyp_name: &str, arg: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis (graceful error if absent — never panic). Use the
    // LAST matching decl so repeated `specialize` (multi-arg) re-applies to the
    // most recently shadowed binding rather than the original `h`.
    let decl = goal
        .local_ctx
        .iter()
        .rev()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    // Get the type and normalize.
    let hyp_ty = state.whnf(&goal, &decl.ty);

    // Check it's a Pi type (`∀ x, P` / `A → B`). A non-Pi `h` (or too many
    // args, surfacing here as a non-Pi codomain on a later iteration) is a
    // graceful error, not a panic.
    match hyp_ty.kind() {
        ExprKind::Pi(_bi, domain, codomain) => {
            // Type check the argument against the binder domain.
            let arg_ty = state.infer_type(&goal, &arg)?;
            if !state.is_def_eq(&goal, &arg_ty, domain) {
                return Err(TacticError::TypeMismatch {
                    expected: format!("{domain:?}"),
                    actual: format!("{arg_ty:?}"),
                });
            }

            // The specialized hypothesis is `old_h arg : codomain[arg/x]`.
            // Re-bind the SAME name to that application via the shared
            // `have`/`let_named` machinery (equivalent to `have h := h arg`,
            // shadowing the old `h`). This records the binding in the proof
            // term so the closed term references no dangling tactic FVar; the
            // application's type is `codomain.instantiate(&arg)` exactly, with
            // no fabrication, and `have_` strictly re-infers it via the kernel
            // path — an ill-typed application errors rather than slipping
            // through.
            let specialized_ty = codomain.instantiate(&arg);
            let specialized_value = Expr::app(Expr::fvar(decl.fvar), arg);
            super::have_(state, hyp_name, specialized_ty, Some(specialized_value))
        }
        _ => Err(TacticError::GoalMismatch(format!(
            "specialize: hypothesis '{hyp_name}' has type {hyp_ty:?}, expected ∀ or →"
        ))),
    }
}

// ============================================================================
// Clear All Unused Tactic
// ============================================================================

/// Clears all hypotheses from the local context that are not used in the goal.
/// This is useful for cleaning up the context after complex case splits.
///
/// # Example
/// ```text
/// -- h1 : P, h2 : Q, h3 : R ⊢ P
/// clear_all
/// -- h1 : P ⊢ P
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
pub fn clear_all_unused(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Collect free variables used in the target
    let mut all_used = collect_fvars(&goal.target);

    // Iteratively add dependencies
    loop {
        let mut added = false;
        for decl in &goal.local_ctx {
            if all_used.contains(&decl.fvar) {
                let ty_fvars = collect_fvars(&decl.ty);
                for fv in ty_fvars {
                    if !all_used.contains(&fv) {
                        all_used.insert(fv);
                        added = true;
                    }
                }
            }
        }
        if !added {
            break;
        }
    }

    // Remove unused hypotheses
    let goal = state.current_goal_mut().ok_or(TacticError::NoGoals)?;
    goal.local_ctx.retain(|decl| all_used.contains(&decl.fvar));

    Ok(())
}

/// Collect free variables from an expression.
///
/// Uses the kernel's `ExprVisitor` trait for structural traversal over all
/// ExprKind variants (including Cubical and ZFC extensions). Part of #2092.
///
/// Returns a `HashSet` for O(1) membership testing. Previous `Vec`-based
/// implementation had O(n*f) cost due to linear `contains()` checks.
pub(crate) fn collect_fvars(expr: &Expr) -> HashSet<FVarId> {
    struct FVarCollector<'a> {
        fvars: &'a mut HashSet<FVarId>,
    }

    impl ExprVisitor for FVarCollector<'_> {
        type Result = ();

        fn combine(&self, _a: (), _b: ()) {}

        fn visit_fvar(&mut self, id: FVarId) {
            self.fvars.insert(id);
        }
    }

    let mut fvars = HashSet::new();
    let mut visitor = FVarCollector { fvars: &mut fvars };
    visitor.visit_expr(expr);
    fvars
}

// ============================================================================
// Rename All Tactic
// ============================================================================

/// Tactic: rename_all
///
/// Renames multiple hypotheses at once according to a mapping.
///
/// # Example
/// ```text
/// -- h1 : P, h2 : Q ⊢ R
/// rename_all [h1 → hP, h2 → hQ]
/// -- hP : P, hQ : Q ⊢ R
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `HypothesisNotFound` if any source name doesn't exist
pub fn rename_all(state: &mut ProofState, renames: Vec<(&str, &str)>) -> TacticResult {
    for (old_name, new_name) in renames {
        rename(state, old_name, new_name)?;
    }
    Ok(())
}

// ============================================================================
// Apply Fun Tactic
// ============================================================================

/// Tactic: apply_fun - Applies a function to both sides of an equality hypothesis.
pub fn apply_fun(state: &mut ProofState, func: Expr, hyp_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let hyp_idx = goal
        .local_ctx
        .iter()
        .position(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;
    let hyp_decl = goal.local_ctx[hyp_idx].clone();

    let hyp_ty = state.metas.instantiate(&hyp_decl.ty);

    let (eq_type, lhs, rhs, _levels) = match_equality(&hyp_ty).map_err(|_| {
        TacticError::GoalMismatch(format!(
            "apply_fun: hypothesis '{hyp_name}' must be an equality"
        ))
    })?;

    let new_lhs = Expr::app(func.clone(), lhs.clone());
    let new_rhs = Expr::app(func.clone(), rhs.clone());
    let result_ty = state.infer_type(&goal, &new_lhs)?;
    let result_level = infer_sort_level(
        state,
        &goal,
        &result_ty,
        "apply_fun: cannot infer equality target universe",
    )?;

    let new_eq = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![result_level.clone()]),
                result_ty.clone(),
            ),
            new_lhs.clone(),
        ),
        new_rhs.clone(),
    );

    let eq_proof = EqProofBuilder::mk_congr_arg(CongrArgArgs {
        u: infer_sort_level(
            state,
            &goal,
            &eq_type,
            "apply_fun: cannot infer equality source universe",
        )?,
        v: result_level,
        alpha: eq_type,
        beta: result_ty,
        a1: lhs,
        a2: rhs,
        f: func,
        h: Expr::fvar(hyp_decl.fvar),
    });

    replace_local_hyp_with_proof(state, &goal, hyp_idx, new_eq, eq_proof)
}

/// Tactic: apply_fun_goal - Applies a function to both sides of an equality goal.
pub fn apply_fun_goal(state: &mut ProofState, func: Expr) -> TacticResult {
    apply_fun_goal_impl::apply_fun_goal(state, func)
}

// ============================================================================
// Clear Except Tactic
// ============================================================================

/// Tactic: clear_except - Clears all hypotheses except the specified ones.
pub fn clear_except(state: &mut ProofState, keep: &[&str]) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let mut fvars_to_keep: HashSet<FVarId> = HashSet::new();

    for name in keep {
        if let Some(decl) = goal.local_ctx.iter().find(|d| d.name == *name) {
            fvars_to_keep.insert(decl.fvar);
        }
    }

    let target = state.metas.instantiate(&goal.target);
    fvars_to_keep.extend(collect_fvars(&target));

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    loop {
        let mut added = false;
        for decl in &goal.local_ctx {
            if fvars_to_keep.contains(&decl.fvar) {
                let ty_fvars = collect_fvars(&decl.ty);
                for fv in ty_fvars {
                    if !fvars_to_keep.contains(&fv) {
                        fvars_to_keep.insert(fv);
                        added = true;
                    }
                }
            }
        }
        if !added {
            break;
        }
    }

    let goal = state.current_goal_mut().ok_or(TacticError::NoGoals)?;
    goal.local_ctx
        .retain(|decl| fvars_to_keep.contains(&decl.fvar));
    Ok(())
}

// ============================================================================
// Replace Tactics
// ============================================================================

/// Tactic: replace - Replaces a hypothesis with a new one.
///
/// Creates a new goal to prove the replacement type.
pub fn replace(state: &mut ProofState, hyp_name: &str, new_type: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let hyp_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;
    let hyp_decl = hyp_decl.clone();

    let goals_snapshot = state.goals.clone();
    let metas_snapshot = state.metas.clone();
    let next_fvar_snapshot = state.next_fvar;

    let proof_meta_id = state.fresh_meta(new_type.clone());
    let proof_expr = Expr::fvar(MetaState::to_fvar(proof_meta_id));

    if let Err(err) =
        state.replace_local_decl_with_value(hyp_decl.fvar, new_type.clone(), proof_expr)
    {
        state.goals = goals_snapshot;
        state.metas = metas_snapshot;
        state.next_fvar = next_fvar_snapshot;
        state.invalidate_tc_cache();
        return Err(err);
    }

    let new_goal = Goal {
        meta_id: proof_meta_id,
        target: new_type,
        local_ctx: goal.local_ctx,
        tag: goal.tag,
    };

    state.goals.push_back(new_goal);
    Ok(())
}

/// Tactic: replace_hyp - Replaces a hypothesis with explicit proof term.
pub fn replace_hyp(
    state: &mut ProofState,
    hyp_name: &str,
    new_type: Expr,
    proof: Expr,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let hyp_fvar = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .map(|decl| decl.fvar)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;
    state
        .replace_local_decl_with_value(hyp_fvar, new_type, proof)
        .map(|_| ())
}
