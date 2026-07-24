// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enhanced existential introduction and constructor tactics.
//!
//! Provides `use_tactic` (multi-witness existential introduction with optional
//! auto-closing), `refine_constructor` (smart constructor dispatch for Or,
//! And, Iff, Exists, and general inductives), and `use_with_constructor`
//! (combined witness + constructor).
//!
//! These build on the primitives in `existential.rs` (`existsi`, `match_exists`),
//! `connective.rs` (`split_`, `left_`), and `proof_term.rs` (`apply`).

use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

use super::core::{Goal, ProofState, TacticError, TacticResult};
use super::existential::{existsi, match_exists};
use super::simp::beta_reduce;

// =============================================================================
// use_tactic - Multi-witness existential introduction
// =============================================================================

/// Provide witnesses for nested existential goals.
///
/// Applies `existsi` for each witness in order. After all witnesses are consumed,
/// attempts to close the remaining goal with `rfl` (useful when the predicate
/// becomes a trivial equality after substitution).
///
/// # Example
/// ```text
/// -- Goal: exists x y, x + y = 5
/// use 2, 3
/// -- Goal: 2 + 3 = 5   (if not closed by rfl)
/// ```
///
/// # Contract
///
/// REQUIRES: `witnesses` is non-empty
/// REQUIRES: Each witness is compatible with the existential at its nesting level
/// ENSURES: On Ok, `existsi` has been applied for each witness in order
/// ENSURES: On Ok, an attempt is made to close the final goal via `rfl` (best-effort)
/// ENSURES: On Err(MissingArgument), no witnesses provided; state unchanged
pub(crate) fn use_tactic(state: &mut ProofState, witnesses: Vec<Expr>) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    if witnesses.is_empty() {
        return Err(TacticError::MissingArgument {
            tactic: "use".into(),
            expected: "at least one witness".into(),
        });
    }

    // Apply existsi for each witness
    for witness in witnesses {
        existsi(state, witness)?;
    }

    // Try to close the remaining goal with rfl (best-effort, ignore failure)
    let _ = super::combinator::try_tactic_preserving_state(state, super::proof_term::rfl);

    Ok(())
}

// =============================================================================
// refine_constructor - Smart constructor tactic
// =============================================================================

/// Enhanced constructor tactic with special handling for common connectives.
///
/// Dispatches based on the head constant of the WHNF target:
///
/// - `And` / `Iff`: delegates to `split_` (produces two subgoals)
/// - `Or`: delegates to `left_` (applies `Or.inl`, first constructor)
/// - `Exists`: creates a fresh metavariable witness and applies `Exists.intro`,
///   producing two subgoals (witness type and predicate applied to witness)
/// - Other inductive: applies the first constructor via `apply`
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: Goal target head (after WHNF) is a const
/// ENSURES: On Ok, the appropriate constructor is applied
/// ENSURES: On Err(GoalMismatch), target is not a recognized inductive type
pub(crate) fn refine_constructor(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.whnf(&goal, &goal.target);

    let head = target.get_app_fn().clone();

    match head.kind() {
        // And / Iff => split into two subgoals
        ExprKind::Const(name, _)
            if *name == Name::from_string("And") || *name == Name::from_string("Iff") =>
        {
            super::connective::split_(state)
        }

        // Or => apply first constructor (Or.inl)
        ExprKind::Const(name, _) if *name == Name::from_string("Or") => {
            super::connective::left_(state)
        }

        // Exists => create witness meta + proof meta
        ExprKind::Const(name, _) if *name == Name::from_string("Exists") => {
            refine_constructor_exists(state, &goal, &target)
        }

        // General inductive type => apply first constructor
        ExprKind::Const(name, levels) => {
            if let Some(ind_info) = state.env.get_inductive(name) {
                if let Some(ctor_name) = ind_info.constructor_names.first() {
                    let ctor = Expr::const_(ctor_name.clone(), levels.clone());
                    return super::proof_term::apply(state, ctor);
                }
            }
            Err(TacticError::GoalMismatch(format!(
                "refine_constructor: not an inductive type: {name}"
            )))
        }

        _ => Err(TacticError::GoalMismatch(
            "refine_constructor: goal is not an application of a constant".to_string(),
        )),
    }
}

/// Handle the Exists case for `refine_constructor`.
///
/// Creates a fresh metavariable as the witness and applies `Exists.intro`,
/// producing two subgoals: one for the witness (type `alpha`) and one for
/// the predicate applied to the witness (type `pred witness`, beta-reduced).
fn refine_constructor_exists(state: &mut ProofState, goal: &Goal, target: &Expr) -> TacticResult {
    // Check that Exists.intro exists in the environment
    let exists_intro_name = Name::from_string("Exists.intro");
    if state.env.get_const(&exists_intro_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Exists.intro".to_string(),
        });
    }

    // Parse Exists {alpha} pred
    let (alpha, pred) = match_exists(target).ok_or_else(|| {
        TacticError::GoalMismatch(
            "refine_constructor: goal is not of the form 'exists x, P x'".to_string(),
        )
    })?;

    // Create a fresh metavariable for the witness (type: alpha)
    let witness_meta_id = state.fresh_meta(alpha.clone());
    let witness_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(witness_meta_id)));

    // The new predicate goal is: pred witness (beta-reduced)
    let proof_target_unreduced = Expr::app(pred.clone(), witness_meta.clone());
    let proof_target = beta_reduce(&proof_target_unreduced);
    let proof_meta_id = state.fresh_meta(proof_target.clone());

    // Infer universe level for alpha
    let alpha_ty = state.infer_type(goal, &alpha)?;
    let level = match alpha_ty.kind() {
        ExprKind::Sort(l) => l.clone(),
        _ => Level::zero(), // Fallback for Prop-valued types
    };

    // Build: Exists.intro {alpha} {pred} witness proof
    // Exists.intro : {alpha : Sort u} -> {p : alpha -> Prop} -> (w : alpha) -> p w -> Exists p
    let exists_intro = Expr::const_(exists_intro_name, vec![level]);
    let proof = Expr::app(
        Expr::app(
            Expr::app(Expr::app(exists_intro, alpha.clone()), pred),
            witness_meta,
        ),
        Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(proof_meta_id))),
    );

    // Close the current goal with the Exists.intro proof
    state.close_goal(goal, proof)?;

    // Push the witness goal (type alpha) and proof goal (type: pred witness)
    // Witness first, then proof (matches Lean 4 ordering)
    let witness_goal = Goal {
        meta_id: witness_meta_id,
        target: alpha,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };
    let proof_goal = Goal {
        meta_id: proof_meta_id,
        target: proof_target,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };

    state.goals.push_front(proof_goal);
    state.goals.push_front(witness_goal);

    Ok(())
}

// =============================================================================
// use_with_constructor - Combined witness + constructor
// =============================================================================

/// Provide witnesses for existentials, then apply constructor on the remainder.
///
/// Combines `existsi` and `refine_constructor`: first applies `existsi` for
/// each witness, then tries `refine_constructor` on whatever goal remains.
/// The `refine_constructor` failure is ignored (witnesses are still applied).
///
/// # Example
/// ```text
/// -- Goal: exists x, x > 0 /\ x < 10
/// use_with_constructor [5]
/// -- Subgoal 1: 5 > 0
/// -- Subgoal 2: 5 < 10
/// ```
///
/// # Contract
///
/// REQUIRES: `witnesses` is non-empty
/// ENSURES: On Ok, existsi applied for each witness, then refine_constructor (best-effort)
pub(crate) fn use_with_constructor(state: &mut ProofState, witnesses: Vec<Expr>) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    if witnesses.is_empty() {
        return Err(TacticError::MissingArgument {
            tactic: "use_with_constructor".into(),
            expected: "at least one witness".into(),
        });
    }

    // Apply existsi for each witness
    for witness in witnesses {
        existsi(state, witness)?;
    }

    // Try to apply constructor on the remaining goal (best-effort)
    let _ = refine_constructor(state);

    Ok(())
}
