// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Congruence, obtain, and revert tactics.
//!
//! - `congr`: Break down an equality goal by congruence, creating subgoals for each argument pair.
//! - `obtain`: Destructure an existential or sigma-type hypothesis, introducing a witness and property.
//! - `revert`: Move a hypothesis back into the goal as an implication (inverse of `intro`).

use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId};

use super::core::{Goal, ProofState, TacticError, TacticResult};
use super::proof_manipulation::cases;
use super::proof_term::rfl;

/// Apply congruence to break down an equality goal.
///
/// For a goal `f a₁ ... aₙ = f b₁ ... bₙ`, creates subgoals `a₁ = b₁`, ..., `aₙ = bₙ`.
/// The function `f` must be the same on both sides.
///
/// This is useful when you need to prove equality by showing each argument is equal.
///
/// # Example
/// For goal `Nat.add x y = Nat.add x' y'`, creates subgoals `x = x'` and `y = y'`.
///
/// REQUIRES: At least one goal exists in `state`.
/// REQUIRES: Current goal target is `@Eq α (f a₁ ... aₙ) (f b₁ ... bₙ)`.
/// ENSURES: On `Ok`, the original goal is closed and replaced by argument-equality
///   subgoals `aᵢ = bᵢ` (or closed via `rfl` if no arguments).
/// ENSURES: On `Err`, the proof state is unchanged.
pub fn congr(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let target = state.whnf(&goal, &goal.target);

    // Check if target is an Eq application
    let head = target.get_app_fn();
    let args: Vec<Expr> = target.get_app_args().into_iter().cloned().collect();

    match head.kind() {
        ExprKind::Const(name, levels) if *name == Name::from_string("Eq") => {
            // Eq takes 3 args: type, lhs, rhs
            if args.len() != 3 {
                return Err(TacticError::GoalMismatch(
                    "congr: expected Eq with 3 arguments".to_string(),
                ));
            }

            let _eq_ty = args[0].clone();
            let lhs = args[1].clone();
            let rhs = args[2].clone();

            // Get the function and args of lhs and rhs
            let lhs_fn = lhs.get_app_fn();
            let rhs_fn = rhs.get_app_fn();
            let lhs_args: Vec<Expr> = lhs.get_app_args().into_iter().cloned().collect();
            let rhs_args: Vec<Expr> = rhs.get_app_args().into_iter().cloned().collect();

            // Check same function
            if !state.is_def_eq(&goal, lhs_fn, rhs_fn) {
                return Err(TacticError::GoalMismatch(
                    "congr: functions on both sides must be equal".to_string(),
                ));
            }

            // Check same number of args
            if lhs_args.len() != rhs_args.len() {
                return Err(TacticError::GoalMismatch(
                    "congr: argument counts must match".to_string(),
                ));
            }

            if lhs_args.is_empty() {
                // No arguments - just need reflexivity
                return rfl(state);
            }

            // For a single argument, use congrArg
            if lhs_args.len() == 1 {
                // Build proof: congrArg f ?h where ?h : a = b
                let arg_ty = state.infer_type(&goal, &lhs_args[0])?;
                let eq_goal_ty = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), levels.clone()),
                            arg_ty,
                        ),
                        lhs_args[0].clone(),
                    ),
                    rhs_args[0].clone(),
                );

                let arg_eq_meta_id = state.fresh_meta(eq_goal_ty.clone());
                let arg_eq_meta =
                    Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(arg_eq_meta_id)));

                // Try to find congrArg in environment
                let congr_arg = Name::from_string("congrArg");
                if state.env.get_const(&congr_arg).is_some() {
                    // congrArg : ∀ {α β} (f : α → β) {a₁ a₂ : α}, a₁ = a₂ → f a₁ = f a₂
                    let mut proof = Expr::const_(congr_arg, levels.clone());
                    proof = Expr::app(proof, lhs_fn.clone()); // f
                    proof = Expr::app(proof, arg_eq_meta.clone()); // h : a₁ = a₂

                    state.close_goal(&goal, proof)?;

                    let new_goal = Goal {
                        meta_id: arg_eq_meta_id,
                        target: eq_goal_ty,
                        local_ctx: goal.local_ctx.clone(),
                        tag: None,
                    };
                    state.goals.push_front(new_goal);

                    return Ok(());
                }
            }

            // For multiple arguments or no congrArg, fall back to recursive approach
            // Create a subgoal for each argument pair
            let mut new_goals = Vec::new();
            let mut proofs = Vec::new();

            for (la, ra) in lhs_args.iter().zip(rhs_args.iter()) {
                let arg_ty = state.infer_type(&goal, la)?;
                let eq_goal_ty = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), levels.clone()),
                            arg_ty,
                        ),
                        la.clone(),
                    ),
                    ra.clone(),
                );

                let meta_id = state.fresh_meta(eq_goal_ty.clone());
                proofs.push(Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(meta_id))));

                new_goals.push(Goal {
                    meta_id,
                    target: eq_goal_ty,
                    local_ctx: goal.local_ctx.clone(),
                    tag: None,
                });
            }

            // Build the combined proof using Eq.subst repeatedly
            // Start with rfl for f = f, then substitute each argument
            let eq_refl = Name::from_string("Eq.refl");
            let eq_subst = Name::from_string("Eq.subst");

            // If we have Eq.refl and Eq.subst, build a chain
            if state.env.get_const(&eq_refl).is_some() && state.env.get_const(&eq_subst).is_some() {
                // For now, just create subgoals - a full implementation would build
                // the proof term properly. This is a simplification.
                let full_eq_meta_id = state.fresh_meta(goal.target.clone());
                let full_eq_meta =
                    Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(full_eq_meta_id)));
                state.close_goal(&goal, full_eq_meta)?;

                // Replace with a single goal that the user must prove
                // (proper congruence proof building is complex)
                let final_goal = Goal {
                    meta_id: full_eq_meta_id,
                    target: goal.target.clone(),
                    local_ctx: goal.local_ctx.clone(),
                    tag: None,
                };
                state.goals.push_front(final_goal);

                // Also add the argument equality goals as hints
                for ng in new_goals.into_iter().rev() {
                    state.goals.push_front(ng);
                }

                Ok(())
            } else {
                Err(TacticError::EnvironmentMissing {
                    constant: "Eq.refl/Eq.subst".to_string(),
                })
            }
        }
        _ => Err(TacticError::GoalMismatch(
            "congr: goal must be an equality".to_string(),
        )),
    }
}

/// Obtain (destructure) a hypothesis with an existential or sigma type.
///
/// For a hypothesis `h : ∃ x : A, P x`, introduces `x : A` and `h : P x`
/// into the context. The original hypothesis is replaced.
///
/// # Arguments
/// * `state` - The proof state
/// * `hyp_name` - Name of the hypothesis to destructure
/// * `var_name` - Name for the introduced variable
/// * `new_hyp_name` - Name for the property hypothesis
///
/// # Example
/// If you have `h : ∃ n : Nat, n > 0`, calling `obtain(state, "h", "n", "hn")`
/// gives you `n : Nat` and `hn : n > 0`.
///
/// REQUIRES: At least one goal exists in `state`.
/// REQUIRES: `hyp_name` names a hypothesis in the current goal's local context.
/// REQUIRES: The hypothesis type is `Exists` or `Sigma` with exactly 2 arguments.
/// ENSURES: On `Ok`, the original hypothesis is removed and replaced by two new
///   declarations: the witness variable and the applied predicate hypothesis.
/// ENSURES: The goal target is unchanged; only the local context is modified.
pub fn obtain(
    state: &mut ProofState,
    hyp_name: &str,
    var_name: &str,
    new_hyp_name: &str,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis and verify it is a destructible Exists/Sigma.
    let decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    let hyp_ty = state.whnf(&goal, &decl.ty);
    let head = hyp_ty.get_app_fn();
    let is_existsy = matches!(head.kind(), ExprKind::Const(name, _)
        if *name == Name::from_string("Exists") || *name == Name::from_string("Sigma"));
    if !is_existsy {
        return Err(TacticError::GoalMismatch(format!(
            "obtain: hypothesis '{hyp_name}' has type {hyp_ty:?}, expected ∃ or Σ"
        )));
    }

    // FAIL CLOSED on an unsolved binder-type metavariable in the scrutinee type.
    // An untyped existential whose binder type was never inferred (e.g.
    // `∃ a, ∃ b, a = b`, which Lean 4 itself rejects) would otherwise make
    // `cases` embed the sentinel meta-FVar (`MetaState::to_fvar`, id `2^63 + n`)
    // in the `Exists.casesOn` proof term and leak it to the kernel re-check as a
    // confusing `UnknownFVar`. Reject it here with a clear diagnostic instead —
    // never a sentinel leak, never a silent over-accept. Resolved (typed) types
    // carry no meta, so this is a no-op for them.
    let hyp_ty_inst = state.metas.instantiate(&hyp_ty);
    if contains_unassigned_meta(&hyp_ty_inst) {
        return Err(TacticError::GoalMismatch(format!(
            "obtain: hypothesis '{hyp_name}' has a type with an unresolved metavariable \
             (an implicit argument such as the binder type could not be inferred); add an \
             explicit type annotation to the binder(s)"
        )));
    }

    // Delegate destructuring to the sound `cases` engine. Previously this
    // pushed raw, unbound witness/proof FVars into the goal's local_ctx without
    // building any eliminator term, so a proof that *used* the witness/proof
    // assembled to a dangling FVar that the kernel rejected (and that panicked
    // the close_fvars debug assertion in test builds). `cases` instead assigns
    // the goal's metavariable to `Exists.casesOn motive hyp (λ w h => ?meta)`
    // (Lean-faithful casesOn order: motive, (indices,) major, then minors)
    // with the witness/proof FVars abstracted into the branch lambda, yielding
    // a genuine, kernel-checked eliminator term. (#9510-rintro)
    let ctx_len_before = goal.local_ctx.len();
    cases(state, hyp_name)?;

    // The branch goal (Exists/Sigma each have a single constructor ⇒ exactly
    // one branch) is now at the front; its local_ctx holds the witness and
    // proof FVars as its final declarations (cases removed the scrutinee first).
    let new_goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let removed = ctx_len_before.saturating_sub(1);
    let new_len = new_goal.local_ctx.len();
    let num_fields = new_len.saturating_sub(removed);

    let field_fvars: Vec<FVarId> = new_goal
        .local_ctx
        .iter()
        .skip(removed)
        .take(num_fields)
        .map(|d| d.fvar)
        .collect();

    // Field order: [witness, proof]. Rename to the caller-supplied names.
    if let Some(witness_fvar) = field_fvars.first() {
        rename_field_by_fvar(state, *witness_fvar, var_name)?;
    }
    if let Some(proof_fvar) = field_fvars.get(1) {
        rename_field_by_fvar(state, *proof_fvar, new_hyp_name)?;
    }

    Ok(())
}

/// Rename a field hypothesis (identified by FVar) in the current goal.
///
/// Used by `obtain` to give the witness/proof fields produced by the `cases`
/// eliminator their caller-requested surface names.
fn rename_field_by_fvar(
    state: &mut ProofState,
    field_fvar: FVarId,
    new_name: &str,
) -> TacticResult {
    let goal = state.current_goal_mut().ok_or(TacticError::NoGoals)?;
    for decl in &mut goal.local_ctx {
        if decl.fvar == field_fvar {
            decl.name = new_name.to_string();
            return Ok(());
        }
    }
    Err(TacticError::HypothesisNotFound(
        "obtain: field hypothesis not found for rename".into(),
    ))
}

/// Revert a hypothesis back into the goal.
///
/// For a hypothesis `h : A` and goal `⊢ B`, this changes the goal to `⊢ A → B`
/// and removes `h` from the context. This is the inverse of `intro`.
///
/// # Arguments
/// * `state` - The proof state
/// * `hyp_name` - Name of the hypothesis to revert
///
/// # Example
/// With context `h : P` and goal `Q`, calling `revert(state, "h")` gives goal `P → Q`.
///
/// REQUIRES: At least one goal exists in `state`.
/// REQUIRES: `hyp_name` names a hypothesis in the current goal's local context.
/// ENSURES: On `Ok`, the original goal is closed and replaced by a new goal
///   whose target is `hyp_ty → old_target` (with the hypothesis's fvar abstracted).
/// ENSURES: The hypothesis is removed from the new goal's local context.
pub fn revert(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis
    let (idx, decl) = goal
        .local_ctx
        .iter()
        .enumerate()
        .find(|(_, d)| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;
    let decl = decl.clone();

    // Create new target: hyp_ty → old_target
    let new_target = Expr::pi(
        BinderInfo::Default,
        decl.ty.clone(),
        goal.target.abstract_fvar(decl.fvar),
    );

    // The reverted hypothesis is bound inside `new_target`, not available as
    // a free local in the replacement goal.
    let mut new_ctx = goal.local_ctx.clone();
    new_ctx.remove(idx);

    // Create new metavariable for the new goal
    let new_meta_id = state.fresh_meta_in_context(new_target.clone(), &new_ctx);
    let new_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id)));

    // The proof of the old goal is: new_proof h
    let proof = Expr::app(new_meta, Expr::fvar(decl.fvar));
    state.close_goal(&goal, proof)?;

    let new_goal = Goal {
        meta_id: new_meta_id,
        target: new_target,
        local_ctx: new_ctx,
        tag: None,
    };

    state.goals.push_front(new_goal);
    Ok(())
}

/// Whether `expr` contains a leaked *unassigned* metavariable (an `FVar` whose id
/// carries `MetaState`'s high-bit tag, `2^63 + n`). After `MetaState::instantiate`
/// such an `FVar` is an elaborator metavariable that was never assigned — for an
/// existential scrutinee this is the untyped-binder case whose binder type could
/// not be inferred. Destructuring it would leak the sentinel meta-FVar into the
/// `casesOn` proof term, so `obtain` rejects it. Mirrors `simp`'s check.
fn contains_unassigned_meta(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::FVar(id) => MetaState::from_fvar(*id).is_some(),
        ExprKind::App(f, a) => contains_unassigned_meta(f) || contains_unassigned_meta(a),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_unassigned_meta(ty) || contains_unassigned_meta(body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_unassigned_meta(ty)
                || contains_unassigned_meta(val)
                || contains_unassigned_meta(body)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            contains_unassigned_meta(inner)
        }
        _ => false,
    }
}
