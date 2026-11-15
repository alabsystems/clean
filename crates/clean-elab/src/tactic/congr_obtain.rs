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
use clean_kernel::{Expr, ExprKind, FVarId};

use super::core::{ProofState, TacticError, TacticResult};
use super::proof_manipulation::cases;

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
    // Lean's `congr` with no depth (`evalCongr`): see `congr_n`.
    super::congr_n::congr_n(state, super::congr_n::CONGR_DEFAULT_DEPTH)
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
    hyp_name: &clean_parser::SurfaceName,
    var_name: &clean_parser::SurfaceName,
    new_hyp_name: &clean_parser::SurfaceName,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis and verify it is a destructible Exists/Sigma.
    let decl = goal
        .local_ctx
        .iter()
        .rev()
        .find(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, hyp_name))
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    let hyp_ty = state.whnf(&goal, &decl.ty);
    let head = hyp_ty.get_app_fn();
    let is_existsy = matches!(head.kind(), ExprKind::Const(name, _)
        if *name == Name::from_string("Exists") || *name == Name::from_string("Sigma"));
    if !is_existsy {
        return Err(TacticError::GoalMismatch(format!(
            "obtain: hypothesis '{hyp_name}' has type {}, expected ∃ or Σ",
            crate::error_render::term(&hyp_ty)
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
    new_name: &clean_parser::SurfaceName,
) -> TacticResult {
    let goal = state.current_goal_mut().ok_or(TacticError::NoGoals)?;
    for decl in &mut goal.local_ctx {
        if decl.fvar == field_fvar {
            decl.name = new_name.clone();
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
/// and removes `h` from the context together with its forward dependencies.
/// A local definition retains a let binder and its value. This is the inverse of `intro`.
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
///   whose target abstracts the selected locals in declaration order, preserving definitions.
/// ENSURES: The hypothesis is removed from the new goal's local context.
pub fn revert(state: &mut ProofState, hyp_name: &clean_parser::SurfaceName) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let decl = goal
        .local_ctx
        .iter()
        .rev()
        .find(|decl| crate::tactic::pattern::names::hypothesis_named(&decl.name, hyp_name))
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;
    super::specialize_generalize::revert_fvar_with_deps(state, decl.fvar).map(|_| ())
}

/// Revert one selected identity after its dependents have been removed.
/// Internal callers walk their dependency list in reverse declaration order.
/// Use the same typed telescope construction, including let values.
pub(crate) fn revert_fvar(state: &mut ProofState, fvar: FVarId) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    if !goal.local_ctx.iter().any(|decl| decl.fvar == fvar) {
        return Err(TacticError::HypothesisNotFound(format!("{fvar:?}")));
    }
    super::major_dependents::revert_fvars(state, &[fvar]).map(|_| ())
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
