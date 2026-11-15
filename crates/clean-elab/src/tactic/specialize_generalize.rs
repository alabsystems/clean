// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enhanced specialize, generalize, and revert tactics.
//!
//! This module extends the basic tactics in `hypothesis.rs`, `generalize.rs`,
//! and `congr_obtain.rs` with multi-argument and at-hypothesis variants:
//!
//! - [`specialize_multi`]: Apply multiple arguments to a universally quantified hypothesis
//! - [`generalize_at`]: Generalize a term in a specific hypothesis (not the goal)
//! - [`revert_many`]: Revert multiple hypotheses in order
//! - `revert_fvar_with_deps`: Revert a selected local and its dependents by identity

use clean_kernel::{BinderInfo, Expr};

use super::core::{ProofState, TacticError, TacticResult};
use super::equality::contains_expr;

// ============================================================================
// Specialize Multi
// ============================================================================

/// Specialize a hypothesis with multiple arguments at once.
///
/// Given `h : forall (x : A) (y : B x), P x y` and arguments `[a, b]`,
/// replaces `h` with `h : P a b`.
///
/// This applies [`super::hypothesis::specialize`] repeatedly for each argument.
///
/// # Arguments
/// * `state` - The proof state
/// * `hyp_name` - Name of the hypothesis to specialize
/// * `args` - Arguments to apply (in order)
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` names a hypothesis in the local context
/// REQUIRES: The hypothesis has at least `args.len()` nested Pi types
/// REQUIRES: Each argument type matches the corresponding Pi domain
/// ENSURES: On Ok, the hypothesis type is the fully applied codomain
/// ENSURES: On Err, state may be partially modified (args applied so far)
///
/// # Example
/// ```text
/// h : forall (x : Nat) (y : Nat), x + y = y + x
///
/// specialize_multi h [3, 5]
///
/// h : 3 + 5 = 5 + 3
/// ```
pub(crate) fn specialize_multi(
    state: &mut ProofState,
    hyp_name: &clean_parser::SurfaceName,
    args: &[Expr],
) -> TacticResult {
    if args.is_empty() {
        return Ok(());
    }

    for arg in args {
        super::hypothesis::specialize(state, hyp_name, arg.clone())?;
    }

    Ok(())
}

// ============================================================================
// Generalize At Hypothesis
// ============================================================================

/// Generalize a term in a specific hypothesis rather than in the goal.
///
/// Given hypothesis `h : P e` and term `e`, replaces all occurrences of `e`
/// in `h`'s type with a fresh universally quantified variable:
/// `h : forall (x : T), P x`.
///
/// This is the hypothesis-targeted variant of [`super::generalize::generalize`].
///
/// # Arguments
/// * `state` - The proof state
/// * `term` - The term to abstract
/// * `var_name` - Name for the new bound variable (display only)
/// * `hyp_name` - Name of the hypothesis to generalize in
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` names a hypothesis in the local context
/// REQUIRES: `term` appears in the hypothesis type
/// ENSURES: On Ok, the hypothesis type has `term` replaced by a bound
///   variable under a new Pi binder: `forall (var_name : T), hyp_ty[term -> bvar 0]`
/// ENSURES: On Err(InvalidTarget), `term` does not appear in hypothesis
///
/// # Example
/// ```text
/// h : 5 + 0 = 5
///
/// generalize_at 5 as n at h
///
/// h : forall (n : Nat), n + 0 = n
/// ```
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn generalize_at(
    state: &mut ProofState,
    term: Expr,
    var_name: &clean_parser::SurfaceName,
    hyp_name: &clean_parser::SurfaceName,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis
    let hyp_idx = goal
        .local_ctx
        .iter()
        .rposition(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, hyp_name))
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;
    let decl = goal.local_ctx[hyp_idx].clone();

    // Check that the term appears in the hypothesis type
    let hyp_ty = state.metas.instantiate(&decl.ty);
    if !contains_expr(&hyp_ty, &term) {
        return Err(TacticError::InvalidTarget {
            tactic: "generalize_at".into(),
            detail: format!("term does not appear in hypothesis '{hyp_name}'"),
        });
    }

    // Infer the type of the term
    let term_ty = state.infer_type(&goal, &term)?;

    // Abstract over the term: replace all occurrences with bvar(0)
    let abstracted = super::equality::abstract_over(&hyp_ty, &term);

    // Wrap in a Pi binder: forall (var_name : term_ty), abstracted
    let generalized_ty = Expr::pi(BinderInfo::Default, term_ty, abstracted);

    state.replace_local_decl_type_validated(decl.fvar, generalized_ty)?;

    // Update the display name to include the generalization info
    // (keep the original name — Lean 4 semantics)
    let _ = var_name; // var_name used for the Pi binder display, already embedded

    Ok(())
}

// ============================================================================
// Revert Many
// ============================================================================

/// Revert multiple hypotheses back into the goal.
///
/// Applies [`super::congr_obtain::revert`] to each hypothesis in order.
/// The hypotheses are reverted in the order given, which means later
/// hypotheses in the list will appear as outer Pi binders.
///
/// # Arguments
/// * `state` - The proof state
/// * `hyp_names` - Names of hypotheses to revert, in order
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: Each name in `hyp_names` exists in the local context at the
///   time it is reverted (earlier reverts may remove dependencies)
/// ENSURES: On Ok, all named hypotheses are removed from context and the
///   goal target is wrapped with corresponding Pi binders
/// ENSURES: On Err, state may be partially modified (some hypotheses reverted)
///
/// # Example
/// ```text
/// x : Nat, y : Nat |- x + y = y + x
///
/// revert_many [y, x]
///
/// |- forall (x : Nat) (y : Nat), x + y = y + x
/// ```
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn revert_many(
    state: &mut ProofState,
    hyp_names: &[&clean_parser::SurfaceName],
) -> TacticResult {
    for name in hyp_names {
        super::congr_obtain::revert(state, name)?;
    }
    Ok(())
}

// ============================================================================
// Revert With Dependencies
// ============================================================================

/// Revert a hypothesis and all hypotheses that depend on it.
///
/// When reverting `x`, any hypothesis whose type mentions `x` must be
/// reverted first (since removing `x` from context would leave a dangling
/// reference). This function computes the dependency closure and reverts
/// in the correct order: dependents first, then `x`.
///
/// # Arguments
/// * `state` - The proof state
/// * `hyp_name` - Name of the hypothesis to revert
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` names a hypothesis in the local context
/// ENSURES: On Ok, `hyp_name` and all transitive dependents are removed
///   from context and appear as Pi binders in the goal target
/// ENSURES: Dependents are reverted before their dependencies (outermost
///   Pi binders correspond to the deepest dependencies)
///
/// # Returns
/// The list of hypothesis names that were reverted (in revert order).
///
/// # Example
/// ```text
/// x : Nat, h : x > 0 |- P x
///
/// revert_with_deps x
///
/// |- forall (x : Nat), x > 0 -> P x
/// ```
/// Both `h` (depends on `x`) and `x` are reverted. `h` is reverted first
/// since it depends on `x`.
#[cfg(test)]
pub(crate) fn revert_with_deps(
    state: &mut ProofState,
    hyp_name: &clean_parser::SurfaceName,
) -> Result<Vec<clean_parser::SurfaceName>, TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the target hypothesis
    let target_decl = goal
        .local_ctx
        .iter()
        .rev()
        .find(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, hyp_name))
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;
    let target_fvar = target_decl.fvar;

    revert_fvar_with_deps(state, target_fvar)
        .map(|reverted| reverted.into_iter().map(|(_, name)| name).collect())
}

/// Revert an exact local and its dependents, retaining identities in the
/// returned revert order. Internal traversals must not re-resolve duplicate names.
pub(crate) fn revert_fvar_with_deps(
    state: &mut ProofState,
    target_fvar: clean_kernel::FVarId,
) -> Result<Vec<(clean_kernel::FVarId, clean_parser::SurfaceName)>, TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    if !goal.local_ctx.iter().any(|decl| decl.fvar == target_fvar) {
        return Err(TacticError::HypothesisNotFound(crate::error_render::fvar(
            target_fvar,
            None,
        )));
    }

    // Compute the set of FVarIds that need to be reverted.
    // Start with the target, then find all hypotheses whose types
    // transitively depend on any FVar in the set.
    let mut to_revert = std::collections::HashSet::new();
    to_revert.insert(target_fvar);

    // Fixed-point: keep adding dependents until stable
    loop {
        let mut added = false;
        for decl in &goal.local_ctx {
            if to_revert.contains(&decl.fvar) {
                continue;
            }
            if super::major_dependents::generalizing_depends_on(state, decl, &to_revert) {
                to_revert.insert(decl.fvar);
                added = true;
            }
        }
        if !added {
            break;
        }
    }

    // Collect names in reverse context order (last-added dependents first)
    // so that dependents are reverted before their dependencies.
    let revert_order: Vec<_> = goal
        .local_ctx
        .iter()
        .rev()
        .filter(|d| to_revert.contains(&d.fvar))
        .map(|d| (d.fvar, d.name.clone()))
        .collect();

    // Construct the complete telescope once, retaining definitions and scope.
    let fvars: Vec<_> = revert_order.iter().map(|(fvar, _)| *fvar).collect();
    super::major_dependents::revert_fvars(state, &fvars)?;

    Ok(revert_order)
}

// ============================================================================
// Generalize In Goal (convenience wrapper)
// ============================================================================

/// Replace a specific subterm in the goal target with a fresh variable.
///
/// This is a thin wrapper around [`super::generalize::generalize`] for
/// API consistency within this module. The term must appear in the goal.
///
/// # Arguments
/// * `state` - The proof state
/// * `term` - The term to replace
/// * `var_name` - Name for the fresh variable
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `term` appears in the current goal target
/// ENSURES: On Ok, the goal is abstracted over `term` with a fresh
///   variable named `var_name`
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn generalize_in_goal(
    state: &mut ProofState,
    term: Expr,
    var_name: &clean_parser::SurfaceName,
) -> TacticResult {
    super::generalize::generalize(state, term, var_name)
}

// ============================================================================
// Specialize Single (convenience re-export)
// ============================================================================

/// Specialize a hypothesis with a single argument.
///
/// This is a convenience re-export of [`super::hypothesis::specialize`]
/// for API consistency within this module.
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn specialize_single(
    state: &mut ProofState,
    hyp_name: &clean_parser::SurfaceName,
    arg: Expr,
) -> TacticResult {
    super::hypothesis::specialize(state, hyp_name, arg)
}

// ============================================================================
// Revert Single (convenience re-export)
// ============================================================================

/// Revert a single hypothesis back into the goal.
///
/// This is a convenience re-export of [`super::congr_obtain::revert`]
/// for API consistency within this module.
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn revert_single(
    state: &mut ProofState,
    hyp_name: &clean_parser::SurfaceName,
) -> TacticResult {
    super::congr_obtain::revert(state, hyp_name)
}
