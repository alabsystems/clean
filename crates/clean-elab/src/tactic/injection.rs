// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `TacticCtx`-based wrappers for injection and discriminate tactics.
//!
//! These wrap the core implementations in [`super::inductive_reasoning`] and
//! add the `eval_*` naming convention for the combinator framework.
//!
//! - `eval_injection`: Given `h : C a₁ a₂ = C b₁ b₂` (same constructor),
//!   derives field equalities `a₁ = b₁`, `a₂ = b₂` as new hypotheses.
//! - `eval_discriminate`: Given `h : C₁ ... = C₂ ...` (different constructors),
//!   closes the goal via noConfusion.

use clean_kernel::name::Name;

use super::combinators::TacticCtx;
use super::core::TacticResult;

/// Injection tactic via `TacticCtx`.
///
/// Given a hypothesis `hyp : C a₁ ... aₙ = C b₁ ... bₙ` where `C` is a
/// constructor, derives equalities `aᵢ = bᵢ` for each field and adds them
/// to the local context.
///
/// Uses `T.noConfusion` to build the injectivity proof. The continuation
/// meta is wrapped in a lambda chain `λ h₁ ... hₖ => ?meta` matching
/// the noConfusion motive type.
///
/// # Contract
///
/// REQUIRES: `ctx.state.goals` is non-empty
/// REQUIRES: `hyp_name` refers to a hypothesis of type `C a₁ ... aₙ = C b₁ ... bₙ`
/// ENSURES: On Ok, new hypotheses `a₁ = b₁`, ..., `aₙ = bₙ` are in context
/// ENSURES: On Err(HypothesisNotFound), `hyp_name` is not in the local context
/// ENSURES: On Err(GoalMismatch), the hypothesis is not an equality of same-constructor terms
pub fn eval_injection(ctx: &mut TacticCtx, hyp_name: &Name) -> TacticResult {
    super::inductive_reasoning::injection(ctx.state, &hyp_name.to_string())
}

/// Discriminate tactic via `TacticCtx`.
///
/// Given a hypothesis `hyp : C₁ args = C₂ args` where `C₁ ≠ C₂` are
/// constructors of the same inductive type, closes the goal because
/// different constructors can never be equal (no confusion principle).
///
/// # Contract
///
/// REQUIRES: `ctx.state.goals` is non-empty
/// REQUIRES: `hyp_name` refers to a hypothesis equating two distinct constructors
/// ENSURES: On Ok, the current goal is closed (contradiction from distinct constructors)
/// ENSURES: On Err(GoalMismatch), the hypothesis does not match the pattern
pub fn eval_discriminate(ctx: &mut TacticCtx, hyp_name: &Name) -> TacticResult {
    super::inductive_reasoning::discriminate(ctx.state, &hyp_name.to_string())
}

/// Injection tactic taking a string hypothesis name.
///
/// Convenience wrapper for registry dispatch where the hypothesis name
/// is already resolved to a string.
///
/// REQUIRES: same as [`eval_injection`]
/// ENSURES: same as [`eval_injection`]
pub fn eval_injection_str(ctx: &mut TacticCtx, hyp_name: &str) -> TacticResult {
    super::inductive_reasoning::injection(ctx.state, hyp_name)
}

/// Discriminate tactic taking a string hypothesis name.
///
/// Convenience wrapper for registry dispatch where the hypothesis name
/// is already resolved to a string.
///
/// REQUIRES: same as [`eval_discriminate`]
/// ENSURES: same as [`eval_discriminate`]
pub fn eval_discriminate_str(ctx: &mut TacticCtx, hyp_name: &str) -> TacticResult {
    super::inductive_reasoning::discriminate(ctx.state, hyp_name)
}

/// Check whether a hypothesis `h : lhs = rhs` has both sides as constructor
/// applications, and if so whether they are the same or different constructors.
///
/// Returns `Some((true, ctor_name))` for same constructors (injection candidate),
/// `Some((false, ctor_name))` for different constructors (discriminate candidate),
/// or `None` if the hypothesis is not an equality of constructor applications.
///
/// This is a lightweight classifier for automation tactics that need to dispatch
/// between injection and discriminate without running either.
#[cfg(test)]
pub(crate) fn classify_constructor_equality(
    state: &super::core::ProofState,
    goal: &super::core::Goal,
    hyp_ty: &clean_kernel::Expr,
) -> Option<(bool, String)> {
    let ty_whnf = state.whnf(goal, hyp_ty);
    let (_eq_type, lhs, rhs, _eq_levels) = super::equality::match_equality(&ty_whnf).ok()?;

    let lhs_whnf = state.whnf(goal, &lhs);
    let rhs_whnf = state.whnf(goal, &rhs);

    let lhs_head = lhs_whnf.get_app_fn();
    let rhs_head = rhs_whnf.get_app_fn();

    let lhs_name = match lhs_head.kind() {
        clean_kernel::ExprKind::Const(name, _) => name.clone(),
        _ => return None,
    };
    let rhs_name = match rhs_head.kind() {
        clean_kernel::ExprKind::Const(name, _) => name.clone(),
        _ => return None,
    };

    // Both must be constructors
    let lhs_ctor = state.env.get_constructor(&lhs_name)?;
    let rhs_ctor = state.env.get_constructor(&rhs_name)?;

    // Must be of the same inductive type
    if lhs_ctor.inductive_name != rhs_ctor.inductive_name {
        return None;
    }

    let same = lhs_name == rhs_name;
    Some((same, lhs_name.to_string()))
}
