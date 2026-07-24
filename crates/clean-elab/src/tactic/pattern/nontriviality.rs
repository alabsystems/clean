// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! nontriviality tactic: create an obligation that the relevant type is nontrivial.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

use super::super::{have_, ProofState, TacticError, TacticResult};
use super::util::{find_first_type, generate_fresh_hyp_name, try_extract_eq, try_infer_expr_type};

/// Configuration for nontriviality tactic
#[derive(Debug, Clone, Default)]
pub struct NontrivialityConfig {
    /// Type to assume is nontrivial (inferred from goal if None)
    pub type_expr: Option<Expr>,
}

impl NontrivialityConfig {
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn with_type(mut self, ty: Expr) -> Self {
        self.type_expr = Some(ty);
        self
    }
}

/// nontriviality tactic: prove the relevant type is nontrivial
///
/// In Mathlib, many lemmas about algebraic structures require that the
/// underlying type has at least two distinct elements. The `nontriviality`
/// tactic creates a proof obligation for this fact when needed.
///
/// # Example
/// ```text
/// -- Goal: a != b (for some type R)
/// nontriviality
/// -- First prove h : Nontrivial R, then continue with h in context
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the original goal is replaced by a `Nontrivial <type>` proof
///   obligation in the original context and a continuation carrying that proved fact
/// ENSURES: The type is inferred from the goal target (inequality, equality, or first type found)
/// ENSURES: No `Nontrivial <type>` proof is assumed or fabricated
/// ENSURES: On Err(InvalidTarget), the type could not be inferred from the goal
pub fn nontriviality(state: &mut ProofState) -> TacticResult {
    nontriviality_with_config(state, NontrivialityConfig::new())
}

/// nontriviality with configuration
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the original goal is replaced by a fresh `Nontrivial <type>`
///   proof obligation and a continuation with that proved fact in scope
/// ENSURES: If `config.type_expr` is `Some(t)`, that type is used; otherwise the type is inferred from the goal
/// ENSURES: No `Nontrivial <type>` proof is assumed or fabricated
pub fn nontriviality_with_config(
    state: &mut ProofState,
    config: NontrivialityConfig,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = goal.target.clone();

    // Determine the type to make nontrivial
    let ty = match config.type_expr {
        Some(t) => t,
        None => infer_nontrivial_type(&target)?,
    };

    // Create the Nontrivial constraint
    let nontrivial_ty = Expr::app(
        Expr::const_(Name::from_string("Nontrivial"), vec![Level::Zero]),
        ty.clone(),
    );

    // Generate a fresh hypothesis name
    let hyp_name = generate_fresh_hyp_name(&goal.local_ctx, "h_nontrivial");

    // Introduce the fact through a proof-carrying continuation.  The first
    // generated goal must establish it; only the continuation may use it.
    have_(state, &hyp_name, nontrivial_ty, None)
}

/// Infer the type that should be nontrivial from the goal
fn infer_nontrivial_type(target: &Expr) -> Result<Expr, TacticError> {
    // Look for patterns that suggest a type:
    // - a != b : infer type from a or b
    // - division, multiplication contexts

    // Check for inequality (not (a = b) or Ne a b)
    if let Some((lhs, _rhs)) = try_extract_ne(target) {
        // Try to infer type from lhs
        if let Some(ty) = try_infer_expr_type(&lhs) {
            return Ok(ty);
        }
    }

    // Check for explicit Eq pattern
    if let Some((lhs, _rhs)) = try_extract_eq(target) {
        if let Some(ty) = try_infer_expr_type(&lhs) {
            return Ok(ty);
        }
    }

    // Default: look for any type variable in the expression
    if let Some(ty) = find_first_type(target) {
        return Ok(ty);
    }

    Err(TacticError::InvalidTarget {
        tactic: "nontriviality".into(),
        detail: "could not infer type from goal".into(),
    })
}

/// Try to extract inequality: Ne a b or not (a = b)
fn try_extract_ne(expr: &Expr) -> Option<(Expr, Expr)> {
    // Ne is App(App(App(Ne, ty), a), b)
    if let ExprKind::App(f1, b) = expr.kind() {
        if let ExprKind::App(f2, a) = f1.kind() {
            if let ExprKind::App(ne_const, _ty) = f2.kind() {
                if let ExprKind::Const(name, _) = ne_const.kind() {
                    let s = name.to_string();
                    if s == "Ne" || s.ends_with(".Ne") {
                        return Some((a.as_ref().clone(), b.as_ref().clone()));
                    }
                }
            }
        }
    }

    // Also check for Not (Eq a b) = App(Not, App(App(App(Eq, ty), a), b))
    if let ExprKind::App(not_const, eq_expr) = expr.kind() {
        if let ExprKind::Const(name, _) = not_const.kind() {
            let s = name.to_string();
            if s == "Not" || s.ends_with(".Not") {
                return try_extract_eq(eq_expr);
            }
        }
    }

    None
}

/// nontriviality with explicit type
///
/// # Contract
///
/// REQUIRES: same as `nontriviality_with_config`
/// ENSURES: Behaves like `nontriviality_with_config(state, config.with_type(ty))`
pub fn nontriviality_of(state: &mut ProofState, ty: Expr) -> TacticResult {
    nontriviality_with_config(state, NontrivialityConfig::new().with_type(ty))
}
