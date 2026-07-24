// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cast-related tactics
//!
//! Tactics for handling type coercions and casts between numeric types.
//!
//! # Tactics
//! - `push_cast` - Push coercions toward leaves of expressions
//! - `exact_mod_cast` - Close goal with exact proof, handling casts automatically
//! - `assumption_mod_cast` - Close goal with assumption, handling casts
//! - `zify` - Convert natural number goals to integer goals
//! - `qify` - Convert integer goals to rational goals
//! - `lift` - Lift values from subtypes to base types

mod coerce;
pub(crate) mod proof_carry;

pub use coerce::{qify, zify};
pub(crate) use proof_carry::{
    rewrite_local_decls_with_cast_lemmas, rewrite_target_with_cast_lemmas, CastRewriteFlavor,
};
// Test-only re-exports: used by tactic test modules
#[cfg(test)]
pub(crate) use coerce::{qify_expr, zify_expr};

#[cfg(test)]
use std::sync::Arc;

#[cfg(test)]
use clean_kernel::expr::ExprKind;
use clean_kernel::Expr;

#[cfg(test)]
use crate::stack_safe;

#[cfg(test)]
use super::is_cast_function;
use super::{
    assumption, exact, norm_cast, norm_num, rfl, ring, try_tactic_preserving_state, ProofState,
    TacticError, TacticResult,
};
#[cfg(test)]
use crate::tactic::get_app_fn;

// =============================================================================
// push_cast: push coercions toward leaves
// =============================================================================

/// Push cast tactic.
///
/// Pushes coercions (casts) toward the leaves of expressions, which is the
/// opposite direction of `norm_cast`. Useful when you want casts at the
/// atomic level.
///
/// # Example
/// ```text
/// -- Goal: ↑(a + b) = ↑a + ↑b
/// push_cast
/// -- Goal: ↑a + ↑b = ↑a + ↑b (then closes with rfl)
/// ```
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, casts in the current goal target are pushed toward leaves.
///   If the pushed forms become syntactically equal, the goal is closed via `rfl`.
/// ENSURES: May further close the goal via `ring` or `norm_num` fallbacks.
pub fn push_cast(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Part of #2516: use proof-carry rewrite via simp engine instead of
    // heuristic AST surgery + replace_target_with_trusted_fallback.
    let rewrote = rewrite_target_with_cast_lemmas(state, "push_cast", CastRewriteFlavor::PushCast)?;

    if rewrote {
        // Closeout order: rfl → ring → norm_num
        if rfl(state).is_ok() {
            return Ok(());
        }
        if ring(state).is_ok() {
            return Ok(());
        }
        if norm_num(state).is_ok() {
            return Ok(());
        }
        return Ok(());
    }

    // Simp engine made no progress — try norm_num directly
    if norm_num(state).is_ok() {
        return Ok(());
    }

    Ok(())
}

/// Push casts toward leaves of an expression
///
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns a structurally equivalent expression where cast applications
///   are distributed over arithmetic operations (add, mul, sub) toward atomic terms.
/// ENSURES: Non-cast sub-expressions are recursively traversed but not modified.
#[cfg(test)]
pub(crate) fn push_casts_to_leaves(expr: &Expr) -> Expr {
    stack_safe(|| match expr.kind() {
        ExprKind::App(f, arg) => {
            // Check for cast application
            if is_cast_function(f) {
                // Push cast into the argument
                return push_cast_into(arg, f);
            }

            // Regular application - recurse
            Expr::app(push_casts_to_leaves(f), push_casts_to_leaves(arg))
        }
        ExprKind::Lam(bind_info, ty, body) => Expr::lam(
            *bind_info,
            push_casts_to_leaves(ty),
            push_casts_to_leaves(body),
        ),
        ExprKind::Pi(bind_info, ty, body) => Expr::pi(
            *bind_info,
            push_casts_to_leaves(ty),
            push_casts_to_leaves(body),
        ),
        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            push_casts_to_leaves(ty),
            push_casts_to_leaves(val),
            push_casts_to_leaves(body),
            *non_dep,
        ),
        ExprKind::Proj(name, idx, inner) => {
            Expr::proj(name.clone(), *idx, push_casts_to_leaves(inner))
        }
        ExprKind::MData(md, inner) => Expr::mdata(md.clone(), push_casts_to_leaves(inner)),
        ExprKind::Squash(inner) => {
            Expr::from_kind(ExprKind::Squash(Arc::new(push_casts_to_leaves(inner))))
        }
        _ => expr.clone(),
    })
}

/// Push a cast into an expression
///
/// REQUIRES: `expr` is a well-formed expression; `cast_fn` is a cast function expression.
/// ENSURES: For add/mul/sub applications, returns the operation with `cast_fn` pushed
///   recursively into each operand.
/// ENSURES: For atomic expressions, returns `App(cast_fn, expr)`.
#[cfg(test)]
pub(crate) fn push_cast_into(expr: &Expr, cast_fn: &Expr) -> Expr {
    stack_safe(|| match expr.kind() {
        ExprKind::App(f, arg2) => {
            if let ExprKind::App(f2, arg1) = f.kind() {
                if let ExprKind::Const(name, _) = get_app_fn(f2).kind() {
                    let name_str = name.to_string();

                    // Push cast over addition
                    if name_str.contains("add") || name_str.contains("Add") {
                        let cast_a = push_cast_into(arg1, cast_fn);
                        let cast_b = push_cast_into(arg2, cast_fn);
                        return Expr::app(Expr::app((**f2).clone(), cast_a), cast_b);
                    }

                    // Push cast over multiplication
                    if name_str.contains("mul") || name_str.contains("Mul") {
                        let cast_a = push_cast_into(arg1, cast_fn);
                        let cast_b = push_cast_into(arg2, cast_fn);
                        return Expr::app(Expr::app((**f2).clone(), cast_a), cast_b);
                    }

                    // Push cast over subtraction
                    if name_str.contains("sub") || name_str.contains("Sub") {
                        let cast_a = push_cast_into(arg1, cast_fn);
                        let cast_b = push_cast_into(arg2, cast_fn);
                        return Expr::app(Expr::app((**f2).clone(), cast_a), cast_b);
                    }
                }
            }
            // Can't push further - apply cast here
            Expr::app(cast_fn.clone(), expr.clone())
        }
        // Atomic - apply cast
        _ => Expr::app(cast_fn.clone(), expr.clone()),
    })
}

// ============================================================================
// Cast-related tactics: exact_mod_cast, assumption_mod_cast
// ============================================================================

/// Configuration for cast normalization.
#[derive(Debug, Clone)]
pub struct CastConfig {
    /// Whether to push casts inward
    pub push_inward: bool,
    /// Whether to pull casts outward
    pub pull_outward: bool,
}

impl Default for CastConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl CastConfig {
    /// Create default configuration (push inward)
    pub fn new() -> Self {
        Self {
            push_inward: true,
            pull_outward: false,
        }
    }
}

/// Close the goal with an exact proof term, automatically handling casts.
///
/// `exact_mod_cast` is like `exact`, but it first normalizes casts in both
/// the goal and the proof term before checking if they match.
///
/// # Example
/// ```text
/// -- h : (n : ℤ) = (m : ℤ)
/// -- Goal: (n : ℚ) = (m : ℚ)
/// exact_mod_cast h
/// ```
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: `proof` is a well-formed proof term.
/// ENSURES: On `Ok(())`, the current goal is closed by `exact` after cast normalization
///   (tries push_cast, then norm_cast, then raw exact).
/// ENSURES: State is preserved on failure (each sub-attempt uses `try_tactic_preserving_state`).
pub fn exact_mod_cast(state: &mut ProofState, proof: Expr) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Try push_cast then exact, preserving state on failure
    if try_tactic_preserving_state(state, |s| {
        let _ = push_cast(s);
        exact(s, proof.clone())
    }) {
        return Ok(());
    }

    // Try norm_cast then exact
    if try_tactic_preserving_state(state, |s| {
        let _ = norm_cast(s);
        exact(s, proof.clone())
    }) {
        return Ok(());
    }

    // Try the original exact
    exact(state, proof)
}

/// Close the goal with an assumption, automatically handling casts.
///
/// `assumption_mod_cast` is like `assumption`, but it normalizes casts
/// before checking if any hypothesis matches the goal.
///
/// # Example
/// ```text
/// -- h : (n : ℤ) < (m : ℤ)
/// -- Goal: (n : ℚ) < (m : ℚ)
/// assumption_mod_cast
/// ```
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the current goal is closed by matching a hypothesis after
///   cast normalization (tries push_cast, then norm_cast, then raw assumption).
/// ENSURES: State is preserved on failure of each sub-attempt.
pub fn assumption_mod_cast(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Try push_cast then assumption, preserving state on failure
    if try_tactic_preserving_state(state, |s| {
        let _ = push_cast(s);
        assumption(s)
    }) {
        return Ok(());
    }

    // Try norm_cast then assumption
    if try_tactic_preserving_state(state, |s| {
        let _ = norm_cast(s);
        assumption(s)
    }) {
        return Ok(());
    }

    // Try regular assumption
    assumption(state)
}

// ============================================================================
// lift - Lift values from subtypes
// ============================================================================

/// Configuration for lift tactic.
#[derive(Debug, Clone)]
pub struct LiftConfig {
    /// Name for the lifted variable
    pub new_name: Option<String>,
    /// Name for the proof that the value satisfies the predicate
    pub proof_name: Option<String>,
}

impl Default for LiftConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl LiftConfig {
    /// Create default configuration
    pub fn new() -> Self {
        Self {
            new_name: None,
            proof_name: None,
        }
    }

    /// Set the name for the lifted variable
    #[must_use]
    pub fn with_name(mut self, name: &str) -> Self {
        self.new_name = Some(name.to_string());
        self
    }

    /// Set the name for the proof
    #[must_use]
    pub fn with_proof(mut self, name: &str) -> Self {
        self.proof_name = Some(name.to_string());
        self
    }
}

/// Lift a value from a subtype to its base type.
///
/// Given a hypothesis `h : ↑n = m` or a subtype element `x : {n : α // P n}`,
/// `lift` introduces the underlying value and a proof of the predicate.
///
/// # Example
/// ```text
/// -- x : ℕ, h : ↑x = (y : ℤ)
/// lift x to ℤ using h
/// -- Currently fails closed: proof-carrying subtype/cast lift is unsupported
/// ```
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: `var_name` identifies a variable in the current goal's local context.
/// ENSURES: Until proof-carrying subtype/cast lifting is implemented, a
///   well-formed request returns `Err(InvalidTarget)` without changing state.
/// ENSURES: Never introduces an unproved placeholder hypothesis.
/// ENSURES: Returns `Err(HypothesisNotFound)` if `var_name` or `using_hyp` is missing.
pub fn lift(state: &mut ProofState, var_name: &str, using_hyp: Option<&str>) -> TacticResult {
    lift_with_config(state, var_name, using_hyp, LiftConfig::new())
}

/// lift with custom configuration
///
/// REQUIRES: `state.goals` is non-empty; `var_name` exists in local context.
/// ENSURES: If `using_hyp` is `Some(h)`, validates that `h` exists in the local context.
/// ENSURES: After validation, returns `Err(InvalidTarget)` without changing state
///   until a semantically correct proof-carrying lift is implemented.
/// ENSURES: Never introduces an unproved placeholder hypothesis.
pub fn lift_with_config(
    state: &mut ProofState,
    var_name: &str,
    using_hyp: Option<&str>,
    config: LiftConfig,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the variable to lift
    let _var_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == var_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(format!("variable '{var_name}' not found")))?
        .clone();

    // Check if there's a hypothesis we can use
    if let Some(hyp_name) = using_hyp {
        let _hyp = goal
            .local_ctx
            .iter()
            .find(|d| d.name == hyp_name)
            .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;
    }

    let _ = config;
    Err(TacticError::InvalidTarget {
        tactic: "lift".into(),
        detail: "proof-carrying subtype/cast lifting is not implemented for this target; refusing to introduce an unproved placeholder".into(),
    })
}
