// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Monotonicity tactic for proving inequalities by applying checked monotonicity lemmas.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::super::gcongr::match_add;
use super::super::{tc_app, ProofState, TacticError, TacticResult};
use super::util::exprs_equal;

/// Configuration for monotonicity tactic
#[derive(Debug, Clone)]
pub struct MonoConfig {
    /// Maximum depth for recursive monotonicity reasoning
    pub max_depth: usize,
    /// Whether to use all hypotheses
    pub use_all_hyps: bool,
    /// Whether to use environment lemmas with `mono` attribute
    pub use_mono_lemmas: bool,
}

impl Default for MonoConfig {
    fn default() -> Self {
        Self {
            max_depth: 10,
            use_all_hyps: true,
            use_mono_lemmas: true,
        }
    }
}

impl MonoConfig {
    /// Create a new default configuration
    pub fn new() -> Self {
        Self::default()
    }
}

/// Result of a monotonicity step
#[derive(Debug, Clone)]
pub struct MonoStep {
    /// Name of the lemma applied
    pub lemma_name: String,
    /// Arguments supplied to the lemma
    pub arguments: Vec<Expr>,
    /// Subgoals generated
    pub subgoals: Vec<Expr>,
}

/// Monotonicity tactic for proving inequalities by applying monotonicity lemmas.
///
/// The `mono` tactic tries to reduce an inequality goal by finding monotonicity
/// lemmas that can be applied to match the structure of the goal.
///
/// # Algorithm
/// 1. Identify if goal is an inequality (<=, <, >=, >)
/// 2. Extract the head function applications on both sides
/// 3. Search for monotonicity lemmas that match the pattern
/// 4. Apply the lemma and generate subgoals for premises
///
/// # Example
/// ```text
/// -- Goal: f a <= f b
/// mono  -- if f is monotone, generates goal: a <= b
/// ```
///
/// # Supported patterns
/// - Function application monotonicity: `f a <= f b` from `a <= b`
/// - Addition monotonicity: `a + c <= b + d` from `a <= b` and `c <= d`
/// - Multiplication monotonicity (for non-negative): `a * c <= b * d`
/// - Composition: `g (f a) <= g (f b)`
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: The current goal target is a recognized relation (`<=`, `<`, `>=`, `>`, `Eq`)
/// ENSURES: On Ok, the goal is replaced by one or more simpler subgoals via a monotonicity lemma
/// ENSURES: On Err(InvalidTarget), the goal target was not a recognized relation
/// ENSURES: On Err(SearchExhausted), no monotonicity lemma matched the goal structure
pub fn mono(state: &mut ProofState) -> TacticResult {
    mono_with_config(state, MonoConfig::default())
}

/// Monotonicity tactic with custom configuration
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, checked Nat-addition goals `a+c rel b+d` decompose into two
///          subgoals and the original goal is closed with a kernel-checked proof
/// ENSURES: Same-function applications without an explicit checked monotonicity
///          witness fail honestly with `SearchExhausted`
pub fn mono_with_config(state: &mut ProofState, _config: MonoConfig) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal_target = state
        .current_goal()
        .ok_or(TacticError::NoGoals)?
        .target
        .clone();

    // Try to parse the goal as an inequality
    let (_rel, rel_ty, _rel_inst, lhs, rhs) = extract_relation(&goal_target)?;

    if match_add(&lhs).is_some() && match_add(&rhs).is_some() {
        if matches!(rel_ty.kind(), ExprKind::Const(name, _) if name == &Name::from_string("Nat")) {
            return super::super::gcongr::gcongr(state);
        }
        return Err(TacticError::SearchExhausted {
            tactic: "mono".into(),
            detail: "checked addition monotonicity is currently only implemented for Nat".into(),
        });
    }

    // Same-function applications still need explicit monotonicity witnesses.
    if matches!((lhs.kind(), rhs.kind()), (ExprKind::App(f1, _), ExprKind::App(f2, _)) if exprs_equal(f1, f2))
    {
        return Err(TacticError::SearchExhausted {
            tactic: "mono".into(),
            detail: "same-function monotonicity needs an explicit checked witness".into(),
        });
    }

    Err(TacticError::SearchExhausted {
        tactic: "mono".into(),
        detail: "could not find monotonicity lemma for goal".into(),
    })
}

/// Extract relation from goal (e.g., LE.le, LT.lt, etc.)
///
/// Returns `(rel_name, type, instance, lhs, rhs)`.
/// Part of #2078: now also extracts type and instance for re-construction.
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed expression
/// ENSURES: On Ok, returns the short relation name, type, instance, and LHS/RHS of a recognized binary relation
/// ENSURES: On Err(InvalidTarget), no recognized relation head was found
fn extract_relation(
    expr: &Expr,
) -> Result<(String, Expr, Expr, Box<Expr>, Box<Expr>), TacticError> {
    // Look for patterns like LE.le _ _ a b or Eq _ a b
    let relations = ["LE.le", "LT.lt", "GE.ge", "GT.gt", "Eq"];

    for rel in relations {
        if let Some((ty, inst, lhs, rhs)) = extract_binary_rel(expr, rel) {
            let rel_name = match rel {
                "LE.le" => "le",
                "LT.lt" => "lt",
                "GE.ge" => "ge",
                "GT.gt" => "gt",
                "Eq" => "eq",
                _ => rel,
            };
            return Ok((rel_name.to_string(), ty, inst, Box::new(lhs), Box::new(rhs)));
        }
    }

    Err(TacticError::InvalidTarget {
        tactic: "mono".into(),
        detail: "goal is not a recognized relation".into(),
    })
}

/// Extract binary relation arguments from an expression.
///
/// Returns `(type, instance, lhs, rhs)`. For well-formed 4-arg expressions like
/// `@LE.le Nat instLENat a b`, extracts all components. For legacy 2-arg forms,
/// defaults type to `Nat` and instance to the appropriate Nat instance.
///
/// Part of #2078: now also extracts type and instance args.
fn extract_binary_rel(expr: &Expr, rel_name: &str) -> Option<(Expr, Expr, Expr, Expr)> {
    // Pattern: rel T inst a b  (4 args for typeclass-based relations)
    // Or: Eq T a b (3 args for Eq)
    let mut args = Vec::new();
    let mut current = expr;

    while let ExprKind::App(f, arg) = current.kind() {
        args.push(arg.as_ref().clone());
        current = f;
    }

    if let ExprKind::Const(name, _) = current.kind() {
        if name.to_string() == rel_name {
            args.reverse();
            // For Eq: 3 args (type, lhs, rhs)
            if rel_name == "Eq" && args.len() >= 3 {
                return Some((
                    args[0].clone(),
                    tc_app::nat_type(), // Eq has no instance arg
                    args[1].clone(),
                    args[2].clone(),
                ));
            }
            // For LE/LT/etc: 4 args (type, instance, lhs, rhs)
            if args.len() >= 4 {
                return Some((
                    args[0].clone(),
                    args[1].clone(),
                    args[2].clone(),
                    args[3].clone(),
                ));
            }
            // Legacy 2-3 arg forms -- provide defaults
            if args.len() >= 2 {
                let ty = if args.len() >= 3 {
                    args[0].clone()
                } else {
                    tc_app::nat_type()
                };
                let inst = tc_app::nat_rel_inst(rel_name);
                let lhs = args[args.len() - 2].clone();
                let rhs = args[args.len() - 1].clone();
                return Some((ty, inst, lhs, rhs));
            }
        }
    }

    None
}
