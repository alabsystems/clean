// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Continuity tactic for proving continuity of functions.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::super::{apply, assumption, ProofState, TacticError, TacticResult};
use super::util::get_app_head;

/// Configuration for continuity tactic
#[derive(Debug, Clone)]
pub struct ContinuityConfig {
    /// Maximum depth for composition search
    pub max_depth: usize,
    /// Whether to use all hypotheses
    pub use_all_hyps: bool,
}

impl Default for ContinuityConfig {
    fn default() -> Self {
        Self {
            max_depth: 8,
            use_all_hyps: true,
        }
    }
}

impl ContinuityConfig {
    /// Create a new default configuration
    pub fn new() -> Self {
        Self::default()
    }
}

/// Continuity tactic for proving continuity of functions
///
/// The `continuity` tactic tries to prove that a function is continuous
/// by applying known continuity lemmas and composing them.
///
/// # Algorithm
/// 1. Check if goal is of form `Continuous f` or `ContinuousAt f x`
/// 2. Decompose f into primitive operations
/// 3. Apply composition/arithmetic continuity lemmas
///
/// # Example
/// ```text
/// -- Goal: Continuous (fun x => x^2 + 2*x + 1)
/// continuity
/// -- Applies: continuous_add, continuous_mul, continuous_pow, continuous_const
/// ```
///
/// # Supported lemmas
/// - continuous_id, continuous_const
/// - continuous_add, continuous_sub, continuous_mul, continuous_neg
/// - continuous_div (with non-zero denominator)
/// - continuous_pow, continuous_exp, continuous_log
/// - Continuous.comp for composition
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: Equivalent to `continuity_with_config(state, ContinuityConfig::default())`
pub fn continuity(state: &mut ProofState) -> TacticResult {
    let mut config = ContinuityConfig::default();
    if let Some(max_depth) = state.options().max_depth_override() {
        config.max_depth = max_depth;
    }
    continuity_with_config(state, config)
}

/// Continuity tactic with custom configuration
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the current goal is discharged either by continuity lemmas or a matching local hypothesis
/// ENSURES: On Err(GoalMismatch), the current goal target is not a supported continuity predicate
/// ENSURES: Recursive lemma search stops once `config.max_depth` steps are taken for a branch
pub fn continuity_with_config(state: &mut ProofState, config: ContinuityConfig) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;

    // Check for Continuous f or ContinuousAt f x patterns
    if !is_continuity_goal(&goal.target) {
        return Err(TacticError::GoalMismatch(
            "goal is not a continuity statement".into(),
        ));
    }

    // Try basic continuity lemmas first
    let basic_lemmas = [
        "continuous_id",
        "continuous_const",
        "Continuous.add",
        "Continuous.sub",
        "Continuous.mul",
        "Continuous.neg",
        "Continuous.pow",
        "Continuous.div",
        "Continuous.comp",
    ];

    // Try to apply each lemma
    for lemma_name in basic_lemmas {
        let lemma = Expr::const_(Name::from_string(lemma_name), vec![]);
        if apply(state, lemma.clone()).is_ok() {
            // Recursively solve subgoals
            let mut depth = 0;
            while !state.goals.is_empty() && depth < config.max_depth {
                if let Some(current) = state.current_goal() {
                    if is_continuity_goal(&current.target) {
                        // Try continuity recursively
                        if continuity_with_config(state, config.clone()).is_err() {
                            break;
                        }
                    } else {
                        // Non-continuity subgoal - try assumption
                        if assumption(state).is_err() {
                            break;
                        }
                    }
                } else {
                    break;
                }
                depth += 1;
            }

            if state.goals.is_empty() {
                return Ok(());
            }
        }
    }

    // Try hypotheses
    if config.use_all_hyps {
        let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
        for decl in &goal.local_ctx {
            if is_continuity_type(&decl.ty) {
                // (#2229: use goal's local context so FVars resolve)
                if state.is_def_eq(&goal, &decl.ty, &goal.target) {
                    // Part of #2154 Tier A: is_def_eq guard verified type match.
                    state.close_goal(&goal, Expr::fvar(decl.fvar))?;
                    return Ok(());
                }
            }
        }
    }

    Err(TacticError::NoProgress {
        tactic: "continuity".into(),
    })
}

/// Check if expression is a continuity goal
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed expression
/// ENSURES: Returns `true` iff the head constant is one of `Continuous`, `ContinuousAt`, `ContinuousOn`, or `ContinuousWithinAt`
pub(crate) fn is_continuity_goal(expr: &Expr) -> bool {
    let head = get_app_head(expr);
    if let ExprKind::Const(name, _) = head.kind() {
        let s = name.to_string();
        s == "Continuous" || s == "ContinuousAt" || s == "ContinuousOn" || s == "ContinuousWithinAt"
    } else {
        false
    }
}

/// Check if type is a continuity statement
fn is_continuity_type(ty: &Expr) -> bool {
    is_continuity_goal(ty)
}
