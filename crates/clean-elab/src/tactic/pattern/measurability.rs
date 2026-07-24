// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Measurability tactic for proving measurability of functions.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::super::{apply, assumption, ProofState, TacticError, TacticResult};
use super::util::get_app_head;

/// Configuration for measurability tactic
#[derive(Debug, Clone)]
pub struct MeasurabilityConfig {
    /// Maximum depth for composition search
    pub max_depth: usize,
    /// Whether to use all hypotheses
    pub use_all_hyps: bool,
}

impl Default for MeasurabilityConfig {
    fn default() -> Self {
        Self {
            max_depth: 8,
            use_all_hyps: true,
        }
    }
}

impl MeasurabilityConfig {
    /// Create a new default configuration
    pub fn new() -> Self {
        Self::default()
    }
}

/// Measurability tactic for proving measurability of functions
///
/// The `measurability` tactic tries to prove that a function is measurable
/// by applying known measurability lemmas and composing them.
///
/// # Algorithm
/// 1. Check if goal is of form `Measurable f` or `AEMeasurable f mu`
/// 2. Decompose f into primitive operations
/// 3. Apply composition/arithmetic measurability lemmas
///
/// # Example
/// ```text
/// -- Goal: Measurable (fun x => x^2 + 2*x)
/// measurability
/// -- Applies: measurable_add, measurable_mul, measurable_pow, measurable_id
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: The current goal target has head `Measurable`, `AEMeasurable`, `StronglyMeasurable`, or `AEStronglyMeasurable`
/// ENSURES: On Ok, the goal is closed by applying known measurability lemmas and recursive composition
/// ENSURES: On Err(GoalMismatch), the goal target was not a measurability statement
/// ENSURES: On Err(NoProgress), lemma search and hypothesis matching were exhausted
pub fn measurability(state: &mut ProofState) -> TacticResult {
    let mut config = MeasurabilityConfig::default();
    if let Some(max_depth) = state.options().max_depth_override() {
        config.max_depth = max_depth;
    }
    measurability_with_config(state, config)
}

/// Measurability tactic with custom configuration
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the goal is closed; recursive subgoals are solved up to `config.max_depth`
/// ENSURES: If `config.use_all_hyps`, local hypotheses with measurability types are tried via def-eq
pub fn measurability_with_config(
    state: &mut ProofState,
    config: MeasurabilityConfig,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;

    // Check for Measurable f or AEMeasurable f mu patterns
    if !is_measurability_goal(&goal.target) {
        return Err(TacticError::GoalMismatch(
            "goal is not a measurability statement".into(),
        ));
    }

    // Try basic measurability lemmas first
    let basic_lemmas = [
        "measurable_id",
        "measurable_const",
        "Measurable.add",
        "Measurable.sub",
        "Measurable.mul",
        "Measurable.neg",
        "Measurable.pow",
        "Measurable.div",
        "Measurable.comp",
        "AEMeasurable.add",
        "AEMeasurable.mul",
    ];

    // Try to apply each lemma
    for lemma_name in basic_lemmas {
        let lemma = Expr::const_(Name::from_string(lemma_name), vec![]);
        if apply(state, lemma.clone()).is_ok() {
            // Recursively solve subgoals
            let mut depth = 0;
            while !state.goals.is_empty() && depth < config.max_depth {
                if let Some(current) = state.current_goal() {
                    if is_measurability_goal(&current.target) {
                        // Try measurability recursively
                        if measurability_with_config(state, config.clone()).is_err() {
                            break;
                        }
                    } else {
                        // Non-measurability subgoal - try assumption
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
            if is_measurability_type(&decl.ty) {
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
        tactic: "measurability".into(),
    })
}

/// Check if expression is a measurability goal
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed expression
/// ENSURES: Returns `true` iff `expr` has head constant `Measurable`, `AEMeasurable`, `StronglyMeasurable`, or `AEStronglyMeasurable`
pub(crate) fn is_measurability_goal(expr: &Expr) -> bool {
    let head = get_app_head(expr);
    if let ExprKind::Const(name, _) = head.kind() {
        let s = name.to_string();
        s == "Measurable"
            || s == "AEMeasurable"
            || s == "StronglyMeasurable"
            || s == "AEStronglyMeasurable"
    } else {
        false
    }
}

/// Check if type is a measurability statement
fn is_measurability_type(ty: &Expr) -> bool {
    is_measurability_goal(ty)
}
