// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Squeeze simp tactic — tracks which lemmas are actually used during
//! simplification and suggests a minimal `simp only [...]` call.

use clean_kernel::Expr;

use crate::tactic::core::{ProofState, TacticError, TacticResult};
use crate::tactic::{assumption, rfl};

use super::budget::SimpBudget;
use super::cache::collect_simp_lemmas_cached;
use super::types::{SimpConfig, SimpResult};

/// Configuration for squeeze_simp
#[derive(Debug, Clone, Default)]
pub struct SqueezeSimpConfig {
    /// Base simp configuration
    pub simp_config: SimpConfig,
    /// Whether to print verbose output about all attempted lemmas
    pub verbose: bool,
}

impl SqueezeSimpConfig {
    pub fn new() -> Self {
        Self::default()
    }
}

/// Result of squeeze_simp showing which lemmas were used
#[derive(Debug, Clone)]
pub struct SqueezeSimpResult {
    /// The lemmas that were actually used during simplification
    pub used_lemmas: Vec<String>,
    /// Suggested replacement: "simp only [lemma1, lemma2, ...]"
    pub suggested_tactic: String,
    /// Whether the goal was closed
    pub closed: bool,
}

#[derive(Debug, Clone)]
struct TrackedSimpStep {
    result: SimpResult,
    applied_named_lemmas: Vec<String>,
    applied_reduction: Option<String>,
}

fn push_unique_lemma(target: &mut Vec<String>, lemma: String) {
    if !target.contains(&lemma) {
        target.push(lemma);
    }
}

fn extend_unique_lemmas(target: &mut Vec<String>, lemmas: impl IntoIterator<Item = String>) {
    for lemma in lemmas {
        push_unique_lemma(target, lemma);
    }
}

/// Tactic: squeeze_simp
///
/// Like `simp`, but tracks which lemmas were actually used during simplification.
/// Returns a `SqueezeSimpResult` with the suggested `simp only [...]` call.
///
/// This is useful for:
/// - Speeding up proofs by replacing `simp` with `simp only [...]`
/// - Making proofs more robust by explicitly listing dependencies
/// - Debugging which lemmas are being applied
///
/// # Example
/// ```text
/// -- Goal: a + 0 + 0 = a
/// squeeze_simp
/// -- Output: "Try: simp only [Nat.add_zero]"
/// -- Goal closed
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
pub fn squeeze_simp(state: &mut ProofState) -> Result<SqueezeSimpResult, TacticError> {
    squeeze_simp_with_config(state, SqueezeSimpConfig::new())
}

/// squeeze_simp with custom configuration
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: `used_lemmas` contains each applied lemma name exactly once, in application order
/// ENSURES: If `closed == true`, the goal was closed via rfl or assumption after simplification
/// ENSURES: If no progress, `used_lemmas` is empty and goal target is unchanged
/// ENSURES: On Err(NoGoals), no goals exist; state unchanged
pub fn squeeze_simp_with_config(
    state: &mut ProofState,
    config: SqueezeSimpConfig,
) -> Result<SqueezeSimpResult, TacticError> {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let mut current_target = goal.target.clone();
    let mut steps = 0;
    let mut used_lemmas: Vec<String> = Vec::new();
    let mut accumulated_proof: Option<Expr> = None;

    // Collect simp lemmas from environment
    let simp_lemmas = collect_simp_lemmas_cached(state, &config.simp_config);

    // `simp?` runs the same traversal `simp` does, so it carries the same
    // per-traversal budget (see `budget.rs`). A trip refuses the whole
    // squeeze rather than suggesting a lemma list assembled from a rewrite
    // the engine could not finish.
    let budget = SimpBudget::for_target(&current_target);

    // Main simplification loop - track which lemmas are actually applied
    while steps < config.simp_config.max_steps {
        budget.refuel();
        let step = simp_expr_tracking(
            state,
            &goal,
            &current_target,
            &simp_lemmas,
            &config.simp_config,
            &budget,
        );

        if let Some(detail) = budget.detail() {
            return Err(TacticError::BudgetExceeded {
                tactic: "simp?".into(),
                detail,
            });
        }

        if step.result.expr != current_target {
            accumulated_proof = match (accumulated_proof.take(), step.result.proof) {
                (None, proof) => proof,
                (proof, None) => proof,
                (Some(p1), Some(p2)) => {
                    Some(super::mk_eq_trans_expr(state, &goal, &p1, &p2).unwrap_or(p2))
                }
            };

            let applied_lemmas = if step.applied_named_lemmas.is_empty() {
                step.applied_reduction.into_iter().collect()
            } else {
                step.applied_named_lemmas
            };
            extend_unique_lemmas(&mut used_lemmas, applied_lemmas);
            current_target = step.result.expr;
            steps += 1;
        } else {
            break;
        }
    }

    let made_progress = current_target != goal.target;

    // Part of #2503: preserve proof-carry target rewrites instead of falling
    // back to trustedArith on successful simplification.
    if made_progress {
        if let Some(proof) = accumulated_proof {
            state.replace_target_eq(current_target.clone(), proof)?;
        } else {
            state.replace_target_def_eq(current_target.clone())?;
        }
    }

    // Try to close with reflexivity
    let closed = if config.simp_config.only_simplify {
        false
    } else {
        rfl(state).is_ok() || assumption(state).is_ok()
    };

    // Generate suggested tactic
    let suggested_tactic = if used_lemmas.is_empty() {
        "simp only []".to_string()
    } else {
        format!("simp only [{}]", used_lemmas.join(", "))
    };

    Ok(SqueezeSimpResult {
        used_lemmas,
        suggested_tactic,
        closed,
    })
}

/// squeeze_simp and apply the result
pub fn squeeze_simp_and_apply(state: &mut ProofState) -> TacticResult {
    let result = squeeze_simp(state)?;
    if result.closed {
        Ok(())
    } else {
        Err(TacticError::NoProgress {
            tactic: "squeeze_simp".into(),
        })
    }
}

mod tracking;
use tracking::simp_expr_tracking;

#[cfg(test)]
mod tests;
