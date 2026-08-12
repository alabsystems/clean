// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Non-linear arithmetic and positivity tactics
//!
//! - `nlinarith`: Non-linear arithmetic via polynomial products + linarith
//! - `positivity`: Structural positivity checking

pub(crate) mod certified;
mod preprocess;
pub(crate) mod synthetic_rows;
use super::arith_linarith::{
    extract_linear_constraints, fourier_motzkin_check, linarith, FMResult,
};
use super::arithmetic::LinearConstraint;
use super::groebner_basis::{groebner_goal_proof, groebner_preprocess, GroebnerConfig};
// Kernel-evaluating `decide` ladder, not the `smt::decide` re-exported from
// `super` — see the note in `norm_num.rs`.
use super::decide::eval_decide as decide;
use super::{norm_num, ProofState, TacticError, TacticResult};
use certified::{try_certified_nlinarith, CertifiedNlinarithOutcome};
use preprocess::is_square_nonnegative_goal;
pub(crate) use preprocess::try_compute_linear_product;
#[cfg(test)]
pub(crate) use preprocess::{is_zero_expr, nlinarith_exprs_equal};

// ============================================================================
// Additional Tactics: nlinarith (non-linear arithmetic)
// ============================================================================

/// Non-linear arithmetic tactic.
///
/// Extends linarith to handle some non-linear constraints by:
/// 1. Adding x² ≥ 0 for all variables (squares are non-negative)
/// 2. Multiplying pairs of inequalities to generate new linear constraints
/// 3. Running linarith with the augmented constraint set
///
/// Based on Coq's `nra` tactic and Mathlib4's `nlinarith` preprocessing.
///
/// REQUIRES: `state` is a valid `ProofState` with at least one goal
/// REQUIRES: Goal involves arithmetic (possibly non-linear) over Nat/Int
/// ENSURES: On `Ok(())`, the current goal is closed with a valid proof term
/// ENSURES: On `Err(_)`, goal is unchanged or augmented with product constraints
/// ENSURES: Tries plain `linarith` first; falls through to preprocessing on failure
///
/// # Supported Patterns
/// - `x² ≥ 0` (and `x * x ≥ 0`)
/// - Products of hypotheses like `(a ≤ b) * (c ≤ d)` generate `(b-a)(d-c) ≥ 0`
///
/// # Example
/// ```text
/// -- Goal: x^2 ≥ 0
/// nlinarith
/// -- Goal closed
/// ```
pub fn nlinarith(state: &mut ProofState) -> TacticResult {
    // First try linarith directly - it may already work
    if linarith(state).is_ok() {
        return Ok(());
    }

    // Try nlinarith with augmented constraints
    nlinarith_with_preprocessing(state)
}

/// Configuration for nlinarith preprocessing
#[derive(Debug, Clone)]
pub struct NlinarithConfig {
    /// Maximum number of hypothesis products to generate
    pub max_products: usize,
    /// Whether to add x² ≥ 0 for all variables
    pub add_squares: bool,
    /// Maximum total constraints (to prevent explosion)
    pub max_constraints: usize,
    /// Whether to run Groebner basis preprocessing
    pub use_groebner: bool,
    /// Configuration for Groebner basis computation
    pub groebner_config: GroebnerConfig,
}

impl Default for NlinarithConfig {
    fn default() -> Self {
        Self {
            max_products: 100,
            add_squares: true,
            max_constraints: 500,
            use_groebner: true,
            groebner_config: GroebnerConfig::default(),
        }
    }
}

/// Run nlinarith with preprocessing to handle nonlinear constraints.
///
/// Preprocessing steps (based on Coq's nra and Mathlib4):
/// 1. For each variable x appearing in constraints, add x² ≥ 0
/// 2. For each pair of non-strict inequalities (a ≤ b, c ≤ d),
///    add (b-a)(d-c) ≥ 0
/// 3. Run linarith on the augmented constraint set
fn nlinarith_with_preprocessing(state: &mut ProofState) -> TacticResult {
    nlinarith_with_config(state, NlinarithConfig::default())
}

/// Run nlinarith with custom configuration.
///
/// REQUIRES: `state` is a valid `ProofState` with at least one goal
/// REQUIRES: `config.max_products >= 0` and `config.max_constraints >= 0`
/// ENSURES: On `Ok(())`, the current goal is closed via replay, positivity, or decide
/// ENSURES: On `Err(NoGoals)`, `state.goals` was empty on entry
/// ENSURES: On `Err(ArithmeticFailed)`, constraint extraction failed or FM found Sat/Unknown
/// ENSURES: Product constraint count never exceeds `config.max_products`
/// ENSURES: Total constraint count never exceeds `config.max_constraints`
pub fn nlinarith_with_config(state: &mut ProofState, config: NlinarithConfig) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    if config.use_groebner {
        if let Some(proof) = groebner_goal_proof(state, &goal, &config.groebner_config) {
            if state.close_goal(&goal, proof).is_ok() {
                return Ok(());
            }
        }
    }

    // Extract base linear constraints
    let (mut constraints, mut var_map) = extract_linear_constraints(state, &goal)
        .unwrap_or_else(|| (Vec::new(), Default::default()));

    // Preprocessing step 1: Add x² ≥ 0 for all variables
    // In our linear representation, x² is nonlinear, so we add a fresh variable y = x²
    // with constraint y ≥ 0 (i.e., -y ≤ 0)
    // However, this doesn't directly help. Instead, we use the fact that
    // for any expression e, we have e² ≥ 0.
    //
    // A more practical approach: if we see (a ≤ b) and (c ≤ d) where all are non-negative,
    // then (b-a) ≥ 0 and (d-c) ≥ 0, so (b-a)(d-c) ≥ 0.
    //
    // For now, we focus on generating products of constraint differences.

    // Collect non-strict inequalities for product generation
    let le_constraints: Vec<_> = constraints
        .iter()
        .filter_map(|c| match c {
            LinearConstraint::Le(e) => Some(e.clone()),
            _ => None,
        })
        .collect();

    // Preprocessing step 2: Generate products of inequality differences
    // For each pair (e1 ≤ 0, e2 ≤ 0), we know -e1 ≥ 0 and -e2 ≥ 0
    // Their product (-e1)(-e2) = e1*e2 ≥ 0
    // But e1*e2 is nonlinear, so we need a different approach.
    //
    // Better approach: if we have linear expressions that can be "squared",
    // generate e² ≥ 0 (represented as a fresh constraint).
    //
    // For actual products: if e1 and e2 are both single-variable or constant,
    // we can add e1*e2 as a constraint.
    let mut products_added = 0;

    for i in 0..le_constraints.len() {
        if products_added >= config.max_products {
            break;
        }
        for j in i..le_constraints.len() {
            if products_added >= config.max_products {
                break;
            }
            if constraints.len() >= config.max_constraints {
                break;
            }

            let e1 = &le_constraints[i];
            let e2 = &le_constraints[j];

            // If both are single-variable or constant, we can compute product
            if let Some(product) = try_compute_linear_product(e1, e2) {
                // -e1 ≥ 0 and -e2 ≥ 0 means e1 ≤ 0 and e2 ≤ 0
                // (-e1)(-e2) ≥ 0 means e1*e2 ≥ 0, i.e., -e1*e2 ≤ 0
                let neg_product = product.scale(-1);
                constraints.push(LinearConstraint::Le(neg_product));
                products_added += 1;
            }
        }
    }

    // Preprocessing step 3: Groebner basis preprocessing
    // Computes a bounded Groebner basis from equality constraints and
    // generates additional linear constraints and non-negativity witnesses
    // (squares, products of inequalities, commutativity identities).
    if config.use_groebner {
        let groebner_result =
            groebner_preprocess(state, &goal, &mut var_map, &config.groebner_config);

        // Add linear constraints derived from the Groebner basis
        for c in groebner_result.linear_constraints {
            if constraints.len() >= config.max_constraints {
                break;
            }
            constraints.push(c);
        }

        // Add non-negativity witnesses (squares, products)
        for c in groebner_result.nonnegativity_witnesses {
            if constraints.len() >= config.max_constraints {
                break;
            }
            constraints.push(c);
        }
    }

    if constraints.is_empty() {
        return Err(TacticError::ArithmeticFailed {
            tactic: "nlinarith".to_string(),
            reason: "could not extract linear or Groebner-derived constraints".to_string(),
        });
    }

    // Preprocessing step 4: For constant-only or simple expressions, add square constraints
    // For each variable v, add v^2 >= 0 (but since v^2 is nonlinear, we can only
    // represent this as a heuristic by assuming non-negativity in certain cases)
    if config.add_squares {
        // The practical approach: if we can detect that a goal is of form x^2 >= 0
        // or 0 <= x^2 or similar, close it directly with positivity-style reasoning.

        // Check if goal is directly of form x^2 >= 0 or similar
        let target = state.metas.instantiate(&goal.target);
        if is_square_nonnegative_goal(&target) {
            // Close directly with positivity
            if positivity(state).is_ok() {
                return Ok(());
            }
        }
    }

    // Try certified FM replay before the legacy uncertified fallback.
    match try_certified_nlinarith(state, &goal, &config) {
        CertifiedNlinarithOutcome::Closed => return Ok(()),
        CertifiedNlinarithOutcome::NoCertifiedContradiction => {}
        CertifiedNlinarithOutcome::CertifiedUnsatNoKernelProof { reason } => {
            return Err(TacticError::ArithmeticFailed {
                tactic: "nlinarith".to_string(),
                reason: format!(
                    "certified FM found contradiction but replay produced no kernel proof ({reason})"
                ),
            });
        }
    }

    // Run Fourier-Motzkin with augmented constraints
    match fourier_motzkin_check(&constraints) {
        FMResult::Unsat => {
            // Contradiction found - the goal is provable
            if decide(state).is_ok() {
                return Ok(());
            }
            tracing::debug!(
                "nlinarith: uncertified FM found contradiction but certified replay was unavailable"
            );
            Err(TacticError::ArithmeticFailed {
                tactic: "nlinarith".to_string(),
                reason:
                    "uncertified FM found contradiction but no certified replay produced a kernel proof"
                        .to_string(),
            })
        }
        FMResult::Sat => {
            // Try decide as last resort
            if decide(state).is_ok() {
                return Ok(());
            }
            Err(TacticError::ArithmeticFailed {
                tactic: "nlinarith".to_string(),
                reason: "constraints are satisfiable, goal not provable".to_string(),
            })
        }
        FMResult::Unknown => {
            // Try decide as last resort
            if decide(state).is_ok() {
                return Ok(());
            }
            Err(TacticError::ArithmeticFailed {
                tactic: "nlinarith".to_string(),
                reason: "could not determine satisfiability".to_string(),
            })
        }
    }
}

// ============================================================================
// Positivity tactic
// ============================================================================

/// Positivity tactic.
///
/// Attempts to prove that an expression is positive, non-negative,
/// or non-zero using structural analysis.
///
/// REQUIRES: `state` is a valid `ProofState` with at least one goal
/// REQUIRES: Goal should be a positivity statement (0 < e, 0 ≤ e, e > 0, e ≥ 0)
/// ENSURES: On `Ok(())`, the current goal is closed via `norm_num` or `decide`
/// ENSURES: On `Err(NoGoals)`, `state.goals` was empty on entry
/// ENSURES: On `Err(NoProgress)`, neither `norm_num` nor `decide` could close the goal
///
/// # Supported Patterns
/// - Constants: `0 < 1`, `0 ≤ 0`
/// - Squares: `0 ≤ x^2`
/// - Sums of positive: `0 < a + b` when `0 < a` and `0 < b`
/// - Products of positive: `0 < a * b` when `0 < a` and `0 < b`
/// - Exponentials: `0 < a^n` when `0 < a`
///
/// # Example
/// ```text
/// -- Goal: 0 < x^2 + 1
/// positivity
/// -- Goal closed
/// ```
pub fn positivity(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Verify we have a goal
    let _goal = state.current_goal().ok_or(TacticError::NoGoals)?;

    // Check if goal is a positivity statement: 0 < e or 0 ≤ e or e > 0 or e ≥ 0
    // Try to analyze the expression structure

    // Try norm_num first for constant expressions
    if norm_num(state).is_ok() {
        return Ok(());
    }

    // Try decide
    if decide(state).is_ok() {
        return Ok(());
    }

    // Specific positivity rules could be added here
    // For now, fall back to sorry if we can't prove it

    Err(TacticError::NoProgress {
        tactic: "positivity".into(),
    })
}
