// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! linear_combination tactic: Prove goals via linear combinations of hypotheses.

use clean_kernel::Expr;

use super::super::{
    decide_eq, rfl, ring, ring_nf, try_tactic_preserving_state, ProofState, TacticError,
    TacticResult,
};
use super::linear_combination_proof::build_linear_combination_eq_proof;
use super::util::try_extract_eq;

/// A coefficient for a hypothesis in a linear combination.
#[derive(Debug, Clone)]
pub struct LinearCoeff {
    /// Name of the hypothesis
    pub hyp_name: String,
    /// Coefficient (rational)
    pub coeff: (i64, u64), // (numerator, denominator)
}

impl LinearCoeff {
    /// Create a coefficient of 1 for a hypothesis
    ///
    /// # Contract
    ///
    /// ENSURES: `self.coeff == (1, 1)` and `self.hyp_name == hyp_name`
    pub fn one(hyp_name: &str) -> Self {
        Self {
            hyp_name: hyp_name.to_string(),
            coeff: (1, 1),
        }
    }

    /// Create a coefficient for a hypothesis
    ///
    /// # Contract
    ///
    /// ENSURES: `self.coeff == (num, denom.max(1))` — denominator is clamped to at least 1
    pub fn new(hyp_name: &str, num: i64, denom: u64) -> Self {
        Self {
            hyp_name: hyp_name.to_string(),
            coeff: (num, denom.max(1)),
        }
    }

    /// Create an integer coefficient for a hypothesis
    ///
    /// # Contract
    ///
    /// ENSURES: `self.coeff == (n, 1)`
    pub fn int(hyp_name: &str, n: i64) -> Self {
        Self {
            hyp_name: hyp_name.to_string(),
            coeff: (n, 1),
        }
    }
}

/// Configuration for linear_combination tactic.
#[derive(Debug, Clone)]
pub struct LinearCombinationConfig {
    /// Whether to normalize the result with ring_nf
    pub normalize: bool,
    /// Whether to use exact match (vs allowing definitional equality)
    pub exact: bool,
}

impl Default for LinearCombinationConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl LinearCombinationConfig {
    /// Create default configuration
    pub fn new() -> Self {
        Self {
            normalize: true,
            exact: false,
        }
    }

    /// Set whether to normalize with ring_nf
    #[must_use]
    pub fn with_normalize(mut self, normalize: bool) -> Self {
        self.normalize = normalize;
        self
    }

    /// Set whether to use exact matching
    #[must_use]
    pub fn with_exact(mut self, exact: bool) -> Self {
        self.exact = exact;
        self
    }
}

/// Prove a goal by taking a linear combination of hypotheses.
///
/// Given hypotheses `h1 : a1 = b1`, `h2 : a2 = b2`, etc., and coefficients
/// `c1`, `c2`, etc., `linear_combination` attempts to prove the goal by
/// showing it equals `c1 * h1 + c2 * h2 + ...`.
///
/// This is useful for proving equalities in rings by combining known equalities.
///
/// # Example
/// ```text
/// -- Given h1 : x + y = 5, h2 : x - y = 1
/// -- Goal: 2 * x = 6
/// linear_combination [h1 * 1, h2 * 1]
/// -- (x + y) + (x - y) = 5 + 1, so 2x = 6
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: The current goal target is an equality (`Eq _ lhs rhs`)
/// REQUIRES: Each `LinearCoeff.hyp_name` names a hypothesis whose type is also an equality
/// ENSURES: On Ok, the current goal is closed (via proof reconstruction,
/// `ring_nf`, `ring`, `rfl`, or `decide_eq`)
/// ENSURES: On Err(GoalMismatch), the goal target was not an equality
/// ENSURES: On Err(HypothesisNotFound), a referenced hypothesis name was missing
/// ENSURES: On Err(SearchExhausted), all closure strategies failed
pub fn linear_combination(state: &mut ProofState, coeffs: Vec<LinearCoeff>) -> TacticResult {
    linear_combination_with_config(state, coeffs, LinearCombinationConfig::new())
}

/// linear_combination with custom configuration
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: The current goal target is an equality (`Eq _ lhs rhs`)
/// REQUIRES: Each `LinearCoeff.hyp_name` names a hypothesis whose type is also an equality
/// ENSURES: On Ok, the current goal is closed; proof reconstruction is tried before exploratory normalization
/// ENSURES: Closure strategy order: proof reconstruction (if coeffs non-empty) → ring_nf (if normalize) → ring → rfl → decide_eq → SearchExhausted
/// ENSURES: On Err(InvalidTarget), a hypothesis type was not an equality
pub fn linear_combination_with_config(
    state: &mut ProofState,
    coeffs: Vec<LinearCoeff>,
    config: LinearCombinationConfig,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    // Check that the target is an equality
    let (lhs, rhs) = try_extract_eq(&target)
        .ok_or_else(|| TacticError::GoalMismatch("goal must be an equality".into()))?;

    // Collect the hypotheses and their coefficients
    let mut combined_lhs_terms: Vec<(i64, u64, Expr)> = Vec::new();
    let mut combined_rhs_terms: Vec<(i64, u64, Expr)> = Vec::new();

    for coeff in &coeffs {
        // Find the hypothesis
        let hyp = goal
            .local_ctx
            .iter()
            .find(|h| h.name == coeff.hyp_name)
            .ok_or_else(|| {
                TacticError::HypothesisNotFound(format!(
                    "linear_combination: hypothesis '{}' not found",
                    coeff.hyp_name
                ))
            })?;

        // Check that the hypothesis is an equality
        let hyp_ty = state.metas.instantiate(&hyp.ty);
        let (hyp_lhs, hyp_rhs) =
            try_extract_eq(&hyp_ty).ok_or_else(|| TacticError::InvalidTarget {
                tactic: "linear_combination".into(),
                detail: format!("hypothesis '{}' must be an equality", coeff.hyp_name),
            })?;

        combined_lhs_terms.push((coeff.coeff.0, coeff.coeff.1, hyp_lhs));
        combined_rhs_terms.push((coeff.coeff.0, coeff.coeff.1, hyp_rhs));
    }

    // Part of #2567: try the shared proof-carry builder before speculative
    // tactics so cancellation-style certificates do not get misclassified by
    // exploratory fallback attempts.
    if !coeffs.is_empty() {
        if let Some(proof) = build_linear_combination_eq_proof(state, &goal, &coeffs) {
            return state
                .close_goal(&goal, proof)
                .map_err(|_| TacticError::SearchExhausted {
                    tactic: "linear_combination".into(),
                    detail: "proof reconstruction succeeded but type check failed".into(),
                });
        }
    }

    // Try to close the goal using ring or ring_nf
    if config.normalize && try_tactic_preserving_trust_ledger(state, ring_nf) {
        return Ok(());
    }

    if try_tactic_preserving_trust_ledger(state, ring) {
        return Ok(());
    }

    // If the LHS and RHS are definitionally equal after the linear combination,
    // we can close with rfl
    if state.is_def_eq(&goal, &lhs, &rhs) {
        return rfl(state);
    }

    // Try to close with decide_eq
    if try_tactic_preserving_trust_ledger(state, decide_eq) {
        return Ok(());
    }

    if !combined_lhs_terms.is_empty() {
        return Err(TacticError::SearchExhausted {
            tactic: "linear_combination".into(),
            detail: "proof reconstruction returned None for verified combination".into(),
        });
    }

    Err(TacticError::SearchExhausted {
        tactic: "linear_combination".into(),
        detail: "could not prove goal with given coefficients".into(),
    })
}

/// Convenience for linear_combination with coefficient 1 for all hypotheses
///
/// # Contract
///
/// REQUIRES: same as `linear_combination`
/// ENSURES: Behaves like `linear_combination(state, coeffs)` where each coefficient is 1
pub fn linear_combination_simple(state: &mut ProofState, hyp_names: Vec<&str>) -> TacticResult {
    let coeffs: Vec<LinearCoeff> = hyp_names
        .iter()
        .map(|name| LinearCoeff::one(name))
        .collect();
    linear_combination(state, coeffs)
}

fn try_tactic_preserving_trust_ledger<F>(state: &mut ProofState, tactic: F) -> bool
where
    F: FnOnce(&mut ProofState) -> TacticResult,
{
    let saved_ledger = state.trust_ledger();
    if try_tactic_preserving_state(state, tactic) {
        true
    } else {
        state.trust_ledger = saved_ledger;
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{env::Declaration, Environment, FVarId, Level, Name};

    use super::super::super::LocalDecl;

    fn setup_env_with_eq() -> Environment {
        let mut env = Environment::new();
        env.init_eq().expect("Eq should initialize");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("N"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("N should add");
        for name in ["x", "y"] {
            env.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_: Expr::const_(Name::from_string("N"), vec![]),
            })
            .expect("constant should add");
        }
        env
    }

    fn make_eq_n(lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    Expr::const_(Name::from_string("N"), vec![]),
                ),
                lhs,
            ),
            rhs,
        )
    }

    #[test]
    fn test_linear_combination_verified_missing_proof_returns_search_exhausted() {
        let env = setup_env_with_eq();
        let x = Expr::const_(Name::from_string("x"), vec![]);
        let y = Expr::const_(Name::from_string("y"), vec![]);
        let mut state = ProofState::with_context(
            env,
            make_eq_n(y.clone(), x.clone()),
            vec![LocalDecl {
                fvar: FVarId::new(0),
                name: "h".to_string(),
                ty: make_eq_n(x, y),
                value: None,
            }],
        );

        let result = linear_combination(&mut state, vec![LinearCoeff::new("h", 1, 2)]);
        assert!(
            matches!(
                result,
                Err(TacticError::SearchExhausted { ref tactic, ref detail })
                    if tactic == "linear_combination"
                        && detail == "proof reconstruction returned None for verified combination"
            ),
            "expected fail-closed SearchExhausted, got: {result:?}"
        );
        assert_eq!(
            state.trust_ledger().trusted_arith_count,
            0,
            "fail-closed linear_combination must not record trustedArith"
        );
        assert!(
            !state.is_complete(),
            "fail-closed linear_combination should leave the goal open"
        );
    }
}
