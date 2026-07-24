// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Neural proof oracle tactic.
//!
//! Provides integration between the clean tactic framework and neural proof
//! oracles (Goedel-Prover-V2-8B, DeepSeek-Prover-V2-7B, etc.).
//!
//! # Architecture
//!
//! The oracle tactic builds an [`OracleRequest`] from the current proof state
//! (goal + hypotheses in pretty-printed Lean 4 syntax) and calls
//! [`ProofOracle::suggest_proof`] to get candidate tactic sequences.
//!
//! The caller is responsible for executing the returned candidates, either:
//! - Via the clean-server `applyTactic` endpoint (for API consumers)
//! - Via recursive tactic evaluation (for integrated proof search)
//!
//! # Example
//!
//! ```text
//! let oracle: &dyn ProofOracle = &my_oracle;
//! let request = build_oracle_request(state);
//! match oracle.suggest_proof(&request) {
//!     Ok(candidates) => {
//!         for candidate in &candidates {
//!             // Try executing candidate.tactic_text via applyTactic
//!         }
//!     }
//!     Err(e) => tracing::warn!("oracle failed: {e}"),
//! }
//! ```

use crate::tactic::{Goal, ProofState, TacticError};
use clean_auto::oracle::{
    sort_oracle_candidates, OracleCandidate, OracleError, OracleRequest, ProofOracle,
};

/// Build an [`OracleRequest`] from the current proof state.
///
/// Extracts the goal type and local hypotheses, formatting them as
/// pretty-printed Lean 4 syntax for model consumption.
///
/// The returned request can be passed to [`ProofOracle::suggest_proof`]
/// to get candidate tactic sequences.
///
/// REQUIRES: At least one goal exists in `state`.
/// ENSURES: On `Ok`, the returned request contains the goal in Lean 4 syntax
///   and all local hypotheses formatted for model consumption.
pub fn build_oracle_request(state: &ProofState) -> Result<OracleRequest, TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    build_oracle_request_for_goal(state, &goal)
}

/// Build an [`OracleRequest`] for a specific goal.
///
/// REQUIRES: `goal.target` and all hypothesis types are well-formed.
/// ENSURES: Goal and hypotheses are formatted via Lean 4 Display (not Debug).
/// ENSURES: Metavariables in the target and hypotheses are instantiated.
pub fn build_oracle_request_for_goal(
    state: &ProofState,
    goal: &Goal,
) -> Result<OracleRequest, TacticError> {
    // Pretty-print the goal type
    let target = state.metas.instantiate(&goal.target);
    let goal_text = format_expr_for_oracle(&target);

    let mut request = OracleRequest::new(goal_text);

    // Add hypotheses from local context
    for decl in &goal.local_ctx {
        let ty = state.metas.instantiate(&decl.ty);
        let name = decl.name.clone();
        let ty_text = format_expr_for_oracle(&ty);
        request = request.with_hypothesis(name, ty_text);
    }

    Ok(request)
}

/// Attempt to prove the current goal using a neural oracle.
///
/// This function:
/// 1. Builds an oracle request from the proof state
/// 2. Calls the oracle to get candidate tactic sequences
/// 3. Returns the candidates for the caller to execute
///
/// Unlike other tactics, this does NOT close the goal directly.
/// The caller must execute the returned tactic candidates (e.g.,
/// by parsing and evaluating them via `eval_tactic`).
///
/// # Returns
///
/// - `Ok(candidates)` with sorted candidates (highest confidence first)
/// - `Err(TacticError)` if no goals exist or oracle fails
///
/// REQUIRES: At least one goal exists in `state`.
/// REQUIRES: `oracle.is_available()` is `true`.
/// ENSURES: On `Ok`, candidates are sorted by confidence descending.
/// ENSURES: The proof state is not modified (read-only operation).
pub fn oracle_suggest(
    state: &ProofState,
    oracle: &dyn ProofOracle,
) -> Result<Vec<OracleCandidate>, TacticError> {
    if !oracle.is_available() {
        return Err(TacticError::OracleFailed {
            detail: "neural oracle is not available".into(),
        });
    }

    let request = build_oracle_request(state)?;

    match oracle.suggest_proof(&request) {
        Ok(mut candidates) => {
            sort_oracle_candidates(&mut candidates);
            Ok(candidates)
        }
        Err(OracleError::Timeout { timeout_ms }) => Err(TacticError::OracleFailed {
            detail: format!("timed out after {timeout_ms}ms"),
        }),
        Err(OracleError::NotConfigured) => Err(TacticError::OracleFailed {
            detail: "no oracle configured".into(),
        }),
        Err(e) => Err(TacticError::OracleFailed {
            detail: format!("{e}"),
        }),
    }
}

/// Format a kernel Expr as a string for oracle consumption.
///
/// Uses the kernel's Lean 4 pretty-printer (Display impl) which produces
/// readable syntax with arrows, named binders, and standard notation.
/// Neural models are trained on Lean 4 syntax, not Rust Debug representations.
fn format_expr_for_oracle(expr: &clean_kernel::Expr) -> String {
    format!("{expr}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tactic::ProofState;
    use clean_kernel::Environment;

    /// Mock oracle that returns fixed candidates for testing.
    struct TestOracle {
        candidates: Vec<OracleCandidate>,
    }

    impl TestOracle {
        fn new(tactics: &[(&str, f64)]) -> Self {
            Self {
                candidates: tactics
                    .iter()
                    .map(|(text, conf)| OracleCandidate::new(*text, *conf))
                    .collect(),
            }
        }
    }

    impl ProofOracle for TestOracle {
        fn suggest_proof(
            &self,
            _request: &OracleRequest,
        ) -> Result<Vec<OracleCandidate>, OracleError> {
            Ok(self.candidates.clone())
        }

        fn model_id(&self) -> &str {
            "test-oracle"
        }

        fn is_available(&self) -> bool {
            true
        }
    }

    #[test]
    fn test_oracle_suggest_sorts_by_confidence() {
        let env = Environment::new();
        // Create a simple goal: Sort(0) as a stand-in
        let goal_ty = clean_kernel::Expr::sort(clean_kernel::Level::zero());
        let state = ProofState::new(env, goal_ty);

        let oracle = TestOracle::new(&[("omega", 0.3), ("exact trivial", 0.9), ("simp", 0.6)]);

        let candidates = oracle_suggest(&state, &oracle).expect("should succeed");
        assert_eq!(candidates.len(), 3);
        // Should be sorted: highest confidence first
        assert!((candidates[0].confidence - 0.9).abs() < f64::EPSILON);
        assert!((candidates[1].confidence - 0.6).abs() < f64::EPSILON);
        assert!((candidates[2].confidence - 0.3).abs() < f64::EPSILON);
        assert_eq!(candidates[0].tactic_text, "exact trivial");
    }

    #[test]
    fn test_oracle_suggest_unavailable() {
        let env = Environment::new();
        let goal_ty = clean_kernel::Expr::sort(clean_kernel::Level::zero());
        let state = ProofState::new(env, goal_ty);

        struct UnavailableOracle;
        impl ProofOracle for UnavailableOracle {
            fn suggest_proof(
                &self,
                _: &OracleRequest,
            ) -> Result<Vec<OracleCandidate>, OracleError> {
                Err(OracleError::NotConfigured)
            }
            fn model_id(&self) -> &str {
                "none"
            }
            fn is_available(&self) -> bool {
                false
            }
        }

        let result = oracle_suggest(&state, &UnavailableOracle);
        assert!(
            result.is_err(),
            "unavailable oracle should return error, got: {:?}",
            result
        );
    }

    #[test]
    fn test_build_oracle_request_captures_goal_as_lean4() {
        let env = Environment::new();
        // Sort(0) = Prop, so the goal text should be "Prop"
        let goal_ty = clean_kernel::Expr::sort(clean_kernel::Level::zero());
        let state = ProofState::new(env, goal_ty);

        let request = build_oracle_request(&state).expect("should build request");
        assert_eq!(
            request.goal, "Prop",
            "Oracle request goal should be Lean 4 syntax, got: {}",
            request.goal
        );
        assert!(
            !request.goal.contains("Sort("),
            "Oracle request goal must not contain Debug artifacts: {}",
            request.goal
        );
    }

    #[test]
    fn test_build_oracle_request_formats_hypotheses_as_lean4() {
        use crate::tactic::LocalDecl;
        use clean_kernel::{Expr, FVarId, Level};

        let env = Environment::new();
        let goal_ty = Expr::sort(Level::zero());
        let mut state = ProofState::new(env, goal_ty);

        // Add hypothesis: n : Nat
        state.goals[0].local_ctx.push(LocalDecl {
            fvar: FVarId::new(1),
            name: "n".to_string(),
            ty: Expr::const_str("Nat"),
            value: None,
        });

        let request = build_oracle_request(&state).expect("should build request");
        assert_eq!(request.hypotheses.len(), 1, "should have one hypothesis");
        let (hyp_name, hyp_ty) = &request.hypotheses[0];
        assert_eq!(hyp_name, "n");
        assert_eq!(
            hyp_ty, "Nat",
            "hypothesis type should be Lean 4 syntax, got: {hyp_ty}"
        );
        assert!(
            !hyp_ty.contains("Const("),
            "hypothesis type must not contain Debug artifacts: {hyp_ty}"
        );
    }

    #[test]
    fn test_format_expr_produces_lean4_syntax() {
        use clean_kernel::{BinderInfo, Expr, Level};

        // Sort(0) = Prop
        let prop = Expr::sort(Level::zero());
        let prop_text = format_expr_for_oracle(&prop);
        assert_eq!(
            prop_text, "Prop",
            "Sort(0) should be 'Prop', got: {prop_text}"
        );

        // Sort(1) = Type
        let type0 = Expr::sort(Level::succ(Level::zero()));
        let type_text = format_expr_for_oracle(&type0);
        assert_eq!(
            type_text, "Type",
            "Sort(1) should be 'Type', got: {type_text}"
        );

        // Const "Nat" = Nat
        let nat = Expr::const_str("Nat");
        let nat_text = format_expr_for_oracle(&nat);
        assert_eq!(
            nat_text, "Nat",
            "Const('Nat') should be 'Nat', got: {nat_text}"
        );

        // App(App(Const "Nat.add"), Lit(0)) should NOT contain "App("
        let add = Expr::const_str("Nat.add");
        let zero = Expr::nat_lit(0);
        let app_expr = Expr::app(add, zero);
        let app_text = format_expr_for_oracle(&app_expr);
        assert!(
            !app_text.contains("App("),
            "Application should use Lean 4 syntax, not Debug: {app_text}"
        );
        assert!(
            app_text.contains("Nat.add"),
            "Application text should contain the function name: {app_text}"
        );

        // Pi (forall): forall _ : Nat, Prop  should produce arrow notation
        let pi_expr = Expr::pi(BinderInfo::Default, nat.clone(), prop.clone());
        let pi_text = format_expr_for_oracle(&pi_expr);
        assert!(
            !pi_text.contains("Pi("),
            "Pi type should use Lean 4 syntax, not Debug: {pi_text}"
        );
    }
}
