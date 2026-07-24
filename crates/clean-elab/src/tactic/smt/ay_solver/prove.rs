// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    is_literal_false_goal, reconstruct_unsat_proof, translate_expr_with_sync, AyError,
    AyProofBackend, AyProofResult, AyResult, DirectAyKernelProof, ExistsWitnessBinding, Expr,
    SmtProveOutcome, SmtSolver, TrustBudget, VariableMapping,
};

impl SmtSolver {
    /// Attempt to prove a proposition
    ///
    /// Returns `SmtProveOutcome` with `proved` flag and optional direct proof.
    /// For the `Fast` path, `direct_proof()` is always `None`.
    /// For the `Verifiable` path, `direct_proof()` is `Some` when proof
    /// reconstruction succeeds, eliminating the need for whole-goal
    /// `trustedAy`.
    ///
    /// # Contract
    ///
    /// REQUIRES: Hypotheses must be asserted before calling (via `translate_and_assert`)
    /// REQUIRES: FVars must be registered (via `register_fvars_from_context`)
    /// ENSURES: On Ok with `proved == true`, the negation of `prop` is UNSAT
    /// ENSURES: On Ok with `direct_proof().is_some()`, proof reconstructed from ay Alethe proof
    /// ENSURES: `direct_trust_subterm_count()` tracks the exact embedded
    ///   `trustedAy` sub-terms in the accepted proof
    /// ENSURES: Fast path retains the solver verification envelope on success
    /// ENSURES: Fast path always returns `direct_proof().is_none()`
    /// ENSURES: On Err, solver encountered an error (timeout, unsupported, etc.)
    pub(crate) fn prove(&mut self, prop: &Expr) -> AyResult<SmtProveOutcome> {
        match self {
            SmtSolver::Fast(backend) => {
                let report = backend.prove_with_report(prop)?;
                if report.is_unknown() {
                    return Err(AyError::Unknown);
                }
                Ok(SmtProveOutcome {
                    proved: report.is_unsat(),
                    direct_proof: None,
                    solver_verification: report.verification(),
                })
            }
            SmtSolver::Verifiable {
                backend,
                translator,
                var_map,
                exists_bindings,
                reconstruction_budget,
                ..
            } => {
                let goal_translation =
                    translate_expr_with_sync(backend, translator, var_map, prop)?;
                let goal_has_exists_skolemizations =
                    !goal_translation.new_exists_skolemizations.is_empty();
                let goal_formula = goal_translation.formula;
                if !is_literal_false_goal(prop) {
                    backend.assert_formula(&format!("(not {})", goal_formula));
                }
                solve_and_reconstruct(
                    backend,
                    var_map,
                    exists_bindings,
                    prop,
                    *reconstruction_budget,
                    goal_has_exists_skolemizations,
                )
            }
            #[cfg(test)]
            SmtSolver::Disabled { reason, .. } => Err(AyError::SolverDisabled(reason.clone())),
        }
    }
}

/// Solve the currently asserted formula and reconstruct a kernel proof on UNSAT.
///
/// `VerificationFailed` from tier-1 proof checking (Alethe/Carcara) is deferred
/// rather than propagated: the error fires *after* ay returned UNSAT, so the
/// solver did prove the goal. Returning `proved = true, direct_proof = None`
/// lets the tactic-level trust enforcement (`select_verified_ay_proof`) attempt
/// bridge reconstruction under its own zero-trust budget.
fn solve_and_reconstruct(
    backend: &mut AyProofBackend,
    var_map: &mut VariableMapping,
    exists_bindings: &[ExistsWitnessBinding],
    prop: &Expr,
    reconstruction_budget: TrustBudget,
    goal_has_exists_skolemizations: bool,
) -> AyResult<SmtProveOutcome> {
    match backend.check_sat() {
        Ok(AyProofResult::Unsat { .. }) => {
            let direct_proof = if !goal_has_exists_skolemizations {
                reconstruct_unsat_proof(
                    backend,
                    var_map,
                    exists_bindings,
                    prop,
                    reconstruction_budget,
                )
                .map(|(proof, trust_subterm_count, residual)| {
                    DirectAyKernelProof::new(proof, trust_subterm_count, residual)
                })
            } else {
                None
            };
            Ok(SmtProveOutcome {
                proved: true,
                direct_proof,
                solver_verification: None,
            })
        }
        Ok(AyProofResult::Sat) => Ok(SmtProveOutcome {
            proved: false,
            direct_proof: None,
            solver_verification: None,
        }),
        Ok(AyProofResult::Unknown) => Err(AyError::Unknown),
        Err(AyError::VerificationFailed(ref msg)) => {
            tracing::debug!("proof verification deferred to tactic-level trust enforcement: {msg}");
            Ok(SmtProveOutcome {
                proved: true,
                direct_proof: None,
                solver_verification: None,
            })
        }
        Err(error) => Err(error),
        _ => Err(AyError::Unknown),
    }
}
