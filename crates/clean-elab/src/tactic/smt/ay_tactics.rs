// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ay integration tactics for domain-specific SMT solving.
//!
//! Each tactic targets a specific SMT logic and falls back to the native
//! `decide` tactic when Ay is unavailable or inconclusive.

#[cfg(feature = "ay-smt")]
use crate::tactic::Goal;
use crate::tactic::{ProofState, TacticResult};
#[cfg(feature = "ay-smt")]
use clean_kernel::Expr;

use super::ay_types::AyConfig;
#[cfg(feature = "ay-smt")]
use super::ay_types::{requires_zero_trust_reconstruction, SmtVerifyPolicy};
#[cfg(feature = "ay-smt")]
use super::bridge_reconstruction::{
    accept_bridge_reconstruction_candidate, attempt_bridge_reconstruction,
    attempt_bridge_reconstruction_with_requirement, try_bridge_reconstruction_candidate,
    RecoveryTrustRequirement,
};
use super::decide::decide;
#[cfg(feature = "ay-smt")]
use super::decide::validate_proof_term;
#[cfg(feature = "ay-smt")]
use super::selected_proof::{
    accept_selected_direct_proof, choose_selected_proof, SelectedDirectProof, SelectedProofChoice,
};

#[cfg(feature = "ay-smt")]
use super::bridge_validation::prepare_smt_proof_validation;
#[cfg(feature = "ay-smt")]
use crate::tactic::TacticError;

#[cfg(feature = "ay-smt")]
use super::ay_solver::{create_smt_backend, DirectAyKernelProof, SmtSolver};
#[cfg(feature = "ay-smt")]
use clean_auto::bridge::ay_contract::AyLogic;

#[cfg(feature = "ay-smt")]
pub(super) fn prepare_kernel_ay_proof(
    state: &mut ProofState,
    tactic_name: &str,
) -> Result<(), TacticError> {
    prepare_smt_proof_validation(state, tactic_name)
}

#[cfg(feature = "ay-smt")]
fn recover_after_invalid_direct_proof(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    tactic_name: &str,
    strict_zero_trust: bool,
    logic: AyLogic,
    validation_error: TacticError,
) -> Result<Expr, TacticError> {
    state.record_invalid_direct_ay_candidate();
    tracing::warn!(
        tactic = tactic_name,
        error = %validation_error,
        logic = %logic,
        "direct ay proof failed kernel validation before selection; trying recovery lane"
    );
    let recovery = if strict_zero_trust {
        attempt_bridge_reconstruction_with_requirement(
            state,
            goal,
            target,
            tactic_name,
            RecoveryTrustRequirement::ZeroTrust,
        )
    } else {
        attempt_bridge_reconstruction(state, goal, target, tactic_name)
    };
    recovery.map_err(|recovery_error| TacticError::SmtFailed {
        tactic: tactic_name.to_string(),
        detail: format!(
            "direct ay proof failed kernel validation before selection: {validation_error}; recovery also failed: {recovery_error}"
        ),
    })
}

#[cfg(feature = "ay-smt")]
pub(super) fn select_verified_ay_proof(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    tactic_name: &str,
    direct_proof: Option<DirectAyKernelProof>,
    verify_policy: SmtVerifyPolicy,
    logic: AyLogic,
) -> Result<Expr, TacticError> {
    let strict_zero_trust = requires_zero_trust_reconstruction(verify_policy, logic);

    match direct_proof {
        Some(direct_proof) => {
            use clean_auto::bridge::ay_contract::ReconstructionQuality;
            let (proof, direct_trust_subterm_count, residual) = direct_proof.into_parts();
            prepare_kernel_ay_proof(state, tactic_name)?;
            let proof = match validate_proof_term(state, goal, &proof, target) {
                Ok(proof) => proof,
                Err(error) => {
                    return recover_after_invalid_direct_proof(
                        state,
                        goal,
                        target,
                        tactic_name,
                        strict_zero_trust,
                        logic,
                        error,
                    );
                }
            };
            let direct_proof =
                SelectedDirectProof::with_residual(proof, direct_trust_subterm_count, residual);
            if ReconstructionQuality::from_trust_count(direct_trust_subterm_count)
                .is_fully_verified()
            {
                return Ok(accept_selected_direct_proof(
                    state,
                    direct_proof,
                    tactic_name,
                    "direct ay",
                ));
            }

            // Partially trusted direct proof — try bridge reconstruction.
            if strict_zero_trust {
                tracing::info!(
                    tactic = tactic_name,
                    direct_trust = direct_trust_subterm_count,
                    logic = %logic,
                    "strict zero-trust policy rejected partially trusted direct proof; requiring zero-trust recovery"
                );
                if let Ok(proof) = attempt_bridge_reconstruction_with_requirement(
                    state,
                    goal,
                    target,
                    tactic_name,
                    RecoveryTrustRequirement::ZeroTrust,
                ) {
                    return Ok(proof);
                }
                tracing::warn!(
                    tactic = tactic_name,
                    direct_trust = direct_trust_subterm_count,
                    logic = %logic,
                    "strict zero-trust policy exhausted all zero-trust fallbacks"
                );
                return Err(TacticError::SmtFailed {
                    tactic: tactic_name.to_string(),
                    detail: format!(
                        "VerifyStrict {logic} requires zero-trust proof \
                         but reconstruction produced {direct_trust_subterm_count} trusted sub-term(s) \
                         and neither bridge nor superposition fallback succeeded"
                    ),
                });
            }

            let bridge_candidate =
                try_bridge_reconstruction_candidate(state, goal, target, tactic_name)
                    .into_candidate();
            match choose_selected_proof(direct_proof, bridge_candidate, tactic_name) {
                SelectedProofChoice::Direct(direct_proof) => Ok(accept_selected_direct_proof(
                    state,
                    direct_proof,
                    tactic_name,
                    "direct ay",
                )),
                SelectedProofChoice::Bridge(candidate) => Ok(
                    accept_bridge_reconstruction_candidate(state, candidate, tactic_name),
                ),
            }
        }
        None => {
            if strict_zero_trust {
                tracing::info!(
                    tactic = tactic_name,
                    logic = %logic,
                    "strict zero-trust policy found no direct proof; requiring zero-trust recovery"
                );
                if let Ok(proof) = attempt_bridge_reconstruction_with_requirement(
                    state,
                    goal,
                    target,
                    tactic_name,
                    RecoveryTrustRequirement::ZeroTrust,
                ) {
                    Ok(proof)
                } else {
                    tracing::warn!(
                        tactic = tactic_name,
                        logic = %logic,
                        "strict zero-trust policy found no accepted zero-trust proof from any lane"
                    );
                    Err(TacticError::SmtFailed {
                        tactic: tactic_name.to_string(),
                        detail: format!(
                            "VerifyStrict {logic} requires zero-trust proof but direct reconstruction, \
                             bridge recovery, and superposition fallback all failed"
                        ),
                    })
                }
            } else {
                attempt_bridge_reconstruction(state, goal, target, tactic_name)
            }
        }
    }
}

#[cfg(feature = "ay-smt")]
pub(super) fn assert_goal_hypotheses_with_drop_count(
    state: &ProofState,
    goal: &Goal,
    backend: &mut SmtSolver,
) -> u32 {
    let mut dropped_hypotheses = 0u32;
    for decl in &goal.local_ctx {
        let hyp_ty = state.metas.instantiate(&decl.ty);
        if !hyp_ty.is_sort()
            && backend
                .translate_and_assert_hypothesis(decl.fvar, &hyp_ty)
                .is_err()
        {
            dropped_hypotheses += 1;
        }
    }
    dropped_hypotheses
}

#[cfg(feature = "ay-smt")]
fn run_ay_tactic(
    state: &mut ProofState,
    config: &AyConfig,
    logic: AyLogic,
    tactic_name: &str,
) -> Result<(), TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    let mut backend = create_smt_backend(config, logic);
    backend
        .register_fvars_from_context(&goal.local_ctx, &state.metas)
        .map_err(|e| TacticError::SmtFailed {
            tactic: tactic_name.to_string(),
            detail: format!("Ay registration error: {e:?}"),
        })?;

    let dropped_hypotheses = assert_goal_hypotheses_with_drop_count(state, &goal, &mut backend);
    if dropped_hypotheses > 0 {
        tracing::warn!(
            tactic = tactic_name,
            dropped = dropped_hypotheses,
            "hypothesis(es) dropped (unsupported by Ay backend)"
        );
    }

    match backend.prove(&target) {
        Ok(outcome) if outcome.proved => {
            if config.is_verbose() {
                if let Some(verification) = outcome.solver_verification() {
                    tracing::debug!(
                        tactic = tactic_name,
                        level = ?verification.level,
                        sat_model_validated = verification.summary.sat_model_validated,
                        unsat_proof_available = verification.summary.unsat_proof_available,
                        unsat_proof_checker_failures =
                            verification.summary.unsat_proof_checker_failures,
                        sat_independent_checks = verification.summary.sat_independent_checks,
                        sat_delegated_checks = verification.summary.sat_delegated_checks,
                        sat_incomplete_checks = verification.summary.sat_incomplete_checks,
                        "retained fast-path solver verification metadata"
                    );
                }
            }
            let proof_term = select_verified_ay_proof(
                state,
                &goal,
                &target,
                tactic_name,
                outcome.into_direct_proof(),
                config.verify_policy(),
                logic,
            )?;
            state.close_goal(&goal, proof_term)?;
            Ok(())
        }
        Ok(_) => Err(TacticError::SmtFailed {
            tactic: tactic_name.to_string(),
            detail: "Ay could not prove goal".to_string(),
        }),
        Err(e) => Err(TacticError::SmtFailed {
            tactic: tactic_name.to_string(),
            detail: format!("Ay error: {e:?}"),
        }),
    }
}

/// Shared Ay tactic pipeline: attempt Ay solving with the given logic, then
/// fall back to the native `decide` tactic on `SmtFailed`. Non-`SmtFailed`
/// errors propagate immediately.
///
/// Each public Ay tactic (`ay_omega`, `ay_bv`, `ay_smt`, `ay_decide`) is a
/// thin wrapper that only specifies its logic and name.
#[cfg(feature = "ay-smt")]
fn ay_tactic_with_fallback(
    state: &mut ProofState,
    config: &AyConfig,
    logic: AyLogic,
    tactic_name: &str,
) -> TacticResult {
    if config.is_verbose() {
        tracing::debug!("[{tactic_name}] Using Ay with logic: {logic}");
    }
    match run_ay_tactic(state, config, logic, tactic_name) {
        Ok(()) => return Ok(()),
        Err(TacticError::SmtFailed { detail, .. }) => {
            if config.is_verbose() {
                tracing::debug!("[{tactic_name}] {detail}, falling back to native");
            }
        }
        Err(error) => return Err(error),
    }
    decide(state)
}

/// Ay tactic specialized for linear integer arithmetic (`QF_LIA`).
/// Falls back to the native solver when Ay is unavailable or inconclusive.
pub fn ay_omega(state: &mut ProofState, config: AyConfig) -> TacticResult {
    #[cfg(feature = "ay-smt")]
    {
        ay_tactic_with_fallback(state, &config, AyLogic::QfLia, "ay_omega")
    }

    #[cfg(not(feature = "ay-smt"))]
    {
        if config.is_verbose() {
            tracing::debug!("[ay_omega] Ay feature not enabled, using native SMT solver");
        }
        decide(state)
    }
}

/// Ay tactic specialized for bitvector goals (`QF_BV`).
/// Falls back to the native solver when Ay is unavailable or inconclusive.
pub fn ay_bv(state: &mut ProofState, config: AyConfig) -> TacticResult {
    #[cfg(feature = "ay-smt")]
    {
        ay_tactic_with_fallback(state, &config, AyLogic::QfBv, "ay_bv")
    }

    #[cfg(not(feature = "ay-smt"))]
    {
        if config.is_verbose() {
            tracing::debug!("[ay_bv] Ay feature not enabled, using native SMT solver");
        }
        decide(state)
    }
}

/// Ay tactic for general SMT theory combinations.
/// Uses `config.effective_logic()` and falls back to the native solver on failure.
pub fn ay_smt(state: &mut ProofState, config: AyConfig) -> TacticResult {
    #[cfg(feature = "ay-smt")]
    {
        let logic = config.effective_logic();
        ay_tactic_with_fallback(state, &config, logic, "ay_smt")
    }

    #[cfg(not(feature = "ay-smt"))]
    {
        if config.is_verbose() {
            let logic = config
                .logic_override()
                .map_or_else(|| "auto-detect".to_string(), |l| l.to_string());
            tracing::debug!(
                "[ay_smt] Ay feature not enabled, using native SMT solver (logic: {logic})"
            );
        }
        decide(state)
    }
}

/// Ay tactic specialized for linear real arithmetic (`QF_LRA`).
/// Falls back to the native solver when Ay is unavailable or inconclusive.
///
/// Used by `linarith` as an SMT-backed fallback when Fourier-Motzkin
/// elimination fails to produce a kernel proof term.
pub fn ay_lra(state: &mut ProofState, config: AyConfig) -> TacticResult {
    #[cfg(feature = "ay-smt")]
    {
        ay_tactic_with_fallback(state, &config, AyLogic::QfLra, "ay_lra")
    }

    #[cfg(not(feature = "ay-smt"))]
    {
        if config.is_verbose() {
            tracing::debug!("[ay_lra] Ay feature not enabled, using native SMT solver");
        }
        decide(state)
    }
}

/// Ay tactic for propositional goals using the SAT-style `QF_UF` lane.
/// Falls back to the native solver when Ay is unavailable or inconclusive.
pub fn ay_decide(state: &mut ProofState, config: AyConfig) -> TacticResult {
    #[cfg(feature = "ay-smt")]
    {
        ay_tactic_with_fallback(state, &config, AyLogic::QfUf, "ay_decide")
    }

    #[cfg(not(feature = "ay-smt"))]
    {
        if config.is_verbose() {
            tracing::debug!("[ay_decide] Ay feature not enabled, using native CDCL solver");
        }
        decide(state)
    }
}
