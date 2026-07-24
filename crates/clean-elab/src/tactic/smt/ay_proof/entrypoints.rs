// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Public DRAT/LRAT certificate entrypoints and shared pipeline.
//!
//! Both public entrypoints delegate to a single shared helper that owns
//! the verify-select-close workflow, differing only in verifier function,
//! operation count, and descriptor strings.

use crate::tactic::drat::{
    verify_and_reconstruct_drat, verify_and_reconstruct_lrat, CnfFormula, DratProof,
    DratProofResult, LratProof,
};
use crate::tactic::{ProofState, TacticError, TacticResult};
use clean_kernel::{Environment, Expr};

use super::selection::{select_verified_certificate_proof, CertificateProofSelection};
use super::AyProofConfig;

/// Ay SAT decision tactic with DRAT proof certificate
///
/// Like `ay_decide`, but accepts a DRAT proof certificate from Ay.
/// The certificate is verified before constructing a kernel proof term.
///
/// # Arguments
/// * `state` - The current proof state
/// * `config` - Configuration including the CNF formula
/// * `drat_proof` - DRAT proof certificate from Ay
///
/// # Example
/// ```text
/// // Ay returns UNSAT with DRAT proof
/// let formula = CnfFormula::parse_dimacs(cnf_text)?;
/// let proof = DratProof::parse(drat_text)?;
/// ay_decide_with_proof(&mut state, config, proof)?;
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `config.formula` encodes the same proposition as the goal target
/// REQUIRES: `config.logic` is the explicit logic classification for this
///   certificate request
/// REQUIRES: `drat_proof` is a DRAT certificate claiming `config.formula` is UNSAT
/// ENSURES: On Ok, the DRAT certificate verified and the goal is closed
/// ENSURES: On Ok without a direct kernel proof, recovers through the shared
///   bridge/superposition lane without synthesizing a whole-goal `trustedAy`
/// ENSURES: On Err(SmtFailed), DRAT verification rejected the certificate
pub fn ay_decide_with_proof(
    state: &mut ProofState,
    config: AyProofConfig,
    drat_proof: DratProof,
) -> TacticResult {
    run_certificate_entrypoint(
        state,
        &config,
        drat_proof.operations.len(),
        "ay_decide_with_proof",
        "DRAT",
        |env, formula, target| verify_and_reconstruct_drat(env, formula, &drat_proof, target),
    )
}

/// Ay SAT decision tactic with LRAT proof certificate
///
/// Like `ay_decide_with_proof`, but uses the more efficient LRAT format.
/// LRAT proofs include clause IDs and RUP hints for faster verification.
///
/// # Arguments
/// * `state` - The current proof state
/// * `config` - Configuration including the CNF formula
/// * `lrat_proof` - LRAT proof certificate from Ay
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `config.formula` encodes the same proposition as the goal target
/// REQUIRES: `config.logic` is the explicit logic classification for this
///   certificate request
/// REQUIRES: `lrat_proof` is an LRAT certificate claiming `config.formula` is UNSAT
/// ENSURES: On Ok, the LRAT certificate verified and the goal is closed
/// ENSURES: On Ok without a direct kernel proof, recovers through the shared
///   bridge/superposition lane without synthesizing a whole-goal `trustedAy`
/// ENSURES: On Err(SmtFailed), LRAT verification rejected the certificate
pub fn ay_decide_with_lrat_proof(
    state: &mut ProofState,
    config: AyProofConfig,
    lrat_proof: LratProof,
) -> TacticResult {
    run_certificate_entrypoint(
        state,
        &config,
        lrat_proof.operations.len(),
        "ay_decide_with_lrat_proof",
        "LRAT",
        |env, formula, target| verify_and_reconstruct_lrat(env, formula, &lrat_proof, target),
    )
}

/// Shared certificate entrypoint pipeline.
///
/// Owns the verify-select-close workflow that both DRAT and LRAT
/// entrypoints previously duplicated:
///
/// 1. fetch the current goal and instantiate the target
/// 2. emit verbose verification log
/// 3. run the provided verifier
/// 4. map failed verification into `TacticError::SmtFailed`
/// 5. delegate proof choice to `selection::select_verified_certificate_proof`
/// 6. emit verbose closing log
/// 7. close the goal
fn run_certificate_entrypoint(
    state: &mut ProofState,
    config: &AyProofConfig,
    operations_len: usize,
    tactic_name: &str,
    certificate_kind: &str,
    verify: impl FnOnce(&Environment, &CnfFormula, &Expr) -> DratProofResult,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    if config.base().is_verbose() {
        tracing::debug!(
            "[{tactic_name}] Verifying {certificate_kind} proof ({operations_len} operations)"
        );
    }

    let result = verify(state.env(), config.formula(), &target);

    if !result.verified {
        let error_msg = result
            .error
            .unwrap_or_else(|| format!("{certificate_kind} verification failed"));
        return Err(TacticError::SmtFailed {
            tactic: tactic_name.into(),
            detail: error_msg,
        });
    }

    let proof_term = select_verified_certificate_proof(
        state,
        result.proof_term,
        CertificateProofSelection {
            goal: &goal,
            target: &target,
            verify_policy: config.base().verify_policy(),
            logic: config.logic(),
            tactic_name,
            certificate_kind,
        },
    )?;

    if config.base().is_verbose() {
        tracing::debug!("[{tactic_name}] {certificate_kind} proof verified, closing goal");
    }

    state.close_goal(&goal, proof_term)?;
    Ok(())
}
