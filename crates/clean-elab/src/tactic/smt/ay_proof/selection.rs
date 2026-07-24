// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate proof-selection and recovery policy.
//!
//! Chooses between the direct certificate proof and bridge recovery,
//! respecting the strict zero-trust policy when required.

use crate::tactic::{Goal, ProofState, TacticError};
use clean_auto::bridge::ay_contract::AyLogic;
use clean_kernel::Expr;

use super::super::ay_types::{requires_zero_trust_reconstruction, SmtVerifyPolicy};
#[cfg(feature = "ay-smt")]
use super::super::bridge_reconstruction::{
    accept_bridge_reconstruction_candidate, try_bridge_reconstruction_candidate,
};
use super::super::bridge_reconstruction::{
    recover_verified_goal_after_reconstruction_gap_with_requirement, RecoveryTrustRequirement,
};
use super::super::bridge_validation::prepare_smt_proof_validation;
use super::super::decide::validate_proof_term;
use super::super::selected_proof::{accept_selected_direct_proof, SelectedDirectProof};
#[cfg(feature = "ay-smt")]
use super::super::selected_proof::{choose_selected_proof, SelectedProofChoice};
use super::super::trusted_subterms::count_embedded_trusted_ay_terms;

#[derive(Clone, Copy)]
pub(super) struct CertificateProofSelection<'a> {
    pub(super) goal: &'a Goal,
    pub(super) target: &'a Expr,
    pub(super) verify_policy: SmtVerifyPolicy,
    pub(super) logic: AyLogic,
    pub(super) tactic_name: &'a str,
    pub(super) certificate_kind: &'a str,
}

fn recover_after_invalid_certificate_direct_proof(
    state: &mut ProofState,
    selection: CertificateProofSelection<'_>,
    validation_error: TacticError,
) -> Result<Expr, TacticError> {
    state.record_invalid_direct_certificate_candidate();
    tracing::warn!(
        tactic = selection.tactic_name,
        certificate_kind = selection.certificate_kind,
        error = %validation_error,
        logic = %selection.logic,
        "certificate direct proof failed kernel validation before selection; trying recovery lane"
    );
    let requirement =
        if requires_zero_trust_reconstruction(selection.verify_policy, selection.logic) {
            RecoveryTrustRequirement::ZeroTrust
        } else {
            RecoveryTrustRequirement::Any
        };
    recover_verified_goal_after_reconstruction_gap_with_requirement(
        state,
        selection.goal,
        selection.target,
        selection.tactic_name,
        requirement,
    )
    .map_err(|recovery_error| TacticError::SmtFailed {
        tactic: selection.tactic_name.to_string(),
        detail: format!(
            "{} direct proof failed kernel validation before selection: {}; recovery also failed: {}",
            selection.certificate_kind, validation_error, recovery_error
        ),
    })
}

pub(super) fn select_verified_certificate_proof(
    state: &mut ProofState,
    proof_term: Option<Expr>,
    selection: CertificateProofSelection<'_>,
) -> Result<Expr, TacticError> {
    match proof_term {
        Some(proof) => select_preferred_certificate_proof(state, proof, selection),
        None => {
            let requirement = if requires_zero_trust_reconstruction(
                selection.verify_policy,
                selection.logic,
            ) {
                tracing::warn!(
                    tactic = selection.tactic_name,
                    certificate_kind = selection.certificate_kind,
                    logic = %selection.logic,
                    "verified certificate had no direct kernel proof; strict policy requires zero-trust recovery"
                );
                RecoveryTrustRequirement::ZeroTrust
            } else {
                tracing::warn!(
                    tactic = selection.tactic_name,
                    certificate_kind = selection.certificate_kind,
                    "verified certificate had no direct kernel proof; recovering via shared fallback lane"
                );
                RecoveryTrustRequirement::Any
            };
            recover_verified_goal_after_reconstruction_gap_with_requirement(
                state,
                selection.goal,
                selection.target,
                selection.tactic_name,
                requirement,
            )
        }
    }
}

#[cfg(feature = "ay-smt")]
fn select_preferred_certificate_proof(
    state: &mut ProofState,
    proof: Expr,
    selection: CertificateProofSelection<'_>,
) -> Result<Expr, TacticError> {
    use clean_auto::bridge::ay_contract::ReconstructionQuality;
    prepare_smt_proof_validation(state, selection.tactic_name)?;
    let proof = match validate_proof_term(state, selection.goal, &proof, selection.target) {
        Ok(proof) => proof,
        Err(error) => {
            return recover_after_invalid_certificate_direct_proof(state, selection, error)
        }
    };
    let direct_trust_subterm_count = count_embedded_trusted_ay_terms(&proof);
    let direct_proof = SelectedDirectProof::new(proof, direct_trust_subterm_count);
    if ReconstructionQuality::from_trust_count(direct_trust_subterm_count).is_fully_verified() {
        return Ok(accept_selected_direct_proof(
            state,
            direct_proof,
            selection.tactic_name,
            selection.certificate_kind,
        ));
    }

    if requires_zero_trust_reconstruction(selection.verify_policy, selection.logic) {
        tracing::warn!(
            tactic = selection.tactic_name,
            certificate_kind = selection.certificate_kind,
            direct_trust_subterm_count,
            logic = %selection.logic,
            "strict zero-trust policy rejected partially trusted direct certificate proof; recovering via zero-trust fallback lane"
        );
        return recover_verified_goal_after_reconstruction_gap_with_requirement(
            state,
            selection.goal,
            selection.target,
            selection.tactic_name,
            RecoveryTrustRequirement::ZeroTrust,
        );
    }

    let bridge_candidate = try_bridge_reconstruction_candidate(
        state,
        selection.goal,
        selection.target,
        selection.tactic_name,
    )
    .into_candidate();
    match choose_selected_proof(direct_proof, bridge_candidate, selection.tactic_name) {
        SelectedProofChoice::Direct(direct_proof) => Ok(accept_selected_direct_proof(
            state,
            direct_proof,
            selection.tactic_name,
            selection.certificate_kind,
        )),
        SelectedProofChoice::Bridge(candidate) => {
            tracing::info!(
                tactic = selection.tactic_name,
                certificate_kind = selection.certificate_kind,
                direct_trust_subterm_count,
                bridge_trust_subterm_count = candidate.trust_subterm_count,
                "certificate direct proof carries more trust than bridge candidate; choosing bridge proof"
            );
            Ok(accept_bridge_reconstruction_candidate(
                state,
                candidate,
                selection.tactic_name,
            ))
        }
    }
}

#[cfg(not(feature = "ay-smt"))]
fn select_preferred_certificate_proof(
    state: &mut ProofState,
    proof: Expr,
    selection: CertificateProofSelection<'_>,
) -> Result<Expr, TacticError> {
    prepare_smt_proof_validation(state, selection.tactic_name)?;
    let proof = match validate_proof_term(state, selection.goal, &proof, selection.target) {
        Ok(proof) => proof,
        Err(error) => {
            return recover_after_invalid_certificate_direct_proof(state, selection, error)
        }
    };
    let direct_trust_subterm_count = count_embedded_trusted_ay_terms(&proof);
    if direct_trust_subterm_count > 0
        && requires_zero_trust_reconstruction(selection.verify_policy, selection.logic)
    {
        tracing::warn!(
            tactic = selection.tactic_name,
            certificate_kind = selection.certificate_kind,
            direct_trust_subterm_count,
            logic = %selection.logic,
            "strict zero-trust policy rejected partially trusted direct certificate proof; recovering via zero-trust fallback lane"
        );
        return recover_verified_goal_after_reconstruction_gap_with_requirement(
            state,
            selection.goal,
            selection.target,
            selection.tactic_name,
            RecoveryTrustRequirement::ZeroTrust,
        );
    }

    Ok(accept_selected_direct_proof(
        state,
        SelectedDirectProof::new(proof, direct_trust_subterm_count),
        selection.tactic_name,
        selection.certificate_kind,
    ))
}

#[cfg(all(test, feature = "ay-smt"))]
pub(in crate::tactic::smt) fn select_verified_certificate_proof_for_test(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    proof_term: Option<Expr>,
    verify_policy: SmtVerifyPolicy,
    logic: AyLogic,
    tactic_name: &str,
    certificate_kind: &str,
) -> Result<Expr, TacticError> {
    select_verified_certificate_proof(
        state,
        proof_term,
        CertificateProofSelection {
            goal,
            target,
            verify_policy,
            logic,
            tactic_name,
            certificate_kind,
        },
    )
}

#[cfg(all(test, not(feature = "ay-smt")))]
mod tests {
    use super::*;
    use clean_kernel::{env::Declaration, Name};

    fn setup_prop_env() -> ProofState {
        let mut env = clean_kernel::Environment::new();
        env.init_true_false().expect("True/False should initialize");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("P"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("P axiom should register");
        ProofState::new(env, Expr::const_(Name::from_string("P"), vec![]))
    }

    #[test]
    fn test_non_ay_certificate_selector_preserves_validation_failure_when_recovery_exhausts() {
        let mut state = setup_prop_env();
        let goal = state.current_goal().expect("should have a goal").clone();
        let target = state.metas.instantiate(&goal.target);

        let err = select_verified_certificate_proof(
            &mut state,
            Some(Expr::type_()),
            CertificateProofSelection {
                goal: &goal,
                target: &target,
                verify_policy: SmtVerifyPolicy::ExtractOnly,
                logic: AyLogic::QfUf,
                tactic_name: "test_non_ay_invalid_direct",
                certificate_kind: "DRAT",
            },
        )
        .expect_err("invalid direct proof should fail closed in the non-ay selector path");

        assert!(
            matches!(
                &err,
                TacticError::SmtFailed { tactic, detail }
                    if tactic == "test_non_ay_invalid_direct"
                        && detail.contains(
                            "DRAT direct proof failed kernel validation before selection"
                        )
                        && detail.contains("recovery also failed")
            ),
            "non-ay certificate selector should preserve the validation failure: {err:?}"
        );
        assert_eq!(
            state.trust_ledger().trusted_ay_count,
            0,
            "failing closed after invalid direct proof should not add trust debt"
        );
    }
}
