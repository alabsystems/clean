// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

pub(super) use super::{
    ay_decide_with_lrat_proof, ay_decide_with_proof,
    ay_proof::select_verified_certificate_proof_for_test,
    ay_proof_count,
    bridge_reconstruction::{install_test_bridge_candidate, BridgeReconstructionCandidate},
    reset_ay_counter, reset_ay_reconstruction_failure_counter, reset_sorry_counter,
};
pub(super) use crate::tactic::drat::{CnfFormula, DratOp, DratProof, LratOp, LratProof};
pub(super) use crate::tactic::smt::SmtVerifyPolicy;
pub(super) use crate::tactic::{
    reset_arith_counter, AyConfig, AyProofConfig, LocalDecl, ProofState, TacticError,
};
pub(super) use clean_auto::bridge::ay_contract::AyLogic;
pub(super) use clean_kernel::env::Declaration;
pub(super) use clean_kernel::sorry::{
    local_ay_reconstruction_success_count, reset_local_ay_reconstruction_success_counter,
};
pub(super) use clean_kernel::{Environment, Expr, FVarId, Level, Name};

mod support;
use support::{
    assert_certificate_recovery_avoids_non_ay_fallbacks, contradiction_drat_proof,
    contradiction_formula, contradiction_lrat_proof, contradiction_state, prop_p,
    reset_all_trust_counters, run_verifystrict_public_certificate_with_injected_candidate,
    setup_certificate_env,
};

pub(super) fn trusted_ay_proof(target: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("trustedAy"), vec![Level::zero()]),
        target,
    )
}

mod certificate_recovery;
mod direct_proof_selection;
mod strict_policy;
mod strict_policy_arith;
