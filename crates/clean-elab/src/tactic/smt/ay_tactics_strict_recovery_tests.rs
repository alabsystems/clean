// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![cfg(feature = "ay-smt")]

use super::ay_tactics::select_verified_ay_proof;
use super::ay_types::SmtVerifyPolicy;
use crate::tactic::ProofState;
use clean_auto::bridge::ay_contract::AyLogic;
use clean_kernel::sorry::{
    local_ay_reconstruction_success_count, reset_local_ay_reconstruction_success_counter,
};
use clean_kernel::{env::Declaration, Environment, Expr, Name};
use serial_test::serial;

fn setup_prop_env() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().expect("True/False should initialize");
    env.init_classical().expect("Classical should initialize");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("P axiom should register");
    env
}

#[test]
#[serial]
fn test_strict_qf_uf_without_direct_proof_fails_when_no_zero_trust_recovery_exists() {
    reset_local_ay_reconstruction_success_counter();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(setup_prop_env(), target.clone());
    let goal = state.current_goal().expect("goal").clone();

    let err = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_strict_no_direct_no_recovery",
        None,
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfUf,
    )
    .expect_err("VerifyStrict QF_UF should fail closed when no zero-trust recovery exists");

    assert!(
        matches!(
            &err,
            crate::tactic::TacticError::SmtFailed { tactic, detail }
                if tactic == "test_strict_no_direct_no_recovery"
                    && detail.contains(
                        "direct reconstruction, bridge recovery, and superposition fallback all failed"
                    )
        ),
        "strict no-direct failure should preserve tactic name and fail-closed detail: {err:?}"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "failing closed without recovery should not add trustedAy debt"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "failing closed without recovery should not record reconstruction success"
    );
    assert!(
        !state.is_complete(),
        "goal should remain open after strict fail-closed recovery exhaustion"
    );
}
