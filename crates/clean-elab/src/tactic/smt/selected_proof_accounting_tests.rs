// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#[cfg(feature = "ay-smt")]
use super::bridge_reconstruction::{
    accept_bridge_reconstruction_candidate, BridgeReconstructionCandidate,
};
#[cfg(feature = "ay-smt")]
use super::decide::close_bridge_verified_goal;
#[cfg(feature = "ay-smt")]
use super::selected_proof::{accept_selected_direct_proof, SelectedDirectProof};
#[cfg(feature = "ay-smt")]
use crate::tactic::ProofState;
#[cfg(feature = "ay-smt")]
use clean_kernel::sorry::{
    local_ay_reconstruction_success_count, reset_local_ay_reconstruction_success_counter,
};
#[cfg(feature = "ay-smt")]
use clean_kernel::{Declaration, Environment, Expr, Level, Name};

#[cfg(feature = "ay-smt")]
fn trusted_ay_term(goal: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("trustedAy"), vec![Level::zero()]),
        Expr::const_(Name::from_string(goal), vec![]),
    )
}

#[cfg(feature = "ay-smt")]
#[test]
#[serial_test::serial]
fn test_close_bridge_verified_goal_records_embedded_trust_from_validated_proof() {
    reset_local_ay_reconstruction_success_counter();
    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let mut env = Environment::new();
    env.init_trusted_ay().expect("add trustedAy axiom");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add P axiom");
    let proof = trusted_ay_term("P");

    let mut state = ProofState::new(env, prop_p.clone());
    let goal = state.current_goal().expect("goal").clone();
    close_bridge_verified_goal(&mut state, &goal, &prop_p, &proof)
        .expect("validated bridge proof should close the goal");

    assert!(
        state.is_complete(),
        "bridge proof should close the active goal"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        1,
        "validated bridge proof should mirror its embedded trustedAy sub-terms"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "plain decide bridge validation should not increment the ay-only reconstruction counter"
    );
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_close_bridge_verified_goal_fails_closed_without_trust() {
    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let invalid_bridge_proof = Expr::const_(Name::from_string("False"), vec![]);
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add P axiom");

    let mut state = ProofState::new(env, prop_p.clone());
    let goal = state.current_goal().expect("goal").clone();
    let result = close_bridge_verified_goal(&mut state, &goal, &prop_p, &invalid_bridge_proof);

    assert!(
        matches!(result, Err(crate::tactic::TacticError::SmtFailed { .. })),
        "invalid bridge proof should now fail closed, got: {result:?}"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "fail-closed bridge recovery must not record trustedAy debt"
    );
    assert_eq!(
        state.trust_ledger().smt_recovery.invalid_bridge_candidates,
        1,
        "failing closed still records the rejected invalid bridge candidate"
    );
    assert!(
        !state.is_complete(),
        "goal should remain open after fail-closed bridge recovery"
    );
}

#[cfg(feature = "ay-smt")]
#[test]
#[serial_test::serial]
fn test_accept_bridge_reconstruction_candidate_records_embedded_trust_and_success() {
    reset_local_ay_reconstruction_success_counter();
    let mut state = ProofState::new(Environment::default(), Expr::prop());
    let proof = Expr::app(trusted_ay_term("P"), trusted_ay_term("Q"));

    let accepted = accept_bridge_reconstruction_candidate(
        &mut state,
        BridgeReconstructionCandidate {
            proof: proof.clone(),
            trust_subterm_count: 2,
        },
        "ay_smt",
    );

    assert_eq!(
        accepted, proof,
        "bridge acceptance should return the chosen proof"
    );
    assert!(
        local_ay_reconstruction_success_count() >= 1,
        "bridge acceptance should record ay reconstruction success"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        2,
        "bridge acceptance should mirror trust from the selected proof"
    );
}

#[cfg(feature = "ay-smt")]
#[test]
#[serial_test::serial]
fn test_accept_selected_direct_proof_records_embedded_trust_from_selected_proof() {
    reset_local_ay_reconstruction_success_counter();
    let mut state = ProofState::new(Environment::default(), Expr::prop());
    let proof = Expr::app(trusted_ay_term("P"), trusted_ay_term("Q"));

    let accepted = accept_selected_direct_proof(
        &mut state,
        SelectedDirectProof::new(proof.clone(), 2),
        "ay_smt",
        "direct ay",
    );

    assert_eq!(
        accepted, proof,
        "direct acceptance should return the chosen proof"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        2,
        "direct acceptance should mirror embedded trustedAy sub-terms from the chosen proof"
    );
    assert_eq!(
        state
            .trust_ledger()
            .trusted_ay_provenance
            .unclassified_steps,
        2,
        "count-only direct acceptance should preserve trustedAy debt as unclassified"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "accepting an already-counted direct ay proof must not double-count reconstruction success"
    );
}

#[cfg(feature = "ay-smt")]
#[test]
#[serial_test::serial]
fn test_accept_selected_direct_proof_records_typed_residual_provenance() {
    use clean_auto::bridge::ay_contract::test_utils::residual_trust_summary_from_source;
    use clean_auto::bridge::ay_contract::ResidualTrustSource;

    reset_local_ay_reconstruction_success_counter();
    let mut state = ProofState::new(Environment::default(), Expr::prop());
    let proof = trusted_ay_term("P");

    let accepted = accept_selected_direct_proof(
        &mut state,
        SelectedDirectProof::with_residual(
            proof.clone(),
            1,
            residual_trust_summary_from_source(ResidualTrustSource::LocalReconstructionGap),
        ),
        "ay_smt",
        "direct ay",
    );

    assert_eq!(accepted, proof);
    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_ay_count, 1);
    assert_eq!(ledger.trusted_ay_provenance.local_gap_steps, 1);
    assert_eq!(ledger.trusted_ay_provenance.unclassified_steps, 0);
}
