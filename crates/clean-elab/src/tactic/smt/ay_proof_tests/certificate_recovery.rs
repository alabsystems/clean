// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use serial_test::serial;

#[test]
fn test_ay_proof_config_new_preserves_inputs() {
    let formula = contradiction_formula();
    let config = AyProofConfig::new(
        AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyStrict),
        AyLogic::QfUf,
        formula.clone(),
    );

    assert_eq!(config.base().verify_policy(), SmtVerifyPolicy::VerifyStrict);
    assert_eq!(config.base().logic_override(), None);
    assert_eq!(config.logic(), AyLogic::QfUf);
    assert!(
        config.base().produces_proofs(),
        "strict verification should preserve the proof-production invariant"
    );
    assert_eq!(config.formula().clauses, formula.clauses);
    assert_eq!(config.formula().num_vars, formula.num_vars);
}

#[test]
#[serial]
fn test_ay_decide_with_proof_verified_certificate_avoids_trusted_ay() {
    reset_all_trust_counters();
    let mut state = contradiction_state();
    let ay_before = ay_proof_count();

    ay_decide_with_proof(
        &mut state,
        AyProofConfig::new(AyConfig::default(), AyLogic::QfUf, contradiction_formula()),
        contradiction_drat_proof(),
    )
    .expect("DRAT-verified contradiction should recover through the shared fallback lane");

    assert!(state.is_complete(), "goal should be closed");
    assert_certificate_recovery_avoids_non_ay_fallbacks(&state, "verified DRAT fallback");
    assert_eq!(
        ay_proof_count() - ay_before,
        0,
        "verified DRAT fallback should avoid whole-goal trustedAy"
    );
}

#[test]
#[serial]
fn test_ay_decide_with_lrat_proof_verified_certificate_avoids_trusted_ay() {
    reset_all_trust_counters();
    let mut state = contradiction_state();
    let ay_before = ay_proof_count();

    ay_decide_with_lrat_proof(
        &mut state,
        AyProofConfig::new(AyConfig::default(), AyLogic::QfUf, contradiction_formula()),
        contradiction_lrat_proof(),
    )
    .expect("LRAT-verified contradiction should recover through the shared fallback lane");

    assert!(state.is_complete(), "goal should be closed");
    assert_certificate_recovery_avoids_non_ay_fallbacks(&state, "verified LRAT fallback");
    assert_eq!(
        ay_proof_count() - ay_before,
        0,
        "verified LRAT fallback should avoid whole-goal trustedAy"
    );
}
