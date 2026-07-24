// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::verify::verify_closed_proof_with_trust_summary;
use crate::handlers::*;
use clean_elab::tactic::{
    convert, sorry as tactic_sorry, ProofState as InternalProofState, ProofTrustLedger,
    SmtRecoveryLedger, TrustedArithProvenanceLedger, TrustedAyProvenanceLedger,
};
use clean_kernel::sorry::{create_sorry_term_with_kind, SorryKind};
use clean_kernel::{Environment, Expr, Name};

async fn solve_proof_state_with_tactics(
    state: &ServerState,
    theorem: &str,
    tactics: &[&str],
) -> String {
    let init_params = InitProofStateParams {
        theorem: theorem.to_string(),
        problem_id: None,
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(state, RequestId::Number(1), init_params).await;
    assert!(
        init_response.error.is_none(),
        "initProofState failed: {:?}",
        init_response.error
    );
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();

    let mut current_state_id = init_result.state_id;
    for (i, tactic) in tactics.iter().enumerate() {
        let apply_params = ApplyTacticParams {
            state_id: current_state_id.clone(),
            goal_id: "g0".to_string(),
            tactic: (*tactic).to_string(),
            timeout_ms: None,
        };
        let apply_response =
            handle_apply_tactic(state, RequestId::Number(i as i64 + 2), apply_params).await;
        assert!(
            apply_response.error.is_none(),
            "Tactic '{}' failed: {:?}",
            tactic,
            apply_response.error
        );
        let apply_result: crate::proof_state::ApplyTacticResult =
            serde_json::from_value(apply_response.result.unwrap()).unwrap();
        assert!(apply_result.success, "Tactic '{}' should succeed", tactic);
        current_state_id = apply_result.new_state_id;
    }

    current_state_id
}

async fn init_interactive_identity_state(state: &ServerState) -> String {
    let init_params = InitProofStateParams {
        theorem: "(A : Type) -> A -> A".to_string(),
        problem_id: Some("interactive_trust_consistency".to_string()),
        timeout_ms: None,
    };
    let init_response = handle_init_proof_state(state, RequestId::Number(1), init_params).await;
    assert!(
        init_response.error.is_none(),
        "initProofState failed: {:?}",
        init_response.error
    );
    let init_result: InitProofStateResult =
        serde_json::from_value(init_response.result.unwrap()).unwrap();
    init_result.state_id
}

async fn apply_tactic_or_expect_success(
    state: &ServerState,
    request_id: i64,
    state_id: &str,
    tactic: &str,
) -> crate::proof_state::ApplyTacticResult {
    let apply_params = ApplyTacticParams {
        state_id: state_id.to_string(),
        goal_id: "g0".to_string(),
        tactic: tactic.to_string(),
        timeout_ms: None,
    };
    let apply_response =
        handle_apply_tactic(state, RequestId::Number(request_id), apply_params).await;
    assert!(
        apply_response.error.is_none(),
        "applyTactic('{tactic}') failed: {:?}",
        apply_response.error
    );
    let apply_result: crate::proof_state::ApplyTacticResult =
        serde_json::from_value(apply_response.result.unwrap()).unwrap();
    assert!(
        apply_result.success,
        "applyTactic('{tactic}') should succeed"
    );
    apply_result
}

async fn solve_identity_proof_interactively(
    state: &ServerState,
) -> (String, crate::proof_state::ApplyTacticResult) {
    let mut state_id = init_interactive_identity_state(state).await;
    let mut final_apply_result = None;

    for (i, tactic) in ["intro A", "intro a", "assumption"].iter().enumerate() {
        let apply_result =
            apply_tactic_or_expect_success(state, i as i64 + 2, &state_id, tactic).await;
        state_id = apply_result.new_state_id.clone();
        final_apply_result = Some(apply_result);
    }

    (
        state_id,
        final_apply_result.expect("final applyTactic result should exist"),
    )
}

fn assert_sorry_provenance(
    summary: &TrustSummary,
    expected_explicit: bool,
    expected_synthetic: bool,
    context: &str,
) {
    let provenance = summary
        .sorry_provenance
        .as_ref()
        .expect("closed-proof trust summaries should include sorry provenance");
    assert_eq!(
        provenance.has_explicit_sorry, expected_explicit,
        "{context}: unexpected explicit sorry provenance"
    );
    assert_eq!(
        provenance.has_synthetic_sorry, expected_synthetic,
        "{context}: unexpected synthetic sorry provenance"
    );
}

fn assert_matching_trust_summary(actual: &TrustSummary, expected: &TrustSummary, context: &str) {
    assert_eq!(
        actual.sorry_count, expected.sorry_count,
        "{context}: sorry_count mismatch"
    );
    assert_eq!(
        actual.sorry_provenance, expected.sorry_provenance,
        "{context}: sorry_provenance mismatch"
    );
    assert_eq!(
        actual.ay_count, expected.ay_count,
        "{context}: ay_count mismatch"
    );
    assert_eq!(
        actual.ay_provenance, expected.ay_provenance,
        "{context}: ay_provenance mismatch"
    );
    assert_eq!(
        actual.arith_count, expected.arith_count,
        "{context}: arith_count mismatch"
    );
    assert_eq!(
        actual.arith_provenance, expected.arith_provenance,
        "{context}: arith_provenance mismatch"
    );
    assert_eq!(
        actual.kernel_check_failures, expected.kernel_check_failures,
        "{context}: kernel_check_failures mismatch"
    );
    assert_eq!(
        actual.fully_verified, expected.fully_verified,
        "{context}: fully_verified mismatch"
    );
}

fn assert_clean_fully_verified_summary(summary: &TrustSummary, context: &str) {
    assert_eq!(
        summary.sorry_count, 0,
        "{context}: sorry_count should stay zero"
    );
    assert_sorry_provenance(summary, false, false, context);
    assert_eq!(summary.ay_count, 0, "{context}: ay_count should stay zero");
    assert!(
        summary.ay_provenance.is_none(),
        "{context}: clean proof should omit ay provenance"
    );
    assert_eq!(
        summary.arith_count, 0,
        "{context}: arith_count should stay zero"
    );
    assert!(
        summary.arith_provenance.is_none(),
        "{context}: clean proof should omit arith provenance"
    );
    assert_eq!(
        summary.kernel_check_failures, 0,
        "{context}: kernel_check_failures should stay zero"
    );
    assert!(
        summary.fully_verified,
        "{context}: clean solved proof must be fully_verified"
    );
}

#[tokio::test]
async fn test_extract_proof_trust_summary_reports_sorry() {
    let mut proof_state = InternalProofState::new(Environment::new(), Expr::prop());
    tactic_sorry(&mut proof_state).expect("sorry should close the proof state");
    assert!(proof_state.is_complete(), "proof state should be complete");

    let state = ServerState::new();
    let state_id = state
        .proof_cache
        .insert(proof_state, None, None, 0)
        .to_string();

    let extract_params = ExtractProofParams {
        state_id,
        format: "term".to_string(),
    };
    let extract_response =
        handle_extract_proof(&state, RequestId::Number(100), extract_params).await;
    assert!(
        extract_response.error.is_none(),
        "extractProof failed: {:?}",
        extract_response.error
    );

    let extract_result: ExtractProofResult =
        serde_json::from_value(extract_response.result.unwrap()).unwrap();
    let trust_summary = extract_result
        .trust_summary
        .expect("extractProof should return a trust summary");

    assert!(extract_result.is_solved, "proof state should be solved");
    assert!(
        extract_result.verification.verified,
        "sorry-backed proofs still type-check in the default environment"
    );
    assert_eq!(trust_summary.sorry_count, 1);
    assert_sorry_provenance(&trust_summary, true, false, "extractProof explicit sorry");
    assert_eq!(trust_summary.ay_count, 0);
    assert!(trust_summary.ay_provenance.is_none());
    assert_eq!(trust_summary.arith_count, 0);
    assert!(trust_summary.arith_provenance.is_none());
    assert_eq!(trust_summary.kernel_check_failures, 0);
    assert!(
        !trust_summary.fully_verified,
        "sorry-backed proofs must not be marked fully verified"
    );
}

#[tokio::test]
async fn test_extract_proof_trust_summary_reports_synthetic_sorry() {
    let env = Environment::with_prelude();
    let mut proof_state = InternalProofState::new(env.clone(), Expr::prop());
    let synthetic = create_sorry_term_with_kind(&env, &Expr::prop(), SorryKind::Synthetic);
    convert(&mut proof_state, synthetic).expect("synthetic sorry should close the proof state");
    proof_state.set_trust_ledger(ProofTrustLedger {
        sorry_count: 1,
        ..ProofTrustLedger::default()
    });
    assert!(proof_state.is_complete(), "proof state should be complete");

    let state = ServerState::new().with_env(env);
    let state_id = state
        .proof_cache
        .insert(proof_state, None, None, 0)
        .to_string();

    let extract_params = ExtractProofParams {
        state_id,
        format: "term".to_string(),
    };
    let extract_response =
        handle_extract_proof(&state, RequestId::Number(100), extract_params).await;
    assert!(
        extract_response.error.is_none(),
        "extractProof failed: {:?}",
        extract_response.error
    );

    let extract_result: ExtractProofResult =
        serde_json::from_value(extract_response.result.unwrap()).unwrap();
    let trust_summary = extract_result
        .trust_summary
        .expect("extractProof should return a trust summary");

    assert!(extract_result.verification.verified);
    assert_eq!(trust_summary.sorry_count, 1);
    assert_sorry_provenance(&trust_summary, false, true, "extractProof synthetic sorry");
    assert_eq!(trust_summary.ay_count, 0);
    assert!(trust_summary.ay_provenance.is_none());
    assert_eq!(trust_summary.arith_count, 0);
    assert!(trust_summary.arith_provenance.is_none());
    assert_eq!(trust_summary.kernel_check_failures, 0);
    assert!(
        !trust_summary.fully_verified,
        "synthetic sorry proofs must not be marked fully verified"
    );
}

#[tokio::test]
async fn test_extract_proof_trust_summary_preserves_trusted_arith_ledger() {
    let env = Environment::with_prelude();
    let mut proof_state =
        InternalProofState::new(env.clone(), Expr::const_(Name::from_string("True"), vec![]));
    convert(
        &mut proof_state,
        Expr::const_(Name::from_string("True.intro"), vec![]),
    )
    .expect("True.intro should close the proof state");
    proof_state.set_trust_ledger(ProofTrustLedger {
        trusted_arith_count: 2,
        trusted_arith_provenance: TrustedArithProvenanceLedger {
            goal_close_helper_steps: 1,
            target_rewrite_helper_steps: 1,
            ..TrustedArithProvenanceLedger::default()
        },
        ..ProofTrustLedger::default()
    });
    assert!(proof_state.is_complete(), "proof state should be complete");

    let state = ServerState::new().with_env(env);
    let state_id = state
        .proof_cache
        .insert(proof_state, None, None, 0)
        .to_string();

    let extract_params = ExtractProofParams {
        state_id,
        format: "term".to_string(),
    };
    let extract_response =
        handle_extract_proof(&state, RequestId::Number(100), extract_params).await;
    assert!(
        extract_response.error.is_none(),
        "extractProof failed: {:?}",
        extract_response.error
    );

    let extract_result: ExtractProofResult =
        serde_json::from_value(extract_response.result.unwrap()).unwrap();
    let trust_summary = extract_result
        .trust_summary
        .expect("extractProof should return a trust summary");

    assert!(
        extract_result.verification.verified,
        "extractProof should still verify the closed proof term"
    );
    assert_eq!(trust_summary.sorry_count, 0);
    assert_sorry_provenance(
        &trust_summary,
        false,
        false,
        "extractProof trustedArith ledger",
    );
    assert_eq!(trust_summary.ay_count, 0);
    assert!(trust_summary.ay_provenance.is_none());
    let provenance = trust_summary
        .arith_provenance
        .as_ref()
        .expect("trustedArith debt should expose provenance details");
    assert!(
        trust_summary.arith_count == 2,
        "extractProof should preserve ledger-backed trustedArith usage"
    );
    assert_eq!(provenance.direct_steps, 0);
    assert_eq!(provenance.goal_close_helper_steps, 1);
    assert_eq!(provenance.target_rewrite_helper_steps, 1);
    assert_eq!(provenance.unclassified_steps, 0);
    assert_eq!(trust_summary.kernel_check_failures, 0);
    assert!(
        !trust_summary.fully_verified,
        "trustedArith-backed proofs must not be marked fully verified"
    );
}

#[tokio::test]
async fn test_extract_proof_trust_summary_reports_fully_verified() {
    let state = ServerState::new();
    let state_id = solve_proof_state_with_tactics(
        &state,
        "(A : Type) -> A -> A",
        &["intro A", "intro a", "assumption"],
    )
    .await;

    let extract_params = ExtractProofParams {
        state_id,
        format: "term".to_string(),
    };
    let extract_response =
        handle_extract_proof(&state, RequestId::Number(100), extract_params).await;
    assert!(
        extract_response.error.is_none(),
        "extractProof failed: {:?}",
        extract_response.error
    );

    let extract_result: ExtractProofResult =
        serde_json::from_value(extract_response.result.unwrap()).unwrap();
    let trust_summary = extract_result
        .trust_summary
        .expect("extractProof should return a trust summary");

    assert!(extract_result.verification.verified, "proof should verify");
    assert_eq!(trust_summary.sorry_count, 0);
    assert_sorry_provenance(&trust_summary, false, false, "extractProof fully verified");
    assert_eq!(trust_summary.ay_count, 0);
    assert!(trust_summary.ay_provenance.is_none());
    assert_eq!(trust_summary.arith_count, 0);
    assert!(trust_summary.arith_provenance.is_none());
    assert_eq!(trust_summary.kernel_check_failures, 0);
    assert!(
        trust_summary.fully_verified,
        "kernel-verified proofs with no trust fallbacks should be fully verified"
    );
}

#[tokio::test]
async fn test_interactive_trust_summary_matches_extract_proof_for_clean_solved_state() {
    let state = ServerState::new();
    let (state_id, final_apply_result) = solve_identity_proof_interactively(&state).await;
    assert!(
        final_apply_result.is_solved,
        "final interactive step should report a solved proof state"
    );

    let apply_trust = final_apply_result
        .trust_summary
        .as_ref()
        .expect("solved applyTactic result should include trust_summary");
    assert_clean_fully_verified_summary(
        apply_trust,
        "applyTactic fully verified interactive state",
    );

    let get_params = GetProofStateParams {
        state_id: state_id.clone(),
        format: crate::proof_state::OutputFormat::Full,
    };
    let get_response = handle_get_proof_state(&state, RequestId::Number(10), get_params).await;
    assert!(
        get_response.error.is_none(),
        "getProofState failed: {:?}",
        get_response.error
    );
    let api_state: crate::proof_state::ApiProofState =
        serde_json::from_value(get_response.result.unwrap()).unwrap();
    assert!(
        api_state.is_solved,
        "getProofState should report the cached solved state as solved"
    );
    let get_trust = api_state
        .trust_summary
        .as_ref()
        .expect("solved getProofState response should include trust_summary");
    assert_matching_trust_summary(
        get_trust,
        apply_trust,
        "getProofState vs applyTactic on clean solved state",
    );

    let extract_params = ExtractProofParams {
        state_id,
        format: "term".to_string(),
    };
    let extract_response =
        handle_extract_proof(&state, RequestId::Number(11), extract_params).await;
    assert!(
        extract_response.error.is_none(),
        "extractProof failed: {:?}",
        extract_response.error
    );
    let extract_result: ExtractProofResult =
        serde_json::from_value(extract_response.result.unwrap()).unwrap();
    assert!(
        extract_result.verification.verified,
        "extractProof should preserve the clean solved kernel verdict"
    );
    let extract_trust = extract_result
        .trust_summary
        .as_ref()
        .expect("extractProof should include trust_summary for solved states");
    assert_matching_trust_summary(
        extract_trust,
        apply_trust,
        "extractProof vs applyTactic on clean solved state",
    );
}

#[test]
fn test_verify_closed_proof_with_trust_summary_uses_kernel_verdict() {
    let env = Environment::with_prelude();
    let target = Expr::prop();
    let invalid_proof = Expr::const_(Name::from_string("Nat"), vec![]);

    let (verified, trust_summary) = verify_closed_proof_with_trust_summary(
        &env,
        &target,
        Some(&invalid_proof),
        ProofTrustLedger::default(),
        0,
    );

    assert!(
        !verified,
        "kernel verification must reject the intentionally wrong proof"
    );
    assert_eq!(trust_summary.sorry_count, 0);
    assert_sorry_provenance(
        &trust_summary,
        false,
        false,
        "verify_closed_proof_with_trust_summary invalid proof",
    );
    assert_eq!(trust_summary.ay_count, 0);
    assert!(trust_summary.ay_provenance.is_none());
    assert_eq!(trust_summary.arith_count, 0);
    assert!(trust_summary.arith_provenance.is_none());
    assert_eq!(trust_summary.kernel_check_failures, 0);
    assert!(
        !trust_summary.fully_verified,
        "fully_verified must follow the final kernel verdict, not raw completeness"
    );
}

#[tokio::test]
async fn test_extract_proof_trust_summary_reports_ay_provenance() {
    let env = Environment::with_prelude();
    let mut proof_state =
        InternalProofState::new(env.clone(), Expr::const_(Name::from_string("True"), vec![]));
    convert(
        &mut proof_state,
        Expr::const_(Name::from_string("True.intro"), vec![]),
    )
    .expect("True.intro should close the proof state");
    proof_state.set_trust_ledger(ProofTrustLedger {
        trusted_ay_count: 2,
        trusted_ay_provenance: TrustedAyProvenanceLedger {
            alethe_trust_steps: 1,
            unclassified_steps: 1,
            ..TrustedAyProvenanceLedger::default()
        },
        ..ProofTrustLedger::default()
    });

    let state = ServerState::new().with_env(env);
    let state_id = state
        .proof_cache
        .insert(proof_state, None, None, 0)
        .to_string();

    let extract_params = ExtractProofParams {
        state_id,
        format: "term".to_string(),
    };
    let extract_response =
        handle_extract_proof(&state, RequestId::Number(101), extract_params).await;
    assert!(
        extract_response.error.is_none(),
        "extractProof failed: {:?}",
        extract_response.error
    );

    let extract_result: ExtractProofResult =
        serde_json::from_value(extract_response.result.unwrap()).unwrap();
    let trust_summary = extract_result
        .trust_summary
        .expect("extractProof should return a trust summary");
    let provenance = trust_summary
        .ay_provenance
        .as_ref()
        .expect("trustedAy debt should expose provenance details");

    assert!(extract_result.verification.verified);
    assert_eq!(trust_summary.sorry_count, 0);
    assert_sorry_provenance(&trust_summary, false, false, "extractProof trustedAy");
    assert_eq!(trust_summary.ay_count, 2);
    assert_eq!(provenance.alethe_trust_steps, 1);
    assert_eq!(provenance.unclassified_steps, 1);
    assert_eq!(provenance.local_gap_steps, 0);
    assert_eq!(trust_summary.arith_count, 0);
    assert!(trust_summary.arith_provenance.is_none());
    assert_eq!(trust_summary.kernel_check_failures, 0);
    assert!(
        !trust_summary.fully_verified,
        "trustedAy-backed proofs must not be marked fully verified"
    );
}

// ==========================================================================
// SMT recovery accounting (#2920)
// ==========================================================================

#[test]
fn test_smt_recovery_surfaces_in_trust_summary_when_ledger_has_events() {
    let ledger = ProofTrustLedger {
        smt_recovery: SmtRecoveryLedger {
            invalid_direct_ay_candidates: 1,
            invalid_direct_certificate_candidates: 0,
            invalid_bridge_candidates: 2,
        },
        ..Default::default()
    };

    let summary = trust_summary_from_ledger(ledger, true, 0);

    assert!(
        summary.fully_verified,
        "zero accepted debt + verified must be fully_verified"
    );
    assert_eq!(summary.sorry_count, 0);
    assert_eq!(summary.ay_count, 0);
    assert_eq!(summary.arith_count, 0);
    let recovery = summary
        .smt_recovery
        .expect("smt_recovery must be present when ledger has recovery events");
    assert_eq!(recovery.invalid_direct_ay_candidates, 1);
    assert_eq!(recovery.invalid_direct_certificate_candidates, 0);
    assert_eq!(recovery.invalid_bridge_candidates, 2);
}

#[test]
fn test_smt_recovery_omitted_from_trust_summary_when_ledger_is_clean() {
    let ledger = ProofTrustLedger::default();
    let summary = trust_summary_from_ledger(ledger, true, 0);

    assert!(summary.fully_verified);
    assert!(
        summary.smt_recovery.is_none(),
        "smt_recovery must be omitted when no recovery events exist"
    );
}

#[test]
fn test_smt_recovery_does_not_affect_fully_verified() {
    let ledger = ProofTrustLedger {
        smt_recovery: SmtRecoveryLedger {
            invalid_direct_ay_candidates: 3,
            invalid_direct_certificate_candidates: 1,
            invalid_bridge_candidates: 1,
        },
        ..Default::default()
    };

    let summary = trust_summary_from_ledger(ledger, true, 0);

    assert!(
        summary.fully_verified,
        "smt_recovery must not participate in fully_verified computation"
    );
    assert!(summary.smt_recovery.is_some());
}

#[test]
fn test_smt_recovery_serializes_as_optional_json_field() {
    let ledger = ProofTrustLedger {
        smt_recovery: SmtRecoveryLedger {
            invalid_direct_ay_candidates: 1,
            invalid_direct_certificate_candidates: 0,
            invalid_bridge_candidates: 0,
        },
        ..Default::default()
    };

    let with_recovery = trust_summary_from_ledger(ledger, true, 0);
    let json_with = serde_json::to_value(&with_recovery).unwrap();
    assert!(
        json_with.get("smt_recovery").is_some(),
        "smt_recovery should appear in JSON when present"
    );

    let clean = trust_summary_from_ledger(ProofTrustLedger::default(), true, 0);
    let json_clean = serde_json::to_value(&clean).unwrap();
    assert!(
        json_clean.get("smt_recovery").is_none(),
        "smt_recovery should be omitted from JSON when None"
    );
}
