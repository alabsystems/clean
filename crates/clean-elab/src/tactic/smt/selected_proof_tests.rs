// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#[cfg(feature = "ay-smt")]
use super::bridge_reconstruction::BridgeProbeOutcome;
use super::bridge_reconstruction::BridgeReconstructionCandidate;
#[cfg(feature = "ay-smt")]
use super::selected_proof::{choose_selected_proof, SelectedProofChoice};
use super::selected_proof::{
    choose_verified_proof_preference, SelectedDirectProof, VerifiedProofPreference,
};
use clean_kernel::{Expr, Name};

fn direct_proof_expr() -> Expr {
    Expr::const_(Name::from_string("directProof"), vec![])
}

fn bridge_candidate(trust_subterm_count: usize) -> BridgeReconstructionCandidate {
    BridgeReconstructionCandidate {
        proof: Expr::const_(Name::from_string("bridgeProof"), vec![]),
        trust_subterm_count,
    }
}

#[test]
fn test_choose_verified_proof_preference_keeps_direct_when_bridge_missing() {
    let direct = SelectedDirectProof::new(direct_proof_expr(), 2);
    assert_eq!(
        choose_verified_proof_preference(&direct, None),
        VerifiedProofPreference::Direct,
        "direct partially-verified proofs should be kept when bridge reconstruction fails"
    );
}

#[test]
fn test_choose_verified_proof_preference_prefers_cleaner_bridge_candidate() {
    let direct = SelectedDirectProof::new(direct_proof_expr(), 2);
    assert_eq!(
        choose_verified_proof_preference(&direct, Some(&bridge_candidate(0))),
        VerifiedProofPreference::Bridge,
        "bridge reconstruction should win when it strictly reduces trust debt"
    );
}

#[test]
fn test_choose_verified_proof_preference_keeps_count_only_direct_on_equal_trust_tie() {
    let direct = SelectedDirectProof::new(direct_proof_expr(), 2);
    assert_eq!(
        choose_verified_proof_preference(&direct, Some(&bridge_candidate(2))),
        VerifiedProofPreference::Direct,
        "count-only direct proofs should keep the existing equal-trust direct preference"
    );
    assert_eq!(
        choose_verified_proof_preference(&direct, Some(&bridge_candidate(3))),
        VerifiedProofPreference::Direct,
        "higher-trust bridge proofs should not displace the direct ay proof"
    );
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_choose_selected_proof_keeps_direct_when_bridge_missing() {
    let direct_proof = direct_proof_expr();

    match choose_selected_proof(
        SelectedDirectProof::new(direct_proof.clone(), 1),
        None,
        "test_ay_direct",
    ) {
        SelectedProofChoice::Direct(selected) => {
            let (proof, trust_subterm_count, _residual) = selected.into_parts_with_residual();
            assert_eq!(
                proof, direct_proof,
                "missing bridge candidate should keep the direct proof"
            );
            assert_eq!(
                trust_subterm_count, 1,
                "direct proof trust accounting should be preserved through selection"
            );
        }
        SelectedProofChoice::Bridge(_) => {
            panic!("missing bridge candidate must not select bridge proof");
        }
    }
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_choose_selected_proof_prefers_cleaner_bridge_candidate() {
    let direct_proof = direct_proof_expr();
    let bridge_candidate = bridge_candidate(0);
    let bridge_proof = bridge_candidate.proof.clone();

    match choose_selected_proof(
        SelectedDirectProof::new(direct_proof, 2),
        Some(bridge_candidate),
        "test_ay_bridge",
    ) {
        SelectedProofChoice::Direct(_) => {
            panic!("cleaner bridge candidate should displace the direct proof");
        }
        SelectedProofChoice::Bridge(selected) => {
            assert_eq!(
                selected.proof, bridge_proof,
                "bridge selection should return the original bridge candidate proof"
            );
            assert_eq!(
                selected.trust_subterm_count, 0,
                "bridge selection should preserve the bridge trust accounting"
            );
        }
    }
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_choose_selected_proof_prefers_cleaner_bridge_probe_outcome_candidate() {
    let direct_proof = direct_proof_expr();
    let bridge_candidate = bridge_candidate(0);
    let bridge_proof = bridge_candidate.proof.clone();

    match choose_selected_proof(
        SelectedDirectProof::new(direct_proof, 2),
        BridgeProbeOutcome::Candidate(bridge_candidate),
        "test_ay_bridge",
    ) {
        SelectedProofChoice::Direct(_) => {
            panic!("cleaner bridge probe outcome candidate should displace the direct proof");
        }
        SelectedProofChoice::Bridge(selected) => {
            assert_eq!(
                selected.proof, bridge_proof,
                "bridge probe outcome candidate should preserve the bridge proof"
            );
            assert_eq!(
                selected.trust_subterm_count, 0,
                "bridge probe outcome candidate should preserve trust accounting"
            );
        }
    }
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_choose_selected_proof_keeps_direct_when_bridge_validation_failed_outcome_is_flattened() {
    let direct_proof = direct_proof_expr();

    match choose_selected_proof(
        SelectedDirectProof::new(direct_proof.clone(), 1),
        BridgeProbeOutcome::ValidationFailed,
        "test_ay_direct",
    ) {
        SelectedProofChoice::Direct(selected) => {
            let (proof, trust_subterm_count, _residual) = selected.into_parts_with_residual();
            assert_eq!(
                proof, direct_proof,
                "validation-failed bridge outcome should behave like a missing bridge candidate"
            );
            assert_eq!(
                trust_subterm_count, 1,
                "direct proof trust accounting should stay unchanged after flattening failure"
            );
        }
        SelectedProofChoice::Bridge(_) => {
            panic!("validation-failed bridge outcome must not select a bridge proof");
        }
    }
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_choose_verified_proof_preference_prefers_bridge_on_equal_trust_local_gap_tie() {
    use clean_auto::bridge::ay_contract::test_utils::residual_trust_summary_from_source;
    use clean_auto::bridge::ay_contract::ResidualTrustSource;

    let direct = SelectedDirectProof::with_residual(
        direct_proof_expr(),
        2,
        residual_trust_summary_from_source(ResidualTrustSource::LocalReconstructionGap),
    );

    assert_eq!(
        choose_verified_proof_preference(&direct, Some(&bridge_candidate(2))),
        VerifiedProofPreference::Bridge,
        "equal-trust validated bridge proofs should displace direct proofs with local reconstruction gaps"
    );
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_choose_verified_proof_preference_keeps_direct_on_equal_trust_arithmetic_boundary_tie() {
    use clean_auto::bridge::ay_contract::test_utils::residual_trust_summary_from_source;
    use clean_auto::bridge::ay_contract::ResidualTrustSource;

    let direct = SelectedDirectProof::with_residual(
        direct_proof_expr(),
        2,
        residual_trust_summary_from_source(ResidualTrustSource::ArithmeticBoundary),
    );

    assert_eq!(
        choose_verified_proof_preference(&direct, Some(&bridge_candidate(2))),
        VerifiedProofPreference::Direct,
        "arithmetic-boundary ties should stay on the direct proof in this bounded slice"
    );
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_choose_selected_proof_keeps_count_only_direct_on_equal_trust_tie() {
    let direct_proof = direct_proof_expr();

    match choose_selected_proof(
        SelectedDirectProof::new(direct_proof.clone(), 2),
        Some(bridge_candidate(2)),
        "test_ay_direct",
    ) {
        SelectedProofChoice::Direct(selected) => {
            let (proof, trust_subterm_count, _residual) = selected.into_parts_with_residual();
            assert_eq!(
                proof, direct_proof,
                "equal-trust bridge candidate should not displace the direct proof"
            );
            assert_eq!(
                trust_subterm_count, 2,
                "direct proof trust accounting should remain unchanged on equal-trust tie"
            );
        }
        SelectedProofChoice::Bridge(_) => {
            panic!("count-only equal-trust bridge candidate must not displace the direct proof");
        }
    }
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_choose_selected_proof_prefers_bridge_on_equal_trust_local_gap_tie() {
    use clean_auto::bridge::ay_contract::test_utils::residual_trust_summary_from_source;
    use clean_auto::bridge::ay_contract::ResidualTrustSource;

    let bridge_candidate = bridge_candidate(2);
    let bridge_proof = bridge_candidate.proof.clone();
    let direct = SelectedDirectProof::with_residual(
        direct_proof_expr(),
        2,
        residual_trust_summary_from_source(ResidualTrustSource::LocalReconstructionGap),
    );

    match choose_selected_proof(direct, Some(bridge_candidate), "test_ay_bridge") {
        SelectedProofChoice::Direct(_) => {
            panic!("equal-trust local-gap direct proof should yield to the validated bridge proof");
        }
        SelectedProofChoice::Bridge(selected) => {
            assert_eq!(
                selected.proof, bridge_proof,
                "local-gap tie-break should return the bridge candidate proof"
            );
            assert_eq!(
                selected.trust_subterm_count, 2,
                "bridge trust accounting should be preserved on equal-trust local-gap ties"
            );
        }
    }
}

/// `with_residual` preserves the typed summary through selection. Part of #2618.
#[cfg(feature = "ay-smt")]
#[test]
fn test_selected_direct_proof_with_residual_preserves_summary() {
    use clean_auto::bridge::ay_contract::test_utils::residual_trust_summary_from_source;
    use clean_auto::bridge::ay_contract::ResidualTrustSource;

    let proof = direct_proof_expr();
    let residual = residual_trust_summary_from_source(ResidualTrustSource::AletheTrustStep);
    let selected = SelectedDirectProof::with_residual(proof.clone(), 1, residual);
    let (returned_proof, trust_count, returned_residual) = selected.into_parts_with_residual();
    assert_eq!(returned_proof, proof);
    assert_eq!(trust_count, 1);
    assert_eq!(
        returned_residual,
        Some(residual),
        "into_parts_with_residual should return the exact residual from construction"
    );
}

/// Count-only constructor yields `None` residual. Part of #2618.
#[cfg(feature = "ay-smt")]
#[test]
fn test_selected_direct_proof_new_has_no_residual() {
    let proof = direct_proof_expr();
    let selected = SelectedDirectProof::new(proof, 0);
    let (_proof, _count, residual) = selected.into_parts_with_residual();
    assert_eq!(
        residual, None,
        "count-only proofs should carry None residual through into_parts_with_residual"
    );
}

/// Selection preserves residual through `choose_selected_proof` when the
/// direct proof wins. Part of #2618.
#[cfg(feature = "ay-smt")]
#[test]
fn test_choose_selected_proof_preserves_residual_on_direct_win() {
    use clean_auto::bridge::ay_contract::test_utils::residual_trust_summary_from_source;
    use clean_auto::bridge::ay_contract::ResidualTrustSource;

    let proof = direct_proof_expr();
    let residual = residual_trust_summary_from_source(ResidualTrustSource::ArithmeticBoundary);
    let direct = SelectedDirectProof::with_residual(proof.clone(), 1, residual);

    match choose_selected_proof(direct, None, "test_ay_direct") {
        SelectedProofChoice::Direct(selected) => {
            let (_p, _count, returned_residual) = selected.into_parts_with_residual();
            assert_eq!(
                returned_residual,
                Some(residual),
                "direct proof selection should preserve the typed residual metadata"
            );
        }
        SelectedProofChoice::Bridge(_) => {
            panic!("missing bridge candidate must not select bridge proof");
        }
    }
}
