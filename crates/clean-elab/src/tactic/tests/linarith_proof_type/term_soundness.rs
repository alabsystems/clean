// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-term and `close_goal` soundness regressions for linarith.

use super::*;
use crate::tactic::core::TacticError;
use serial_test::serial;

fn nat_false_contradiction_state(env: Environment) -> (ProofState, FVarId) {
    let h_id = FVarId::new(0);
    let state = ProofState::with_context(
        env,
        Expr::const_(Name::from_string("False"), vec![]),
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(2)),
            value: None,
        }],
    );
    (state, h_id)
}

/// AC2 (#2133): build_linarith_proof returns proof of type False (via False.elim)
/// for contradictory hypotheses with concrete Nat bounds.
///
/// Given h : 3 ≤ 2 (contradictory), build_linarith_proof must produce a proof
/// whose type matches the goal (False), not a proof of type `3 ≤ 2`.
///
/// Part of #2133.
#[test]
fn test_linarith_proof_term_type_soundness() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let (state, h_id) = nat_false_contradiction_state(Environment::with_prelude());
    let goal = state.current_goal().expect("should have a goal");
    let certificate = LinarithCertificate {
        coefficients: vec![1, 0],
        result_constant: 1,
    };
    let proof = build_linarith_proof(&state, goal, &certificate, &[h_id]);
    assert!(
        proof.is_some(),
        "build_linarith_proof must return Some for contradictory 3 ≤ 2"
    );
    let proof = proof.unwrap();
    assert_ne!(
        proof,
        Expr::fvar(h_id),
        "proof must not be the raw hypothesis (would have type 3 ≤ 2, not False)"
    );
}

/// Verify that close_goal accepts linarith proof terms after WHNF
/// normalization reduces @LE.le Nat instLENat through the typeclass chain.
///
/// Previously this test asserted failure (LE.le vs Nat.le mismatch), but
/// the fix in #2150 adds WHNF normalization of the inferred type before
/// the is_def_eq check, allowing the multi-step reduction chain
/// LE.le → instLENat → Nat.le to complete.
///
/// Part of #2150. Supersedes the original #2133 mismatch test.
#[test]
fn test_linarith_proof_passes_typecheck_with_whnf_normalization() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let env = Environment::with_prelude();
    let (state, h_id) = nat_false_contradiction_state(env.clone());
    let goal = state.current_goal().expect("should have a goal");
    let certificate = LinarithCertificate {
        coefficients: vec![1, 0],
        result_constant: 1,
    };
    let proof = build_linarith_proof(&state, goal, &certificate, &[h_id])
        .expect("should produce a proof term");

    let (mut check_state, _) = nat_false_contradiction_state(env);
    let check_goal = check_state.current_goal().unwrap().clone();
    let result = check_state.close_goal(&check_goal, proof);
    assert!(
        result.is_ok(),
        "close_goal should accept linarith proof after WHNF normalization \
         reduces @LE.le Nat instLENat to Nat.le, got: {result:?}"
    );
    assert!(
        check_state.is_complete(),
        "goal should be closed after close_goal accepts the proof"
    );
}

/// AC3 (#2150): linarith end-to-end uses proof reconstruction, not trustedArith.
///
/// Before #2150, close_goal (then named close_goal_checked) rejected ALL
/// arithmetic proof terms because is_def_eq failed on @LE.le Nat instLENat
/// vs Nat.le. Every linarith call fell through to the trustedArith fallback.
/// With the WHNF normalization fix in close_goal and the (None,None)
/// projection reduction fix in lazy delta,
/// proof reconstruction now succeeds and trustedArith is not invoked.
///
/// This test calls the full `linarith()` entry point (not individual components)
/// and verifies trustedArith counter stays at 0.
///
/// Part of #2150.
#[test]
#[serial]
fn test_linarith_end_to_end_no_trusted_arith_fallback() {
    let (mut state, _) = nat_false_contradiction_state(Environment::with_prelude());

    reset_arith_counter();
    reset_sorry_counter();

    let result = linarith(&mut state);
    assert!(
        result.is_ok(),
        "linarith should close False from contradictory h : 3 ≤ 2, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "goal should be closed after linarith succeeds"
    );
    assert_eq!(
        arith_proof_count(),
        0,
        "trustedArith should NOT be used — proof reconstruction via close_goal \
         should handle the LE.le → Nat.le reduction chain without fallback"
    );
    assert_eq!(
        sorry_count(),
        0,
        "sorry should NOT be used — proof reconstruction should produce a real proof term"
    );
}

/// Part of #2130: close_goal rejects ill-typed arithmetic proofs.
///
/// Given a goal of type `False`, attempting to close it with a proof of type
/// `3 ≤ 2` (an inequality, not False) must fail with TypeCheckFailed or
/// TypeMismatch. This ensures broken proof reconstruction falls through
/// to trustedArith instead of silently succeeding.
#[test]
fn test_close_goal_rejects_ill_typed_proof() {
    let (mut state, h_id) = nat_false_contradiction_state(Environment::with_prelude());

    let goal = state.current_goal().unwrap().clone();
    let ill_typed_proof = Expr::fvar(h_id);
    let result = state.close_goal(&goal, ill_typed_proof);
    assert!(
        matches!(
            result,
            Err(TacticError::TypeCheckFailed(_)) | Err(TacticError::TypeMismatch { .. })
        ),
        "close_goal must reject proof of type 3 ≤ 2 for False goal, got: {result:?}"
    );
    assert!(
        !state.is_complete(),
        "goal must remain open after close_goal rejects ill-typed proof"
    );
}

/// AC3 (#2133): mathverse delegation to linarith produces correct False proofs.
///
/// When mathverse encounters an Arithmetic or LinearCombination contradiction,
/// it delegates to build_linarith_proof via build_mathverse_proof. The delegated
/// proof must be a False derivation (wrapped in False.elim), not the raw
/// hypothesis whose type is an inequality.
#[test]
fn test_mathverse_delegation_produces_false_proof() {
    use crate::tactic::arith_mathverse_proof::build_mathverse_proof;
    use crate::tactic::omega_tactic::{MathverseCertificate, MathverseContradictionType};

    let env = Environment::with_prelude();
    let (state, h_id) = nat_false_contradiction_state(env.clone());
    let goal = state.current_goal().expect("should have a goal");

    let arith_cert = MathverseCertificate {
        coefficients: vec![1],
        uses_goal_negation: false,
        contradiction_type: MathverseContradictionType::Arithmetic,
    };
    let arith_proof = build_mathverse_proof(&state, goal, &arith_cert, &[h_id], &env);
    assert!(
        arith_proof.is_some(),
        "build_mathverse_proof (Arithmetic) must return Some for contradictory 3 ≤ 2"
    );
    assert_ne!(
        arith_proof.unwrap(),
        Expr::fvar(h_id),
        "Arithmetic-delegated proof must not be the raw hypothesis (type 3 ≤ 2, not False)"
    );

    let lc_cert = MathverseCertificate {
        coefficients: vec![1],
        uses_goal_negation: false,
        contradiction_type: MathverseContradictionType::LinearCombination,
    };
    let lc_proof = build_mathverse_proof(&state, goal, &lc_cert, &[h_id], &env);
    assert!(
        lc_proof.is_some(),
        "build_mathverse_proof (LinearCombination) must return Some for contradictory 3 ≤ 2"
    );
    assert_ne!(
        lc_proof.unwrap(),
        Expr::fvar(h_id),
        "LinearCombination-delegated proof must not be the raw hypothesis"
    );
}

/// Part of #2130: close_goal accepts well-typed proofs.
///
/// When the proof term's type matches the goal, close_goal
/// should succeed and close the goal.
#[test]
fn test_close_goal_accepts_well_typed_proof() {
    let env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let h_id = FVarId::new(0);
    let mut state = ProofState::with_context(
        env,
        nat.clone(),
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: nat,
            value: None,
        }],
    );

    let goal = state.current_goal().unwrap().clone();
    let proof = Expr::fvar(h_id);
    let result = state.close_goal(&goal, proof);
    assert!(
        result.is_ok(),
        "close_goal should accept proof whose type matches goal, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "goal should be closed after close_goal succeeds"
    );
}
