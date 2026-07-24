// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for mathverse proof reconstruction.
//!
//! Part of #2531: the mathverse path (both certified and uncertified) should
//! close reconstructible goals without falling back to `trustedArith`.

use super::*;
use crate::tactic::arith_linarith::LinarithCertificate;
use crate::tactic::arith_mathverse_proof::build_mathverse_proof;
use crate::tactic::omega_tactic::{MathverseCertificate, MathverseContradictionType};
use serial_test::serial;

/// State with h : 5 ≤ 3 (contradictory) and goal False.
/// Mathverse should find Unsat via certified FM and reconstruct a kernel proof.
fn contradictory_nat_le_false_state() -> ProofState {
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let h_id = FVarId::new(0);
    let h_ty = make_nat_le_tc(Expr::nat_lit(5), Expr::nat_lit(3));
    ProofState::with_context(
        Environment::with_prelude(),
        false_ty,
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    )
}

fn large_nat_mathverse_replay_fixture() -> (ProofState, FVarId, MathverseCertificate) {
    const LARGE: u64 = 4_000_000_000;
    let large_i128 = i128::from(LARGE);

    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let h_id = FVarId::new(0);
    let h_ty = make_nat_le_tc(Expr::nat_lit(1), Expr::nat_lit(0));

    let state = ProofState::with_context(
        Environment::with_prelude(),
        false_ty,
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );

    let linarith_cert = LinarithCertificate {
        coefficients: vec![large_i128],
        result_constant: large_i128,
    };
    let mathverse_cert = MathverseCertificate {
        contradiction_type: MathverseContradictionType::LinearCombination,
        ..MathverseCertificate::from_linarith(&linarith_cert)
    };

    (state, h_id, mathverse_cert)
}

#[test]
#[serial]
fn test_mathverse_avoids_trusted_arith_on_contradictory_nat_le() {
    reset_all_counters();
    let mut state = contradictory_nat_le_false_state();

    let axiom_before = axiom_snapshot();
    let result = omega(&mut state);

    assert!(
        result.is_ok(),
        "mathverse should close a contradictory Nat inequality, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "goal should be closed after mathverse succeeds"
    );
    assert_no_trusted_axiom_usage(
        "mathverse",
        "contradictory Nat inequality (5 ≤ 3 ⊢ False)",
        axiom_before,
    );

    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "mathverse proof reconstruction must not increment trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "mathverse proof reconstruction must produce a real proof term"
    );
}

#[test]
#[serial]
fn test_mathverse_large_nat_coefficients_avoid_trusted_arith() {
    reset_all_counters();
    let (mut state, h_id, mathverse_cert) = large_nat_mathverse_replay_fixture();
    let goal = state.current_goal().expect("should have a goal").clone();
    let env = state.env().clone();
    let axiom_before = axiom_snapshot();
    let proof = build_mathverse_proof(&state, &goal, &mathverse_cert, &[h_id], &env)
        .expect("build_mathverse_proof should replay the widened Nat FM contradiction");
    state
        .close_goal(&goal, proof)
        .expect("close_goal should accept the widened mathverse contradiction proof");

    assert!(
        state.is_complete(),
        "goal should be closed after widened mathverse proof replay"
    );
    assert_no_trusted_axiom_usage(
        "mathverse",
        "large-coefficient Nat mathverse proof replay (4000000000 ≤ 4000000000*x, 4000000000*x ≤ 0 ⊢ False)",
        axiom_before,
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "widened mathverse proof replay must not increment trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "widened mathverse proof replay must produce a real proof term"
    );
}
