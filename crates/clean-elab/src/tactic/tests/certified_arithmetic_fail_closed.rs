// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::tactic::core::TacticError;
use serial_test::serial;

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

#[test]
#[serial]
fn test_linarith_certified_unsat_fail_closed_without_trusted_axioms() {
    use crate::tactic::arith_linarith::test_only_certified_unsat_without_kernel_proof;

    reset_all_counters();
    let state = contradictory_nat_le_false_state();
    let axiom_before = axiom_snapshot();
    let result =
        test_only_certified_unsat_without_kernel_proof("test-only rejected certified replay");

    assert!(
        matches!(
            result,
            Err(TacticError::ArithmeticFailed { ref tactic, ref reason })
                if tactic == "linarith"
                    && reason.contains("certified FM found contradiction")
        ),
        "linarith should fail closed on certified-unsat replay failure, got: {result:?}"
    );
    assert_eq!(
        axiom_snapshot(),
        axiom_before,
        "fail-closed linarith must not emit trusted axioms"
    );
    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.trusted_ay_count, 0);
    assert_eq!(ledger.sorry_count, 0);
    assert!(
        !state.is_complete(),
        "fail-closed linarith should leave the goal open"
    );
}

#[test]
#[serial]
fn test_mathverse_certified_arithmetic_fail_closed_without_trusted_axioms() {
    use crate::tactic::omega_tactic::test_only_certified_arithmetic_contradiction_without_kernel_proof;

    reset_all_counters();
    let state = contradictory_nat_le_false_state();
    let axiom_before = axiom_snapshot();
    let result = test_only_certified_arithmetic_contradiction_without_kernel_proof(
        "test-only rejected arithmetic replay",
    );

    assert!(
        matches!(
            result,
            Err(TacticError::ArithmeticFailed { ref tactic, ref reason })
                if tactic == "mathverse"
                    && reason.contains("certified arithmetic contradiction")
        ),
        "mathverse should fail closed on certified arithmetic replay failure, got: {result:?}"
    );
    assert_eq!(
        axiom_snapshot(),
        axiom_before,
        "fail-closed mathverse must not emit trusted axioms"
    );
    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.trusted_ay_count, 0);
    assert_eq!(ledger.sorry_count, 0);
    assert!(
        !state.is_complete(),
        "fail-closed mathverse should leave the goal open"
    );
}
