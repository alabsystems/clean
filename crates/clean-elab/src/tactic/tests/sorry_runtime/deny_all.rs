// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Proves a non-trivial theorem entirely sorry-free (#2160 T2).
///
/// This test verifies that at least one non-trivial theorem can be proved
/// without any sorry term generation. It uses the linarith tactic to derive
/// False from contradictory hypotheses (a ≤ 0, 1 ≤ a).
///
/// Under `DENY_SORRY=1`, this test would also pass because no sorry is
/// generated — the proof is fully kernel-verified.
#[test]
#[serial]
fn deny_all_sorry_non_trivial_theorem() {
    reset_sorry_counter();

    // Non-trivial theorem: derive False from a ≤ 0 ∧ 1 ≤ a
    let env = Environment::with_prelude();
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let a_fvar = FVarId::new(900);
    let h1_fvar = FVarId::new(901);
    let h2_fvar = FVarId::new(902);

    let h1_ty = make_nat_le_tc(Expr::fvar(a_fvar), Expr::nat_lit(0));
    let h2_ty = make_nat_le_tc(Expr::nat_lit(1), Expr::fvar(a_fvar));

    let mut state = ProofState::with_context(
        env,
        false_ty,
        vec![
            LocalDecl {
                fvar: a_fvar,
                name: "a".to_string(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: h1_fvar,
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_fvar,
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    let result = linarith(&mut state);
    assert!(
        result.is_ok(),
        "linarith should succeed on contradictory hypotheses"
    );

    let sorry_total = u64::from(state.trust_ledger().sorry_count);
    assert_eq!(
        sorry_total, 0,
        "Non-trivial theorem proof should produce 0 sorry terms, got {sorry_total}"
    );
}
