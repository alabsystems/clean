// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_elab::tactic::{nlinarith_with_config, NlinarithConfig};
use clean_elab::{LocalDecl, ProofState};
use clean_kernel::{Environment, Expr, FVarId, Name};

fn make_nat_le_tc(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("LE.le"),
                        vec![clean_kernel::Level::zero()],
                    ),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLENat"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

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
fn test_nlinarith_with_config_certified_replay_avoids_trusted_arith_integration() {
    let mut state = contradictory_nat_le_false_state();

    let result = nlinarith_with_config(&mut state, NlinarithConfig::default());

    assert!(
        result.is_ok(),
        "nlinarith_with_config should replay the certified FM contradiction, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "goal should be closed after nlinarith_with_config succeeds"
    );

    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "certified nlinarith replay must not increment trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "certified nlinarith replay must produce a real proof term"
    );
}
