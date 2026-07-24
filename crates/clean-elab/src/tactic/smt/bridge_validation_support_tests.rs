// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::bridge_validation::{init_bridge_validation_support, prepare_smt_proof_validation};
use super::decide::validate_proof_term;
use crate::tactic::ProofState;
use clean_kernel::{Environment, Expr, Level, Name};

fn real_type() -> Expr {
    Expr::const_(Name::from_string("Real"), vec![])
}

fn real_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn real_le(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    real_type(),
                ),
                Expr::const_(Name::from_string("instLEReal"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

#[test]
fn test_bridge_validation_support_bootstraps_minimal_env() {
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::prop());

    init_bridge_validation_support(&mut state);

    assert!(
        state
            .env()
            .get_const(&Name::from_string("Nat.le_trans"))
            .is_some(),
        "minimal env should gain Nat.le_trans after bridge validation bootstrap"
    );
    assert!(
        state
            .env()
            .get_const(&Name::from_string("Nat.lt_of_lt_of_le"))
            .is_some(),
        "minimal env should gain Nat.lt_of_lt_of_le after bridge validation bootstrap"
    );
    assert!(
        state
            .env()
            .get_const(&Name::from_string("Int.le_trans"))
            .is_some(),
        "minimal env should gain Int.le_trans after bridge validation bootstrap"
    );
    assert!(
        state
            .env()
            .get_const(&Name::from_string("Real.le_trans"))
            .is_some(),
        "minimal env should gain Real.le_trans after bridge validation bootstrap (QF_LRA support, #2955)"
    );
    assert!(
        state
            .env()
            .get_const(&Name::from_string("instLEReal"))
            .is_some(),
        "minimal env should gain instLEReal after bridge validation bootstrap (QF_LRA support, #2955)"
    );
    assert!(
        state
            .env()
            .get_const(&Name::from_string("instLinearOrderReal"))
            .is_some(),
        "minimal env should gain instLinearOrderReal after bridge validation bootstrap (QF_LRA support, #2955)"
    );
}

/// Verify that the shared bootstrap does more than load symbols: it must make a
/// minimal environment capable of kernel-validating a Real proof term without
/// manual per-test preloading.
#[test]
fn test_prepare_smt_proof_validation_validates_real_proof_for_qf_lra() {
    let zero = real_of_nat(0);
    let goal_ty = real_le(zero.clone(), zero.clone());
    let env = Environment::new();
    let mut state = ProofState::new(env, goal_ty.clone());

    prepare_smt_proof_validation(&mut state, "test_qf_lra_bootstrap")
        .expect("shared bootstrap should prepare minimal env for Real proof validation");

    let goal = state.current_goal().expect("should have a goal").clone();
    let proof = Expr::app(
        Expr::const_(Name::from_string("Real.le_refl"), vec![]),
        zero,
    );

    let result = validate_proof_term(&state, &goal, &proof, &goal_ty);
    assert!(
        result.is_ok(),
        "shared bootstrap must let minimal env kernel-validate a Real proof for strict QF_LRA support (#2955), got {result:?}"
    );
}

#[test]
fn test_bridge_validation_support_is_idempotent() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_le().unwrap();
    env.init_lt().unwrap();

    let mut state = ProofState::new(env, Expr::prop());
    init_bridge_validation_support(&mut state);
    init_bridge_validation_support(&mut state);

    assert!(
        state
            .env()
            .get_const(&Name::from_string("Nat.le_trans"))
            .is_some(),
        "Nat.le_trans should remain available after repeated initialization"
    );
    assert!(
        state
            .env()
            .get_const(&Name::from_string("Real.le_trans"))
            .is_some(),
        "Real.le_trans should remain available after repeated initialization (#2955)"
    );
}
