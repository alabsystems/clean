// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for certified mathverse modular proof carry.

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

// setup_env_with_parity_bridge() is the shared helper from tests/mod.rs

fn setup_env_with_divisibility_bridge() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_true_false().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Dvd.dvd"),
        level_params: vec![],
        type_: Expr::arrow(nat.clone(), Expr::arrow(nat, Expr::prop())),
    })
    .unwrap();

    env
}

#[test]
#[serial]
fn test_mathverse_parity_theorem_bridge_avoids_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_parity_bridge();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let n_fvar = FVarId::new(0);

    let mut state = ProofState::with_context(
        env,
        Expr::const_(Name::from_string("False"), vec![]),
        vec![
            LocalDecl {
                fvar: n_fvar,
                name: "n".into(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h_even".into(),
                ty: Expr::app(
                    Expr::const_(Name::from_string("Even"), vec![]),
                    Expr::fvar(n_fvar),
                ),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h_odd".into(),
                ty: Expr::app(
                    Expr::const_(Name::from_string("Odd"), vec![]),
                    Expr::fvar(n_fvar),
                ),
                value: None,
            },
        ],
    );

    let axiom_before = axiom_snapshot();
    let result = omega(&mut state);

    assert!(
        result.is_ok(),
        "mathverse should close theorem-backed Even/Odd contradiction, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "goal should be closed after mathverse succeeds"
    );
    assert_no_trusted_axiom_usage(
        "mathverse",
        "Even/Odd contradiction with explicit Nat.even_and_odd_elim bridge",
        axiom_before,
    );

    let ledger = state.trust_ledger();
    assert_eq!(ledger.sorry_count, 0);
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.trusted_ay_count, 0);
}

#[test]
#[serial]
fn test_mathverse_divisibility_negation_avoids_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_divisibility_bridge();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let n_fvar = FVarId::new(0);
    let dvd_three_n = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Dvd.dvd"), vec![]),
            Expr::nat_lit(3),
        ),
        Expr::fvar(n_fvar),
    );

    let mut state = ProofState::with_context(
        env,
        Expr::const_(Name::from_string("False"), vec![]),
        vec![
            LocalDecl {
                fvar: n_fvar,
                name: "n".into(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h_divides".into(),
                ty: dvd_three_n.clone(),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h_not_divides".into(),
                ty: Expr::app(Expr::const_(Name::from_string("Not"), vec![]), dvd_three_n),
                value: None,
            },
        ],
    );

    let axiom_before = axiom_snapshot();
    let result = omega(&mut state);

    assert!(
        result.is_ok(),
        "mathverse should close direct divisibility contradiction, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "goal should be closed after mathverse succeeds"
    );
    assert_no_trusted_axiom_usage("mathverse", "Dvd.dvd / Not contradiction", axiom_before);

    let ledger = state.trust_ledger();
    assert_eq!(ledger.sorry_count, 0);
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.trusted_ay_count, 0);
}
