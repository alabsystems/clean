// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Zero-valued fractional coefficient regressions for `linear_combination`.

use super::*;
use clean_kernel::env::Declaration;
use pattern::linear_combination;

fn nat_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn int_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn setup_nat_transitivity_goal_with_unused_refl_hyp() -> ProofState {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas()
        .expect("Nat arithmetic lemmas should initialize");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .expect("Nat variable axiom should add");
    }

    ProofState::with_context(
        env,
        make_eq(nat.clone(), nat_var("a"), nat_var("c")),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: make_eq(nat.clone(), nat_var("a"), nat_var("b")),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: make_eq(nat.clone(), nat_var("b"), nat_var("c")),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h3".to_string(),
                ty: make_eq(nat, nat_var("c"), nat_var("c")),
                value: None,
            },
        ],
    )
}

fn setup_int_transitivity_goal_with_unused_refl_hyp() -> ProofState {
    let mut env = Environment::with_prelude();
    env.init_int_euclidean_domain_inst()
        .expect("Int ring lemmas should initialize");

    let int = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int.clone(),
        })
        .expect("Int variable axiom should add");
    }

    ProofState::with_context(
        env,
        make_eq(int.clone(), int_var("a"), int_var("c")),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: make_eq(int.clone(), int_var("a"), int_var("b")),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: make_eq(int.clone(), int_var("b"), int_var("c")),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h3".to_string(),
                ty: make_eq(int, int_var("c"), int_var("c")),
                value: None,
            },
        ],
    )
}

#[test]
fn test_linear_combination_tactic_nat_zero_fractional_coeff_keeps_cancellation_bridge() {
    let mut state = setup_nat_transitivity_goal_with_unused_refl_hyp();

    linear_combination(
        &mut state,
        vec![
            LinearCoeff::one("h1"),
            LinearCoeff::one("h2"),
            LinearCoeff::new("h3", 0, 2),
        ],
    )
    .expect("zero-valued fractional Nat coeff should not block cancellation recovery");

    assert!(
        state.is_complete(),
        "linear_combination should still close the Nat transitivity goal"
    );
    assert!(
        state.proof_term().is_some(),
        "linear_combination should still leave an extractable Nat proof term"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "zero-valued fractional Nat coeff must not force trustedArith"
    );
}

#[test]
fn test_linear_combination_tactic_int_zero_fractional_coeff_keeps_cancellation_bridge() {
    let mut state = setup_int_transitivity_goal_with_unused_refl_hyp();

    linear_combination(
        &mut state,
        vec![
            LinearCoeff::one("h1"),
            LinearCoeff::one("h2"),
            LinearCoeff::new("h3", 0, 2),
        ],
    )
    .expect("zero-valued fractional Int coeff should not block cancellation recovery");

    assert!(
        state.is_complete(),
        "linear_combination should still close the Int transitivity goal"
    );
    assert!(
        state.proof_term().is_some(),
        "linear_combination should still leave an extractable Int proof term"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "zero-valued fractional Int coeff must not force trustedArith"
    );
}
