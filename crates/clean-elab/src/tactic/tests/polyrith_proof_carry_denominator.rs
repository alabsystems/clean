// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat/Int constant-rational denominator-bridge regressions (#2590).

use super::*;
use clean_kernel::env::Declaration;

fn nat_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn int_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), lhs),
        rhs,
    )
}

fn int_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.add"), vec![]), lhs),
        rhs,
    )
}

fn nat_mul(coeff: u64, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            Expr::nat_lit(coeff),
        ),
        rhs,
    )
}

fn int_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn int_mul(coeff: u64, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat(coeff),
        ),
        rhs,
    )
}

fn setup_three_hyp_nat_denominator_bridge_state(goal_lhs: Expr, goal_rhs: Expr) -> ProofState {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas()
        .expect("Nat arithmetic lemmas should initialize");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["a", "b", "c", "d", "e", "f"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .expect("Nat variable axiom should add");
    }

    ProofState::with_context(
        env,
        make_eq(nat.clone(), goal_lhs, goal_rhs),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: make_eq(
                    nat.clone(),
                    nat_mul(2, nat_var("a")),
                    nat_mul(2, nat_var("b")),
                ),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: make_eq(nat.clone(), nat_var("c"), nat_var("d")),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h3".to_string(),
                ty: make_eq(nat, nat_var("e"), nat_var("f")),
                value: None,
            },
        ],
    )
}

fn setup_three_hyp_int_denominator_bridge_state(goal_lhs: Expr, goal_rhs: Expr) -> ProofState {
    let mut env = Environment::with_prelude();
    env.init_int_euclidean_domain_inst()
        .expect("Int ring lemmas should initialize");

    let int = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["a", "b", "c", "d", "e", "f"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int.clone(),
        })
        .expect("Int variable axiom should add");
    }

    ProofState::with_context(
        env,
        make_eq(int.clone(), goal_lhs, goal_rhs),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: make_eq(
                    int.clone(),
                    int_mul(2, int_var("a")),
                    int_mul(2, int_var("b")),
                ),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: make_eq(int.clone(), int_var("c"), int_var("d")),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h3".to_string(),
                ty: make_eq(int, int_var("e"), int_var("f")),
                value: None,
            },
        ],
    )
}

fn linear_coeffs_from_cert(cert: &PolyrithCertificate) -> Vec<LinearCoeff> {
    let mut coeffs = Vec::new();
    for (name, poly) in &cert.coefficients {
        if let Some((num, den)) = poly.as_constant_coeff() {
            if num != 0 {
                coeffs.push(LinearCoeff::new(name, num, den));
            }
        }
    }
    coeffs
}

fn assert_closed_clean_proof(state: &ProofState, context: &str) {
    assert!(state.is_complete(), "{context}: state should be complete");
    assert!(
        state.proof_term().is_some(),
        "{context}: proof_term() should be extractable"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "{context}: trustedArith should stay at 0"
    );
    assert_eq!(ledger.sorry_count, 0, "{context}: sorry should stay at 0");
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "{context}: trustedAy should stay at 0"
    );
}

#[test]
fn test_polyrith_three_hyp_rational_coeff_nat_cert_pipeline_clears_denominators_e2e() {
    use super::super::polynomial::Polynomial;

    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(1, 2)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
            ("h3".to_string(), Polynomial::constant(-1, 1)),
        ],
        verified: true,
        explanation: "three-hyp Nat denominator bridge".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(
        coeffs.len(),
        3,
        "cert should still translate all constant coeffs"
    );

    let mut state = setup_three_hyp_nat_denominator_bridge_state(
        nat_add(nat_var("f"), nat_add(nat_var("c"), nat_var("a"))),
        nat_add(nat_var("e"), nat_add(nat_var("b"), nat_var("d"))),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("Nat rational three-hypothesis cert should reconstruct via denominator clearing");

    state
        .close_goal(&goal, proof)
        .expect("Nat rational three-hypothesis cert proof should close the goal");
    assert_closed_clean_proof(&state, "Nat rational three-hypothesis polyrith proof-carry");
}

#[test]
fn test_linear_combination_tactic_three_hyp_rational_nat_goal_closes_without_trust() {
    let mut state = setup_three_hyp_nat_denominator_bridge_state(
        nat_add(nat_var("f"), nat_add(nat_var("c"), nat_var("a"))),
        nat_add(nat_var("e"), nat_add(nat_var("b"), nat_var("d"))),
    );

    linear_combination(
        &mut state,
        vec![
            LinearCoeff::new("h1", 1, 2),
            LinearCoeff::one("h2"),
            LinearCoeff::int("h3", -1),
        ],
    )
    .expect("linear_combination should close the Nat rational three-hypothesis goal");

    assert_closed_clean_proof(
        &state,
        "Nat rational three-hypothesis linear_combination proof-carry",
    );
}

#[test]
fn test_polyrith_three_hyp_rational_coeff_int_cert_pipeline_clears_denominators_e2e() {
    use super::super::polynomial::Polynomial;

    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(1, 2)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
            ("h3".to_string(), Polynomial::constant(-1, 1)),
        ],
        verified: true,
        explanation: "three-hyp Int denominator bridge".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(
        coeffs.len(),
        3,
        "cert should still translate all constant coeffs"
    );

    let mut state = setup_three_hyp_int_denominator_bridge_state(
        int_add(int_var("f"), int_add(int_var("c"), int_var("a"))),
        int_add(int_var("e"), int_add(int_var("b"), int_var("d"))),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("Int rational three-hypothesis cert should reconstruct via denominator clearing");

    state
        .close_goal(&goal, proof)
        .expect("Int rational three-hypothesis cert proof should close the goal");
    assert_closed_clean_proof(&state, "Int rational three-hypothesis polyrith proof-carry");
}

#[test]
fn test_linear_combination_tactic_three_hyp_rational_int_goal_closes_without_trust() {
    let mut state = setup_three_hyp_int_denominator_bridge_state(
        int_add(int_var("f"), int_add(int_var("c"), int_var("a"))),
        int_add(int_var("e"), int_add(int_var("b"), int_var("d"))),
    );

    linear_combination(
        &mut state,
        vec![
            LinearCoeff::new("h1", 1, 2),
            LinearCoeff::one("h2"),
            LinearCoeff::int("h3", -1),
        ],
    )
    .expect("linear_combination should close the Int rational three-hypothesis goal");

    assert_closed_clean_proof(
        &state,
        "Int rational three-hypothesis linear_combination proof-carry",
    );
}
