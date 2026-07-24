// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Multi-hypothesis polyrith proof-carry regressions (#2526).
//!
//! Covers the shared `linear_combination` proof builder and the end-to-end
//! `polyrith` tactic path for weighted two-hypothesis Nat certificates.

use super::*;
use clean_kernel::env::Declaration;

fn nat_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), lhs),
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

fn int_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn int_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.add"), vec![]), lhs),
        rhs,
    )
}

fn setup_two_hyp_nat_state(goal_lhs: Expr, goal_rhs: Expr) -> ProofState {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas()
        .expect("Nat arithmetic lemmas should initialize");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["a", "b", "c", "d"] {
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
                ty: make_eq(nat.clone(), nat_var("a"), nat_var("b")),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: make_eq(nat, nat_var("c"), nat_var("d")),
                value: None,
            },
        ],
    )
}

fn setup_two_hyp_int_state(goal_lhs: Expr, goal_rhs: Expr) -> ProofState {
    let mut env = Environment::with_prelude();
    env.init_int_euclidean_domain_inst()
        .expect("Int ring lemmas should initialize");

    let int = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["a", "b", "c", "d"] {
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
                ty: make_eq(int.clone(), int_var("a"), int_var("b")),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: make_eq(int, int_var("c"), int_var("d")),
                value: None,
            },
        ],
    )
}

fn setup_three_hyp_nat_state(goal_lhs: Expr, goal_rhs: Expr) -> ProofState {
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
                ty: make_eq(nat.clone(), nat_var("a"), nat_var("b")),
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
fn test_polyrith_two_hyp_cert_pipeline_commuted_goal_e2e() {
    use super::super::polynomial::Polynomial;

    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(1, 1)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
        ],
        verified: true,
        explanation: "two-hyp commuted goal".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(coeffs.len(), 2, "cert should yield two coefficients");

    let mut state = setup_two_hyp_nat_state(
        nat_add(nat_var("c"), nat_var("a")),
        nat_add(nat_var("d"), nat_var("b")),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("two-hypothesis cert should reconstruct a proof for the commuted goal");

    state
        .close_goal(&goal, proof)
        .expect("two-hypothesis cert proof should close the goal");
    assert_closed_clean_proof(&state, "two-hypothesis polyrith proof-carry");
}

#[test]
fn test_polyrith_two_hyp_scaled_cert_pipeline_commuted_goal_e2e() {
    use super::super::polynomial::Polynomial;

    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(2, 1)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
        ],
        verified: true,
        explanation: "two-hyp weighted commuted goal".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(coeffs.len(), 2, "cert should yield two coefficients");
    assert_eq!(coeffs[0].coeff, (2, 1), "h1 should carry coefficient 2");
    assert_eq!(coeffs[1].coeff, (1, 1), "h2 should carry coefficient 1");

    let mut state = setup_two_hyp_nat_state(
        nat_add(nat_var("c"), nat_mul(2, nat_var("a"))),
        nat_add(nat_var("d"), nat_mul(2, nat_var("b"))),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("weighted two-hypothesis cert should reconstruct a proof for the commuted goal");

    state
        .close_goal(&goal, proof)
        .expect("weighted two-hypothesis cert proof should close the goal");
    assert_closed_clean_proof(&state, "weighted two-hypothesis polyrith proof-carry");
}

#[test]
fn test_polyrith_tactic_two_hyp_scaled_goal_closes_without_trust() {
    let mut state = setup_two_hyp_nat_state(
        nat_add(nat_var("c"), nat_mul(2, nat_var("a"))),
        nat_add(nat_var("d"), nat_mul(2, nat_var("b"))),
    );

    polyrith(&mut state)
        .expect("polyrith should find and reconstruct the weighted two-hypothesis certificate");

    assert_closed_clean_proof(
        &state,
        "weighted two-hypothesis polyrith tactic proof-carry",
    );
}

#[test]
fn test_polyrith_two_hyp_int_cert_pipeline_commuted_goal_e2e() {
    use super::super::polynomial::Polynomial;

    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(1, 1)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
        ],
        verified: true,
        explanation: "two-hyp Int commuted goal".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(coeffs.len(), 2, "cert should yield two coefficients");

    let mut state = setup_two_hyp_int_state(
        int_add(int_var("c"), int_var("a")),
        int_add(int_var("d"), int_var("b")),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("two-hypothesis Int cert should reconstruct a proof for the commuted goal");

    state
        .close_goal(&goal, proof)
        .expect("two-hypothesis Int cert proof should close the goal");
    assert_closed_clean_proof(&state, "two-hypothesis Int polyrith proof-carry");
}

#[test]
fn test_polyrith_tactic_two_hyp_int_commuted_goal_closes_without_trust() {
    let mut state = setup_two_hyp_int_state(
        int_add(int_var("c"), int_var("a")),
        int_add(int_var("d"), int_var("b")),
    );

    polyrith(&mut state)
        .expect("polyrith should find and reconstruct the Int commuted two-hypothesis certificate");

    assert_closed_clean_proof(&state, "two-hypothesis Int polyrith tactic proof-carry");
}

#[test]
fn test_linear_combination_tactic_two_hyp_int_mixed_sign_goal_closes_without_trust() {
    let mut state = setup_two_hyp_int_state(
        int_add(int_var("c"), int_var("b")),
        int_add(int_var("d"), int_var("a")),
    );

    linear_combination(
        &mut state,
        vec![LinearCoeff::int("h1", -1), LinearCoeff::one("h2")],
    )
    .expect("linear_combination should close the mixed-sign Int goal");

    assert_closed_clean_proof(&state, "mixed-sign Int linear_combination proof-carry");
}

#[test]
fn test_polyrith_three_hyp_weighted_cert_pipeline_commuted_goal_e2e() {
    use super::super::polynomial::Polynomial;

    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(2, 1)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
            ("h3".to_string(), Polynomial::constant(-1, 1)),
        ],
        verified: true,
        explanation: "three-hyp weighted commuted goal".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(coeffs.len(), 3, "cert should yield three coefficients");
    assert_eq!(coeffs[0].coeff, (2, 1), "h1 should carry coefficient 2");
    assert_eq!(coeffs[1].coeff, (1, 1), "h2 should carry coefficient 1");
    assert_eq!(coeffs[2].coeff, (-1, 1), "h3 should carry coefficient -1");

    let mut state = setup_three_hyp_nat_state(
        nat_add(
            nat_var("f"),
            nat_add(nat_var("c"), nat_mul(2, nat_var("a"))),
        ),
        nat_add(
            nat_var("e"),
            nat_add(nat_mul(2, nat_var("b")), nat_var("d")),
        ),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("weighted three-hypothesis cert should reconstruct a proof for the commuted goal");

    state
        .close_goal(&goal, proof)
        .expect("weighted three-hypothesis cert proof should close the goal");
    assert_closed_clean_proof(&state, "weighted three-hypothesis polyrith proof-carry");
}

#[test]
fn test_linear_combination_tactic_three_hyp_weighted_goal_closes_without_trust() {
    let mut state = setup_three_hyp_nat_state(
        nat_add(
            nat_var("f"),
            nat_add(nat_var("c"), nat_mul(2, nat_var("a"))),
        ),
        nat_add(
            nat_var("e"),
            nat_add(nat_mul(2, nat_var("b")), nat_var("d")),
        ),
    );

    linear_combination(
        &mut state,
        vec![
            LinearCoeff::new("h1", 2, 1),
            LinearCoeff::one("h2"),
            LinearCoeff::int("h3", -1),
        ],
    )
    .expect("linear_combination should close the weighted three-hypothesis goal");

    assert_closed_clean_proof(
        &state,
        "weighted three-hypothesis linear_combination tactic proof-carry",
    );
}
