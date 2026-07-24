// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Weighted Int polyrith proof-carry regressions (#2526).

use super::*;
use clean_kernel::env::Declaration;

fn int_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn int_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.add"), vec![]), lhs),
        rhs,
    )
}

fn int_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn int_neg_succ(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(n),
    )
}

fn int_mul_expr(coeff: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.mul"), vec![]), coeff),
        rhs,
    )
}

fn int_mul(coeff: u64, rhs: Expr) -> Expr {
    int_mul_expr(int_of_nat(coeff), rhs)
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
fn test_weighted_int_goal_is_polynomial_expr() {
    let expr = int_add(int_var("c"), int_mul(2, int_var("a")));
    assert!(
        is_polynomial_expr(&expr),
        "Int.ofNat-backed weighted terms should parse as polynomials"
    );
}

#[test]
fn test_negative_weighted_int_goal_is_polynomial_expr() {
    let expr = int_add(int_var("c"), int_mul_expr(int_neg_succ(1), int_var("a")));
    assert!(
        is_polynomial_expr(&expr),
        "Int.negSucc-backed weighted terms should parse as polynomials"
    );
}

#[test]
fn test_polyrith_two_hyp_weighted_int_cert_pipeline_commuted_goal_e2e() {
    use super::super::polynomial::Polynomial;

    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(2, 1)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
        ],
        verified: true,
        explanation: "two-hyp weighted Int commuted goal".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(coeffs.len(), 2, "cert should yield two coefficients");
    assert_eq!(coeffs[0].coeff, (2, 1), "h1 should carry coefficient 2");
    assert_eq!(coeffs[1].coeff, (1, 1), "h2 should carry coefficient 1");

    let mut state = setup_two_hyp_int_state(
        int_add(int_var("c"), int_mul(2, int_var("a"))),
        int_add(int_var("d"), int_mul(2, int_var("b"))),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("weighted two-hypothesis Int cert should reconstruct a proof for the commuted goal");

    state
        .close_goal(&goal, proof)
        .expect("weighted two-hypothesis Int cert proof should close the goal");
    assert_closed_clean_proof(&state, "weighted two-hypothesis Int polyrith proof-carry");
}

#[test]
fn test_polyrith_two_hyp_negative_weighted_int_cert_pipeline_commuted_goal_e2e() {
    use super::super::polynomial::Polynomial;

    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(-2, 1)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
        ],
        verified: true,
        explanation: "two-hyp negative weighted Int commuted goal".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(coeffs.len(), 2, "cert should yield two coefficients");
    assert_eq!(coeffs[0].coeff, (-2, 1), "h1 should carry coefficient -2");
    assert_eq!(coeffs[1].coeff, (1, 1), "h2 should carry coefficient 1");

    let mut state = setup_two_hyp_int_state(
        int_add(int_var("c"), int_mul_expr(int_neg_succ(1), int_var("a"))),
        int_add(int_var("d"), int_mul_expr(int_neg_succ(1), int_var("b"))),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("negative weighted two-hypothesis Int cert should reconstruct a proof for the commuted goal");

    state
        .close_goal(&goal, proof)
        .expect("negative weighted two-hypothesis Int cert proof should close the goal");
    assert_closed_clean_proof(
        &state,
        "negative weighted two-hypothesis Int polyrith proof-carry",
    );
}

#[test]
fn test_polyrith_tactic_two_hyp_weighted_int_goal_closes_without_trust() {
    let mut state = setup_two_hyp_int_state(
        int_add(int_var("c"), int_mul(2, int_var("a"))),
        int_add(int_var("d"), int_mul(2, int_var("b"))),
    );

    polyrith(&mut state)
        .expect("polyrith should find and reconstruct the weighted Int certificate");

    assert_closed_clean_proof(
        &state,
        "weighted two-hypothesis Int polyrith tactic proof-carry",
    );
}

#[test]
fn test_polyrith_tactic_two_hyp_negative_weighted_int_goal_closes_without_trust() {
    let mut state = setup_two_hyp_int_state(
        int_add(int_var("c"), int_mul_expr(int_neg_succ(1), int_var("a"))),
        int_add(int_var("d"), int_mul_expr(int_neg_succ(1), int_var("b"))),
    );

    polyrith(&mut state)
        .expect("polyrith should find and reconstruct the negative weighted Int certificate");

    assert_closed_clean_proof(
        &state,
        "negative weighted two-hypothesis Int polyrith tactic proof-carry",
    );
}

#[test]
fn test_polyrith_tactic_int_symmetry_goal_closes_without_trust() {
    let mut state = setup_two_hyp_int_state(int_var("b"), int_var("a"));

    polyrith(&mut state)
        .expect("polyrith should still use symmetry for an Int reversed-equality goal");

    assert_closed_clean_proof(&state, "Int symmetry polyrith tactic proof-carry");
}
