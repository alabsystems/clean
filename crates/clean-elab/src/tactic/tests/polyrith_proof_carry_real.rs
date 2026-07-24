// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real carrier polyrith proof-carry regressions (#2635).
//!
//! Covers the remaining site-5 Real lane by forcing `polyrith` to recover a
//! half-integer certificate: one hypothesis is scaled by `1/2`, but the goal
//! itself stays in the polynomial subset (`Real.add`, `Real.mul`, `Real.ofInt`)
//! so certificate search remains available.

use super::*;
use clean_kernel::env::Declaration;

fn real_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn real_of_int(n: i64) -> Expr {
    let int_expr = if n >= 0 {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(n as u64),
        )
    } else {
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(n.unsigned_abs() - 1),
        )
    };
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    )
}

fn real_mul_expr(coeff: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.mul"), vec![]), coeff),
        rhs,
    )
}

fn real_mul(coeff: i64, rhs: Expr) -> Expr {
    real_mul_expr(real_of_int(coeff), rhs)
}

fn real_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.add"), vec![]), lhs),
        rhs,
    )
}

fn setup_real_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_real_complex_analysis()
        .expect("Real complex analysis should initialize");
    env.init_cast_simp_lemmas()
        .expect("cast simp lemmas should initialize");
    env
}

fn setup_two_hyp_real_state(goal_lhs: Expr, goal_rhs: Expr) -> ProofState {
    let mut env = setup_real_env();

    let real = Expr::const_(Name::from_string("Real"), vec![]);
    for name in ["a", "b", "c", "d"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: real.clone(),
        })
        .expect("Real variable axiom should add");
    }

    ProofState::with_context(
        env,
        make_eq(real.clone(), goal_lhs, goal_rhs),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: make_eq(
                    real.clone(),
                    real_mul(2, real_var("a")),
                    real_mul(2, real_var("b")),
                ),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: make_eq(real, real_var("c"), real_var("d")),
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
fn test_polyrith_real_half_integer_cert_reconstructs_without_trust() {
    use super::super::polynomial::Polynomial;

    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(1, 2)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
        ],
        verified: true,
        explanation: "goal = (1/2) * h1 + 1 * h2".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(
        coeffs.len(),
        2,
        "cert should yield two non-zero coefficients"
    );
    assert_eq!(coeffs[0].coeff, (1, 2), "h1 should carry coefficient 1/2");
    assert_eq!(coeffs[1].coeff, (1, 1), "h2 should carry coefficient 1");

    let mut state = setup_two_hyp_real_state(
        real_add(real_var("c"), real_var("a")),
        real_add(real_var("d"), real_var("b")),
    );
    let goal = state.current_goal().expect("goal should exist").clone();

    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("Real half-integer cert should reconstruct a proof");

    state
        .close_goal(&goal, proof)
        .expect("Real half-integer cert proof should close the goal");
    assert_closed_clean_proof(&state, "Real half-integer polyrith proof-carry");
}

#[test]
fn test_real_scaled_integer_replay_closes_without_trust() {
    let mut state = setup_two_hyp_real_state(
        real_mul(2, real_add(real_var("c"), real_var("a"))),
        real_mul(2, real_add(real_var("d"), real_var("b"))),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let coeffs = vec![LinearCoeff::one("h1"), LinearCoeff::int("h2", 2)];

    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("scaled integer Real replay should reconstruct a proof");

    state
        .close_goal(&goal, proof)
        .expect("scaled integer Real replay should close the goal");
    assert_closed_clean_proof(&state, "scaled integer Real replay");
}

#[test]
fn test_polyrith_tactic_real_half_integer_cert_closes_without_trust() {
    let mut state = setup_two_hyp_real_state(
        real_add(real_var("c"), real_var("a")),
        real_add(real_var("d"), real_var("b")),
    );

    polyrith(&mut state)
        .expect("polyrith should find and reconstruct the Real half-integer certificate");

    assert_closed_clean_proof(&state, "Real half-integer polyrith tactic");
}
