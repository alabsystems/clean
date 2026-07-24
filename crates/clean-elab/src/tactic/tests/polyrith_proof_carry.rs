// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for polyrith certificate proof reconstruction (#2526).
//!
//! Verifies that `cert_to_linear_coeffs` correctly translates polynomial
//! certificates to LinearCoeffs and that unsupported cases fail closed.

use super::*;

#[test]
fn test_polyrith_config_default_values() {
    let config = PolyrithConfig::default();
    assert_eq!(config.max_degree, 4);
    assert!(config.try_simple);
    assert_eq!(config.max_hyps, 10);
}

#[test]
fn test_polyrith_cert_constant_coefficients() {
    // Constant integer coefficients should be extractable
    use super::super::polynomial::Polynomial;
    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(2, 1)),
            ("h2".to_string(), Polynomial::constant(-1, 1)),
        ],
        verified: true,
        explanation: "test".to_string(),
    };

    // Extract via the same path polyrith uses internally
    let mut coeffs = Vec::new();
    for (name, poly) in &cert.coefficients {
        if let Some((num, den)) = poly.as_constant_coeff() {
            if num != 0 {
                coeffs.push(LinearCoeff::new(name, num, den));
            }
        }
    }

    assert_eq!(coeffs.len(), 2);
    assert_eq!(coeffs[0].hyp_name, "h1");
    assert_eq!(coeffs[0].coeff, (2, 1));
    assert_eq!(coeffs[1].hyp_name, "h2");
    assert_eq!(coeffs[1].coeff, (-1, 1));
}

#[test]
fn test_polyrith_cert_variable_coefficient_fails_closed() {
    // Non-constant coefficient should cause fail-closed behavior
    use super::super::polynomial::Polynomial;
    let x_poly = Polynomial::var(0); // x (not constant)

    let cert = PolyrithCertificate {
        coefficients: vec![("h1".to_string(), x_poly)],
        verified: true,
        explanation: "test".to_string(),
    };

    // Should fail to extract
    for (_, poly) in &cert.coefficients {
        assert!(
            poly.as_constant_coeff().is_none(),
            "variable coefficient should return None"
        );
    }
}

#[test]
fn test_polyrith_cert_zero_coefficient_skipped() {
    // Zero coefficients should be skipped
    use super::super::polynomial::Polynomial;
    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(0, 1)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
        ],
        verified: true,
        explanation: "test".to_string(),
    };

    let mut coeffs = Vec::new();
    for (name, poly) in &cert.coefficients {
        if let Some((num, den)) = poly.as_constant_coeff() {
            if num != 0 {
                coeffs.push(LinearCoeff::new(name, num, den));
            }
        }
    }

    assert_eq!(coeffs.len(), 1, "zero coefficient should be skipped");
    assert_eq!(coeffs[0].hyp_name, "h2");
}

// ============================================================================
// End-to-end polyrith certificate → proof builder pipeline tests (#2526 iter 2)
//
// These tests verify the complete polyrith proof-carry path:
// PolyrithCertificate → LinearCoeff extraction → build_linear_combination_eq_proof
// → extractable proof term with clean trust ledger.
// ============================================================================

/// Helper: build a ProofState with an equality goal and named hypothesis.
///
/// Creates `hyp_name : lhs = rhs` in local context and goal `goal_lhs = goal_rhs`,
/// all over type N (from setup_env_with_full_eq).
fn setup_polyrith_eq_state(
    env: Environment,
    hyp_name: &str,
    hyp_lhs: Expr,
    hyp_rhs: Expr,
    goal_lhs: Expr,
    goal_rhs: Expr,
) -> ProofState {
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let eq_target = make_eq(n_ty.clone(), goal_lhs, goal_rhs);
    let h_ty = make_eq(n_ty, hyp_lhs, hyp_rhs);

    ProofState::with_context(
        env,
        eq_target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: hyp_name.to_string(),
            ty: h_ty,
            value: None,
        }],
    )
}

#[test]
fn test_polyrith_cert_to_proof_builder_e2e() {
    // Full pipeline: polyrith certificate with coeff=1 → extract LinearCoeffs →
    // build_linear_combination_eq_proof → extractable proof term → clean ledger.
    //
    // Simulates: polyrith finds cert {h: 1}, then proof builder produces
    // a kernel-valid proof without trustedArith.
    use super::super::polynomial::Polynomial;

    let cert = PolyrithCertificate {
        coefficients: vec![("h".to_string(), Polynomial::constant(1, 1))],
        verified: true,
        explanation: "test cert".to_string(),
    };

    // Step 1: Extract LinearCoeffs (same path as polyrith.close_with_verified_cert)
    let mut coeffs = Vec::new();
    for (name, poly) in &cert.coefficients {
        if let Some((num, den)) = poly.as_constant_coeff() {
            if num != 0 {
                coeffs.push(LinearCoeff::new(name, num, den));
            }
        }
    }
    assert_eq!(coeffs.len(), 1, "cert should yield 1 non-zero coeff");

    // Step 2: Build proof state with h : x = y ⊢ x = y
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let mut state = setup_polyrith_eq_state(env, "h", x.clone(), y.clone(), x, y);
    let goal = state.current_goal().unwrap().clone();

    // Step 3: Proof builder produces proof
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("polyrith cert with coeff=1 should produce kernel proof");

    // Step 4: Close goal, verify extractable proof term
    state
        .close_goal(&goal, proof)
        .expect("polyrith-derived proof should close the goal");
    assert!(state.is_complete(), "state should be complete");
    assert!(
        state.proof_term().is_some(),
        "proof_term() should be extractable"
    );

    // Step 5: Trust ledger verification — zero trusted axiom usage
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "polyrith proof-carry must not use trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "polyrith proof-carry must not use sorry"
    );
}

#[test]
fn test_polyrith_cert_symmetry_proof_carry_e2e() {
    // Polyrith certificate with coeff=-1 (symmetry) → proof builder → clean ledger.
    // Simulates: polyrith finds cert {h: -1} for a reversed-equality goal.
    use super::super::polynomial::Polynomial;

    let cert = PolyrithCertificate {
        coefficients: vec![("h".to_string(), Polynomial::constant(-1, 1))],
        verified: true,
        explanation: "test symmetry cert".to_string(),
    };

    let mut coeffs = Vec::new();
    for (name, poly) in &cert.coefficients {
        if let Some((num, den)) = poly.as_constant_coeff() {
            if num != 0 {
                coeffs.push(LinearCoeff::new(name, num, den));
            }
        }
    }
    assert_eq!(coeffs.len(), 1);

    // h : x = y ⊢ y = x (reversed)
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let mut state = setup_polyrith_eq_state(env, "h", x.clone(), y.clone(), y, x);
    let goal = state.current_goal().unwrap().clone();

    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("polyrith cert with coeff=-1 should produce Eq.symm proof");

    state.close_goal(&goal, proof).expect("should close");
    assert!(state.is_complete());
    assert!(state.proof_term().is_some());
    assert_eq!(state.trust_ledger().trusted_arith_count, 0);
}

#[test]
fn test_polyrith_cert_rational_coeff_falls_through() {
    // Polyrith certificate with rational coefficient (1/2) should fail at the
    // proof builder (returns None), confirming fail-closed behavior.
    // Production `polyrith` now returns ArithmeticFailed instead of
    // closing with trustedArith when reconstruction cannot produce a proof.
    use super::super::polynomial::Polynomial;

    let cert = PolyrithCertificate {
        coefficients: vec![("h".to_string(), Polynomial::constant(1, 2))],
        verified: true,
        explanation: "test rational cert".to_string(),
    };

    let mut coeffs = Vec::new();
    for (name, poly) in &cert.coefficients {
        if let Some((num, den)) = poly.as_constant_coeff() {
            if num != 0 {
                coeffs.push(LinearCoeff::new(name, num, den));
            }
        }
    }
    assert_eq!(coeffs.len(), 1, "rational coeff should still extract");
    assert_eq!(coeffs[0].coeff, (1, 2), "coefficient should be 1/2");

    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let state = setup_polyrith_eq_state(env, "h", x.clone(), y.clone(), x, y);
    let goal = state.current_goal().unwrap().clone();

    let result = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    );
    assert!(
        result.is_none(),
        "rational coefficient should fail closed at proof builder (den != 1)"
    );
}

// ============================================================================
// Error case tests
// ============================================================================

#[test]
fn test_polyrith_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = polyrith(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_polyrith_non_equality_goal() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = polyrith(&mut state);
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}
