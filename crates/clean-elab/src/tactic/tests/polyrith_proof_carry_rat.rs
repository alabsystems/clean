// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rat carrier polyrith proof-carry regressions (#2526, #2573, #2589).
//!
//! Validates that the shared linear combination proof builder works for
//! Rat-typed hypotheses with integer and bounded fractional coefficients,
//! including the commuted-goal scratch-normalization slice from #2589.
//! Rat carrier uses `Rat.ofInt`/`Rat.div` for coefficient rendering and
//! `Rat.add`/`Rat.mul` for binary operations. Denominator clearing remains
//! out of scope here.

use super::super::polynomial::Polynomial;
use super::*;
use clean_kernel::env::Declaration;

fn rat_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn rat_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Rat.add"), vec![]), lhs),
        rhs,
    )
}

fn rat_div(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Rat.div"), vec![]), lhs),
        rhs,
    )
}

fn rat_inv(expr: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Rat.inv"), vec![]), expr)
}

fn rat_of_int(n: i64) -> Expr {
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
        Expr::const_(Name::from_string("Rat.ofInt"), vec![]),
        int_expr,
    )
}

fn rat_mul_expr(coeff: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Rat.mul"), vec![]), coeff),
        rhs,
    )
}

fn rat_mul(coeff: i64, rhs: Expr) -> Expr {
    rat_mul_expr(rat_of_int(coeff), rhs)
}

fn rat_fraction_div(num: i64, den: u64) -> Expr {
    rat_div(
        rat_of_int(num),
        rat_of_int(i64::try_from(den).expect("test denominator should fit i64")),
    )
}

fn rat_fraction_mul_inv(num: i64, den: u64) -> Expr {
    rat_mul_expr(
        rat_of_int(num),
        rat_inv(rat_of_int(
            i64::try_from(den).expect("test denominator should fit i64"),
        )),
    )
}

fn rat_mul_fraction_div(num: i64, den: u64, rhs: Expr) -> Expr {
    rat_mul_expr(rat_fraction_div(num, den), rhs)
}

fn setup_two_hyp_rat_state(goal_lhs: Expr, goal_rhs: Expr) -> ProofState {
    let mut env = Environment::with_prelude();
    env.init_rat_field_inst()
        .expect("Rat field instance should initialize");
    env.init_cast_simp_lemmas()
        .expect("cast simp lemmas should initialize");

    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    for name in ["a", "b", "c", "d"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: rat.clone(),
        })
        .expect("Rat variable axiom should add");
    }

    ProofState::with_context(
        env,
        make_eq(rat.clone(), goal_lhs, goal_rhs),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: make_eq(rat.clone(), rat_var("a"), rat_var("b")),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: make_eq(rat, rat_var("c"), rat_var("d")),
                value: None,
            },
        ],
    )
}

fn setup_single_hyp_rat_state(goal_lhs: Expr, goal_rhs: Expr) -> ProofState {
    let mut env = Environment::with_prelude();
    env.init_rat_field_inst()
        .expect("Rat field instance should initialize");
    env.init_cast_simp_lemmas()
        .expect("cast simp lemmas should initialize");

    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: rat.clone(),
        })
        .expect("Rat variable axiom should add");
    }

    ProofState::with_context(
        env,
        make_eq(rat.clone(), goal_lhs, goal_rhs),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: make_eq(rat, rat_var("a"), rat_var("b")),
            value: None,
        }],
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
fn test_weighted_rat_goal_is_polynomial_expr() {
    let expr = rat_add(rat_mul(2, rat_var("a")), rat_var("c"));
    assert!(
        is_polynomial_expr(&expr),
        "Rat.ofInt-backed weighted terms should parse as polynomials"
    );
}

#[test]
fn test_negative_weighted_rat_goal_is_polynomial_expr() {
    let expr = rat_add(rat_mul(-2, rat_var("a")), rat_var("c"));
    assert!(
        is_polynomial_expr(&expr),
        "negative Rat.ofInt-backed weighted terms should parse as polynomials"
    );
}

#[test]
fn test_fractional_div_rat_goal_is_polynomial_expr() {
    let expr = rat_add(
        rat_mul_fraction_div(1, 2, rat_var("a")),
        rat_mul_fraction_div(1, 2, rat_var("c")),
    );
    assert!(
        is_polynomial_expr(&expr),
        "Rat.div-backed fractional weighted terms should parse as polynomials"
    );
}

#[test]
fn test_fractional_mul_inv_rat_goal_is_polynomial_expr() {
    let expr = rat_add(
        rat_mul_expr(rat_fraction_mul_inv(1, 2), rat_var("a")),
        rat_mul_expr(rat_fraction_mul_inv(1, 2), rat_var("c")),
    );
    assert!(
        is_polynomial_expr(&expr),
        "Rat.mul/Rat.inv-backed fractional weighted terms should parse as polynomials"
    );
}

#[test]
fn test_fractional_rat_proof_builder_single_hyp_closes_without_trust() {
    let mut state = setup_single_hyp_rat_state(
        rat_mul_fraction_div(1, 2, rat_var("a")),
        rat_mul_fraction_div(1, 2, rat_var("b")),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let coeffs = vec![LinearCoeff::new("h", 1, 2)];

    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("fractional Rat coefficient should reconstruct a direct-close proof");

    state
        .close_goal(&goal, proof)
        .expect("fractional Rat proof should close the single-hypothesis goal");
    assert_closed_clean_proof(&state, "single-hypothesis fractional Rat proof builder");
}

#[test]
fn test_fractional_rat_linear_combination_tactic_closes_without_trust() {
    let mut state = setup_single_hyp_rat_state(
        rat_mul_fraction_div(1, 2, rat_var("a")),
        rat_mul_fraction_div(1, 2, rat_var("b")),
    );

    linear_combination(&mut state, vec![LinearCoeff::new("h", 1, 2)])
        .expect("linear_combination should close the fractional Rat goal");

    assert_closed_clean_proof(
        &state,
        "single-hypothesis fractional Rat linear_combination",
    );
}

#[test]
fn test_fractional_rat_proof_builder_commuted_goal_closes_without_trust() {
    let mut state = setup_two_hyp_rat_state(
        rat_add(rat_var("c"), rat_mul_fraction_div(1, 2, rat_var("a"))),
        rat_add(rat_var("d"), rat_mul_fraction_div(1, 2, rat_var("b"))),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let coeffs = vec![LinearCoeff::new("h1", 1, 2), LinearCoeff::new("h2", 1, 1)];

    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("fractional Rat commuted goal should reconstruct via scratch normalization");

    state
        .close_goal(&goal, proof)
        .expect("fractional Rat commuted proof should close the goal");
    assert_closed_clean_proof(&state, "commuted fractional Rat proof builder");
}

#[test]
fn test_fractional_rat_linear_combination_commuted_goal_closes_without_trust() {
    let mut state = setup_two_hyp_rat_state(
        rat_add(rat_var("c"), rat_mul_fraction_div(1, 2, rat_var("a"))),
        rat_add(rat_var("d"), rat_mul_fraction_div(1, 2, rat_var("b"))),
    );

    linear_combination(
        &mut state,
        vec![LinearCoeff::new("h1", 1, 2), LinearCoeff::new("h2", 1, 1)],
    )
    .expect("linear_combination should close the commuted fractional Rat goal");

    assert_closed_clean_proof(&state, "commuted fractional Rat linear_combination");
}

#[test]
fn test_ring_nf_fractional_rat_commuted_goal_closes_without_trust() {
    let mut state = setup_two_hyp_rat_state(
        rat_add(rat_mul_fraction_div(1, 2, rat_var("a")), rat_var("c")),
        rat_add(rat_var("c"), rat_mul_fraction_div(1, 2, rat_var("a"))),
    );

    ring_nf(&mut state).expect("ring_nf should close the commuted fractional Rat goal");

    assert_closed_clean_proof(&state, "commuted fractional Rat ring_nf");
}

// --- Pipeline-level tests (certificate → proof builder → close) ---

#[test]
fn test_polyrith_two_hyp_rat_identity_cert_pipeline_e2e() {
    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(1, 1)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
        ],
        verified: true,
        explanation: "two-hyp Rat identity goal".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(coeffs.len(), 2, "cert should yield two coefficients");

    // Goal matches accumulator output order: Rat.add(a, c) = Rat.add(b, d)
    let mut state = setup_two_hyp_rat_state(
        rat_add(rat_var("a"), rat_var("c")),
        rat_add(rat_var("b"), rat_var("d")),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("identity two-hypothesis Rat cert should reconstruct a proof");

    state
        .close_goal(&goal, proof)
        .expect("identity two-hypothesis Rat cert proof should close the goal");
    assert_closed_clean_proof(&state, "identity two-hypothesis Rat polyrith proof-carry");
}

#[test]
fn test_polyrith_two_hyp_weighted_rat_cert_pipeline_e2e() {
    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(2, 1)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
        ],
        verified: true,
        explanation: "two-hyp weighted Rat goal".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(coeffs.len(), 2, "cert should yield two coefficients");
    assert_eq!(coeffs[0].coeff, (2, 1), "h1 should carry coefficient 2");

    // Goal matches accumulator output: Rat.add(Rat.mul(2, a), c) = Rat.add(Rat.mul(2, b), d)
    let mut state = setup_two_hyp_rat_state(
        rat_add(rat_mul(2, rat_var("a")), rat_var("c")),
        rat_add(rat_mul(2, rat_var("b")), rat_var("d")),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("weighted two-hypothesis Rat cert should reconstruct a proof");

    state
        .close_goal(&goal, proof)
        .expect("weighted two-hypothesis Rat cert proof should close the goal");
    assert_closed_clean_proof(&state, "weighted two-hypothesis Rat polyrith proof-carry");
}

#[test]
fn test_polyrith_rat_symmetry_single_hyp_e2e() {
    let cert = PolyrithCertificate {
        coefficients: vec![("h1".to_string(), Polynomial::constant(-1, 1))],
        verified: true,
        explanation: "single-hyp Rat symmetry goal".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(coeffs.len(), 1, "cert should yield one coefficient");
    assert_eq!(coeffs[0].coeff, (-1, 1), "h1 should carry coefficient -1");

    // h1 : a = b, goal: b = a (symmetry)
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let mut env = Environment::with_prelude();
    env.init_rat_field_inst()
        .expect("Rat field instance should initialize");
    env.init_cast_simp_lemmas()
        .expect("cast simp lemmas should initialize");
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: rat.clone(),
        })
        .expect("Rat variable axiom should add");
    }

    let mut state = ProofState::with_context(
        env,
        make_eq(rat.clone(), rat_var("b"), rat_var("a")),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h1".to_string(),
            ty: make_eq(rat, rat_var("a"), rat_var("b")),
            value: None,
        }],
    );

    let goal = state.current_goal().expect("goal should exist").clone();
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("symmetry Rat cert should reconstruct a proof");

    state
        .close_goal(&goal, proof)
        .expect("symmetry Rat cert proof should close the goal");
    assert_closed_clean_proof(&state, "symmetry Rat polyrith proof-carry");
}

#[test]
fn test_polyrith_rat_negative_weighted_cert_pipeline_e2e() {
    let cert = PolyrithCertificate {
        coefficients: vec![
            ("h1".to_string(), Polynomial::constant(-2, 1)),
            ("h2".to_string(), Polynomial::constant(1, 1)),
        ],
        verified: true,
        explanation: "two-hyp negative weighted Rat goal".to_string(),
    };
    let coeffs = linear_coeffs_from_cert(&cert);
    assert_eq!(coeffs.len(), 2, "cert should yield two coefficients");
    assert_eq!(coeffs[0].coeff, (-2, 1), "h1 should carry coefficient -2");

    // Negative-weighted: symmetrize h1 (b=a) then scale by 2.
    // Accumulator output: Rat.add(Rat.mul(2, b), c) = Rat.add(Rat.mul(2, a), d)
    let mut state = setup_two_hyp_rat_state(
        rat_add(rat_mul(2, rat_var("b")), rat_var("c")),
        rat_add(rat_mul(2, rat_var("a")), rat_var("d")),
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let proof = pattern::linear_combination_proof::build_linear_combination_eq_proof(
        &state, &goal, &coeffs,
    )
    .expect("negative weighted two-hypothesis Rat cert should reconstruct a proof");

    state
        .close_goal(&goal, proof)
        .expect("negative weighted two-hypothesis Rat cert proof should close the goal");
    assert_closed_clean_proof(
        &state,
        "negative weighted two-hypothesis Rat polyrith proof-carry",
    );
}

#[test]
fn test_polyrith_tactic_two_hyp_weighted_rat_goal_closes_without_trust() {
    let mut state = setup_two_hyp_rat_state(
        rat_add(rat_mul(2, rat_var("a")), rat_var("c")),
        rat_add(rat_mul(2, rat_var("b")), rat_var("d")),
    );

    polyrith(&mut state)
        .expect("polyrith should find and reconstruct the weighted Rat certificate");

    assert_closed_clean_proof(
        &state,
        "weighted two-hypothesis Rat polyrith tactic proof-carry",
    );
}

#[test]
fn test_polyrith_tactic_two_hyp_negative_weighted_rat_goal_closes_without_trust() {
    let mut state = setup_two_hyp_rat_state(
        rat_add(rat_mul(2, rat_var("b")), rat_var("c")),
        rat_add(rat_mul(2, rat_var("a")), rat_var("d")),
    );

    polyrith(&mut state)
        .expect("polyrith should find and reconstruct the negative weighted Rat certificate");

    assert_closed_clean_proof(
        &state,
        "negative weighted two-hypothesis Rat polyrith tactic proof-carry",
    );
}

#[test]
fn test_polyrith_tactic_two_hyp_fractional_rat_goal_closes_without_trust() {
    let mut state = setup_two_hyp_rat_state(
        rat_add(
            rat_mul_fraction_div(1, 2, rat_var("a")),
            rat_mul_fraction_div(1, 2, rat_var("c")),
        ),
        rat_add(
            rat_mul_fraction_div(1, 2, rat_var("b")),
            rat_mul_fraction_div(1, 2, rat_var("d")),
        ),
    );

    polyrith(&mut state)
        .expect("polyrith should find and reconstruct the fractional Rat certificate");

    assert_closed_clean_proof(&state, "two-hypothesis fractional Rat polyrith tactic");
}

#[test]
fn test_polyrith_tactic_two_hyp_fractional_rat_commuted_goal_closes_without_trust() {
    let mut state = setup_two_hyp_rat_state(
        rat_add(rat_var("c"), rat_mul_fraction_div(1, 2, rat_var("a"))),
        rat_add(rat_var("d"), rat_mul_fraction_div(1, 2, rat_var("b"))),
    );

    polyrith(&mut state)
        .expect("polyrith should find and reconstruct the commuted fractional Rat certificate");

    assert_closed_clean_proof(
        &state,
        "two-hypothesis commuted fractional Rat polyrith tactic",
    );
}
