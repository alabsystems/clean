// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for linear_combination proof reconstruction (#2526).
//!
//! Verifies that the shared proof builder produces kernel-valid proof terms
//! and that unsupported cases fail closed (return None, not trustedArith).

use super::*;
use clean_kernel::env::Declaration;
use pattern::{linear_combination, linear_combination_proof::build_linear_combination_eq_proof};

/// Helper: build a ProofState with an equality goal and local hypothesis.
///
/// Creates `h : a = b` in local context and goal `lhs = rhs`, all over type N.
fn setup_eq_goal_with_hyp(
    env: Environment,
    hyp_lhs: Expr,
    hyp_rhs: Expr,
    goal_lhs: Expr,
    goal_rhs: Expr,
) -> ProofState {
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let eq_target = make_eq(n_ty.clone(), goal_lhs, goal_rhs);
    let mut state = ProofState::new(env, eq_target);

    // Add hypothesis h : hyp_lhs = hyp_rhs
    let h_ty = make_eq(n_ty, hyp_lhs, hyp_rhs);
    let h_fvar = state.fresh_fvar();
    if let Some(goal) = state.current_goal_mut() {
        goal.local_ctx.push(LocalDecl {
            name: "h".to_string(),
            fvar: h_fvar,
            ty: h_ty,
            value: None,
        });
    }

    state
}

fn nat_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), lhs),
        rhs,
    )
}

fn setup_nat_sum_goal_with_two_hyps(goal_lhs: Expr, goal_rhs: Expr) -> ProofState {
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

#[test]
fn test_linear_combination_proof_builder_empty_coeffs() {
    // Empty coefficients should return None
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let state = setup_eq_goal_with_hyp(env, x.clone(), y.clone(), x, y);
    let goal = state.current_goal().unwrap().clone();

    let result = build_linear_combination_eq_proof(&state, &goal, &[]);
    assert!(result.is_none(), "empty coefficients should return None");
}

#[test]
fn test_linear_combination_proof_builder_missing_hyp() {
    // Referencing a non-existent hypothesis should return None
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let state = setup_eq_goal_with_hyp(env, x.clone(), y.clone(), x, y);
    let goal = state.current_goal().unwrap().clone();

    let coeffs = vec![LinearCoeff::one("nonexistent")];
    let result = build_linear_combination_eq_proof(&state, &goal, &coeffs);
    assert!(result.is_none(), "missing hypothesis should return None");
}

#[test]
fn test_linear_combination_proof_builder_rational_coeff_fails_closed() {
    // Rational (non-integer) coefficients should fail closed
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let state = setup_eq_goal_with_hyp(env, x.clone(), y.clone(), x, y);
    let goal = state.current_goal().unwrap().clone();

    let coeffs = vec![LinearCoeff::new("h", 1, 2)]; // rational 1/2
    let result = build_linear_combination_eq_proof(&state, &goal, &coeffs);
    assert!(
        result.is_none(),
        "rational coefficients should fail closed (return None)"
    );
}

// ============================================================================
// End-to-end proof builder tests (#2526 iteration 2)
//
// These tests exercise the full pipeline: hypothesis + goal → proof builder →
// extractable proof term → trust ledger verification. This confirms that the
// proof builder produces kernel-valid proofs that close goals without any
// trustedArith fallback.
// ============================================================================

#[test]
fn test_proof_builder_identity_coeff_produces_proof() {
    // h : x = y ⊢ x = y with coefficient 1
    // The proof builder should return Some(proof) — the hypothesis itself.
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let state = setup_eq_goal_with_hyp(env, x.clone(), y.clone(), x, y);
    let goal = state.current_goal().unwrap().clone();

    let coeffs = vec![LinearCoeff::one("h")];
    let result = build_linear_combination_eq_proof(&state, &goal, &coeffs);
    assert!(
        result.is_some(),
        "identity coefficient (1) should produce an extractable proof term"
    );
}

#[test]
fn test_proof_builder_identity_closes_goal_and_extracts_proof_term() {
    // Full pipeline: proof builder → close_goal → proof_term() extraction.
    // Verifies that the proof is not just Some(expr) but actually type-checks
    // against the goal and produces a complete, extractable proof state.
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let mut state = setup_eq_goal_with_hyp(env, x.clone(), y.clone(), x, y);
    let goal = state.current_goal().unwrap().clone();

    let coeffs = vec![LinearCoeff::one("h")];
    let proof = build_linear_combination_eq_proof(&state, &goal, &coeffs)
        .expect("identity coefficient should produce proof");

    state
        .close_goal(&goal, proof)
        .expect("proof from builder should type-check and close the goal");
    assert!(
        state.is_complete(),
        "state should be complete after closing"
    );
    assert!(
        state.proof_term().is_some(),
        "proof_term() should be extractable from completed state"
    );
}

#[test]
fn test_proof_builder_identity_trust_ledger_clean() {
    // Verifies zero trust: no trustedArith, no sorry, no trustedAy after
    // building and closing with the proof builder.
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let mut state = setup_eq_goal_with_hyp(env, x.clone(), y.clone(), x, y);
    let goal = state.current_goal().unwrap().clone();

    let coeffs = vec![LinearCoeff::one("h")];
    let proof = build_linear_combination_eq_proof(&state, &goal, &coeffs)
        .expect("identity coefficient should produce proof");

    state.close_goal(&goal, proof).expect("should close");
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "identity proof must not use trustedArith"
    );
    assert_eq!(ledger.sorry_count, 0, "identity proof must not use sorry");
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "identity proof must not use trustedAy"
    );
}

#[test]
fn test_proof_builder_symmetry_coeff_produces_proof() {
    // h : x = y ⊢ y = x with coefficient -1
    // The proof builder should return Eq.symm applied to the hypothesis.
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    // Note: hyp is (x = y) but goal is (y = x) — reversed
    let state = setup_eq_goal_with_hyp(env, x.clone(), y.clone(), y, x);
    let goal = state.current_goal().unwrap().clone();

    let coeffs = vec![LinearCoeff::int("h", -1)];
    let result = build_linear_combination_eq_proof(&state, &goal, &coeffs);
    assert!(
        result.is_some(),
        "symmetry coefficient (-1) should produce an extractable proof term"
    );
}

#[test]
fn test_proof_builder_symmetry_closes_goal_clean_ledger() {
    // Full pipeline for symmetry: proof builder → close_goal → extract → clean ledger.
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let mut state = setup_eq_goal_with_hyp(env, x.clone(), y.clone(), y, x);
    let goal = state.current_goal().unwrap().clone();

    let coeffs = vec![LinearCoeff::int("h", -1)];
    let proof = build_linear_combination_eq_proof(&state, &goal, &coeffs)
        .expect("symmetry coefficient should produce proof");

    state
        .close_goal(&goal, proof)
        .expect("Eq.symm proof should type-check and close the goal");
    assert!(
        state.is_complete(),
        "state should be complete after closing"
    );
    assert!(
        state.proof_term().is_some(),
        "proof_term() should be extractable"
    );

    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "symmetry proof must not use trustedArith"
    );
    assert_eq!(ledger.sorry_count, 0, "symmetry proof must not use sorry");
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "symmetry proof must not use trustedAy"
    );
}

#[test]
fn test_proof_builder_two_hyp_commuted_goal_uses_scratch_normalization() {
    // h1 : a = b, h2 : c = d ⊢ c + a = d + b
    // The combined proof is built as a + c = b + d, so the builder must use
    // scratch-state ring_nf normalization on both sides to match the commuted goal.
    let goal_lhs = nat_add(nat_var("c"), nat_var("a"));
    let goal_rhs = nat_add(nat_var("d"), nat_var("b"));
    let mut state = setup_nat_sum_goal_with_two_hyps(goal_lhs, goal_rhs);
    let goal = state.current_goal().expect("goal should exist").clone();

    let coeffs = vec![LinearCoeff::one("h1"), LinearCoeff::one("h2")];
    let proof = build_linear_combination_eq_proof(&state, &goal, &coeffs)
        .expect("two-hypothesis commuted goal should reconstruct via scratch normalization");

    state
        .close_goal(&goal, proof)
        .expect("scratch-normalized proof should type-check and close the goal");
    assert!(
        state.is_complete(),
        "state should be complete after closing"
    );
    assert!(
        state.proof_term().is_some(),
        "proof_term() should be extractable after scratch normalization"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "scratch-normalized proof must not use trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "scratch-normalized proof must not use sorry"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "scratch-normalized proof must not use trustedAy"
    );
}

#[test]
fn test_linear_combination_tactic_two_hyp_commuted_goal_closes_without_trusted_arith() {
    // End-to-end tactic path for #2526 iteration 3: ring_nf/ring/rfl/decide_eq
    // all fail on the raw goal, then linear_combination reconstructs the proof
    // from hypotheses and closes without any trusted fallback.
    let goal_lhs = nat_add(nat_var("c"), nat_var("a"));
    let goal_rhs = nat_add(nat_var("d"), nat_var("b"));
    let mut state = setup_nat_sum_goal_with_two_hyps(goal_lhs, goal_rhs);

    linear_combination(
        &mut state,
        vec![LinearCoeff::one("h1"), LinearCoeff::one("h2")],
    )
    .expect("linear_combination should close the commuted two-hypothesis goal");

    assert!(
        state.is_complete(),
        "linear_combination should close the goal"
    );
    assert!(
        state.proof_term().is_some(),
        "linear_combination should leave an extractable proof term"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "linear_combination proof-carry path must avoid trustedArith"
    );
    assert_eq!(ledger.sorry_count, 0, "proof-carry path must avoid sorry");
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "proof-carry path must avoid trustedAy"
    );
}
