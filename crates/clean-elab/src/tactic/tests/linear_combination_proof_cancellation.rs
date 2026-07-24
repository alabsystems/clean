// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cancellation-boundary regressions for linear_combination proof replay.

use super::*;
use clean_kernel::env::Declaration;
use pattern::{linear_combination, linear_combination_proof::build_linear_combination_eq_proof};

fn nat_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn int_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn rat_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
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

fn rat_div(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Rat.div"), vec![]), lhs),
        rhs,
    )
}

fn rat_fraction_div(num: i64, den: u64) -> Expr {
    rat_div(
        rat_of_int(num),
        rat_of_int(i64::try_from(den).expect("test denominator should fit i64")),
    )
}

fn rat_scaled(num: i64, den: u64, var: Expr) -> Expr {
    rat_mul_expr(rat_fraction_div(num, den), var)
}

fn setup_nat_transitivity_goal() -> ProofState {
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
                ty: make_eq(nat, nat_var("b"), nat_var("c")),
                value: None,
            },
        ],
    )
}

fn setup_int_transitivity_goal() -> ProofState {
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
                ty: make_eq(int, int_var("b"), int_var("c")),
                value: None,
            },
        ],
    )
}

#[test]
fn test_proof_builder_two_hyp_transitivity_goal_uses_cancellation_bridge() {
    let mut state = setup_nat_transitivity_goal();
    let goal = state.current_goal().expect("goal should exist").clone();

    let proof = build_linear_combination_eq_proof(
        &state,
        &goal,
        &[LinearCoeff::one("h1"), LinearCoeff::one("h2")],
    )
    .expect("two-hypothesis transitivity goal should reconstruct via cancellation");

    state
        .close_goal(&goal, proof)
        .expect("cancellation-bridge proof should type-check and close the goal");
    assert!(
        state.is_complete(),
        "state should be complete after cancellation reconstruction"
    );
    assert!(
        state.proof_term().is_some(),
        "proof_term() should be extractable after cancellation reconstruction"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "cancellation bridge must not use trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "cancellation bridge must not use sorry"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "cancellation bridge must not use trustedAy"
    );
}

#[test]
fn test_linear_combination_tactic_two_hyp_transitivity_goal_closes_without_trusted_arith() {
    let mut state = setup_nat_transitivity_goal();

    linear_combination(
        &mut state,
        vec![LinearCoeff::one("h1"), LinearCoeff::one("h2")],
    )
    .expect("linear_combination should close the transitivity goal without trustedArith");

    assert!(
        state.is_complete(),
        "linear_combination should close the transitivity goal"
    );
    assert!(
        state.proof_term().is_some(),
        "linear_combination should leave an extractable proof term"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "linear_combination cancellation path must avoid trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "linear_combination cancellation path must avoid sorry"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "linear_combination cancellation path must avoid trustedAy"
    );
}

#[test]
fn test_proof_builder_int_transitivity_goal_uses_cancellation_bridge() {
    let mut state = setup_int_transitivity_goal();
    let goal = state.current_goal().expect("goal should exist").clone();

    let proof = build_linear_combination_eq_proof(
        &state,
        &goal,
        &[LinearCoeff::one("h1"), LinearCoeff::one("h2")],
    )
    .expect("Int transitivity goal should reconstruct via cancellation");

    state
        .close_goal(&goal, proof)
        .expect("Int cancellation-bridge proof should type-check and close the goal");
    assert!(
        state.is_complete(),
        "state should be complete after Int cancellation reconstruction"
    );
    assert!(
        state.proof_term().is_some(),
        "proof_term() should be extractable after Int cancellation reconstruction"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "Int cancellation bridge must not use trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "Int cancellation bridge must not use sorry"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "Int cancellation bridge must not use trustedAy"
    );
}

#[test]
fn test_linear_combination_tactic_int_transitivity_goal_closes_without_trusted_arith() {
    let mut state = setup_int_transitivity_goal();

    linear_combination(
        &mut state,
        vec![LinearCoeff::one("h1"), LinearCoeff::one("h2")],
    )
    .expect("linear_combination should close the Int transitivity goal without trustedArith");

    assert!(
        state.is_complete(),
        "linear_combination should close the Int transitivity goal"
    );
    assert!(
        state.proof_term().is_some(),
        "linear_combination should leave an extractable Int proof term"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "Int linear_combination cancellation path must avoid trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "Int linear_combination cancellation path must avoid sorry"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "Int linear_combination cancellation path must avoid trustedAy"
    );
}

/// Set up a Rat state where two hypotheses share an additive witness on one side.
///
/// h1: a = b (Rat), h2: c = c (Rat, trivial)
/// With fractional coeff 1/2 on both:
///   combined = (1/2)*a + (1/2)*c = (1/2)*b + (1/2)*c
///   shared witness = (1/2)*c
///   after cancellation = (1/2)*a = (1/2)*b
///
/// Goal: (1/2)*a = (1/2)*b
/// Direct close fails (combined type ≠ goal type).
/// Cancellation bridge finds shared witness (1/2)*c, both connecting equalities
/// are identities (no ring_nf Rat commutativity needed), and Rat.add_right_cancel
/// produces the final proof.
fn setup_rat_fractional_cancellation_goal() -> ProofState {
    let mut env = Environment::with_prelude();
    env.init_rat_field_inst()
        .expect("Rat field instance should initialize");
    env.init_cast_simp_lemmas()
        .expect("Cast simp lemmas (Rat.ofInt) should initialize");

    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: rat.clone(),
        })
        .expect("Rat variable axiom should add");
    }

    // goal: (1/2)*a = (1/2)*b
    let goal_lhs = rat_scaled(1, 2, rat_var("a"));
    let goal_rhs = rat_scaled(1, 2, rat_var("b"));

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
                ty: make_eq(rat, rat_var("c"), rat_var("c")),
                value: None,
            },
        ],
    )
}

/// TP-1 (#2588): Rat proof-builder cancellation regression.
///
/// Two hypotheses with constant fractional coefficient (1/2 each) on the Rat
/// carrier.  The combined equality `(1/2)*a + (1/2)*c = (1/2)*b + (1/2)*c`
/// does not direct-close against the goal `(1/2)*a = (1/2)*b`.  The
/// cancellation bridge finds the shared additive witness `(1/2)*c`, applies
/// `Rat.add_right_cancel`, and closes the goal.
///
/// Before #2588 this returned `None` at the fractional early-return guard.
///
/// Part of #2588.
#[test]
fn test_proof_builder_rat_fractional_cancellation_bridge() {
    let mut state = setup_rat_fractional_cancellation_goal();
    let goal = state.current_goal().expect("goal should exist").clone();

    let proof = build_linear_combination_eq_proof(
        &state,
        &goal,
        &[LinearCoeff::new("h1", 1, 2), LinearCoeff::new("h2", 1, 2)],
    )
    .expect("Rat fractional cancellation should produce a proof via Rat.add_right_cancel");

    state
        .close_goal(&goal, proof)
        .expect("Rat fractional cancellation proof should type-check and close the goal");
    assert!(
        state.is_complete(),
        "state should be complete after Rat fractional cancellation"
    );
    assert!(
        state.proof_term().is_some(),
        "proof_term() should be extractable after Rat fractional cancellation"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "Rat fractional cancellation must not use trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "Rat fractional cancellation must not use sorry"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "Rat fractional cancellation must not use trustedAy"
    );
}

/// TP-2 (#2588): Rat tactic-level verified-cert regression.
///
/// Uses the `linear_combination` tactic entry point with the same fractional
/// Rat coefficients so the entire pipeline is exercised end-to-end:
/// coefficient rendering → weighted equality → cancellation bridge →
/// Rat.add_right_cancel → kernel-checked close.
///
/// Part of #2588.
#[test]
fn test_linear_combination_tactic_rat_fractional_cancellation_closes_without_trust() {
    let mut state = setup_rat_fractional_cancellation_goal();

    linear_combination(
        &mut state,
        vec![LinearCoeff::new("h1", 1, 2), LinearCoeff::new("h2", 1, 2)],
    )
    .expect("linear_combination should close Rat fractional cancellation without trustedArith");

    assert!(
        state.is_complete(),
        "linear_combination should close the Rat fractional cancellation goal"
    );
    assert!(
        state.proof_term().is_some(),
        "linear_combination should leave an extractable Rat proof term"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "Rat fractional linear_combination must avoid trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "Rat fractional linear_combination must avoid sorry"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "Rat fractional linear_combination must avoid trustedAy"
    );
}
