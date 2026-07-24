// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Part of #2601: Int identity/distribution regression tests for ring_nf.
//! Verifies that ring_nf closes Int identity, annihilator, and distribution
//! goals without trustedArith after the shared theorem surface was extended.

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

fn int_identity_env() -> (Environment, Expr) {
    let mut env = Environment::with_prelude();
    env.init_int_euclidean_domain_inst()
        .expect("Int euclidean domain inst should initialize");
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    for name in &["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int.clone(),
        })
        .unwrap();
    }
    (env, int)
}

fn int_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn int_add(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.add"), vec![]), a),
        b,
    )
}

fn int_mul(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.mul"), vec![]), a),
        b,
    )
}

/// Int zero as emitted by Int proof-building code: `Int.ofNat Nat.zero`.
fn int_zero() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    )
}

/// Int one as used in lemma types: `Int.ofNat (Nat.succ Nat.zero)`.
fn int_one() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ),
    )
}

fn assert_ring_nf_int_clean(state: &ProofState, axiom_before: (u64, u64), context: &str) {
    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "{context}: should NOT use trustedArith"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "{context}: per-state trusted count should stay at 0"
    );
    assert!(
        state.is_complete(),
        "{context}: goal should be fully closed"
    );
    assert!(
        state.proof_term().is_some(),
        "{context}: proof_term() should be extractable"
    );
}

#[test]
fn test_ring_normalize_int_zero() {
    let zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
    let norm = ring_normalize(&zero);
    assert_eq!(norm, RingExpr::Const(0));
}

#[test]
fn test_ring_normalize_int_of_nat_one() {
    let one = int_one();
    let norm = ring_normalize(&one);
    assert_eq!(norm, RingExpr::Const(1));
}

// =============================================================================
// Additive identity: Int.add_zero / Int.zero_add
// =============================================================================

/// Part of #2601: ring_nf closes `a + Int.ofNat 0 = a` for Int via Int.add_zero.
#[test]
#[serial]
fn test_ring_nf_int_add_zero() {
    reset_arith_counter();
    let (env, int) = int_identity_env();
    let a = int_var("a");

    let lhs = int_add(a.clone(), int_zero());
    let mut state = ProofState::new(env, make_eq(int, lhs, a));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close Int add_zero identity goal");

    assert_ring_nf_int_clean(&state, axiom_before, "Int add_zero");
}

/// Part of #2601: ring_nf closes `Int.ofNat 0 + a = a` for Int via Int.zero_add.
#[test]
#[serial]
fn test_ring_nf_int_zero_add() {
    reset_arith_counter();
    let (env, int) = int_identity_env();
    let a = int_var("a");

    let lhs = int_add(int_zero(), a.clone());
    let mut state = ProofState::new(env, make_eq(int, lhs, a));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close Int zero_add identity goal");

    assert_ring_nf_int_clean(&state, axiom_before, "Int zero_add");
}

// =============================================================================
// Multiplicative identity: Int.mul_one / Int.one_mul
// =============================================================================

/// Part of #2601: ring_nf closes `a * 1 = a` for Int via Int.mul_one.
#[test]
#[serial]
fn test_ring_nf_int_mul_one() {
    reset_arith_counter();
    let (env, int) = int_identity_env();
    let a = int_var("a");

    let lhs = int_mul(a.clone(), int_one());
    let mut state = ProofState::new(env, make_eq(int, lhs, a));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close Int mul_one identity goal");

    assert_ring_nf_int_clean(&state, axiom_before, "Int mul_one");
}

/// Part of #2601: ring_nf closes `1 * a = a` for Int via Int.one_mul.
#[test]
#[serial]
fn test_ring_nf_int_one_mul() {
    reset_arith_counter();
    let (env, int) = int_identity_env();
    let a = int_var("a");

    let lhs = int_mul(int_one(), a.clone());
    let mut state = ProofState::new(env, make_eq(int, lhs, a));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close Int one_mul identity goal");

    assert_ring_nf_int_clean(&state, axiom_before, "Int one_mul");
}

// =============================================================================
// Multiplicative annihilator: Int.mul_zero / Int.zero_mul
// =============================================================================

/// Part of #2601: ring_nf closes `a * Int.ofNat 0 = Int.ofNat 0` for Int via Int.mul_zero.
#[test]
#[serial]
fn test_ring_nf_int_mul_zero() {
    reset_arith_counter();
    let (env, int) = int_identity_env();
    let a = int_var("a");

    let lhs = int_mul(a, int_zero());
    let mut state = ProofState::new(env, make_eq(int, lhs, int_zero()));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close Int mul_zero annihilator goal");

    assert_ring_nf_int_clean(&state, axiom_before, "Int mul_zero");
}

/// Part of #2601: ring_nf closes `Int.ofNat 0 * a = Int.ofNat 0` for Int via Int.zero_mul.
#[test]
#[serial]
fn test_ring_nf_int_zero_mul() {
    reset_arith_counter();
    let (env, int) = int_identity_env();
    let a = int_var("a");

    let lhs = int_mul(int_zero(), a);
    let mut state = ProofState::new(env, make_eq(int, lhs, int_zero()));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close Int zero_mul annihilator goal");

    assert_ring_nf_int_clean(&state, axiom_before, "Int zero_mul");
}

// =============================================================================
// Distribution: Int.left_distrib / Int.right_distrib
// =============================================================================

/// Part of #2601: ring_nf closes `a * (b + c) = a * b + a * c` for Int.
#[test]
#[serial]
fn test_ring_nf_int_left_distrib() {
    reset_arith_counter();
    let (env, int) = int_identity_env();
    let a = int_var("a");
    let b = int_var("b");
    let c = int_var("c");

    let lhs = int_mul(a.clone(), int_add(b.clone(), c.clone()));
    let rhs = int_add(int_mul(a.clone(), b), int_mul(a, c));

    let mut state = ProofState::new(env, make_eq(int, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close Int left_distrib goal");

    assert_ring_nf_int_clean(&state, axiom_before, "Int left_distrib");
}

/// Part of #2601: ring_nf closes `(a + b) * c = a * c + b * c` for Int.
#[test]
#[serial]
fn test_ring_nf_int_right_distrib() {
    reset_arith_counter();
    let (env, int) = int_identity_env();
    let a = int_var("a");
    let b = int_var("b");
    let c = int_var("c");

    let lhs = int_mul(int_add(a.clone(), b.clone()), c.clone());
    let rhs = int_add(int_mul(a, c.clone()), int_mul(b, c));

    let mut state = ProofState::new(env, make_eq(int, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close Int right_distrib goal");

    assert_ring_nf_int_clean(&state, axiom_before, "Int right_distrib");
}
