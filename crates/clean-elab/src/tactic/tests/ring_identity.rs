// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Part of #2442: ring_nf identity axiom proof tests.
//! Verifies that ring_nf closes identity/annihilator goals without trustedArith.

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

fn ring_nf_identity_env() -> (Environment, Expr) {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas().unwrap();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in &["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }
    (env, nat)
}

/// Part of #2442: ring_nf closes `a + 0 = a` via Nat.add_zero without trustedArith.
#[test]
#[serial]
fn test_ring_nf_add_zero_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_identity_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Goal: Nat.add a Nat.zero = a
    let lhs = Expr::app(Expr::app(nat_add, a.clone()), zero);
    let mut state = ProofState::new(env, make_eq(nat, lhs, a));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close add_zero identity goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

/// Part of #2442: ring_nf closes `0 + a = a` via Nat.zero_add without trustedArith.
#[test]
#[serial]
fn test_ring_nf_zero_add_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_identity_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Goal: Nat.add Nat.zero a = a
    let lhs = Expr::app(Expr::app(nat_add, zero), a.clone());
    let mut state = ProofState::new(env, make_eq(nat, lhs, a));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close zero_add identity goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

/// Part of #2442: ring_nf closes `(a + 0) + b = a + b` via congruence + identity.
#[test]
#[serial]
fn test_ring_nf_add_zero_congr_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_identity_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Goal: (a + 0) + b = a + b
    let a_plus_zero = Expr::app(Expr::app(nat_add.clone(), a.clone()), zero);
    let lhs = Expr::app(Expr::app(nat_add.clone(), a_plus_zero), b.clone());
    let rhs = Expr::app(Expr::app(nat_add, a), b);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close congruence+identity goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

/// Part of #2442: ring_nf closes `a = a + 0` (reverse identity) via Eq.symm.
#[test]
#[serial]
fn test_ring_nf_reverse_add_zero_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_identity_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Goal: a = Nat.add a Nat.zero (reverse of add_zero)
    let rhs = Expr::app(Expr::app(nat_add, a.clone()), zero);
    let mut state = ProofState::new(env, make_eq(nat, a, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close reverse add_zero goal via Eq.symm");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

// --- Multiplicative identity axiom tests (mul_one, one_mul) ---

/// Part of #2442: ring_nf closes `a * 1 = a` via Nat.mul_one without trustedArith.
#[test]
#[serial]
fn test_ring_nf_mul_one_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_identity_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // Goal: Nat.mul a (Nat.succ Nat.zero) = a
    let lhs = Expr::app(Expr::app(nat_mul, a.clone()), one);
    let mut state = ProofState::new(env, make_eq(nat, lhs, a));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close mul_one identity goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

/// Part of #2442: ring_nf closes `1 * a = a` via Nat.one_mul without trustedArith.
#[test]
#[serial]
fn test_ring_nf_one_mul_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_identity_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // Goal: Nat.mul (Nat.succ Nat.zero) a = a
    let lhs = Expr::app(Expr::app(nat_mul, one), a.clone());
    let mut state = ProofState::new(env, make_eq(nat, lhs, a));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close one_mul identity goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

// --- Multiplicative annihilator tests (mul_zero, zero_mul) ---

/// Part of #2442: ring_nf closes `a * 0 = 0` via Nat.mul_zero without trustedArith.
#[test]
#[serial]
fn test_ring_nf_mul_zero_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_identity_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Goal: Nat.mul a Nat.zero = Nat.zero
    let lhs = Expr::app(Expr::app(nat_mul, a), zero.clone());
    let mut state = ProofState::new(env, make_eq(nat, lhs, zero));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close mul_zero annihilator goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

/// Part of #2442: ring_nf closes `0 * a = 0` via Nat.zero_mul without trustedArith.
#[test]
#[serial]
fn test_ring_nf_zero_mul_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_identity_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Goal: Nat.mul Nat.zero a = Nat.zero
    let lhs = Expr::app(Expr::app(nat_mul, zero.clone()), a);
    let mut state = ProofState::new(env, make_eq(nat, lhs, zero));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close zero_mul annihilator goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

/// Part of #2442: ring_nf closes `a = a * 1` (reverse mul_one) via Eq.symm.
#[test]
#[serial]
fn test_ring_nf_reverse_mul_one_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_identity_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // Goal: a = Nat.mul a (Nat.succ Nat.zero) (reverse of mul_one)
    let rhs = Expr::app(Expr::app(nat_mul, a.clone()), one);
    let mut state = ProofState::new(env, make_eq(nat, a, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close reverse mul_one goal via Eq.symm");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

/// Part of #2442: ring_nf closes `(a * 1) * b = a * b` via congruence + mul_one.
#[test]
#[serial]
fn test_ring_nf_mul_one_congr_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_identity_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // Goal: (a * 1) * b = a * b
    let a_mul_one = Expr::app(Expr::app(nat_mul.clone(), a.clone()), one);
    let lhs = Expr::app(Expr::app(nat_mul.clone(), a_mul_one), b.clone());
    let rhs = Expr::app(Expr::app(nat_mul, a), b);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close congruence+mul_one goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}
