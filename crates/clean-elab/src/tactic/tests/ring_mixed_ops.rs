// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Part of #2442: ring_nf mixed add/mul proof tests.
//! Verifies that ring_nf handles cross-operation expressions (add inside mul,
//! mul inside add) without trustedArith.

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

fn ring_nf_mixed_env() -> (Environment, Expr) {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas().unwrap();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in &["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }
    (env, nat)
}

fn assert_kernel_valid_closed_proof(state: &ProofState, context: &str) {
    let goal_ty = state
        .goal_type()
        .expect("completed proof state should retain the original goal type");
    let proof = state
        .closed_proof()
        .expect("completed proof state should expose a closed proof term");
    let tc = TypeChecker::new(state.env());
    assert!(
        tc.check_type(&proof, &goal_ty).is_ok(),
        "{context}: closed proof must type-check against the original goal"
    );
}

// --- Mul identity inside add chain ---

/// Part of #2442: ring_nf closes `(a * 1) + b = a + b` via congruence(mul_one) + add.
/// Tests cross-operation proof: mul identity elimination as a child of add.
#[test]
#[serial]
fn test_ring_nf_mul_one_inside_add_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_mixed_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // Goal: (a * 1) + b = a + b
    let a_mul_one = Expr::app(Expr::app(nat_mul, a.clone()), one);
    let lhs = Expr::app(Expr::app(nat_add.clone(), a_mul_one), b.clone());
    let rhs = Expr::app(Expr::app(nat_add, a), b);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close mul_one-inside-add goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_kernel_valid_closed_proof(&state, "mul_one inside add");
}

/// Part of #2442: ring_nf closes `a + (b * 1) = a + b` via congruence(mul_one) on rhs.
#[test]
#[serial]
fn test_ring_nf_mul_one_inside_add_rhs_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_mixed_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // Goal: a + (b * 1) = a + b
    let b_mul_one = Expr::app(Expr::app(nat_mul, b.clone()), one);
    let lhs = Expr::app(Expr::app(nat_add.clone(), a.clone()), b_mul_one);
    let rhs = Expr::app(Expr::app(nat_add, a), b);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close mul_one-inside-add-rhs goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_kernel_valid_closed_proof(&state, "mul_one inside add rhs");
}

// --- Add identity inside mul chain ---

/// Part of #2442: ring_nf closes `(a + 0) * b = a * b` via congruence(add_zero) + mul.
/// Tests cross-operation proof: add identity elimination as a child of mul.
#[test]
#[serial]
fn test_ring_nf_add_zero_inside_mul_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_mixed_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Goal: (a + 0) * b = a * b
    let a_plus_zero = Expr::app(Expr::app(nat_add, a.clone()), zero);
    let lhs = Expr::app(Expr::app(nat_mul.clone(), a_plus_zero), b.clone());
    let rhs = Expr::app(Expr::app(nat_mul, a), b);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close add_zero-inside-mul goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_kernel_valid_closed_proof(&state, "add_zero inside mul");
}

// --- Mul annihilator inside add chain ---

/// Part of #2442: ring_nf closes `a + (b * 0) = a` via add(congruence(mul_zero), add_zero).
/// Tests cross-operation proof: mul annihilator reduces to zero, then add identity.
#[test]
#[serial]
fn test_ring_nf_mul_zero_inside_add_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_mixed_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Goal: a + (b * 0) = a
    let b_mul_zero = Expr::app(Expr::app(nat_mul, b), zero);
    let lhs = Expr::app(Expr::app(nat_add, a.clone()), b_mul_zero);

    let mut state = ProofState::new(env, make_eq(nat, lhs, a));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close mul_zero-inside-add goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_kernel_valid_closed_proof(&state, "mul_zero inside add");
}

// --- Cross-operation with commutativity ---

/// Part of #2442: ring_nf closes `(b * a) + c = (a * b) + c` via
/// congruence(mul_comm) inside an add expression.
#[test]
#[serial]
fn test_ring_nf_mul_comm_inside_add_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_mixed_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);

    // Goal: (b * a) + c = (a * b) + c
    let ba = Expr::app(Expr::app(nat_mul.clone(), b.clone()), a.clone());
    let ab = Expr::app(Expr::app(nat_mul, a), b);
    let lhs = Expr::app(Expr::app(nat_add.clone(), ba), c.clone());
    let rhs = Expr::app(Expr::app(nat_add, ab), c);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close mul_comm-inside-add goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_kernel_valid_closed_proof(&state, "mul_comm inside add");
}

/// Part of #2442: ring_nf closes `(a + b) * 1 = a + b` via mul_one of an add expr.
/// Tests identity elimination where the surviving child is itself a compound expression.
#[test]
#[serial]
fn test_ring_nf_add_expr_times_one_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_mixed_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // Goal: (a + b) * 1 = a + b
    let a_plus_b = Expr::app(Expr::app(nat_add, a.clone()), b.clone());
    let lhs = Expr::app(Expr::app(nat_mul, a_plus_b.clone()), one);

    let mut state = ProofState::new(env, make_eq(nat, lhs, a_plus_b));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close (a+b)*1 = a+b goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_kernel_valid_closed_proof(&state, "add expr times one");
}

// --- Double identity elimination across operations ---

/// Part of #2442: ring_nf closes `(a * 1) + (b + 0) = a + b` via
/// double cross-operation identity elimination (mul_one on lhs, add_zero on rhs).
#[test]
#[serial]
fn test_ring_nf_double_identity_mixed_ops_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_mixed_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // Goal: (a * 1) + (b + 0) = a + b
    let a_mul_one = Expr::app(Expr::app(nat_mul, a.clone()), one);
    let b_plus_zero = Expr::app(Expr::app(nat_add.clone(), b.clone()), zero);
    let lhs = Expr::app(Expr::app(nat_add.clone(), a_mul_one), b_plus_zero);
    let rhs = Expr::app(Expr::app(nat_add, a), b);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close double-identity mixed-ops goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_kernel_valid_closed_proof(&state, "double identity mixed ops");
}

// --- Distributivity ---

/// Part of #2442: ring_nf closes `a * (b + c) = a * b + a * c` via Nat.left_distrib.
#[test]
#[serial]
fn test_ring_nf_left_distrib_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_mixed_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);

    // Goal: a * (b + c) = a * b + a * c
    let b_plus_c = Expr::app(Expr::app(nat_add.clone(), b.clone()), c.clone());
    let lhs = Expr::app(Expr::app(nat_mul.clone(), a.clone()), b_plus_c);
    let ab = Expr::app(Expr::app(nat_mul.clone(), a.clone()), b);
    let ac = Expr::app(Expr::app(nat_mul, a), c);
    let rhs = Expr::app(Expr::app(nat_add, ab), ac);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close left-distrib goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_kernel_valid_closed_proof(&state, "left distrib");
}

/// Part of #2442: ring_nf closes `(a + b) * c = a * c + b * c` via Nat.right_distrib.
#[test]
#[serial]
fn test_ring_nf_right_distrib_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_mixed_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);

    // Goal: (a + b) * c = a * c + b * c
    let a_plus_b = Expr::app(Expr::app(nat_add.clone(), a.clone()), b.clone());
    let lhs = Expr::app(Expr::app(nat_mul.clone(), a_plus_b), c.clone());
    let ac = Expr::app(Expr::app(nat_mul.clone(), a), c.clone());
    let bc = Expr::app(Expr::app(nat_mul, b), c);
    let rhs = Expr::app(Expr::app(nat_add, ac), bc);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close right-distrib goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_kernel_valid_closed_proof(&state, "right distrib");
}

/// Part of #2442: ring_nf closes `(a + b) * (a + b) = a*a + a*b + b*a + b*b`
/// via nested distributivity plus cross-term commutativity normalization.
#[test]
#[serial]
fn test_ring_nf_nested_distrib_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_mixed_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);

    // Goal: (a + b) * (a + b) = a*a + a*b + b*a + b*b
    let a_plus_b = Expr::app(Expr::app(nat_add.clone(), a.clone()), b.clone());
    let lhs = Expr::app(Expr::app(nat_mul.clone(), a_plus_b.clone()), a_plus_b);

    let aa = Expr::app(Expr::app(nat_mul.clone(), a.clone()), a.clone());
    let ab = Expr::app(Expr::app(nat_mul.clone(), a.clone()), b.clone());
    let ba = Expr::app(Expr::app(nat_mul.clone(), b.clone()), a.clone());
    let bb = Expr::app(Expr::app(nat_mul.clone(), b.clone()), b);
    let rhs = Expr::app(
        Expr::app(
            nat_add.clone(),
            Expr::app(Expr::app(nat_add.clone(), aa), ab),
        ),
        Expr::app(Expr::app(nat_add, ba), bb),
    );

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close nested-distrib goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_kernel_valid_closed_proof(&state, "nested distrib");
}
