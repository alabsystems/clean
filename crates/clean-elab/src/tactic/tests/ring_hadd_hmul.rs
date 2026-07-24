// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Part of #3368: ring_nf kernel-verified proof tests for HAdd.hAdd / HMul.hMul
//! (typeclass-based operations from Lean 4).
//!
//! Verifies that ring_nf produces kernel-checkable proofs for goals expressed
//! using HAdd.hAdd and HMul.hMul, with abstract ring axioms (add_comm,
//! add_assoc, mul_comm, mul_assoc, left_distrib, right_distrib).
//!
//! # Kernel-level expression form (#3368)
//!
//! The prelude registers `HAdd.hAdd` as a 3-level constant with signature
//! `{α β γ : Type*} → [inst : HAdd α β γ] → α → β → γ` (6 args). Earlier
//! versions of this file built expressions as `Expr::app(Expr::app(HAdd.hAdd[], a), b)`
//! which passed 0 levels and 2 args — the kernel type-checker rejected the
//! referenced `HAdd.hAdd` const at axiom registration time with
//! `LevelCountMismatch { expected: 3, got: 0 }`.
//!
//! The fix routes every `a + b` / `a * b` construction through [`hadd_nat`] /
//! [`hmul_nat`] which build fully-applied `@HAdd.hAdd.{0,0,0} Nat Nat Nat
//! instHAddNat a b` forms. The ring proof surface's `get_app_fn()` peels
//! prefix args, so this remains compatible with the surface dispatcher.

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

/// Build `@Eq.{1} Nat lhs rhs` for the test environment.
fn eq_nat(nat: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat.clone(), lhs, rhs],
    )
}

/// Build `@HAdd.hAdd.{0,0,0} Nat Nat Nat instHAddNat a b` (6-arg, 3-level).
///
/// Matches the fully-applied form produced by elaboration of `a + b` for Nat.
/// Required so the kernel type-checker accepts axiom types that reference
/// `HAdd.hAdd` (Part of #3368).
fn hadd_nat(a: Expr, b: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instHAddNat"), vec![]);
    let hadd = Expr::const_(
        Name::from_string("HAdd.hAdd"),
        vec![Level::zero(), Level::zero(), Level::zero()],
    );
    Expr::apps(hadd, [nat.clone(), nat.clone(), nat, inst, a, b])
}

/// Build `@HMul.hMul.{0,0,0} Nat Nat Nat instHMulNat a b` (6-arg, 3-level).
///
/// Required so the kernel type-checker accepts axiom types that reference
/// `HMul.hMul` (Part of #3368).
fn hmul_nat(a: Expr, b: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instHMulNat"), vec![]);
    let hmul = Expr::const_(
        Name::from_string("HMul.hMul"),
        vec![Level::zero(), Level::zero(), Level::zero()],
    );
    Expr::apps(hmul, [nat.clone(), nat.clone(), nat, inst, a, b])
}

/// Register a binary commutativity axiom: `∀ a b : Nat, op a b = op b a`.
///
/// `op_app` builds the fully-applied operator expression (`hadd_nat` or `hmul_nat`).
fn add_comm_axiom(
    env: &mut Environment,
    nat: &Expr,
    axiom_name: &str,
    op_app: &dyn Fn(Expr, Expr) -> Expr,
) {
    let (a, b) = (Expr::bvar(1), Expr::bvar(0));
    let lhs = op_app(a.clone(), b.clone());
    let rhs = op_app(b, a);
    let ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), eq_nat(nat, lhs, rhs)),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(axiom_name),
        level_params: vec![],
        type_: ty,
    })
    .unwrap();
}

/// Register a binary associativity axiom: `∀ a b c, op (op a b) c = op a (op b c)`.
fn add_assoc_axiom(
    env: &mut Environment,
    nat: &Expr,
    axiom_name: &str,
    op_app: &dyn Fn(Expr, Expr) -> Expr,
) {
    let (a, b, c) = (Expr::bvar(2), Expr::bvar(1), Expr::bvar(0));
    let ab = op_app(a.clone(), b.clone());
    let lhs = op_app(ab, c.clone());
    let bc = op_app(b, c);
    let rhs = op_app(a, bc);
    let ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, nat.clone(), eq_nat(nat, lhs, rhs)),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(axiom_name),
        level_params: vec![],
        type_: ty,
    })
    .unwrap();
}

/// Register left distributivity: `∀ a b c, mul a (add b c) = add (mul a b) (mul a c)`.
fn add_left_distrib_axiom(env: &mut Environment, nat: &Expr) {
    let (a, b, c) = (Expr::bvar(2), Expr::bvar(1), Expr::bvar(0));
    let bc = hadd_nat(b.clone(), c.clone());
    let lhs = hmul_nat(a.clone(), bc);
    let ab = hmul_nat(a.clone(), b);
    let ac = hmul_nat(a, c);
    let rhs = hadd_nat(ab, ac);
    let ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, nat.clone(), eq_nat(nat, lhs, rhs)),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("left_distrib"),
        level_params: vec![],
        type_: ty,
    })
    .unwrap();
}

/// Register right distributivity: `∀ a b c, mul (add a b) c = add (mul a c) (mul b c)`.
fn add_right_distrib_axiom(env: &mut Environment, nat: &Expr) {
    let (a, b, c) = (Expr::bvar(2), Expr::bvar(1), Expr::bvar(0));
    let ab = hadd_nat(a.clone(), b.clone());
    let lhs = hmul_nat(ab, c.clone());
    let ac = hmul_nat(a, c.clone());
    let bc = hmul_nat(b, c);
    let rhs = hadd_nat(ac, bc);
    let ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, nat.clone(), eq_nat(nat, lhs, rhs)),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("right_distrib"),
        level_params: vec![],
        type_: ty,
    })
    .unwrap();
}

/// Set up an environment with HAdd.hAdd/HMul.hMul expressions and abstract
/// ring axioms (add_comm, add_assoc, etc.) registered as standalone constants.
///
/// The abstract axiom names match the Semiring typeclass fields that ring_nf
/// looks up in the proof surface (ring_proof_surface.rs).
fn ring_nf_hadd_env() -> (Environment, Expr) {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas()
        .expect("nat arith lemmas should init");
    // Register instHMulNat so hmul_nat references resolve in the kernel.
    env.init_nat_hmul_inst()
        .expect("Nat HMul instance should initialize");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    for name in &["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }

    add_comm_axiom(&mut env, &nat, "add_comm", &hadd_nat);
    add_assoc_axiom(&mut env, &nat, "add_assoc", &hadd_nat);
    add_comm_axiom(&mut env, &nat, "mul_comm", &hmul_nat);
    add_assoc_axiom(&mut env, &nat, "mul_assoc", &hmul_nat);
    add_left_distrib_axiom(&mut env, &nat);
    add_right_distrib_axiom(&mut env, &nat);

    (env, nat)
}

// --- HAdd.hAdd commutativity ---

/// Part of #3368: ring_nf closes `HAdd.hAdd a b = HAdd.hAdd b a` via add_comm.
#[test]
#[serial]
fn test_ring_nf_hadd_comm_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_hadd_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Goal: HAdd.hAdd a b = HAdd.hAdd b a
    let lhs = hadd_nat(a.clone(), b.clone());
    let rhs = hadd_nat(b, a);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close HAdd commutativity goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

// --- HAdd.hAdd associativity ---

/// Part of #3368: ring_nf closes `HAdd.hAdd (HAdd.hAdd a b) c = HAdd.hAdd a (HAdd.hAdd b c)`.
#[test]
#[serial]
fn test_ring_nf_hadd_assoc_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_hadd_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Goal: (a + b) + c = a + (b + c)
    let ab = hadd_nat(a.clone(), b.clone());
    let bc = hadd_nat(b, c.clone());
    let lhs = hadd_nat(ab, c);
    let rhs = hadd_nat(a, bc);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close HAdd associativity goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

// --- HMul.hMul commutativity ---

/// Part of #3368: ring_nf closes `HMul.hMul a b = HMul.hMul b a` via mul_comm.
#[test]
#[serial]
fn test_ring_nf_hmul_comm_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_hadd_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Goal: HMul.hMul a b = HMul.hMul b a
    let lhs = hmul_nat(a.clone(), b.clone());
    let rhs = hmul_nat(b, a);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close HMul commutativity goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

// --- HMul.hMul associativity ---

/// Part of #3368: ring_nf closes HMul.hMul associativity.
#[test]
#[serial]
fn test_ring_nf_hmul_assoc_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_hadd_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Goal: (a * b) * c = a * (b * c)
    let ab = hmul_nat(a.clone(), b.clone());
    let bc = hmul_nat(b, c.clone());
    let lhs = hmul_nat(ab, c);
    let rhs = hmul_nat(a, bc);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close HMul associativity goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

// --- Left distributivity ---

/// Part of #3368: ring_nf closes `HMul.hMul a (HAdd.hAdd b c) = HAdd.hAdd (HMul.hMul a b) (HMul.hMul a c)`.
#[test]
#[serial]
fn test_ring_nf_hadd_hmul_left_distrib_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_hadd_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Goal: a * (b + c) = a*b + a*c
    let b_plus_c = hadd_nat(b.clone(), c.clone());
    let lhs = hmul_nat(a.clone(), b_plus_c);
    let ab = hmul_nat(a.clone(), b);
    let ac = hmul_nat(a, c);
    let rhs = hadd_nat(ab, ac);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close HMul left-distrib goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

// --- Right distributivity ---

/// Part of #3368: ring_nf closes `HMul.hMul (HAdd.hAdd a b) c = HAdd.hAdd (HMul.hMul a c) (HMul.hMul b c)`.
#[test]
#[serial]
fn test_ring_nf_hadd_hmul_right_distrib_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_hadd_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Goal: (a + b) * c = a*c + b*c
    let a_plus_b = hadd_nat(a.clone(), b.clone());
    let lhs = hmul_nat(a_plus_b, c.clone());
    let ac = hmul_nat(a, c.clone());
    let bc = hmul_nat(b, c);
    let rhs = hadd_nat(ac, bc);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close HMul right-distrib goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

// --- Congruence: comm inside sub-expression ---

/// Part of #3368: ring_nf closes `HAdd.hAdd (HAdd.hAdd b a) c = HAdd.hAdd (HAdd.hAdd a b) c`
/// via congruence + add_comm.
#[test]
#[serial]
fn test_ring_nf_hadd_congr_comm_no_trusted_arith() {
    reset_arith_counter();
    let (env, nat) = ring_nf_hadd_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Goal: (b + a) + c = (a + b) + c
    let ba = hadd_nat(b.clone(), a.clone());
    let ab = hadd_nat(a, b);
    let lhs = hadd_nat(ba, c.clone());
    let rhs = hadd_nat(ab, c);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close HAdd congr-comm goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
}

// --- Ring normalization: basic `ring` tactic (rfl-based) ---

/// Part of #3368: `ring` tactic closes `HAdd.hAdd a b = HAdd.hAdd b a` via normalization + rfl.
/// This tests the simpler `ring` tactic (not `ring_nf`) which works by normalizing
/// both sides to the same RingExpr and then using rfl.
#[test]
fn test_ring_hadd_comm_rfl() {
    let (env, nat) = ring_nf_hadd_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let lhs = hadd_nat(a.clone(), b.clone());
    let rhs = hadd_nat(b, a);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));

    // The `ring` tactic normalizes both sides and closes with rfl if they match.
    ring(&mut state).expect("ring should close HAdd commutativity via rfl");
    assert!(state.is_complete(), "goal should be fully closed");
}
