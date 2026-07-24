// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ring normalize round-trip tests (Prover verification of W2-1986)
//! Verifies: make_add/make_mul/make_neg produce multi-arg forms that
//! ring_normalize parses back correctly, and that the full round-trip
//! (normalize → to_expr → normalize) is idempotent.

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::expr::ExprKind;
use serial_test::serial;

#[test]
fn test_ring_normalize_roundtrip_hadd_6arg() {
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // make_add produces: @HAdd.hAdd Nat Nat Nat instHAddNat a b
    let add_expr = make_add(&a, &b, &mut state);

    let head = add_expr.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "HAdd.hAdd"),
        "make_add head should be HAdd.hAdd, got {:?}",
        head.kind()
    );

    let norm = ring_normalize(&add_expr);
    match &norm {
        RingExpr::Add(terms) => {
            assert_eq!(terms.len(), 2, "a + b should have 2 terms");
            assert!(terms.contains(&RingExpr::Var("a".to_string())));
            assert!(terms.contains(&RingExpr::Var("b".to_string())));
        }
        _ => panic!(
            "ring_normalize of 6-arg HAdd should produce Add, got {:?}",
            norm
        ),
    }
}

#[test]
fn test_ring_normalize_roundtrip_hmul_6arg() {
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let mul_expr = make_mul(&a, &b, &mut state);

    let head = mul_expr.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "HMul.hMul"),
        "make_mul head should be HMul.hMul"
    );

    let norm = ring_normalize(&mul_expr);
    match &norm {
        RingExpr::Mul(terms) => {
            assert_eq!(terms.len(), 2, "a * b should have 2 terms");
            assert!(terms.contains(&RingExpr::Var("a".to_string())));
            assert!(terms.contains(&RingExpr::Var("b".to_string())));
        }
        _ => panic!(
            "ring_normalize of 6-arg HMul should produce Mul, got {:?}",
            norm
        ),
    }
}

#[test]
fn test_ring_normalize_roundtrip_neg_3arg() {
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));

    let a = Expr::const_(Name::from_string("a"), vec![]);

    let neg_expr = make_neg(&a, &mut state);

    let head = neg_expr.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "Neg.neg"),
        "make_neg head should be Neg.neg"
    );

    let norm = ring_normalize(&neg_expr);
    match &norm {
        RingExpr::Neg(inner) => {
            assert_eq!(
                **inner,
                RingExpr::Var("a".to_string()),
                "Neg should wrap Var(a)"
            );
        }
        _ => panic!(
            "ring_normalize of 3-arg Neg should produce Neg, got {:?}",
            norm
        ),
    }
}

#[test]
fn test_ring_normalize_full_roundtrip_add() {
    // Full round-trip: make_add → ring_normalize → ring_expr_to_expr → ring_normalize
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let add_expr = make_add(&a, &b, &mut state);
    let norm1 = ring_normalize(&add_expr);
    let reconstructed = ring_expr_to_expr(&norm1, &mut state);
    let norm2 = ring_normalize(&reconstructed);

    assert_eq!(
        norm1, norm2,
        "round-trip normalize->to_expr->normalize should be idempotent"
    );
}

#[test]
fn test_ring_normalize_full_roundtrip_nested() {
    // Full round-trip with nested expression: (a + b) * c
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    let add_ab = make_add(&a, &b, &mut state);
    let mul_expr = make_mul(&add_ab, &c, &mut state);

    let norm1 = ring_normalize(&mul_expr);
    let reconstructed = ring_expr_to_expr(&norm1, &mut state);
    let norm2 = ring_normalize(&reconstructed);

    assert_eq!(norm1, norm2, "nested round-trip should be idempotent");
}

fn ring_nf_commutativity_state() -> ProofState {
    let mut env = Environment::with_prelude();
    // Ring axiom proofs need Nat.add_comm etc. Part of #2442.
    env.init_nat_arith_lemmas().unwrap();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let lhs = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            a.clone(),
        ),
        b.clone(),
    );
    let rhs = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), b),
        a,
    );

    ProofState::new(env, make_eq(nat, lhs, rhs))
}

fn assert_closed_proof_type_checks(state: &ProofState, check_ctx: clean_kernel::LocalContext) {
    let closed_proof = state
        .closed_proof()
        .expect("completed ring_nf state should preserve closed_proof() extraction");
    let goal_ty = state
        .goal_type()
        .expect("completed ring_nf state should retain the original goal type");
    let tc = TypeChecker::with_context(state.env(), check_ctx);
    assert!(
        tc.check_type(&closed_proof, &goal_ty).is_ok(),
        "ring_nf closed proof must type-check against the original goal type"
    );
}

#[test]
#[serial]
fn test_ring_nf_commutativity_closes_by_ring_axiom_no_trusted_arith() {
    reset_arith_counter();
    let mut state = ring_nf_commutativity_state();
    let check_goal = state
        .current_goal()
        .expect("commutativity state should have a goal")
        .clone();
    let check_ctx = state.build_local_ctx(&check_goal);
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "proof state should start with no trusted fallbacks"
    );
    let axiom_before = axiom_snapshot();

    // Part of #2442: ring_nf should close commutativity goals directly using
    // Nat.add_comm, without trustedArith or target replacement.
    ring_nf(&mut state).expect("ring_nf should close the commutativity goal via ring axiom");

    // No trustedArith should be used — the proof is via Nat.add_comm.
    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "ring_nf commutativity should NOT increment the global arith counter"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "ring_nf commutativity should NOT increment the per-state trusted count"
    );

    // The goal should be fully closed after ring_nf (no separate rfl needed).
    assert!(
        state.is_complete(),
        "ring_nf should close the commutativity goal directly"
    );
    assert!(
        state.proof_term().is_some(),
        "ring_nf axiom proof must preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "ring_nf axiom proof must preserve closed_proof() extraction"
    );
    assert_closed_proof_type_checks(&state, check_ctx);
}

/// Part of #2442: ring_nf closes associativity goals via Nat.add_assoc
/// without trustedArith.
#[test]
#[serial]
fn test_ring_nf_associativity_closes_by_ring_axiom_no_trusted_arith() {
    reset_arith_counter();
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

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);

    // Goal: (a + b) + c = a + (b + c)
    let ab = Expr::app(Expr::app(nat_add.clone(), a.clone()), b.clone());
    let bc = Expr::app(Expr::app(nat_add.clone(), b), c.clone());
    let lhs = Expr::app(Expr::app(nat_add.clone(), ab), c);
    let rhs = Expr::app(Expr::app(nat_add, a), bc);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let check_goal = state
        .current_goal()
        .expect("associativity state should have a goal")
        .clone();
    let check_ctx = state.build_local_ctx(&check_goal);
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close the associativity goal via ring axiom");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "ring_nf associativity should NOT increment the global arith counter"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "ring_nf associativity should NOT use trustedArith"
    );
    assert!(
        state.is_complete(),
        "ring_nf should close the associativity goal directly"
    );
    assert_closed_proof_type_checks(&state, check_ctx);
}

/// Helper: create an environment with Nat variables a, b, c and ring axiom lemmas.
fn ring_nf_three_var_env() -> (Environment, Expr, Expr, Expr) {
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
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    (env, a, b, c)
}

/// Part of #2442: ring_nf closes congruence goals (comm inside a subexpression)
/// via congrArg + Nat.add_comm, without trustedArith.
///
/// Goal: (b + a) + c = (a + b) + c
/// Proof: congrArg (Nat.add · c) (Nat.add_comm b a)
#[test]
#[serial]
fn test_ring_nf_congr_comm_left_no_trusted_arith() {
    reset_arith_counter();
    let (env, a, b, c) = ring_nf_three_var_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);

    // Goal: (b + a) + c = (a + b) + c
    let ba = Expr::app(Expr::app(nat_add.clone(), b.clone()), a.clone());
    let ab = Expr::app(Expr::app(nat_add.clone(), a), b);
    let lhs = Expr::app(Expr::app(nat_add.clone(), ba), c.clone());
    let rhs = Expr::app(Expr::app(nat_add, ab), c);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let check_goal = state
        .current_goal()
        .expect("left-congruence state should have a goal")
        .clone();
    let check_ctx = state.build_local_ctx(&check_goal);
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close congruence-comm goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "ring_nf congruence-comm should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_closed_proof_type_checks(&state, check_ctx);
}

/// Part of #2442: ring_nf closes reverse-associativity goals via Eq.symm of
/// Nat.add_assoc, without trustedArith.
///
/// Goal: a + (b + c) = (a + b) + c
/// Proof: Eq.symm (Nat.add_assoc a b c)
#[test]
#[serial]
fn test_ring_nf_reverse_assoc_no_trusted_arith() {
    reset_arith_counter();
    let (env, a, b, c) = ring_nf_three_var_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);

    // Goal: a + (b + c) = (a + b) + c  (reverse of assoc)
    let bc = Expr::app(Expr::app(nat_add.clone(), b.clone()), c.clone());
    let ab = Expr::app(Expr::app(nat_add.clone(), a.clone()), b);
    let lhs = Expr::app(Expr::app(nat_add.clone(), a), bc);
    let rhs = Expr::app(Expr::app(nat_add, ab), c);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let check_goal = state
        .current_goal()
        .expect("reverse-associativity state should have a goal")
        .clone();
    let check_ctx = state.build_local_ctx(&check_goal);
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close reverse-assoc goal via Eq.symm");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "ring_nf reverse-assoc should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_closed_proof_type_checks(&state, check_ctx);
}

/// Part of #2442: ring_nf closes comm+assoc chain goals via Eq.trans,
/// without trustedArith.
///
/// Goal: (b + a) + c = a + (b + c)
/// Proof: Eq.trans (congrArg _ (Nat.add_comm b a)) (Nat.add_assoc a b c)
///   or: Eq.trans (Nat.add_comm on left) (Nat.add_assoc)
#[test]
#[serial]
fn test_ring_nf_comm_then_assoc_chain_no_trusted_arith() {
    reset_arith_counter();
    let (env, a, b, c) = ring_nf_three_var_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);

    // Goal: (b + a) + c = a + (b + c)
    let ba = Expr::app(Expr::app(nat_add.clone(), b.clone()), a.clone());
    let bc = Expr::app(Expr::app(nat_add.clone(), b), c.clone());
    let lhs = Expr::app(Expr::app(nat_add.clone(), ba), c);
    let rhs = Expr::app(Expr::app(nat_add, a), bc);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let check_goal = state
        .current_goal()
        .expect("comm-then-assoc state should have a goal")
        .clone();
    let check_ctx = state.build_local_ctx(&check_goal);
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close comm+assoc chain goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "ring_nf comm+assoc chain should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_closed_proof_type_checks(&state, check_ctx);
}

/// Part of #2442: ring_nf closes congruence on right subexpression goals
/// via congrArg, without trustedArith.
///
/// Goal: a + (c + b) = a + (b + c)
/// Proof: congrArg (Nat.add a) (Nat.add_comm c b)
#[test]
#[serial]
fn test_ring_nf_congr_comm_right_no_trusted_arith() {
    reset_arith_counter();
    let (env, a, b, c) = ring_nf_three_var_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);

    // Goal: a + (c + b) = a + (b + c)
    let cb = Expr::app(Expr::app(nat_add.clone(), c.clone()), b.clone());
    let bc = Expr::app(Expr::app(nat_add.clone(), b), c);
    let lhs = Expr::app(Expr::app(nat_add.clone(), a.clone()), cb);
    let rhs = Expr::app(Expr::app(nat_add, a), bc);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let check_goal = state
        .current_goal()
        .expect("right-congruence state should have a goal")
        .clone();
    let check_ctx = state.build_local_ctx(&check_goal);
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close right-congruence-comm goal");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "ring_nf right-congruence-comm should NOT use trustedArith"
    );
    assert_eq!(state.trusted_axiom_count(), 0);
    assert!(state.is_complete(), "goal should be fully closed");
    assert_closed_proof_type_checks(&state, check_ctx);
}

// ---- False-positive regression tests for contains("add")/contains("neg") fragility ----
// Bug: ring_normalize_binop uses op_str.contains("add") which matches non-operator
// constants like Nat.add_le_add, AddCommGroup.toAdd, instAddCommGroupInt.
// The correct approach (used by polyrith.rs and algebra.rs) is exact string matching.
//
// These tests assert the CURRENT (buggy) behavior so they serve as canaries:
// when F2 is fixed (contains→exact matching), these assertions will FAIL,
// and the fixing Worker must update them to assert correct behavior.
// See #2078 F2.

#[test]
fn test_ring_normalize_non_operator_add_le_add_not_treated_as_addition() {
    // Nat.add_le_add is a PROOF lemma, not an addition operator.
    // CORRECT behavior: should return Unknown (not Add).
    // CURRENT (buggy): returns Add([Var("h1"), Var("h2")]) due to contains("add").
    let add_le_add = Expr::const_(Name::from_string("Nat.add_le_add"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);
    let h1 = Expr::const_(Name::from_string("h1"), vec![]);
    let h2 = Expr::const_(Name::from_string("h2"), vec![]);

    // Build: ((((((Nat.add_le_add a) b) c) d) h1) h2)
    let expr = Expr::apps(add_le_add, [a, b, c, d, h1, h2]);

    let norm = ring_normalize(&expr);
    // Assert BUGGY behavior — when F2 is fixed, change to assert !matches!(Add).
    assert!(
        matches!(&norm, RingExpr::Add(terms) if terms.len() == 2),
        "CANARY: expected Add (known bug #2078 F2) but got {norm:?}. \
         If F2 was fixed, update this assertion to: !matches!(norm, RingExpr::Add(_))"
    );
}

#[test]
fn test_ring_normalize_non_operator_negsucc_not_treated_as_negation() {
    // Int.negSucc is a CONSTRUCTOR, not a negation operator.
    // CORRECT behavior: should return Unknown (not Neg).
    // CURRENT (buggy): returns Neg(Var("n")) due to contains("neg").
    let neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let expr = Expr::app(neg_succ, n);

    let norm = ring_normalize(&expr);
    // Assert BUGGY behavior — when F2 is fixed, change to assert !matches!(Neg).
    assert!(
        matches!(&norm, RingExpr::Neg(_)),
        "CANARY: expected Neg (known bug #2078 F2) but got {norm:?}. \
         If F2 was fixed, update this assertion to: !matches!(norm, RingExpr::Neg(_))"
    );
}

#[test]
fn test_ring_normalize_non_operator_add_comm_not_treated_as_addition() {
    // Nat.add_comm is a PROOF (commutativity lemma), not addition.
    // CORRECT behavior: should return Unknown (not Add).
    // CURRENT (buggy): returns Add due to contains("add").
    let add_comm = Expr::const_(Name::from_string("Nat.add_comm"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let expr = Expr::apps(add_comm, [a, b]);

    let norm = ring_normalize(&expr);
    // Assert BUGGY behavior — when F2 is fixed, change to assert !matches!(Add).
    assert!(
        matches!(&norm, RingExpr::Add(_)),
        "CANARY: expected Add (known bug #2078 F2) but got {norm:?}. \
         If F2 was fixed, update this assertion to: !matches!(norm, RingExpr::Add(_))"
    );
}

// ---- Constant power normalization (tactic-divergence: ring vs Lean 4) ----
// Lean 4's `ring` closes `(2 : Nat) ^ 3 = 8`, but Clean's `ring_normalize`
// previously kept `Pow(Const(2), 3)` symbolic — distinct from `Const(8)` — so
// the fast-path equality gate failed and `ring` returned ArithmeticFailed even
// though the goal is definitionally true (the kernel reduces `Nat.pow 2 3`).
// Fix: fold `Const(b) ^ n` to `Const(b^n)` (and `_ ^ 0` to `Const(1)`).

#[test]
fn test_ring_normalize_const_pow_evaluates_to_const() {
    // 2 ^ 3 should normalize to the constant 8 (matching Lean's `ring`).
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));
    let pow = make_pow(&Expr::nat_lit(2), &Expr::nat_lit(3), &mut state);
    let norm = ring_normalize(&pow);
    assert_eq!(
        norm,
        RingExpr::Const(8),
        "2 ^ 3 should fold to Const(8), got {norm:?}"
    );
}

#[test]
fn test_ring_normalize_pow_zero_evaluates_to_one() {
    // a ^ 0 should normalize to 1 for any base (universal ring identity).
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let pow = make_pow(&a, &Expr::nat_lit(0), &mut state);
    let norm = ring_normalize(&pow);
    assert_eq!(
        norm,
        RingExpr::Const(1),
        "a ^ 0 should fold to Const(1), got {norm:?}"
    );
}

#[test]
fn test_ring_normalize_symbolic_pow_stays_symbolic() {
    // Negative case: a ^ 2 (non-constant base, exponent > 1) must NOT collapse
    // to a constant — it stays a symbolic Pow so we never fabricate a value.
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let pow = make_pow(&a, &Expr::nat_lit(2), &mut state);
    let norm = ring_normalize(&pow);
    assert_eq!(
        norm,
        RingExpr::Pow(Box::new(RingExpr::Var("a".to_string())), 2),
        "a ^ 2 should stay symbolic, got {norm:?}"
    );
}

#[test]
fn test_ring_normalize_const_pow_overflow_stays_symbolic() {
    // Negative case: an exponent large enough to overflow u64 must keep the
    // power symbolic rather than wrapping to a wrong constant.
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));
    let big = make_pow(&Expr::nat_lit(2), &Expr::nat_lit(200), &mut state);
    let norm = ring_normalize(&big);
    assert_eq!(
        norm,
        RingExpr::Pow(Box::new(RingExpr::Const(2)), 200),
        "2 ^ 200 overflows u64 and must stay symbolic, got {norm:?}"
    );
}

/// Positive end-to-end: `ring` now closes `Nat.pow 2 3 = 8` (Lean 4 parity).
/// The proof is the kernel `rfl` discharged by `Nat.pow` literal reduction —
/// zero domain axioms, fully kernel-checkable.
#[test]
#[serial]
fn test_ring_closes_constant_nat_pow_goal() {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas().unwrap();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Goal: Nat.pow 2 3 = 8
    let lhs = Expr::apps(
        Expr::const_(Name::from_string("Nat.pow"), vec![]),
        [Expr::nat_lit(2), Expr::nat_lit(3)],
    );
    let mut state = ProofState::new(env, make_eq(nat, lhs, Expr::nat_lit(8)));
    let check_goal = state
        .current_goal()
        .expect("constant-pow state should have a goal")
        .clone();
    let check_ctx = state.build_local_ctx(&check_goal);

    ring(&mut state).expect("ring should close `Nat.pow 2 3 = 8` (Lean 4 parity)");

    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "constant-pow ring proof must not use trustedArith"
    );
    assert!(state.is_complete(), "goal should be fully closed");
    assert_closed_proof_type_checks(&state, check_ctx);
}

/// Negative end-to-end: `ring` must NOT close a false constant-power goal.
/// `Nat.pow 2 3 = 9` is false, so ring must report failure (no over-firing).
#[test]
#[serial]
fn test_ring_rejects_false_constant_nat_pow_goal() {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas().unwrap();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Goal: Nat.pow 2 3 = 9  (FALSE: 2^3 = 8 ≠ 9)
    let lhs = Expr::apps(
        Expr::const_(Name::from_string("Nat.pow"), vec![]),
        [Expr::nat_lit(2), Expr::nat_lit(3)],
    );
    let mut state = ProofState::new(env, make_eq(nat, lhs, Expr::nat_lit(9)));

    let result = ring(&mut state);
    assert!(
        result.is_err(),
        "ring must reject the false goal `Nat.pow 2 3 = 9`, got {result:?}"
    );
    assert!(
        !state.is_complete(),
        "false goal must remain open after ring fails"
    );
}
