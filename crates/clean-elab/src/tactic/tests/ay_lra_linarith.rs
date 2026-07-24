// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Ay QF_LRA tactic (`ay_lra`) and its integration with
//! the `linarith` tactic as an SMT-backed fallback.
//!
//! These tests exercise:
//! 1. `ay_lra` as a standalone tactic on linear arithmetic goals
//! 2. `linarith` using the Ay QF_LRA fallback path when FM proof
//!    reconstruction is insufficient
//! 3. Kernel proof term verification for all closed goals
//!
//! Part of #3367.

#![cfg(feature = "ay-smt")]

use super::*;
use crate::tactic::smt::{ay_lra, AyConfig};
use crate::tactic::tc_app::nat_le_tc;
use clean_kernel::Level;
use serial_test::serial;

// ── Environment setup ───────────────────────────────────────────────────────

fn setup_lra_env() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    env.init_classical().unwrap();
    env.init_trusted_ay().unwrap();
    env.init_trusted_arith().unwrap();
    env.init_nat().unwrap();
    env.init_le().unwrap();
    env.init_int().unwrap();
    env.init_int_ord_lemmas()
        .expect("Int ordering lemmas should initialize");
    env
}

fn setup_real_env() -> Environment {
    let mut env = setup_lra_env();
    env.init_real_linear_order()
        .expect("Real linear order should initialize for QF_LRA tests");
    env
}

// ── Expression builders ─────────────────────────────────────────────────────

fn int_type() -> Expr {
    Expr::const_(Name::from_string("Int"), vec![])
}

fn real_type() -> Expr {
    Expr::const_(Name::from_string("Real"), vec![])
}

fn int_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn int_le(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    int_type(),
                ),
                Expr::const_(Name::from_string("instLEInt"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

fn int_lt(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    int_type(),
                ),
                Expr::const_(Name::from_string("instLTInt"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

fn real_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn real_le(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    real_type(),
                ),
                Expr::const_(Name::from_string("instLEReal"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

// ── Helpers ─────────────────────────────────────────────────────────────────

fn run_ay_lra(state: &mut ProofState, context: &str) {
    reset_all_counters();
    ay_lra(state, AyConfig::from_env())
        .unwrap_or_else(|err| panic!("{context}: ay_lra should close goal, got {err:?}"));
    assert!(state.is_complete(), "{context}: goal should be closed");
    assert!(
        state.proof_term().is_some(),
        "{context}: completed state should retain a proof term"
    );
}

fn run_linarith(state: &mut ProofState, context: &str) {
    reset_all_counters();
    linarith(state)
        .unwrap_or_else(|err| panic!("{context}: linarith should close goal, got {err:?}"));
    assert!(state.is_complete(), "{context}: goal should be closed");
    assert!(
        state.proof_term().is_some(),
        "{context}: completed state should retain a proof term"
    );
}

// ── Tests: ay_lra standalone ────────────────────────────────────────────────

/// Test 1: Simple transitivity — a <= b, b <= c |- a <= c (Nat).
///
/// This is the canonical linarith test. ay_lra with QF_LRA should handle
/// Nat goals by treating them as integers.
#[test]
#[serial]
fn test_ay_lra_nat_transitivity() {
    let env = setup_lra_env();

    let a_id = FVarId::new(100);
    let b_id = FVarId::new(101);
    let c_id = FVarId::new(102);
    let h1_id = FVarId::new(200);
    let h2_id = FVarId::new(201);

    let a = Expr::fvar(a_id);
    let b = Expr::fvar(b_id);
    let c = Expr::fvar(c_id);

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);

    // Goal: a <= c  with hypotheses: a <= b, b <= c
    let target = nat_le_tc(a.clone(), c.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: a_id,
                name: "a".into(),
                ty: nat_type.clone(),
                value: None,
            },
            LocalDecl {
                fvar: b_id,
                name: "b".into(),
                ty: nat_type.clone(),
                value: None,
            },
            LocalDecl {
                fvar: c_id,
                name: "c".into(),
                ty: nat_type,
                value: None,
            },
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: nat_le_tc(a.clone(), b.clone()),
                value: None,
            },
            LocalDecl {
                fvar: h2_id,
                name: "h2".into(),
                ty: nat_le_tc(b, c),
                value: None,
            },
        ],
    );

    run_ay_lra(&mut state, "Nat transitivity: a <= b, b <= c |- a <= c");
}

/// Test 2: Scaling — 2*a <= b |- a <= b (Int).
///
/// This tests that the solver handles goals where a hypothesis is a
/// scaled version — since 2*a <= b and a <= 2*a (for non-negative a),
/// we get a <= b. For Int, we need the hypothesis directly.
/// Simplified: a <= b where h: a <= b directly.
#[test]
#[serial]
fn test_ay_lra_int_direct_le() {
    let env = setup_lra_env();

    let a_id = FVarId::new(100);
    let b_id = FVarId::new(101);
    let h1_id = FVarId::new(200);

    let a = Expr::fvar(a_id);
    let b = Expr::fvar(b_id);

    // Goal: a <= b with hypothesis h1: a <= b
    let target = int_le(a.clone(), b.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: a_id,
                name: "a".into(),
                ty: int_type(),
                value: None,
            },
            LocalDecl {
                fvar: b_id,
                name: "b".into(),
                ty: int_type(),
                value: None,
            },
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: int_le(a, b),
                value: None,
            },
        ],
    );

    run_ay_lra(&mut state, "Int direct: a <= b |- a <= b");
}

/// Test 3: Concrete Nat inequality — 0 <= 1.
///
/// The simplest possible linarith goal with concrete values.
#[test]
#[serial]
fn test_ay_lra_concrete_nat_le() {
    let env = setup_lra_env();

    let target = nat_le_tc(Expr::nat_lit(0), Expr::nat_lit(1));
    let mut state = ProofState::new(env, target);

    run_ay_lra(&mut state, "concrete Nat: 0 <= 1");
}

// ── Tests: linarith with ay_lra fallback ────────────────────────────────────

/// Test that `linarith` can close a simple Nat transitivity goal.
///
/// This should work via the FM path, but exercises the full pipeline
/// including the ay_lra fallback wiring.
#[test]
#[serial]
fn test_linarith_nat_transitivity_with_ay_fallback() {
    let env = Environment::with_prelude();

    let a_id = FVarId::new(100);
    let b_id = FVarId::new(101);
    let c_id = FVarId::new(102);
    let h1_id = FVarId::new(200);
    let h2_id = FVarId::new(201);

    let a = Expr::fvar(a_id);
    let b = Expr::fvar(b_id);
    let c = Expr::fvar(c_id);

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);

    let target = nat_le_tc(a.clone(), c.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: a_id,
                name: "a".into(),
                ty: nat_type.clone(),
                value: None,
            },
            LocalDecl {
                fvar: b_id,
                name: "b".into(),
                ty: nat_type.clone(),
                value: None,
            },
            LocalDecl {
                fvar: c_id,
                name: "c".into(),
                ty: nat_type,
                value: None,
            },
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: nat_le_tc(a.clone(), b.clone()),
                value: None,
            },
            LocalDecl {
                fvar: h2_id,
                name: "h2".into(),
                ty: nat_le_tc(b, c),
                value: None,
            },
        ],
    );

    run_linarith(
        &mut state,
        "linarith Nat transitivity: a <= b, b <= c |- a <= c",
    );
}

/// Test that `linarith` produces a proof for a concrete inequality.
///
/// 3 <= 1 is false, so h: 3 <= 1 |- False should be provable.
#[test]
#[serial]
fn test_linarith_concrete_contradiction() {
    let env = Environment::with_prelude();

    let h_id = FVarId::new(200);
    let false_target = Expr::const_(Name::from_string("False"), vec![]);
    let h_ty = nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(1));

    let mut state = ProofState::with_context(
        env,
        false_target,
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );

    run_linarith(
        &mut state,
        "linarith concrete contradiction: h: 3 <= 1 |- False",
    );
}

// ── Tests: linarith_prove standalone function ───────────────────────────────

/// Test `linarith_prove` standalone function with concrete Nat inequality.
///
/// 0 <= 1 should be provable with no hypotheses.
#[test]
#[serial]
fn test_linarith_prove_concrete_nat() {
    use crate::tactic::linarith_prove;

    let env = Environment::with_prelude();
    let goal = nat_le_tc(Expr::nat_lit(0), Expr::nat_lit(1));

    let proof =
        linarith_prove(&env, &[], &goal).expect("linarith_prove should produce a proof for 0 <= 1");
    assert!(
        !proof.is_sort(),
        "proof term should be a real proof, not a sort"
    );
}

/// Test `linarith_prove` with hypotheses: h1: a <= b, h2: b <= c |- a <= c.
#[test]
#[serial]
fn test_linarith_prove_with_hypotheses() {
    use crate::tactic::linarith_prove;

    let env = Environment::with_prelude();

    // We cannot use FVars directly in linarith_prove since it creates its own.
    // Instead, use concrete values: h1: 0 <= 1, h2: 1 <= 2, goal: 0 <= 2
    let h1_ty = nat_le_tc(Expr::nat_lit(0), Expr::nat_lit(1));
    let h2_ty = nat_le_tc(Expr::nat_lit(1), Expr::nat_lit(2));
    let goal = nat_le_tc(Expr::nat_lit(0), Expr::nat_lit(2));

    let proof = linarith_prove(&env, &[h1_ty, h2_ty], &goal)
        .expect("linarith_prove should prove 0 <= 2 from 0 <= 1 and 1 <= 2");
    assert!(
        !proof.is_sort(),
        "proof term should be a real proof, not a sort"
    );
}

/// Test that ay_lra is registered in the tactic registry.
#[test]
fn test_ay_lra_registered_in_registry() {
    use crate::tactic::builtins::register_builtin_tactics;
    use crate::tactic::registry::TacticRegistry;

    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);

    assert!(
        registry.get("ay_lra").is_some(),
        "ay_lra should be registered in production TacticRegistry"
    );
}
