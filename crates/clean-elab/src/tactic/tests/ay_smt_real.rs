// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Strict `QF_LRA` end-to-end tactic canaries for elaborated Lean `Real` terms.
//!
//! These tests exercise the full tactic path (translate → ay solve → proof
//! reconstruct → kernel type-check) for Lean-elaborated Real expressions under
//! `VerifyStrict + QF_LRA`. They pin the composition of `#2793`–`#2796`
//! translator fixes: `Real.ofNat`, `Real.ofInt`, `Real.add`, `Real.sub`,
//! `Real.mul`, and bounded `Real.div` on the zero-trust lane.
//!
//! Part of #2798.

#![cfg(feature = "ay-smt")]

use super::*;
use crate::tactic::smt::{ay_smt, AyConfig, SmtVerifyPolicy};
use clean_auto::bridge::ay_contract::AyLogic;
use clean_kernel::Level;
use serial_test::serial;

// ── Environment ──────────────────────────────────────────────────────────────

fn setup_ay_real_env() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    env.init_classical().unwrap();
    env.init_trusted_ay().unwrap();
    env.init_trusted_arith().unwrap();
    env.init_int_ord_lemmas()
        .expect("Int ordering lemmas should initialize for Real SMT downcast recovery");
    env.init_real_linear_order()
        .expect("Real linear order should initialize for strict QF_LRA tactic canaries");
    env
}

// ── Expression builders ──────────────────────────────────────────────────────

fn real_type() -> Expr {
    Expr::const_(Name::from_string("Real"), vec![])
}

/// `Real.ofNat n` — constructor-form coercion from Nat literal.
fn real_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

/// `Real.ofInt (Int.ofNat n)` — constructor-form coercion from non-negative Int.
fn real_of_int_of_nat(n: u64) -> Expr {
    let int_expr = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    );
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    )
}

/// `@LT.lt.{0} Real instLTReal lhs rhs` — typeclass-resolved strict less-than.
fn real_lt(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    real_type(),
                ),
                Expr::const_(Name::from_string("instLTReal"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

/// `@LE.le.{0} Real instLEReal lhs rhs` — typeclass-resolved less-or-equal.
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

/// `Real.add lhs rhs` — direct 2-arg addition.
fn real_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.add"), vec![]), lhs),
        rhs,
    )
}

/// `Real.sub lhs rhs` — direct 2-arg subtraction.
fn real_sub(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.sub"), vec![]), lhs),
        rhs,
    )
}

/// `Real.mul lhs rhs` — direct 2-arg multiplication.
fn real_mul(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.mul"), vec![]), lhs),
        rhs,
    )
}

/// `Real.div lhs rhs` — direct 2-arg division (bounded: concrete denominator only).
fn real_div(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.div"), vec![]), lhs),
        rhs,
    )
}

// ── Test harness ─────────────────────────────────────────────────────────────

fn strict_qf_lra_config() -> AyConfig {
    AyConfig::default()
        .with_verify_policy(SmtVerifyPolicy::VerifyStrict)
        .with_logic(AyLogic::QfLra)
}

/// Run `ay_smt` under `VerifyStrict + QF_LRA` and assert zero-trust closure.
fn run_strict_qf_lra_canary(state: &mut ProofState, context: &str) {
    reset_all_counters();
    ay_smt(state, strict_qf_lra_config())
        .unwrap_or_else(|err| panic!("{context}: strict QF_LRA canary should close, got {err:?}"));
    assert!(state.is_complete(), "{context}: goal should be closed");
    assert!(
        state.proof_term().is_some(),
        "{context}: completed state should retain a proof term"
    );

    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "{context}: strict QF_LRA canary must not record trustedAy debt"
    );
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "{context}: strict QF_LRA canary must not record trustedArith debt"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "{context}: strict QF_LRA canary must not fall back to sorry"
    );
}

// ── Tests ────────────────────────────────────────────────────────────────────

/// Solver-level diagnostic: confirm `SmtSolver::prove` handles concrete
/// Real.ofNat expressions under the strict QF_LRA configuration.
///
/// Exercises the translate → ay solve path at the solver level (bypasses
/// the tactic-level proof selection and trust budget enforcement).
/// Pins #2794 (Real.ofNat lowering).
#[test]
#[serial]
fn test_ay_smt_real_diagnostic_solver_translate_and_prove() {
    use crate::tactic::smt::SmtSolver;

    let config = strict_qf_lra_config();
    let target = real_lt(real_of_nat(0), real_of_nat(1));

    let mut solver = SmtSolver::from_config(&config, AyLogic::QfLra);
    let outcome = solver
        .prove(&target)
        .expect("ay should handle Real.ofNat 0 < Real.ofNat 1");
    assert!(
        outcome.proved,
        "ay should prove Real.ofNat 0 < Real.ofNat 1"
    );
}

/// Hypothesis forwarding for concrete `Real.ofNat` comparison:
/// h : Real.ofNat 0 < Real.ofNat 1 ⊢ Real.ofNat 0 < Real.ofNat 1.
///
/// Simplest canary: exercises `Real.ofNat` lowering + Real LT instance
/// on the strict zero-trust QF_LRA lane with hypothesis-based closure.
/// Pins #2794 (Real.ofNat lowering).
#[test]
#[serial]
fn test_ay_smt_real_strict_qf_lra_concrete_ofnat_lt() {
    let env = setup_ay_real_env();
    let h_fvar = FVarId::new(107);
    let prop = real_lt(real_of_nat(0), real_of_nat(1));
    let mut state = ProofState::with_context(
        env,
        prop.clone(),
        vec![LocalDecl {
            fvar: h_fvar,
            name: "h".to_string(),
            ty: prop,
            value: None,
        }],
    );
    run_strict_qf_lra_canary(&mut state, "Real.ofNat 0 < Real.ofNat 1");
}

/// Hypothesis forwarding with `Real.add` + `Real.ofNat`:
/// x : Real, h : x < Real.add x (Real.ofNat 1) ⊢ x < Real.add x (Real.ofNat 1).
///
/// Pins #2794 (Real.ofNat) and #2796 (Real.add) on the strict zero-trust
/// tactic path with symbolic variable registration.
#[test]
#[serial]
fn test_ay_smt_real_strict_qf_lra_add_ofnat_hypothesis_forwarding() {
    let env = setup_ay_real_env();
    let x_fvar = FVarId::new(100);
    let h_fvar = FVarId::new(101);
    let x = Expr::fvar(x_fvar);

    // x < (x + Real.ofNat 1)
    let prop = real_lt(x.clone(), real_add(x, real_of_nat(1)));

    let mut state = ProofState::with_context(
        env,
        prop.clone(),
        vec![
            LocalDecl {
                fvar: x_fvar,
                name: "x".to_string(),
                ty: real_type(),
                value: None,
            },
            LocalDecl {
                fvar: h_fvar,
                name: "h".to_string(),
                ty: prop,
                value: None,
            },
        ],
    );
    run_strict_qf_lra_canary(&mut state, "Real.add + Real.ofNat hypothesis forwarding");
}

/// Transitivity with `Real.sub` + `Real.ofNat`:
/// x : Real, h1 : x ≤ Real.sub x (Real.ofNat 0), h2 : Real.sub x (Real.ofNat 0) ≤ x
/// ⊢ x ≤ x.
///
/// Pins #2796 (Real.sub lowering) on the strict zero-trust tactic path.
#[test]
#[serial]
fn test_ay_smt_real_strict_qf_lra_sub_transitivity() {
    let env = setup_ay_real_env();
    let x_fvar = FVarId::new(102);
    let h1_fvar = FVarId::new(103);
    let h2_fvar = FVarId::new(104);
    let x = Expr::fvar(x_fvar);

    // (x - Real.ofNat 0) — should equal x semantically
    let x_sub_0 = real_sub(x.clone(), real_of_nat(0));
    let h1_ty = real_le(x.clone(), x_sub_0.clone()); // x ≤ (x - 0)
    let h2_ty = real_le(x_sub_0, x.clone()); // (x - 0) ≤ x
    let target = real_le(x.clone(), x.clone()); // x ≤ x

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: x_fvar,
                name: "x".to_string(),
                ty: real_type(),
                value: None,
            },
            LocalDecl {
                fvar: h1_fvar,
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_fvar,
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );
    run_strict_qf_lra_canary(&mut state, "Real.sub transitivity");
}

/// Hypothesis-based with `Real.mul` + `Real.div` + `Real.ofInt(Int.ofNat _)`:
/// x : Real, h : Real.mul (Real.div (Real.ofInt (Int.ofNat 1)) (Real.ofNat 2)) x ≤ x
/// ⊢ Real.mul (Real.div (Real.ofInt (Int.ofNat 1)) (Real.ofNat 2)) x ≤ x.
///
/// Pins #2794 (Real.ofInt), #2795 (Real.div), and #2796 (Real.mul) on the
/// strict zero-trust tactic path.
#[test]
#[serial]
fn test_ay_smt_real_strict_qf_lra_mul_div_ofint_hypothesis() {
    let env = setup_ay_real_env();
    let x_fvar = FVarId::new(105);
    let h_fvar = FVarId::new(106);
    let x = Expr::fvar(x_fvar);

    // half = Real.div (Real.ofInt (Int.ofNat 1)) (Real.ofNat 2)
    let half = real_div(real_of_int_of_nat(1), real_of_nat(2));
    // (half * x) ≤ x
    let prop = real_le(real_mul(half, x.clone()), x.clone());

    let mut state = ProofState::with_context(
        env,
        prop.clone(),
        vec![
            LocalDecl {
                fvar: x_fvar,
                name: "x".to_string(),
                ty: real_type(),
                value: None,
            },
            LocalDecl {
                fvar: h_fvar,
                name: "h".to_string(),
                ty: prop,
                value: None,
            },
        ],
    );
    run_strict_qf_lra_canary(
        &mut state,
        "Real.mul + Real.div + Real.ofInt hypothesis forwarding",
    );
}
