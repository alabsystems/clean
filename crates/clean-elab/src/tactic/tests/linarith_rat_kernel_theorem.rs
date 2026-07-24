// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rat kernel-theorem tests for `linarith_kernel_theorem` (#3367).
//!
//! Validates that linarith produces kernel-verified proof terms for
//! Rat-valued inequality chains via the `Int.cast_le_prop` downcast in
//! `arith_linarith_rat_downcast`. Split from `arith_linarith_kernel.rs`
//! to keep that file under the 500-line limit.

use clean_kernel::env::Environment;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Expr;

use crate::tactic::arith_linarith_kernel::{linarith_kernel_theorem, LinarithKernelError};

/// Build `@LE.le.{0} Rat instLERat lhs rhs`.
fn make_rat_le_tc(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    Expr::const_(Name::from_string("Rat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLERat"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

/// Build a Rat literal as `Rat.ofInt (Int.ofNat n)` — the form
/// recognized by the linarith constraint parser.
fn rat_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Rat.ofInt"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(n),
        ),
    )
}

fn false_expr() -> Expr {
    Expr::const_(Name::from_string("False"), vec![])
}

fn init_rat_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_rat_ord()
        .expect("Rat ordering lemmas should initialize");
    env.init_cast_simp_lemmas()
        .expect("Rat.ofInt cast lemmas should initialize");
    env
}

/// Rat contradiction: FM detects UNSAT and Rat→Int downcast produces a
/// kernel-verified False proof via `Int.cast_le_prop` (#3367).
#[test]
fn test_kernel_theorem_rat_contradiction() {
    let mut env = init_rat_env();
    let h_ty = make_rat_le_tc(rat_of_nat(5), rat_of_nat(3));
    let goal = false_expr();

    let result = linarith_kernel_theorem(&mut env, "rat_contra_5_3", &[h_ty], &goal);
    assert!(
        result.is_ok(),
        "linarith_kernel_theorem should succeed for Rat 5 <= 3 |- False, got: {result:?}"
    );

    let info = env
        .get_const(&Name::from_string("rat_contra_5_3"))
        .expect("theorem should register");
    assert!(
        info.value.is_some(),
        "Rat contradiction theorem should have a proof value (not an axiom)"
    );
}

/// Two-hypothesis Rat Farkas chain: `Rat.le_trans` chain proof downcast to
/// `Int.le` via `Int.cast_le_prop`, then concrete contradiction close via
/// `Int.NonNeg` case analysis. Covers the #3367 acceptance criterion
/// "Farkas-style combinations of linear inequalities over Rat".
#[test]
fn test_kernel_theorem_rat_two_hyp_chain() {
    let mut env = init_rat_env();
    let h1_ty = make_rat_le_tc(rat_of_nat(7), rat_of_nat(4));
    let h2_ty = make_rat_le_tc(rat_of_nat(4), rat_of_nat(1));
    let goal = false_expr();

    let result = linarith_kernel_theorem(&mut env, "rat_chain_7_4_1", &[h1_ty, h2_ty], &goal);
    assert!(
        result.is_ok(),
        "linarith_kernel_theorem should succeed for Rat 2-hyp chain, got: {result:?}"
    );

    let info = env
        .get_const(&Name::from_string("rat_chain_7_4_1"))
        .expect("theorem should register");
    assert!(
        info.value.is_some(),
        "Rat chain theorem should have a proof value (not an axiom)"
    );
}

/// Farkas accumulation over Rat (3 hypotheses forming a chain).
///
/// h1 : 9 ≤ 6, h2 : 6 ≤ 3, h3 : 3 ≤ 0  →  9 ≤ 0, contradiction.
/// Exercises the same `Rat.le_trans` chain builder as the 2-hyp case plus
/// additional chain steps, validating the N-hypothesis Farkas path.
#[test]
fn test_kernel_theorem_rat_three_hyp_farkas_chain() {
    let mut env = init_rat_env();
    let h1_ty = make_rat_le_tc(rat_of_nat(9), rat_of_nat(6));
    let h2_ty = make_rat_le_tc(rat_of_nat(6), rat_of_nat(3));
    let h3_ty = make_rat_le_tc(rat_of_nat(3), rat_of_nat(0));
    let goal = false_expr();

    let result =
        linarith_kernel_theorem(&mut env, "rat_farkas_3hyp", &[h1_ty, h2_ty, h3_ty], &goal);
    assert!(
        result.is_ok(),
        "linarith_kernel_theorem should succeed for Rat 3-hyp Farkas chain, got: {result:?}"
    );
}

/// Rat proof quality: the kernel proof must not reference `sorry` or
/// `trustedArith`. The downcast transports via `Int.cast_le_prop` and
/// `Eq.mpr`, both foundational.
#[test]
fn test_kernel_theorem_rat_no_sorry_no_trusted_arith() {
    fn contains_const(expr: &Expr, name_str: &str) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => name == &Name::from_string(name_str),
            ExprKind::App(f, a) => contains_const(f, name_str) || contains_const(a, name_str),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                contains_const(ty, name_str) || contains_const(body, name_str)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                contains_const(ty, name_str)
                    || contains_const(val, name_str)
                    || contains_const(body, name_str)
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                contains_const(inner, name_str)
            }
            _ => false,
        }
    }

    let mut env = init_rat_env();
    let h_ty = make_rat_le_tc(rat_of_nat(5), rat_of_nat(3));
    let goal = false_expr();

    let proof = linarith_kernel_theorem(&mut env, "rat_soundness", &[h_ty], &goal)
        .expect("Rat downcast should produce a kernel-verified proof");

    assert!(
        !contains_const(&proof, "sorry"),
        "Rat proof must not contain sorry"
    );
    assert!(
        !contains_const(&proof, "trustedArith"),
        "Rat proof must not contain trustedArith"
    );
}

/// Satisfiable Rat inequality must not be provable — guards against false
/// positives in the Rat path.
#[test]
fn test_kernel_theorem_rat_rejects_satisfiable() {
    let mut env = init_rat_env();
    // 1 <= 3 is satisfiable; no contradiction.
    let h_ty = make_rat_le_tc(rat_of_nat(1), rat_of_nat(3));
    let goal = false_expr();

    let result = linarith_kernel_theorem(&mut env, "rat_sat", &[h_ty], &goal);
    assert!(
        matches!(result, Err(LinarithKernelError::TacticFailed(_))),
        "satisfiable Rat constraint must not produce a False proof, got: {result:?}"
    );
}
