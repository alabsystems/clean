// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Nat.pow` folds only up to Lean's exponent cap.
//!
//! Lean's `reduce_pow` returns none when the exponent is above
//! `ReducePowMaxExp = 1 << 24`, for every base (`type_checker.cpp`,
//! v4.30.0-rc2); its kernel then δ-unfolds `Nat.pow` and fails with deep
//! recursion, so pinned Lean refuses `Nat.pow 1 16777217 = 1 := rfl` and
//! `Nat.pow 0 16777217 = 0 := rfl` (`replay_forged/ReplayForgedPowCap`,
//! measured 2026-10-23). `checked_pow_big` folded `0^n` and `1^n` before
//! any exponent bound, so Clean admitted both. The exponent `2^24` itself
//! still folds in both kernels.

use super::*;
use crate::env::Environment;
use crate::expr::BigNat;
use crate::level::Level;
use crate::tc::{TypeChecker, TypeError};

const CAP: u64 = 1 << 24;

fn nat(v: u64) -> Expr {
    Expr::nat_lit(v)
}

fn pow(base: u64, exp: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.pow"), vec![]),
        [nat(base), nat(exp)],
    )
}

/// `@Eq.refl Nat rhs : @Eq Nat lhs rhs`, checked by the kernel.
fn rfl_checks(env: &Environment, lhs: Expr, rhs: Expr) -> Result<(), TypeError> {
    let one = Level::succ(Level::zero());
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
        [nat_ty.clone(), lhs, rhs.clone()],
    );
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![one]),
        [nat_ty, rhs],
    );
    TypeChecker::new(env).check_type(&refl, &eq)
}

/// The fold itself: Lean's boundary is inclusive, and every base declines
/// above it.
#[test]
fn test_checked_pow_big_declines_above_leans_exponent_cap_for_every_base() {
    for base in [0, 1] {
        assert_eq!(
            BigNat::Small(base).checked_pow_big(&BigNat::Small(CAP)),
            Some(BigNat::Small(base)),
            "{base}^(2^24) folds, as in Lean"
        );
        assert_eq!(
            BigNat::Small(base).checked_pow_big(&BigNat::Small(CAP + 1)),
            None,
            "{base}^(2^24+1) declines, as in Lean"
        );
        assert_eq!(
            BigNat::Small(base).checked_pow_big(&BigNat::Big(vec![0, 1])),
            None,
            "{base}^(2^64) declines"
        );
    }
    assert_eq!(
        BigNat::Small(0).checked_pow_big(&BigNat::Small(0)),
        Some(BigNat::Small(1))
    );
    assert_eq!(
        BigNat::Small(2).checked_pow_big(&BigNat::Small(10)),
        Some(BigNat::Small(1024))
    );
}

/// The kernel: the forged `rfl` equations Lean refuses are refused, and the
/// controls at the cap and below it are admitted. Past the declined fold the
/// application stays stuck (the literal exponent is a large recursion count,
/// `native_nat_binop_grind_stuck`), so the refusal is a type mismatch, not a
/// δ-walk of 2^24 steps.
#[test]
fn test_nat_pow_rfl_above_the_exponent_cap_is_refused() {
    let env = Environment::with_prelude();
    rfl_checks(&env, pow(1, CAP), nat(1)).expect("1^(2^24) = 1 by the fold");
    rfl_checks(&env, pow(0, CAP), nat(0)).expect("0^(2^24) = 0 by the fold");
    rfl_checks(&env, pow(2, 10), nat(1024)).expect("2^10 = 1024 by the fold");
    for (base, value) in [(1, 1), (0, 0)] {
        let err = rfl_checks(&env, pow(base, CAP + 1), nat(value))
            .expect_err("Lean refuses this equation (deep recursion)");
        assert!(
            matches!(err, TypeError::TypeMismatch { .. }),
            "{base}^(2^24+1): refused as a mismatch of the stuck application: {err:?}"
        );
    }
}

fn bin(op: &str, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(op), vec![]), [a, b])
}

/// KNOWN GAP (R140's open half; the 2026-10-24 review's K1), pinned so it
/// fails loudly the day it closes. Lean's `reduce_bin_nat_op` and
/// `reduce_pow` whnf both operands before folding, so an outer `Nat.mul`/
/// `Nat.add`/`Nat.sub`/`Nat.pow` over `1^(2^24+1)` recurses into the over-cap
/// power and pinned Lean refuses each equation below (deep recursion;
/// `replay_forged/ReplayForgedPowCapOuter`, measured 2026-10-24). Clean's
/// kernel leaves the inner power stuck and δ-reduces the outer operation by
/// its recursion on the SECOND argument, which never inspects the stuck
/// operand, so it admits each. Every admitted equation is true.
#[test]
fn test_outer_nat_op_over_an_over_cap_pow_is_admitted_known_gap() {
    let env = Environment::with_prelude();
    let over = || pow(1, CAP + 1);
    let cases = [
        ("Nat.mul", bin("Nat.mul", over(), nat(0)), nat(0)),
        ("Nat.add", bin("Nat.add", over(), nat(0)), over()),
        ("Nat.sub", bin("Nat.sub", over(), nat(0)), over()),
        ("Nat.pow", bin("Nat.pow", over(), nat(0)), nat(1)),
    ];
    for (op, lhs, rhs) in cases {
        rfl_checks(&env, lhs, rhs).unwrap_or_else(|err| {
            panic!("{op} over 1^(2^24+1): the gap closed — flip this pin to a refusal: {err:?}")
        });
    }
}
