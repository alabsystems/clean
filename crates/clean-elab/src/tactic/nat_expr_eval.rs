// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared Nat expression evaluator.
//!
//! Evaluates ground Nat expressions to `Option<u64>` using checked arithmetic.
//! This is the single production implementation — `norm.rs` and
//! `arith_linarith_close.rs` both import from here.
//!
//! Extracted from duplicated copies per design #2542.

use clean_kernel::{Expr, ExprKind};

use crate::stack_safe;

/// Evaluate a natural number expression to a concrete `u64` value.
///
/// # Supported heads
///
/// - Nat literal
/// - `Nat.zero`
/// - `Nat.one` / `1`
/// - `Nat.succ`
/// - `Nat.add`, `HAdd.hAdd`, `Add.add` (addition)
/// - `Nat.mul`, `HMul.hMul`, `Mul.mul` (multiplication)
/// - `Nat.sub`, `HSub.hSub`, `Sub.sub` (saturating subtraction)
/// - `Nat.pow`, `HPow.hPow`, `Pow.pow` (exponentiation)
/// - `Nat.mod`, `HMod.hMod`, `Mod.mod` (modulo, `n % 0 = n`)
/// - `Nat.div`, `HDiv.hDiv`, `Div.div` (truncating division, `n / 0 = 0`)
/// - `Nat.gcd` (Euclidean GCD, `gcd 0 y = y`, `gcd x 0 = x`)
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed expression
/// ENSURES: Returns `Some(n)` iff `expr` is a ground Nat expression evaluable to `n`
/// ENSURES: Returns `None` for symbolic expressions, non-Nat types, or overflow
/// ENSURES: All arithmetic is checked (`checked_add`, `checked_mul`, `checked_pow`)
/// ENSURES: Nat subtraction uses `saturating_sub` (Lean Nat semantics)
/// ENSURES: Nat mod/div follow Lean 4 conventions: `n % 0 = n`, `n / 0 = 0`
/// ENSURES: Returns `None` when exponent exceeds `u32::MAX`
/// ENSURES: Recursion terminates via `stack_safe` guard
pub(crate) fn eval_nat_expr(expr: &Expr) -> Option<u64> {
    stack_safe(|| match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => n.to_u64(),

        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            if name_str == "Nat.zero" {
                Some(0)
            } else if name_str == "Nat.one" || name_str == "1" {
                Some(1)
            } else {
                None
            }
        }

        ExprKind::App(_, _) => {
            let args = expr.get_app_args();
            if let ExprKind::Const(op_name, _) = expr.get_app_fn().kind() {
                let op_str = op_name.to_string();

                // Unary: Nat.succ
                if op_str == "Nat.succ" {
                    let arg = args.last()?;
                    return eval_nat_expr(arg)?.checked_add(1);
                }

                // Numeric literal: `@OfNat.ofNat Nat n inst`. Lean elaborates a
                // surface numeral like the `2` in `2 * n` as this application,
                // whose kernel value for `Nat` is exactly the numeral `n` (the
                // `instOfNatNat n` instance is the identity `⟨n⟩`). Peel it so
                // linear-coefficient extraction (and every other `eval_nat_expr`
                // caller) sees the raw value; without this, `2 * n` reads as a
                // non-linear product and `omega`/`linarith` on Nat goals like
                // `n + n = 2 * n` wrongly reports "could not extract linear
                // constraints". The Nat-type guard keeps a stray `OfNat.ofNat`
                // at another type from being mis-valued here; the kernel re-check
                // in `close_goal` remains the soundness gate regardless.
                if op_str == "OfNat.ofNat" && args.len() == 3 {
                    if let ExprKind::Const(ty_name, _) = args[0].kind() {
                        if ty_name.to_string() == "Nat" {
                            return eval_nat_expr(args[1]);
                        }
                    }
                    return None;
                }

                if args.len() >= 2 {
                    let l = eval_nat_expr(args[args.len() - 2])?;
                    let r = eval_nat_expr(args[args.len() - 1])?;

                    match op_str.as_str() {
                        // Addition
                        "Nat.add" | "HAdd.hAdd" | "Add.add" => {
                            return l.checked_add(r);
                        }
                        // Multiplication
                        "Nat.mul" | "HMul.hMul" | "Mul.mul" => {
                            return l.checked_mul(r);
                        }
                        // Subtraction (saturating per Lean Nat semantics)
                        "Nat.sub" | "HSub.hSub" | "Sub.sub" => {
                            return Some(l.saturating_sub(r));
                        }
                        // Exponentiation
                        "Nat.pow" | "HPow.hPow" | "Pow.pow" => {
                            let exp = u32::try_from(r).ok()?;
                            return l.checked_pow(exp);
                        }
                        // Modulo (Lean 4 convention: `n % 0 = n`). `checked_rem`
                        // returns `None` on a zero divisor; Lean defines that
                        // case as the dividend. The kernel's native `Nat.mod`
                        // reducer agrees, so a `rfl`/witness close still
                        // type-checks.
                        "Nat.mod" | "HMod.hMod" | "Mod.mod" => {
                            return Some(l.checked_rem(r).unwrap_or(l));
                        }
                        // Truncating division (Lean 4 convention: `n / 0 = 0`).
                        // `checked_div` returns `None` on a zero divisor; Lean
                        // defines that case as `0`.
                        "Nat.div" | "HDiv.hDiv" | "Div.div" => {
                            return Some(l.checked_div(r).unwrap_or(0));
                        }
                        // Euclidean GCD. Lean 4's `Nat.gcd` is the bare prelude
                        // head (no `HGcd`/typeclass form), defined so that
                        // `gcd 0 y = y`, `gcd x 0 = x`, `gcd x y = gcd y x`.
                        // The kernel's native `reduce_nat` reducer computes this
                        // with the identical Euclidean loop (`nat_gcd` in
                        // `tc/reduction/nat.rs`), so a `rfl`/`reduce_eq` close or
                        // a constructive `Nat.le` comparison witness built from
                        // this value stays kernel-checkable byte-for-byte.
                        "Nat.gcd" => {
                            return Some(nat_gcd(l, r));
                        }
                        _ => {}
                    }
                }
            }

            None
        }

        _ => None,
    })
}

/// Euclidean GCD on `u64`, matching Lean 4's `Nat.gcd` and the kernel's native
/// `reduce_nat` reducer (`nat_gcd` in `tc/reduction/nat.rs`).
///
/// `gcd 0 0 = 0`, `gcd 0 y = y`, `gcd x 0 = x`. No overflow is possible — the
/// result never exceeds `max(a, b)`.
fn nat_gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}
