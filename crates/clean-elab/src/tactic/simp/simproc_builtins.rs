// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Built-in simproc implementations for Nat arithmetic.
//!
//! Each simproc evaluates ground expressions of a specific head constant.
//! All built-in Nat simprocs produce `proof: None` because ground Nat
//! computations are definitionally equal in the kernel.
//!
//! Bool and Prop simprocs are in [`super::simproc_builtins_bool`].

use clean_kernel::name::Name;
use clean_kernel::Expr;

use crate::tactic::core::{Goal, ProofState};
use crate::tactic::nat_expr_eval::eval_nat_expr;

use super::simproc::{Simproc, SimprocResult, SimprocSet};
use super::types::SimpResult;

/// Build a Nat literal expression from a u64 value.
fn mk_nat_lit(n: u64) -> Expr {
    Expr::nat_lit(n)
}

/// Register built-in Nat arithmetic simprocs into the given set.
///
/// ENSURES: Registers simprocs for add, mul, pow, sub, succ, gcd, mod, div
pub(crate) fn register_nat_arith(set: &mut SimprocSet) {
    // Nat.reduceAdd — matches on Nat.add, HAdd.hAdd, Add.add
    for disc in &["Nat.add", "HAdd.hAdd", "Add.add"] {
        set.register(Simproc {
            name: Name::from_string("Nat.reduceAdd"),
            discriminant: Name::from_string(disc),
            proc: simproc_nat_reduce_add,
            priority: 1000,
        });
    }

    // Nat.reduceMul — matches on Nat.mul, HMul.hMul, Mul.mul
    for disc in &["Nat.mul", "HMul.hMul", "Mul.mul"] {
        set.register(Simproc {
            name: Name::from_string("Nat.reduceMul"),
            discriminant: Name::from_string(disc),
            proc: simproc_nat_reduce_mul,
            priority: 1000,
        });
    }

    // Nat.reducePow — matches on Nat.pow, HPow.hPow, Pow.pow
    for disc in &["Nat.pow", "HPow.hPow", "Pow.pow"] {
        set.register(Simproc {
            name: Name::from_string("Nat.reducePow"),
            discriminant: Name::from_string(disc),
            proc: simproc_nat_reduce_pow,
            priority: 1000,
        });
    }

    // Nat.reduceSub — matches on Nat.sub, HSub.hSub, Sub.sub
    for disc in &["Nat.sub", "HSub.hSub", "Sub.sub"] {
        set.register(Simproc {
            name: Name::from_string("Nat.reduceSub"),
            discriminant: Name::from_string(disc),
            proc: simproc_nat_reduce_sub,
            priority: 1000,
        });
    }

    // Nat.reduceSucc
    set.register(Simproc {
        name: Name::from_string("Nat.reduceSucc"),
        discriminant: Name::from_string("Nat.succ"),
        proc: simproc_nat_reduce_succ,
        priority: 1000,
    });

    // Nat.reduceGcd
    set.register(Simproc {
        name: Name::from_string("Nat.reduceGcd"),
        discriminant: Name::from_string("Nat.gcd"),
        proc: simproc_nat_reduce_gcd,
        priority: 1000,
    });

    // Nat.reduceMod — matches on Nat.mod, HMod.hMod, Mod.mod
    for disc in &["Nat.mod", "HMod.hMod", "Mod.mod"] {
        set.register(Simproc {
            name: Name::from_string("Nat.reduceMod"),
            discriminant: Name::from_string(disc),
            proc: simproc_nat_reduce_mod,
            priority: 1000,
        });
    }

    // Nat.reduceDiv — matches on Nat.div, HDiv.hDiv, Div.div
    for disc in &["Nat.div", "HDiv.hDiv", "Div.div"] {
        set.register(Simproc {
            name: Name::from_string("Nat.reduceDiv"),
            discriminant: Name::from_string(disc),
            proc: simproc_nat_reduce_div,
            priority: 1000,
        });
    }
}

/// Register built-in Nat comparison simprocs into the given set.
///
/// ENSURES: Registers simprocs for beq, lt, le
pub(crate) fn register_nat_comparisons(set: &mut SimprocSet) {
    // Nat.reduceBEq — BEq for Nat
    set.register(Simproc {
        name: Name::from_string("Nat.reduceBEq"),
        discriminant: Name::from_string("BEq.beq"),
        proc: simproc_nat_reduce_beq,
        priority: 900, // Lower than arithmetic to let arithmetic fire first
    });

    // Nat.reduceLt — Nat.blt for deciding <
    set.register(Simproc {
        name: Name::from_string("Nat.reduceLt"),
        discriminant: Name::from_string("Nat.blt"),
        proc: simproc_nat_reduce_lt,
        priority: 900,
    });

    // Nat.reduceLe — Nat.ble for deciding <=
    set.register(Simproc {
        name: Name::from_string("Nat.reduceLe"),
        discriminant: Name::from_string("Nat.ble"),
        proc: simproc_nat_reduce_le,
        priority: 900,
    });
}

// ============================================================================
// Binary Nat arithmetic simprocs
// ============================================================================

/// Helper: extract the last two arguments from an expression and evaluate
/// them as ground Nat values. Returns `None` if fewer than 2 args or either
/// is symbolic.
fn eval_binary_nat_args(expr: &Expr) -> Option<(u64, u64)> {
    let args = expr.get_app_args();
    if args.len() < 2 {
        return None;
    }
    let l = eval_nat_expr(args[args.len() - 2])?;
    let r = eval_nat_expr(args[args.len() - 1])?;
    Some((l, r))
}

/// Nat.reduceAdd: evaluate `m + n` for Nat literals.
fn simproc_nat_reduce_add(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let Some((l, r)) = eval_binary_nat_args(expr) else {
        return SimprocResult::Continue;
    };
    let Some(result) = l.checked_add(r) else {
        return SimprocResult::Continue;
    };
    SimprocResult::Done(SimpResult {
        expr: mk_nat_lit(result),
        proof: None,
    })
}

/// Nat.reduceMul: evaluate `m * n` for Nat literals.
fn simproc_nat_reduce_mul(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let Some((l, r)) = eval_binary_nat_args(expr) else {
        return SimprocResult::Continue;
    };
    let Some(result) = l.checked_mul(r) else {
        return SimprocResult::Continue;
    };
    SimprocResult::Done(SimpResult {
        expr: mk_nat_lit(result),
        proof: None,
    })
}

/// Nat.reducePow: evaluate `m ^ n` for Nat literals.
fn simproc_nat_reduce_pow(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let Some((base, exp)) = eval_binary_nat_args(expr) else {
        return SimprocResult::Continue;
    };
    let Ok(exp_u32) = u32::try_from(exp) else {
        return SimprocResult::Continue;
    };
    let Some(result) = base.checked_pow(exp_u32) else {
        return SimprocResult::Continue;
    };
    SimprocResult::Done(SimpResult {
        expr: mk_nat_lit(result),
        proof: None,
    })
}

/// Nat.reduceSub: evaluate `m - n` for Nat literals (saturating).
fn simproc_nat_reduce_sub(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let Some((l, r)) = eval_binary_nat_args(expr) else {
        return SimprocResult::Continue;
    };
    SimprocResult::Done(SimpResult {
        expr: mk_nat_lit(l.saturating_sub(r)),
        proof: None,
    })
}

/// Nat.reduceMod: evaluate `m % n` for Nat literals.
fn simproc_nat_reduce_mod(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let Some((a, b)) = eval_binary_nat_args(expr) else {
        return SimprocResult::Continue;
    };
    // Lean Nat: n % 0 = n
    let result = if b == 0 { a } else { a % b };
    SimprocResult::Done(SimpResult {
        expr: mk_nat_lit(result),
        proof: None,
    })
}

/// Nat.reduceDiv: evaluate `m / n` for Nat literals.
fn simproc_nat_reduce_div(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let Some((a, b)) = eval_binary_nat_args(expr) else {
        return SimprocResult::Continue;
    };
    // Lean Nat: n / 0 = 0
    let result = a.checked_div(b).unwrap_or(0);
    SimprocResult::Done(SimpResult {
        expr: mk_nat_lit(result),
        proof: None,
    })
}

// ============================================================================
// Unary Nat simprocs
// ============================================================================

/// Nat.reduceSucc: evaluate `Nat.succ n` for Nat literals.
fn simproc_nat_reduce_succ(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let args = expr.get_app_args();
    if args.is_empty() {
        return SimprocResult::Continue;
    }
    let arg = args.last().expect("invariant: args non-empty");

    let Some(n) = eval_nat_expr(arg) else {
        return SimprocResult::Continue;
    };
    let Some(result) = n.checked_add(1) else {
        return SimprocResult::Continue;
    };
    SimprocResult::Done(SimpResult {
        expr: mk_nat_lit(result),
        proof: None,
    })
}

/// Nat.reduceGcd: evaluate `Nat.gcd m n` for Nat literals.
fn simproc_nat_reduce_gcd(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let Some((a, b)) = eval_binary_nat_args(expr) else {
        return SimprocResult::Continue;
    };
    SimprocResult::Done(SimpResult {
        expr: mk_nat_lit(gcd(a, b)),
        proof: None,
    })
}

/// Euclidean GCD algorithm.
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

// ============================================================================
// Nat comparison simprocs
// ============================================================================

/// Nat.reduceBEq: evaluate `BEq.beq m n` for Nat literals.
fn simproc_nat_reduce_beq(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let Some((a, b)) = eval_binary_nat_args(expr) else {
        return SimprocResult::Continue;
    };
    let result_name = if a == b { "Bool.true" } else { "Bool.false" };
    SimprocResult::Done(SimpResult {
        expr: Expr::const_(Name::from_string(result_name), vec![]),
        proof: None,
    })
}

/// Nat.reduceLt: evaluate `Nat.blt m n` for Nat literals.
fn simproc_nat_reduce_lt(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let Some((a, b)) = eval_binary_nat_args(expr) else {
        return SimprocResult::Continue;
    };
    let result_name = if a < b { "Bool.true" } else { "Bool.false" };
    SimprocResult::Done(SimpResult {
        expr: Expr::const_(Name::from_string(result_name), vec![]),
        proof: None,
    })
}

/// Nat.reduceLe: evaluate `Nat.ble m n` for Nat literals.
fn simproc_nat_reduce_le(_state: &ProofState, _goal: &Goal, expr: &Expr) -> SimprocResult {
    let Some((a, b)) = eval_binary_nat_args(expr) else {
        return SimprocResult::Continue;
    };
    let result_name = if a <= b { "Bool.true" } else { "Bool.false" };
    SimprocResult::Done(SimpResult {
        expr: Expr::const_(Name::from_string(result_name), vec![]),
        proof: None,
    })
}
