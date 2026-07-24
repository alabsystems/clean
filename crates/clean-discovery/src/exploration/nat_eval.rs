// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conservative closed-Nat-expression evaluator for counterexample filtering.
//!
//! This module provides a small, fail-closed interpreter for closed natural
//! number expressions built from `Nat` arithmetic constants applied to bound
//! variables and `Nat` literals. It is used by the counterexample filter to
//! test candidate equations on concrete sampled inputs *before* kernel
//! verification.
//!
//! # Soundness contract
//!
//! The counterexample filter is a **reject-only** filter that runs strictly
//! *before* kernel verification — accepted candidates still go through full
//! kernel type checking. The only safety requirement is therefore:
//!
//! > **Never reject a true equation.**
//!
//! Consequently [`test_equation`] returns `false` (reject) **only** when it
//! finds a concrete sample where *both* sides evaluate to definite, different
//! values. On any unsupported construct, unbound variable, `u64` overflow, or
//! `BigNat::Big` literal, evaluation returns `None` and the equation is treated
//! as inconclusive (it survives). False negatives — failing to reject a false
//! equation — are acceptable; the kernel catches those.
//!
//! # Determinism
//!
//! Sample inputs are produced by a fixed-seed xorshift64 generator. The seed is
//! derived deterministically from the candidate equation's structure (the
//! cached structural hash of its statement), so the same candidate always
//! yields the same verdict. No wall-clock or entropy source is consulted.

use std::collections::HashMap;

use clean_kernel::{BigNat, Expr, ExprKind, Literal};

/// A binding environment mapping de Bruijn indices (as they appear in the
/// equation body) to concrete `u64` values.
pub(super) type NatBinding = HashMap<u32, u64>;

/// Recursion guard: closed Nat terms produced by the pattern generator are
/// shallow, so a generous bound still keeps evaluation fail-closed without
/// risking stack exhaustion on adversarial input.
const MAX_EVAL_DEPTH: u32 = 64;

/// Supported closed `Nat` binary operations, mirroring Lean `Nat` semantics.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NatOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
}

impl NatOp {
    /// Classify a function constant name as a supported `Nat` operation.
    ///
    /// Returns `None` for any unrecognised operator so the caller fails closed.
    fn from_name(name: &str) -> Option<Self> {
        // Match on the final dotted component to tolerate both `Nat.add` and a
        // bare `add`, but require the component to *be* the operation rather
        // than merely contain it (avoids misclassifying, e.g., "readd").
        let last = name.rsplit('.').next().unwrap_or(name);
        match last {
            "add" => Some(NatOp::Add),
            "sub" => Some(NatOp::Sub),
            "mul" => Some(NatOp::Mul),
            "div" => Some(NatOp::Div),
            "mod" => Some(NatOp::Mod),
            "pow" => Some(NatOp::Pow),
            _ => None,
        }
    }

    /// Apply the operation with Lean `Nat` semantics.
    ///
    /// Returns `None` on `u64` overflow (we decline rather than wrap) so that
    /// an overflowing sample is treated as inconclusive, never a counterexample.
    fn apply(self, a: u64, b: u64) -> Option<u64> {
        match self {
            // Decline on overflow rather than wrapping.
            NatOp::Add => a.checked_add(b),
            // Lean `Nat.sub` is saturating (truncated) subtraction.
            NatOp::Sub => Some(a.saturating_sub(b)),
            NatOp::Mul => a.checked_mul(b),
            // Lean `Nat.div` by zero is 0 (`checked_div` returns None on b == 0).
            NatOp::Div => Some(a.checked_div(b).unwrap_or(0)),
            // Lean `Nat.mod` by zero is the dividend (`checked_rem` is None on b == 0).
            NatOp::Mod => Some(a.checked_rem(b).unwrap_or(a)),
            // Lean `Nat.pow`: a^0 = 1 (including 0^0 = 1); decline on overflow.
            NatOp::Pow => {
                if b > u32::MAX as u64 {
                    return None;
                }
                a.checked_pow(b as u32)
            }
        }
    }
}

/// Evaluate a closed `Nat` expression under the given bindings.
///
/// Returns `Some(value)` only when `expr` is built entirely from supported
/// constructs — `Nat` literals, bound variables present in `bindings`, and
/// applications of recognised binary `Nat` operations to exactly two evaluable
/// arguments. Returns `None` (fail-closed) on any unsupported construct: lambda,
/// pi, sort, free variable, metadata, unknown constant, unbound variable,
/// `BigNat::Big` literal, wrong arity, or `u64` overflow.
pub(super) fn eval_nat_expr(expr: &Expr, bindings: &NatBinding) -> Option<u64> {
    eval_inner(expr, bindings, 0)
}

fn eval_inner(expr: &Expr, bindings: &NatBinding, depth: u32) -> Option<u64> {
    if depth >= MAX_EVAL_DEPTH {
        return None;
    }
    match expr.kind() {
        // Bound variable: look up its sampled value. Unbound => fail closed.
        ExprKind::BVar(idx) => bindings.get(idx).copied(),
        // Nat literal: only small (u64-representable) values are evaluable.
        ExprKind::Lit(Literal::Nat(BigNat::Small(v))) => Some(*v),
        ExprKind::Lit(_) => None,
        // Transparent metadata wrapper: descend.
        ExprKind::MData(_, inner) => eval_inner(inner, bindings, depth + 1),
        // Application: must be a recognised binary Nat op applied to two args.
        ExprKind::App(_, _) => {
            let head = expr.get_app_fn();
            let op = match head.kind() {
                ExprKind::Const(name, _) => NatOp::from_name(&name.to_string())?,
                _ => return None,
            };
            // Arguments in source order.
            let args = expr.get_app_args();
            if args.len() != 2 {
                return None;
            }
            let a = eval_inner(args[0], bindings, depth + 1)?;
            let b = eval_inner(args[1], bindings, depth + 1)?;
            op.apply(a, b)
        }
        // Everything else is unsupported: fail closed.
        _ => None,
    }
}

/// Strip the leading `Pi` binders of a candidate statement and extract the
/// equated left- and right-hand sides if the body is `@Eq S lhs rhs`.
///
/// Returns `Some((num_binders, lhs, rhs))` where `num_binders` is the count of
/// universally quantified variables (so the free `BVar` indices in `lhs`/`rhs`
/// range over `0..num_binders`). Returns `None` when the statement is not a
/// universally quantified equality (e.g. an implication / ordering goal, or a
/// non-`Eq` body), so the caller falls back to the structural heuristic.
pub(super) fn extract_eq_body(statement: &Expr) -> Option<(u32, Expr, Expr)> {
    let mut num_binders: u32 = 0;
    let mut body = statement.strip_mdata();
    while let ExprKind::Pi(_, _, inner) = body.kind() {
        num_binders = num_binders.checked_add(1)?;
        body = inner.strip_mdata();
    }

    // The body must be `@Eq S lhs rhs`: a constant `Eq` head with 3 arguments.
    let head = body.get_app_fn();
    let is_eq = matches!(
        head.kind(),
        ExprKind::Const(name, _) if name.to_string() == "Eq"
    );
    if !is_eq {
        return None;
    }
    let args = body.get_app_args();
    if args.len() != 3 {
        return None;
    }
    // args[0] = sort, args[1] = lhs, args[2] = rhs (in source order).
    // `args[i]` is `&Expr`, so clone the pointee explicitly to obtain an owned `Expr`.
    Some((num_binders, Expr::clone(args[1]), Expr::clone(args[2])))
}

/// xorshift64 step — a small, deterministic, allocation-free PRNG.
fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

/// Derive a deterministic, non-zero seed from a candidate equation's structure.
///
/// Uses the statement's cached structural hash mixed with the function names so
/// that distinct candidates get distinct sample sequences, while the *same*
/// candidate always produces the *same* sequence (no clock / entropy).
pub(super) fn deterministic_seed(statement: &Expr, func_names: &[String]) -> u64 {
    // Start from the structural hash of the statement.
    let mut seed = u64::from(statement.hash_cached()).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    for name in func_names {
        for byte in name.bytes() {
            seed = seed
                .wrapping_mul(0x0100_0000_01B3)
                .wrapping_add(u64::from(byte));
        }
    }
    // xorshift64 requires a non-zero state.
    seed | 1
}

/// Draw the next sample value for a variable from the PRNG state.
///
/// Values are biased toward small naturals (where most arithmetic
/// counterexamples live) by taking the result modulo a small bound, while still
/// occasionally producing larger values.
pub(super) fn sample_u64(state: &mut u64) -> u64 {
    let raw = xorshift64(state);
    // Mix two regimes: mostly small values (0..16), sometimes mid-range.
    if raw & 0b11 == 0 {
        raw % 1000
    } else {
        raw % 16
    }
}

/// Outcome of computationally testing a candidate equation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum EquationVerdict {
    /// A concrete sample made both sides evaluate to definite, different
    /// values: the equation is false and must be rejected.
    Counterexample,
    /// Both sides were Nat-evaluable on every sample and never disagreed: the
    /// equation survives this filter (no counterexample exists in the samples).
    NoCounterexample,
    /// At least one side was not Nat-evaluable (unsupported construct, unbound
    /// variable, overflow, ...). The caller should fall back to the heuristic.
    Inconclusive,
}

/// Test a candidate equation `lhs == rhs` (closed under `num_binders` Nat
/// variables) on `samples` deterministically-sampled assignments.
///
/// - Returns [`EquationVerdict::Counterexample`] **only** when a concrete sample
///   makes both sides evaluate to definite, *different* values.
/// - Returns [`EquationVerdict::NoCounterexample`] when both sides were always
///   evaluable and never disagreed.
/// - Returns [`EquationVerdict::Inconclusive`] when some side could not be
///   evaluated (so neither rejecting nor trusting the survive verdict is sound).
///
/// This never reports a counterexample on an inconclusive/overflow sample, so a
/// true equation is never rejected.
pub(super) fn test_equation(
    lhs: &Expr,
    rhs: &Expr,
    num_binders: u32,
    samples: u32,
    seed: u64,
) -> EquationVerdict {
    let mut state = seed;
    let mut all_evaluable = true;
    let mut any_sample = false;
    for _ in 0..samples {
        any_sample = true;
        let mut bindings: NatBinding = HashMap::with_capacity(num_binders as usize);
        for idx in 0..num_binders {
            bindings.insert(idx, sample_u64(&mut state));
        }
        match (eval_nat_expr(lhs, &bindings), eval_nat_expr(rhs, &bindings)) {
            // Definite, concrete counterexample: reject immediately.
            (Some(l), Some(r)) if l != r => return EquationVerdict::Counterexample,
            // Both definite and equal on this sample: keep going.
            (Some(_), Some(_)) => {}
            // Either side inconclusive on this sample.
            _ => all_evaluable = false,
        }
    }
    if any_sample && all_evaluable {
        EquationVerdict::NoCounterexample
    } else {
        EquationVerdict::Inconclusive
    }
}

#[cfg(test)]
#[path = "nat_eval_tests.rs"]
mod tests;
