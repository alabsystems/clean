// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The micro-checker's OWN native Nat/Bool reductions (independent IOTA).
//!
//! These are re-implementations — from scratch, on the micro-checker's own
//! [`num_bigint::BigUint`] — of the closed-Nat reductions the main kernel
//! performs in `tc/reduction/nat.rs`. They are the IOTA half of the diversity
//! gate: the `:= rfl` B-def corpus reduces `Nat.add / Nat.sub / Nat.mul /
//! Nat.div / Nat.mod / Nat.pow / Nat.land / Nat.lor / Nat.xor /
//! Nat.shiftLeft / Nat.shiftRight` and the `Nat.beq / Nat.ble` predicates on
//! closed literals; the bitwise `Bool` ops follow.
//!
//! INDEPENDENCE: nothing here calls the kernel. Every operation is a fresh
//! `BigUint` computation. A bug in the kernel's `BigNat` path that this code
//! does not share would surface as a micro/kernel DISAGREEMENT — which is the
//! whole point of a second checker.
//!
//! FAIL-CLOSED: the supported-op table is a CLOSED allowlist. Any other
//! `Nat.*` / recursor head returns `None` from [`reduce_nat_app`], and the
//! caller (`checker::whnf_impl`) leaves the term stuck; the gate then reports
//! the decl `Unsupported` rather than silently accepting it. (Lean's bounded
//! shift/pow guards are mirrored so the two reducers agree on those edges.)

use num_bigint::BigUint;
use num_traits::{ToPrimitive, Zero};

use crate::expr::stack_safe;

use super::types::{MicroExpr, MicroLiteral};

/// Names of the closed-Nat binary ops the micro-checker models natively.
/// A CLOSED allowlist (see module doc): anything not here stays stuck.
pub(super) const NAT_BINOPS: &[&str] = &[
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.div",
    "Nat.mod",
    "Nat.pow",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "Nat.beq",
    "Nat.ble",
];

/// Names of the closed-`Bool` binary ops the micro-checker models natively.
/// `Bool.beq` (boolean equality) reduces a pair of `Bool` constructors to a
/// `Bool` constructor. A CLOSED allowlist: anything else stays stuck.
///
/// The boolean *connectives* (`Bool.and` / `Bool.or` / `Bool.xor` / `Bool.not`,
/// and their `and`/`or` aliases) are NOT listed here on purpose: the prelude
/// defines them as `Bool.rec`-based reducible defs, so the micro-checker reduces
/// them by DELTA-unfolding their body and then firing its OWN `Bool.rec` IOTA
/// (see `checker::reduce_recursor`). Re-deriving them through the recursor — the
/// same path the kernel takes — keeps the two reducers honest about the
/// connectives' semantics rather than hard-coding a second truth table.
pub(super) const BOOL_BINOPS: &[&str] = &["Bool.beq"];

/// Extract a closed `BigUint` from a fully-reduced `MicroExpr`.
///
/// Recognises a `Nat` literal and the `Nat.zero` constructor. (`Nat.succ`
/// of a literal is handled by the caller's whnf before this is reached for
/// the corpus, but we also accept `Nat.succ <lit>` here for robustness.)
pub(super) fn as_nat(e: &MicroExpr) -> Option<BigUint> {
    stack_safe(|| as_nat_impl(e))
}

fn as_nat_impl(e: &MicroExpr) -> Option<BigUint> {
    match e {
        MicroExpr::Lit(MicroLiteral::Nat(n)) => Some(n.clone()),
        MicroExpr::Const(name) if &**name == "Nat.zero" => Some(BigUint::ZERO),
        MicroExpr::App(f, a) => match &**f {
            MicroExpr::Const(name) if &**name == "Nat.succ" => {
                let inner = as_nat(a)?;
                Some(inner + 1u32)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Build a `Nat` literal `MicroExpr` from a `BigUint`.
fn nat_lit(n: BigUint) -> MicroExpr {
    MicroExpr::Lit(MicroLiteral::Nat(n))
}

fn bool_const(b: bool) -> MicroExpr {
    MicroExpr::Const(if b {
        std::sync::Arc::from("Bool.true")
    } else {
        std::sync::Arc::from("Bool.false")
    })
}

/// Recognise a fully-reduced `MicroExpr` as a `Bool` constructor.
///
/// `Bool.true` -> `Some(true)`, `Bool.false` -> `Some(false)`. Anything else
/// (a stuck native op, an unknown const, a non-`Bool` value) -> `None`, so the
/// `Bool.rec` / `Bool.beq` IOTA fails closed instead of guessing.
pub(super) fn as_bool(e: &MicroExpr) -> Option<bool> {
    match e {
        MicroExpr::Const(name) => match &**name {
            "Bool.true" => Some(true),
            "Bool.false" => Some(false),
            _ => None,
        },
        _ => None,
    }
}

/// Try to reduce a closed-`Bool` op `op` applied to already-reduced args.
///
/// Currently models `Bool.beq` (boolean equality). Returns `Some(result)` iff
/// `op` is modeled AND every argument is a closed `Bool` constructor; otherwise
/// `None` (the caller leaves the term stuck and the gate fails closed). This is
/// the micro-checker's OWN boolean equality — it shares nothing with the kernel.
pub(super) fn reduce_bool_app(op: &str, args: &[MicroExpr]) -> Option<MicroExpr> {
    let [a1, a2] = args else { return None };
    let x = as_bool(a1)?;
    let y = as_bool(a2)?;
    match op {
        "Bool.beq" => Some(bool_const(x == y)),
        _ => None,
    }
}

/// Try to reduce a Nat application head `op` applied to already-reduced args.
///
/// Returns `Some(result)` if `op` is a modeled Nat op AND every argument is a
/// closed Nat; otherwise `None` (the caller leaves the term stuck and the gate
/// fails closed). Mirrors `tc/reduction/nat.rs::reduce_nat` semantics:
///
/// * `Nat.sub` is truncated (floored) at zero.
/// * `Nat.div`/`Nat.mod` use Lean semantics: `n/0 = 0`, `n%0 = n`.
/// * `Nat.beq`/`Nat.ble` produce `Bool.true`/`Bool.false`.
/// * `Nat.pow`/`Nat.shiftLeft` keep the same bounded guards Lean's kernel uses
///   so the two reducers agree on the over-large edges (return `None` there).
pub(super) fn reduce_nat_app(op: &str, args: &[MicroExpr]) -> Option<MicroExpr> {
    // Unary: Nat.succ
    if op == "Nat.succ" {
        let [a] = args else { return None };
        let n = as_nat(a)?;
        return Some(nat_lit(n + 1u32));
    }

    let [a1, a2] = args else { return None };
    let x = as_nat(a1)?;
    let y = as_nat(a2)?;

    let result = match op {
        "Nat.add" => nat_lit(x + y),
        "Nat.sub" => nat_lit(if x >= y { x - y } else { BigUint::ZERO }),
        "Nat.mul" => nat_lit(x * y),
        "Nat.div" => nat_lit(if y.is_zero() { BigUint::ZERO } else { x / y }),
        "Nat.mod" => nat_lit(if y.is_zero() { x } else { x % y }),
        "Nat.pow" => {
            // Bounded guard matching the kernel: exponent capped, result
            // capped at 1024 bits, else leave stuck (None).
            let exp = y.to_u32()?;
            if exp > 1023 {
                return None;
            }
            let r = x.pow(exp);
            if r.bits() > 1024 {
                return None;
            }
            nat_lit(r)
        }
        "Nat.land" => nat_lit(x & y),
        "Nat.lor" => nat_lit(x | y),
        "Nat.xor" => nat_lit(x ^ y),
        "Nat.shiftLeft" => {
            if x.is_zero() {
                return Some(nat_lit(BigUint::ZERO));
            }
            let shift = y.to_u64()?;
            if shift > 1024 {
                return None;
            }
            let r = x << shift;
            if r.bits() > 1024 + 64 {
                return None;
            }
            nat_lit(r)
        }
        "Nat.shiftRight" => {
            let shift = match y.to_u64() {
                Some(s) if s <= u64::MAX / 2 => s,
                _ => return Some(nat_lit(BigUint::ZERO)),
            };
            nat_lit(x >> shift)
        }
        "Nat.beq" => bool_const(x == y),
        "Nat.ble" => bool_const(x <= y),
        _ => return None,
    };
    Some(result)
}
