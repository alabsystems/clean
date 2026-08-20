// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FUSION (design 2026-06-20-fusion-obligation-as-clean-expr): the
//! lowering-time owner of the per-obligation-kind `Expr` encoders.
//!
//! Each function here takes a node's OWN fields (op, type, operands) and
//! returns the obligation as a `clean_kernel::Expr`. This is the PROMOTION of
//! `clean-reflect/tests/fused_overflow.rs::obligation_expr_from_object` (the
//! side derivation) into the producer: the goal is born from the same field
//! bindings that construct the `Inst`, so program-change => Expr-change is
//! structural, not a test discipline.
//!
//! Consumers (the trust-ir-bridge lowering site, a re-checker, certify) call
//! these to build the [`crate::proof::ExprObligation`] they stamp as
//! [`crate::proof::ProofAnnotation::Goal`] in the SAME builder chain that
//! stamps the cheap safety marker.
//!
//! The whole module is gated on `clean-expr` so the default zero-dependency
//! trust-ir format build never references clean-kernel.

// Per-obligation-kind encoders. Each submodule mirrors the OVERFLOW pair below
// (`overflow_goal` / `overflow_obligation`): a `*_goal(...)` that mints the
// kernel-checkable `Expr` from the node's OWN fields, and a `*_obligation(...)`
// that wraps it in an [`ExprObligation`] with node-sourced hypotheses, ready to
// stamp as [`crate::proof::ProofAnnotation::Goal`] at the matching lowering site.
// All are gated by the parent module's `#[cfg(feature = "clean-expr")]` in lib.rs.
pub mod castoverflow;
// R-L1 Step 3: the L1 contract tier of the verified reflection R. Grounds
// `Precondition`/`Postcondition`/`LoopInvariant`/`RefinementType` predicate
// formulas into kernel-checkable CIC terms — the contract sibling of the L0
// safety encoders below. Fail-closed: an ungroundable predicate produces NO
// `CleanCic`/`Certified` evidence (see `contract::contract_clean_cic_certificate`).
pub mod contract;
pub mod divnonzero;
pub mod indexinbounds;
pub mod negationoverflow;
pub mod shiftinrange;

use crate::inst::OverflowOp;
use crate::proof::ExprObligation;
use crate::ty::Ty;
use crate::value::ValueId;
use clean_kernel::{BigNat, Expr, Level, Name};

/// Errors a per-kind encoder can fail-closed with, rather than minting a wrong
/// or vacuous goal for an unsupported shape.
///
/// Manual `Display`/`Error` impls (not `thiserror`): the `trust-ir` crate keeps
/// zero required external dependencies, and the `clean-expr` feature only adds
/// `clean-kernel`, not an error-derive crate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoweringError {
    /// The instruction's type carries no bit width (e.g. an aggregate), so the
    /// modular overflow goal cannot be formed.
    NoBitWidth(Ty),
    /// The overflow op is outside the fragment this encoder supports. Mirrors
    /// the fail-closed behaviour of the clean-reflect derivation: the add-shaped
    /// goal must not be silently reused for a sub/mul node.
    UnsupportedOp(OverflowOp),
}

impl core::fmt::Display for LoweringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LoweringError::NoBitWidth(ty) => {
                write!(f, "overflow obligation: type {ty:?} has no bit width")
            }
            LoweringError::UnsupportedOp(op) => {
                write!(
                    f,
                    "overflow obligation: op {op:?} not supported by this encoder"
                )
            }
        }
    }
}

impl std::error::Error for LoweringError {}

/// `2^bits` as a Clean `Nat` literal.
///
/// `BigNat::from_limbs` handles widths at/past `u64` (e.g. the U64 modulus
/// `2^64 = [0, 1]` little-endian). Identical to `fused_overflow.rs::modulus_lit`.
fn modulus_lit(bits: u32) -> Expr {
    if bits < 64 {
        Expr::nat_lit(1u64 << bits)
    } else {
        let whole = (bits / 64) as usize;
        let rem = bits % 64;
        let mut limbs = vec![0u64; whole];
        limbs.push(1u64 << rem);
        Expr::bignat_lit(BigNat::from_limbs(limbs))
    }
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.add"), [a, b])
}

fn nat_ble(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.ble"), [a, b])
}

/// The "does NOT overflow" goal: `@Eq Bool overflow Bool.false`.
///
/// Mirrors `fused_overflow.rs::not_overflow_goal` — the kernel-checkable
/// negation of the overflow claim, the same shape `trust-certify`'s
/// "kernel proves the obligation" gate accepts.
fn not_overflow_goal(overflow: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            Expr::const_str("Bool"),
            overflow,
            Expr::const_str("Bool.false"),
        ],
    )
}

/// Build the no-overflow goal `Expr` for an `Inst::Overflow` from its OWN
/// fields. The modulus comes from `ty` (`2^bit_width(ty)`); the addends come
/// from the symbolic operand literals supplied by the lowering context.
///
/// For `AddOverflow` the proposition is
/// `@Eq Bool (Nat.ble modulus (Nat.add a b)) Bool.false`, i.e. "the add does
/// not reach the modulus". Fails closed for ops outside this fragment so a node
/// edit (`AddOverflow -> SubOverflow`) re-shapes the obligation rather than
/// reusing the add goal — exactly `fused_overflow.rs::test_change_coupling_add_to_sub`.
///
/// `operands` are the concrete operand values the node implies, as `Nat`
/// literals; in the lowering pipeline they are sourced from the resolved
/// operand context (symbolic operands hand in the literal facts they carry).
pub fn overflow_goal(op: OverflowOp, ty: Ty, operands: (u64, u64)) -> Result<Expr, LoweringError> {
    match op {
        OverflowOp::AddOverflow => {
            let bits = ty
                .bit_width()
                .ok_or_else(|| LoweringError::NoBitWidth(ty.clone()))?;
            let modulus = modulus_lit(bits);
            let (a, b) = operands;
            let sum = nat_add(Expr::nat_lit(a), Expr::nat_lit(b));
            Ok(not_overflow_goal(nat_ble(modulus, sum)))
        }
        other => Err(LoweringError::UnsupportedOp(other)),
    }
}

/// Build the full [`ExprObligation`] (goal + node-sourced operand hypotheses)
/// for an `Inst::Overflow`, ready to stamp as
/// [`crate::proof::ProofAnnotation::Goal`] in the lowering builder chain.
///
/// The hypotheses are the node's own operand facts: each operand value is a
/// `Nat` in the kernel context, sourced from the node, not an external model.
pub fn overflow_obligation(
    op: OverflowOp,
    ty: Ty,
    lhs: ValueId,
    rhs: ValueId,
    operands: (u64, u64),
) -> Result<ExprObligation, LoweringError> {
    let goal = overflow_goal(op, ty, operands)?;
    Ok(ExprObligation::new(goal)
        .with_hypothesis(format!("%{}", lhs.index()), Expr::const_str("Nat"))
        .with_hypothesis(format!("%{}", rhs.index()), Expr::const_str("Nat")))
}
