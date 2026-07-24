// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared constructors for typeclass method applications.
//!
//! Typeclass methods like `LE.le`, `HAdd.hAdd`, `Neg.neg` require implicit
//! type and instance arguments in their fully-applied kernel form.
//! This module provides constructors that enforce the correct arity,
//! eliminating the copy-paste bug class where only explicit args are provided.
//!
//! # Reference
//!
//! - `LE.le : {α : Type u} → [inst : LE α] → α → α → Prop` — 4 args
//! - `HAdd.hAdd : {α β γ : Type*} → [inst : HAdd α β γ] → α → β → γ` — 6 args
//! - `Neg.neg : {α : Type u} → [inst : Neg α] → α → α` — 3 args
//!
//! See also: `crates/clean-kernel/src/env/order.rs` (nat_le_tc reference impl).
//!
//! Part of #2078.

use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

/// Build a fully-applied binary comparison relation:
/// `@Rel.{u} α inst lhs rhs`
///
/// For `LE.le`, `LT.lt`, `GE.ge`, `GT.gt`. These have signature:
///   `{α : Type u} → [inst : Rel α] → α → α → Prop`
///
/// Note: `GE.ge` takes an `[LE α]` instance; `GT.gt` takes an `[LT α]` instance.
///
/// REQUIRES: `rel` is a const expression for a 4-arg relation; `ty` is the type argument;
///   `inst` is the typeclass instance; `lhs` and `rhs` are the operands.
/// ENSURES: Returns `App(App(App(App(rel, ty), inst), lhs), rhs)` — exactly 4 args applied.
pub(crate) fn mk_tc_rel(rel: Expr, ty: Expr, inst: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(Expr::app(Expr::app(Expr::app(rel, ty), inst), lhs), rhs)
}

/// Build a fully-applied heterogeneous binary operation:
/// `@HOp.{u,v,w} α β γ inst a b`
///
/// For `HAdd.hAdd`, `HMul.hMul`, `HPow.hPow`. These have signature:
///   `{α : Type u} → {β : Type v} → {γ : Type w} → [inst : HOp α β γ] → α → β → γ`
///
/// REQUIRES: `op` is a const expression for a 6-arg heterogeneous operator.
/// ENSURES: Returns the fully-applied expression with exactly 6 args:
///   `App(App(App(App(App(App(op, alpha), beta), gamma), inst), a), b)`.
#[cfg(test)]
pub(crate) fn mk_tc_hbinop(
    op: Expr,
    alpha: Expr,
    beta: Expr,
    gamma: Expr,
    inst: Expr,
    a: Expr,
    b: Expr,
) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(Expr::app(op, alpha), beta), gamma),
                inst,
            ),
            a,
        ),
        b,
    )
}

/// Build a fully-applied unary typeclass operation:
/// `@Op.{u} α inst a`
///
/// For `Neg.neg`. Signature: `{α : Type u} → [inst : Neg α] → α → α`
///
/// REQUIRES: `op` is a const expression for a 3-arg unary operator.
/// ENSURES: Returns `App(App(App(op, ty), inst), a)` — exactly 3 args applied.
#[cfg(test)]
pub(crate) fn mk_tc_unop(op: Expr, ty: Expr, inst: Expr, a: Expr) -> Expr {
    Expr::app(Expr::app(Expr::app(op, ty), inst), a)
}

/// Return the default Nat instance name for a comparison relation.
///
/// Returns the concrete instance constant for Nat:
/// - `LE.le` / `GE.ge` → `instLENat`
/// - `LT.lt` / `GT.gt` → `instLTNat`
///
/// REQUIRES: `rel_name` is a relation identifier (e.g., "LE.le", "GT.gt").
/// ENSURES: Returns a `Const` expression for the Nat-specific instance.
/// ENSURES: Unrecognized names default to `instLENat`.
pub(crate) fn nat_rel_inst(rel_name: &str) -> Expr {
    let inst_name = match rel_name {
        "LE.le" | "GE.ge" | "le" | "ge" => "instLENat",
        "LT.lt" | "GT.gt" | "lt" | "gt" => "instLTNat",
        _ => return Expr::const_(Name::from_string("instLENat"), vec![]),
    };
    Expr::const_(Name::from_string(inst_name), vec![])
}

/// Return the default Nat instance for a heterogeneous arithmetic operation.
///
/// - `HAdd.hAdd` → `instHAddNat`
/// - `HMul.hMul` → `instHMulNat`
/// - `HPow.hPow` → `instHPowNatNat`
/// - `Neg.neg` → `instNegInt`
///
/// REQUIRES: `op_name` is an arithmetic operator identifier.
/// ENSURES: Returns a `Const` expression for the Nat-specific arithmetic instance.
/// ENSURES: Unrecognized names default to `instHAddNat`.
#[cfg(test)]
pub(crate) fn nat_arith_inst(op_name: &str) -> Expr {
    let inst_name = match op_name {
        "HAdd.hAdd" => "instHAddNat",
        "HMul.hMul" => "instHMulNat",
        "HPow.hPow" => "instHPowNatNat",
        "Neg.neg" => "instNegInt",
        _ => return Expr::const_(Name::from_string("instHAddNat"), vec![]),
    };
    Expr::const_(Name::from_string(inst_name), vec![])
}

/// Return the comparison relation instance for a given type expression.
///
/// Lean 4 names instances as `inst{LE|LT}{TypeName}`, e.g. `instLENat`,
/// `instLTInt`, `instLEReal`. For non-const type expressions, falls back
/// to the Nat instance.
///
/// Note: `GE.ge` uses an `LE` instance; `GT.gt` uses an `LT` instance.
///
/// REQUIRES: `ty` is a well-formed type expression; `rel_name` is a relation identifier.
/// ENSURES: Returns a `Const` expression `inst{LE|LT}{TypeName}` matching the type.
/// ENSURES: Non-const type expressions fall back to the Nat instance.
pub(crate) fn rel_inst_for_type(ty: &Expr, rel_name: &str) -> Expr {
    use clean_kernel::expr::ExprKind;
    let type_suffix = match ty.kind() {
        ExprKind::Const(name, _) => name.to_string(),
        _ => "Nat".to_string(),
    };
    let prefix = match rel_name {
        "LE.le" | "GE.ge" | "le" | "ge" => "instLE",
        "LT.lt" | "GT.gt" | "lt" | "gt" => "instLT",
        _ => "instLE",
    };
    Expr::const_(Name::from_string(&format!("{prefix}{type_suffix}")), vec![])
}

/// The `Nat` type constant.
///
/// ENSURES: Returns `Const("Nat", [])`.
pub(crate) fn nat_type() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// Build `@LE.le.{0} Nat instLENat lhs rhs`.
///
/// Nat-specific convenience wrapper around [`mk_tc_rel`]. Does not require
/// `ProofState`, making it suitable for proof reconstruction code that builds
/// expressions outside an elaboration context.
///
/// Mirrors `clean-kernel::env::order::nat_le_tc` for the elab layer.
///
/// REQUIRES: `lhs` and `rhs` are Nat-typed expressions.
/// ENSURES: Returns the fully-applied 4-arg form `LE.le.{0} Nat instLENat lhs rhs`.
pub(crate) fn nat_le_tc(lhs: Expr, rhs: Expr) -> Expr {
    // Universe zero correct: LE.le : {α : Type u} with Nat : Type 0, so u = 0
    mk_tc_rel(
        Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
        nat_type(),
        Expr::const_(Name::from_string("instLENat"), vec![]),
        lhs,
        rhs,
    )
}

/// Build `@LT.lt.{0} Nat instLTNat lhs rhs`.
///
/// Nat-specific convenience wrapper around [`mk_tc_rel`]. Does not require
/// `ProofState`, making it suitable for proof reconstruction code that builds
/// expressions outside an elaboration context.
///
/// Mirrors `clean-kernel::env::order::nat_lt_tc` for the elab layer.
///
/// REQUIRES: `lhs` and `rhs` are Nat-typed expressions.
/// ENSURES: Returns the fully-applied 4-arg form `LT.lt.{0} Nat instLTNat lhs rhs`.
pub(crate) fn nat_lt_tc(lhs: Expr, rhs: Expr) -> Expr {
    // Universe zero correct: LT.lt : {α : Type u} with Nat : Type 0, so u = 0
    mk_tc_rel(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        nat_type(),
        Expr::const_(Name::from_string("instLTNat"), vec![]),
        lhs,
        rhs,
    )
}

/// Build `@GE.ge.{0} Nat instLENat lhs rhs`.
///
/// `GE.ge` shares the `LE` instance (`instLENat`); `a ≥ b` is definitionally
/// `b ≤ a`. Nat-specific wrapper around [`mk_tc_rel`], usable outside an
/// elaboration context.
///
/// REQUIRES: `lhs` and `rhs` are Nat-typed expressions.
/// ENSURES: Returns the fully-applied 4-arg form `GE.ge.{0} Nat instLENat lhs rhs`.
pub(crate) fn nat_ge_tc(lhs: Expr, rhs: Expr) -> Expr {
    mk_tc_rel(
        Expr::const_(Name::from_string("GE.ge"), vec![Level::zero()]),
        nat_type(),
        Expr::const_(Name::from_string("instLENat"), vec![]),
        lhs,
        rhs,
    )
}

/// Build `@GT.gt.{0} Nat instLTNat lhs rhs`.
///
/// `GT.gt` shares the `LT` instance (`instLTNat`); `a > b` is definitionally
/// `b < a`. Nat-specific wrapper around [`mk_tc_rel`], usable outside an
/// elaboration context.
///
/// REQUIRES: `lhs` and `rhs` are Nat-typed expressions.
/// ENSURES: Returns the fully-applied 4-arg form `GT.gt.{0} Nat instLTNat lhs rhs`.
pub(crate) fn nat_gt_tc(lhs: Expr, rhs: Expr) -> Expr {
    mk_tc_rel(
        Expr::const_(Name::from_string("GT.gt"), vec![Level::zero()]),
        nat_type(),
        Expr::const_(Name::from_string("instLTNat"), vec![]),
        lhs,
        rhs,
    )
}
