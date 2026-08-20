// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FUSION (design 2026-06-20-fusion-obligation-as-clean-expr): the
//! lowering-time owner of the per-kind `Expr` encoder for the
//! **ShiftInRange** obligation (the `ProofAnnotation::ShiftInRange` marker,
//! `proof.rs:55`).
//!
//! A shift instruction (`Inst::BinOp { op: Shl | LShr | AShr, ty, .. }`) is
//! well-defined only when the shift AMOUNT is strictly less than the bit width
//! of the shifted type: `amt < bit_width(ty)`. A shift by `>= bit_width` is
//! undefined behaviour (LLVM `poison`; Rust debug panic). This module mints
//! that proposition as a `clean_kernel::Expr` born from the node's OWN fields
//! (the shift op selects the obligation; `ty` gives the width; the amount comes
//! from the resolved operand context), exactly mirroring the overflow encoder
//! pair in [`crate::clean_expr_lowering`].
//!
//! The kernel-checkable goal is
//!
//! ```text
//! @Eq Bool (Nat.blt amt width) Bool.true     -- "amt < width" holds
//! ```
//!
//! where `width = bit_width(ty)` is a `Nat` literal read off the OBJECT and
//! `amt` is the concrete shift amount the node implies. `Nat.blt` is a native
//! prelude reducer (`Nat.blt : Nat -> Nat -> Bool`,
//! `clean-kernel/src/env/order_nat_cmp.rs:537`), so the kernel definitionally
//! reduces `Nat.blt amt width` and accepts the hand `@Eq.refl Bool Bool.true`
//! proof ONLY when the shift amount is genuinely in range — the de Bruijn
//! criterion, no external `.lean`.
//!
//! Fail-closed: a non-shift `BinOp` op returns `Err` so a node edit
//! (`Shl -> Add`) re-shapes the obligation rather than reusing a stale
//! shift-range goal — the ShiftInRange analogue of
//! `fused_overflow.rs::test_change_coupling_add_to_sub`.
//!
//! The whole module is gated on `clean-expr`; the default zero-dependency
//! trust-ir format build never references clean-kernel.
//!
//! ## Integration
//!
//! The `clean-expr` feature exposes this module at
//! [`crate::clean_expr_lowering::shiftinrange`]. The module graph is integrated,
//! but this file does not establish that a producer bridge calls it. A consumer
//! can construct the node-coupled obligation through the canonical path:
//!
//! ```rust
//! use trust_ir::clean_expr_lowering::shiftinrange::shift_in_range_obligation;
//! use trust_ir::{BinOp, Ty, ValueId};
//!
//! let obligation = shift_in_range_obligation(
//!     BinOp::Shl,
//!     Ty::U32,
//!     ValueId::new(1),
//!     3,
//! )
//! .expect("a shift amount below the type width has a ShiftInRange obligation");
//! ```
//!
//! A producer that uses this helper must stamp the returned obligation in the
//! same builder chain as `ProofAnnotation::ShiftInRange`. The example
//! demonstrates obligation construction only; it is not evidence of a
//! production bridge call site.

use crate::inst::BinOp;
use crate::proof::ExprObligation;
use crate::ty::Ty;
use crate::value::ValueId;
use clean_kernel::{Expr, Level, Name};

/// Errors the ShiftInRange encoder can fail-closed with, rather than minting a
/// wrong or vacuous goal for an unsupported shape.
///
/// Manual `Display`/`Error` impls (not `thiserror`): the `trust-ir` crate keeps
/// zero required external dependencies, and the `clean-expr` feature only adds
/// `clean-kernel`, not an error-derive crate. Mirrors
/// [`crate::clean_expr_lowering::LoweringError`] but is a distinct, self-contained
/// type so this file edits no shared module. (Integrator may, optionally, fold
/// these variants into the shared `LoweringError` — see the report.)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ShiftLoweringError {
    /// The shifted type carries no bit width (e.g. an aggregate / pointer with
    /// no static width), so the `amt < width` goal cannot be formed.
    NoBitWidth(Ty),
    /// The `BinOp` op is not a shift. The shift-range goal must not be silently
    /// reused for a non-shift node (`Shl -> Add` must re-shape).
    NotAShift(BinOp),
}

impl core::fmt::Display for ShiftLoweringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ShiftLoweringError::NoBitWidth(ty) => {
                write!(f, "shift-in-range obligation: type {ty:?} has no bit width")
            }
            ShiftLoweringError::NotAShift(op) => {
                write!(
                    f,
                    "shift-in-range obligation: op {op:?} is not a shift (Shl/LShr/AShr)"
                )
            }
        }
    }
}

impl std::error::Error for ShiftLoweringError {}

/// `Nat.blt a b` — the native prelude `<` on `Nat` returning `Bool`.
fn nat_blt(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.blt"), [a, b])
}

/// The "shift amount IS in range" goal: `@Eq Bool (Nat.blt amt width) Bool.true`.
///
/// Mirrors the overflow encoder's `not_overflow_goal` shape, but the SAFE case
/// is `Bool.true` (amt < width holds) rather than `Bool.false`: ShiftInRange is
/// a positive in-range claim, where NoOverflow is a negative does-not-fire claim.
/// The kernel reduces `Nat.blt amt width` and accepts `Eq.refl Bool Bool.true`
/// only when the reduction yields `Bool.true`.
fn in_range_goal(in_range_bool: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            Expr::const_str("Bool"),
            in_range_bool,
            Expr::const_str("Bool.true"),
        ],
    )
}

/// Build the shift-in-range goal `Expr` for a shift `Inst::BinOp` from its OWN
/// fields. The width comes from `ty` (`bit_width(ty)`); the shift amount comes
/// from the concrete operand value the node implies.
///
/// For `Shl`/`LShr`/`AShr` the proposition is
/// `@Eq Bool (Nat.blt amt width) Bool.true`, i.e. "the shift amount is strictly
/// below the bit width". Fails closed for non-shift ops so a node edit re-shapes
/// the obligation rather than reusing the shift goal.
///
/// `amt` is the concrete shift amount the node implies, as a `Nat` literal; in
/// the lowering pipeline it is sourced from the resolved operand context (a
/// symbolic shift hands in the literal amount fact it carries).
pub fn shift_in_range_goal(op: BinOp, ty: Ty, amt: u64) -> Result<Expr, ShiftLoweringError> {
    match op {
        BinOp::Shl | BinOp::LShr | BinOp::AShr => {
            let bits = ty
                .bit_width()
                .ok_or_else(|| ShiftLoweringError::NoBitWidth(ty.clone()))?;
            // bit widths are small (<= 128 for the integer types that admit
            // shifts), so `width` always fits a `Nat` u64 literal.
            let width = Expr::nat_lit(u64::from(bits));
            let amount = Expr::nat_lit(amt);
            Ok(in_range_goal(nat_blt(amount, width)))
        }
        other => Err(ShiftLoweringError::NotAShift(other)),
    }
}

/// Build the full [`ExprObligation`] (goal + node-sourced shift-amount
/// hypothesis) for a shift `Inst::BinOp`, ready to stamp as
/// [`crate::proof::ProofAnnotation::Goal`] in the lowering builder chain.
///
/// The hypothesis is the node's own shift-amount operand fact: the amount value
/// is a `Nat` in the kernel context, sourced from the node, not an external
/// model. (The shifted value `lhs` is irrelevant to the in-range obligation, so
/// it is intentionally NOT carried — only the amount governs definedness.)
pub fn shift_in_range_obligation(
    op: BinOp,
    ty: Ty,
    shift_amount_operand: ValueId,
    amt: u64,
) -> Result<ExprObligation, ShiftLoweringError> {
    let goal = shift_in_range_goal(op, ty, amt)?;
    Ok(ExprObligation::new(goal).with_hypothesis(
        format!("%{}", shift_amount_operand.index()),
        Expr::const_str("Nat"),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, LocalContext, TypeChecker};

    /// Hand proof term `@Eq.refl Bool Bool.true` — proves the in-range goal
    /// exactly when `Nat.blt amt width` reduces to `Bool.true`. The kernel does
    /// the reduction itself; it is not told the answer.
    fn refl_true() -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [Expr::const_str("Bool"), Expr::const_str("Bool.true")],
        )
    }

    /// Kernel-discharge an obligation: build the LocalContext from its
    /// node-sourced hypotheses, then `check_type(term, &goal)` under
    /// `Environment::with_prelude()` ONLY — the same gate trust-certify uses.
    fn discharge(ob: &ExprObligation, proof_term: &Expr) -> bool {
        let env = Environment::with_prelude();
        let mut ctx = LocalContext::new();
        for (name, ty) in &ob.hypotheses {
            ctx.push(
                Name::from_string(name),
                ty.clone(),
                clean_kernel::BinderInfo::Default,
            );
        }
        let tc = TypeChecker::with_context(&env, ctx);
        tc.check_type(proof_term, &ob.goal).is_ok()
    }

    #[test]
    fn test_goal_shape_is_function_of_node_fields() {
        // Shl on U32, amount 3: goal = @Eq Bool (Nat.blt 3 32) Bool.true.
        let goal = shift_in_range_goal(BinOp::Shl, Ty::U32, 3)
            .expect("shift on a width-carrying type has a representable goal");
        // @Eq Bool <in-range-bool> Bool.true
        let eq_args = goal.get_app_args();
        assert_eq!(eq_args.len(), 3, "@Eq takes (Sort, lhs, rhs)");
        assert_eq!(
            eq_args[2],
            &Expr::const_str("Bool.true"),
            "ShiftInRange is a positive in-range claim => Bool.true on the safe side"
        );
        let in_range_bool = eq_args[1];
        let blt_args = in_range_bool.get_app_args();
        assert_eq!(blt_args.len(), 2, "Nat.blt takes (amt, width)");
        assert_eq!(
            blt_args[0],
            &Expr::nat_lit(3),
            "amount arg is the operand 3"
        );
        assert_eq!(
            blt_args[1],
            &Expr::nat_lit(32),
            "width arg is bit_width(U32) = 32, read off the node's `ty`"
        );
    }

    #[test]
    fn test_goal_is_well_typed_via_kernel_check_type() {
        // The minted goal must itself be a well-typed `Prop` the kernel accepts
        // (the obligation is a kernel term, not string-soup). Check the SAFE
        // case discharges with the hand `rfl` term: U32, amount 3 < 32 in range.
        let ob = shift_in_range_obligation(BinOp::Shl, Ty::U32, ValueId::new(1), 3)
            .expect("in-range shift has a representable obligation");
        assert!(
            discharge(&ob, &refl_true()),
            "U32 shift by 3 is in range (3 < 32): the kernel must discharge the goal, \
             proving the minted Expr is well-typed and definitionally true"
        );
    }

    #[test]
    fn test_out_of_range_shift_is_unverified_fail_closed() {
        // U8, amount 8: 8 < 8 is FALSE, so Nat.blt 8 8 reduces to Bool.false and
        // the goal @Eq Bool Bool.false Bool.true is REJECTED — fail closed.
        let ob = shift_in_range_obligation(BinOp::Shl, Ty::U8, ValueId::new(1), 8)
            .expect("out-of-range shift still has a representable (false) goal");
        assert!(
            !discharge(&ob, &refl_true()),
            "U8 shift by 8 is out of range (8 !< 8): the kernel must REFUSE the goal"
        );
    }

    #[test]
    fn test_change_coupling_amount_flips_verdict_and_goal() {
        // CHANGE-COUPLING on the shift AMOUNT (the field that governs this
        // obligation). FIXED type U8. amount 7 (in range) vs amount 8 (out of
        // range): BOTH the goal Expr's amount arg AND the kernel verdict move.
        let ob_in =
            shift_in_range_obligation(BinOp::LShr, Ty::U8, ValueId::new(1), 7).expect("in-range");
        let ob_out = shift_in_range_obligation(BinOp::LShr, Ty::U8, ValueId::new(1), 8)
            .expect("representable out-of-range goal");

        // The goals differ in exactly the amount argument of Nat.blt.
        assert_ne!(
            ob_in.goal, ob_out.goal,
            "the goal Expr is change-coupled: changing the shift amount changed the goal"
        );
        assert_eq!(
            ob_in.goal.get_app_args()[1].get_app_args()[0],
            &Expr::nat_lit(7),
            "in-range goal amount arg is 7"
        );
        assert_eq!(
            ob_out.goal.get_app_args()[1].get_app_args()[0],
            &Expr::nat_lit(8),
            "out-of-range goal amount arg is 8"
        );

        // And the verdict flips with the field edit.
        assert!(
            discharge(&ob_in, &refl_true()),
            "U8 shift by 7 in range => PROVEN"
        );
        assert!(
            !discharge(&ob_out, &refl_true()),
            "U8 shift by 8 out of range => UNVERIFIED: verdict flipped with the amount edit"
        );
    }

    #[test]
    fn test_change_coupling_shl_to_add_fails_closed() {
        // CHANGE-COUPLING (op change). The encoder only mints a goal for shift
        // ops; a non-shift `BinOp` fails closed rather than reusing the shift
        // goal — the ShiftInRange analogue of fused_overflow's add->sub test.
        assert!(
            shift_in_range_goal(BinOp::Shl, Ty::U32, 3).is_ok(),
            "Shl has a representable shift-range goal"
        );
        assert!(
            matches!(
                shift_in_range_goal(BinOp::Add, Ty::U32, 3),
                Err(ShiftLoweringError::NotAShift(BinOp::Add))
            ),
            "changing op Shl -> Add must re-shape (fail closed), not reuse the shift goal"
        );
    }

    #[test]
    fn test_no_bit_width_type_fails_closed() {
        // A type with no static bit width cannot form the modular in-range goal.
        assert!(
            matches!(
                shift_in_range_goal(BinOp::Shl, Ty::Unit, 3),
                Err(ShiftLoweringError::NoBitWidth(_))
            ),
            "a width-less type must fail closed, not mint a vacuous goal"
        );
    }
}
