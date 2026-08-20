// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FUSION (design 2026-06-20-fusion-obligation-as-clean-expr): the per-kind
//! `Expr` encoder for the **DivNonZero** obligation (divisor != 0 for the
//! integer division ops `UDiv` / `SDiv` / `URem` / `SRem`).
//!
//! This is the divisor-non-zero sibling of `clean_expr_lowering::overflow_goal`
//! / `overflow_obligation`. It takes a division node's OWN fields (the `BinOp`,
//! the operand type `ty`, the two operand `ValueId`s, and the divisor's concrete
//! value as a `Nat` fact) and returns the obligation as a `clean_kernel::Expr`,
//! so the goal is born from the same field bindings that construct the
//! `Inst::BinOp`. Program-change => Expr-change is structural, not a test
//! discipline.
//!
//! ## The goal shape (mirrors the overflow `Eq Bool _ Bool.false` shape)
//!
//! "divisor != 0" is encoded as the kernel-checkable Bool proposition
//!
//! ```text
//! @Eq Bool (Nat.beq divisor 0) Bool.false
//! ```
//!
//! i.e. "`divisor =? 0` is `false`". `Nat.beq` is a native prelude reducer, so
//! the kernel definitionally reduces `Nat.beq d 0` to `Bool.true` exactly when
//! `d == 0` and `Bool.false` otherwise. The hand proof term
//! `@Eq.refl Bool Bool.false` (the SAME term that discharges the overflow goal)
//! is accepted by the kernel iff the divisor genuinely is non-zero — fail-closed
//! on a zero divisor. This is the de Bruijn criterion: the kernel proves the
//! object's own obligation, not a comparison to an external `.lean`.
//!
//! ## Integration note (this file is self-contained on purpose)
//!
//! The `clean-expr` feature exposes this module at
//! [`crate::clean_expr_lowering::divnonzero`]. The module graph is integrated,
//! but this file does not establish that a producer lowering site calls it. A
//! consumer can construct the node-coupled obligation through the canonical
//! path:
//!
//! ```rust
//! use trust_ir::clean_expr_lowering::divnonzero::divnonzero_obligation;
//! use trust_ir::{BinOp, Ty, ValueId};
//!
//! let obligation = divnonzero_obligation(
//!     BinOp::UDiv,
//!     Ty::U32,
//!     ValueId::new(0),
//!     ValueId::new(1),
//!     7,
//! )
//! .expect("a non-zero integer divisor has a DivNonZero obligation");
//! ```
//!
//! A producer that uses this helper must stamp the returned obligation in the
//! same builder chain as its cheap `ProofAnnotation::DivNonZero` marker. The
//! example demonstrates obligation construction only; it is not evidence of a
//! production bridge call site.
//!
//! The whole module is gated on `clean-expr` so the default zero-dependency
//! trust-ir format build never references clean-kernel.

use crate::inst::BinOp;
use crate::proof::ExprObligation;
use crate::ty::Ty;
use crate::value::ValueId;
use clean_kernel::{Expr, Level, Name};

/// Errors the DivNonZero encoder can fail-closed with, rather than minting a
/// wrong or vacuous goal for an unsupported shape.
///
/// Manual `Display`/`Error` impls (not `thiserror`): the `trust-ir` crate keeps
/// zero required external dependencies, and the `clean-expr` feature only adds
/// `clean-kernel`, not an error-derive crate. Mirrors
/// `clean_expr_lowering::LoweringError`; kept as its own type so this file stays
/// self-contained (no shared-module edit). The integrator may merge the two
/// variants into the shared `LoweringError` if desired.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DivNonZeroLoweringError {
    /// The `BinOp` is not one of the integer division ops that carry a
    /// divisor-non-zero obligation (`UDiv` / `SDiv` / `URem` / `SRem`). Fails
    /// closed so a node edit (e.g. `UDiv -> Add`) re-shapes the obligation
    /// rather than reusing a stale div goal — the analogue of the overflow
    /// encoder's `UnsupportedOp`.
    NotADivisionOp(BinOp),
    /// The operand type is not an integer type (e.g. a float or aggregate
    /// type), so it is not an integer-division shape this encoder models. Fails
    /// closed. (Float div-by-zero is defined IEEE behaviour, not a `DivNonZero`
    /// obligation.)
    NonIntegerType(Ty),
}

impl core::fmt::Display for DivNonZeroLoweringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DivNonZeroLoweringError::NotADivisionOp(op) => {
                write!(
                    f,
                    "div-non-zero obligation: op {op:?} is not an integer division op"
                )
            }
            DivNonZeroLoweringError::NonIntegerType(ty) => {
                write!(
                    f,
                    "div-non-zero obligation: type {ty:?} is not an integer type"
                )
            }
        }
    }
}

impl std::error::Error for DivNonZeroLoweringError {}

/// True iff `op` is an integer division/remainder op that carries a
/// divisor-non-zero obligation. Float div (`FDiv`/`FRem`) is excluded: IEEE-754
/// division by zero is a defined result (±inf / NaN), not UB, so it carries no
/// `DivNonZero` obligation.
fn is_integer_division(op: BinOp) -> bool {
    matches!(op, BinOp::UDiv | BinOp::SDiv | BinOp::URem | BinOp::SRem)
}

/// `Nat.beq a b` — boolean equality on `Nat`, a native prelude reducer.
fn nat_beq(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.beq"), [a, b])
}

/// The "is `Bool.false`" wrapper: `@Eq Bool inner Bool.false`.
///
/// Identical in shape to `clean_expr_lowering::not_overflow_goal` — the
/// kernel-checkable negation of a Bool claim, the same shape trust-certify's
/// "kernel proves the obligation" gate accepts and that `@Eq.refl Bool
/// Bool.false` discharges.
fn bool_is_false(inner: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            Expr::const_str("Bool"),
            inner,
            Expr::const_str("Bool.false"),
        ],
    )
}

/// Build the divisor-non-zero goal `Expr` for an `Inst::BinOp` division from its
/// OWN fields.
///
/// The proposition is `@Eq Bool (Nat.beq divisor 0) Bool.false` — "the divisor
/// equals zero is false", i.e. the divisor is non-zero. `divisor` is the
/// concrete divisor value the node implies, as a `Nat` literal; in the lowering
/// pipeline it is sourced from the resolved operand context (the divisor of the
/// division — the `rhs`).
///
/// Fails closed for non-division ops (so a node edit re-shapes the obligation
/// rather than reusing the div goal) and for non-integer types (float / opaque),
/// mirroring `overflow_goal`'s fail-closed envelope.
pub fn divnonzero_goal(op: BinOp, ty: Ty, divisor: u64) -> Result<Expr, DivNonZeroLoweringError> {
    if !is_integer_division(op) {
        return Err(DivNonZeroLoweringError::NotADivisionOp(op));
    }
    // An integer division's operand type must be an integer; reject float /
    // aggregate / pointer shapes (those are not integer-division nodes). Note
    // floats DO carry a bit width, so the check is `is_integer`, not
    // `bit_width().is_some()`.
    if !ty.is_integer() {
        return Err(DivNonZeroLoweringError::NonIntegerType(ty));
    }
    Ok(bool_is_false(nat_beq(
        Expr::nat_lit(divisor),
        Expr::nat_lit(0),
    )))
}

/// Build the full [`ExprObligation`] (goal + node-sourced operand hypotheses)
/// for an `Inst::BinOp` division, ready to stamp as
/// [`crate::proof::ProofAnnotation::Goal`] in the lowering builder chain that
/// stamps the cheap `ProofAnnotation::DivNonZero` marker.
///
/// The hypotheses are the node's own operand facts: each operand value (the
/// dividend `lhs` and divisor `rhs`) is a `Nat` in the kernel context, sourced
/// from the node, not an external model — mirroring `overflow_obligation`.
pub fn divnonzero_obligation(
    op: BinOp,
    ty: Ty,
    lhs: ValueId,
    rhs: ValueId,
    divisor: u64,
) -> Result<ExprObligation, DivNonZeroLoweringError> {
    let goal = divnonzero_goal(op, ty, divisor)?;
    Ok(ExprObligation::new(goal)
        .with_hypothesis(format!("%{}", lhs.index()), Expr::const_str("Nat"))
        .with_hypothesis(format!("%{}", rhs.index()), Expr::const_str("Nat")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, LocalContext, TypeChecker};

    /// The hand proof term `@Eq.refl Bool Bool.false` — the SAME term that
    /// discharges the overflow goal. Proves `@Eq Bool x Bool.false` exactly when
    /// `x` reduces to `Bool.false`; the kernel does the `Nat.beq` reduction.
    fn refl_false() -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [Expr::const_str("Bool"), Expr::const_str("Bool.false")],
        )
    }

    /// Kernel-discharge an obligation: build the local context from its
    /// node-sourced hypotheses, then `check_type(term, &goal)` under
    /// `Environment::with_prelude()` ONLY — the same gate trust-certify uses,
    /// no external `.lean`. Returns true iff the kernel accepts.
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
    fn test_divnonzero_goal_shape_is_function_of_the_node() {
        // The goal is a FUNCTION of the node's fields: head `Eq`, with the inner
        // Bool being `Nat.beq divisor 0`.
        // goal = @Eq Bool (Nat.beq 7 0) Bool.false
        let goal = divnonzero_goal(BinOp::UDiv, Ty::U32, 7).expect("u32 udiv has a goal");
        let eq_args = goal.get_app_args();
        assert_eq!(eq_args.len(), 3, "@Eq takes (Bool, beq-expr, Bool.false)");
        assert_eq!(eq_args[0], &Expr::const_str("Bool"), "Eq is over Bool");
        assert_eq!(
            eq_args[2],
            &Expr::const_str("Bool.false"),
            "the divisor-is-zero Bool must be claimed false"
        );
        // inner = Nat.beq 7 0
        let beq_args = eq_args[1].get_app_args();
        assert_eq!(beq_args.len(), 2, "Nat.beq takes (divisor, 0)");
        assert_eq!(
            beq_args[0],
            &Expr::nat_lit(7),
            "the divisor operand is read off the node"
        );
        assert_eq!(beq_args[1], &Expr::nat_lit(0), "compared against zero");
    }

    #[test]
    fn test_divnonzero_goal_is_well_typed_via_check_type() {
        // WELL-TYPEDNESS: the kernel must accept the proof term against the goal
        // for a non-zero divisor — which is exactly type-checking the goal Prop
        // (a malformed goal would not type-check) AND discharging it.
        let ob = divnonzero_obligation(BinOp::UDiv, Ty::U32, ValueId::new(0), ValueId::new(1), 7)
            .expect("u32 udiv 7 has a representable obligation");
        assert!(
            discharge(&ob, &refl_false()),
            "divisor 7 != 0: the kernel must type-check refl against the well-typed goal"
        );
    }

    #[test]
    fn test_divnonzero_zero_divisor_fails_closed() {
        // A zero divisor: `Nat.beq 0 0` reduces to `Bool.true`, so the goal
        // becomes `@Eq Bool Bool.true Bool.false` and the refl proof is REFUSED.
        let ob = divnonzero_obligation(BinOp::UDiv, Ty::U32, ValueId::new(0), ValueId::new(1), 0)
            .expect("the obligation is still representable; it just won't discharge");
        assert!(
            !discharge(&ob, &refl_false()),
            "divisor 0: the kernel must REFUSE to discharge — fail closed"
        );
    }

    #[test]
    fn test_divnonzero_change_coupling_divisor_field() {
        // CHANGE-COUPLING (divisor field). Mutate ONLY the divisor value the node
        // implies (7 -> 0) and BOTH the goal Expr AND the verdict move, because
        // the goal is materialized from that field.
        let ob_nonzero =
            divnonzero_obligation(BinOp::SRem, Ty::I64, ValueId::new(0), ValueId::new(1), 7)
                .expect("srem 7 obligation");
        let ob_zero =
            divnonzero_obligation(BinOp::SRem, Ty::I64, ValueId::new(0), ValueId::new(1), 0)
                .expect("srem 0 obligation");

        // The goal Expr changed (its divisor argument).
        assert_ne!(
            ob_nonzero.goal, ob_zero.goal,
            "the goal Expr is change-coupled to the divisor field"
        );
        // And the verdict flipped.
        assert!(discharge(&ob_nonzero, &refl_false()), "divisor 7 => PROVEN");
        assert!(
            !discharge(&ob_zero, &refl_false()),
            "divisor 0 => UNVERIFIED: verdict flipped with the field edit"
        );
    }

    #[test]
    fn test_divnonzero_non_division_op_fails_closed() {
        // CHANGE-COUPLING (op change). The encoder only mints the div goal; a
        // non-division op (e.g. Add) fails closed rather than reusing the div
        // goal — the analogue of the overflow encoder's add->sub re-shape.
        let div = divnonzero_goal(BinOp::URem, Ty::U16, 5);
        assert!(div.is_ok(), "urem has a representable goal");
        let add = divnonzero_goal(BinOp::Add, Ty::U16, 5);
        assert_eq!(
            add,
            Err(DivNonZeroLoweringError::NotADivisionOp(BinOp::Add)),
            "changing op Div -> Add must re-shape the obligation, not reuse the div goal"
        );
    }

    #[test]
    fn test_divnonzero_float_type_fails_closed() {
        // Float division (FDiv) has no DivNonZero obligation (IEEE div-by-zero is
        // defined), and float types have no bit width: fail closed on both axes.
        let by_op = divnonzero_goal(BinOp::FDiv, Ty::F64, 3);
        assert_eq!(
            by_op,
            Err(DivNonZeroLoweringError::NotADivisionOp(BinOp::FDiv)),
            "FDiv is not an integer division op"
        );
        // Even an integer-division op over a float type fails closed on the type.
        let by_ty = divnonzero_goal(BinOp::UDiv, Ty::F64, 3);
        assert_eq!(
            by_ty,
            Err(DivNonZeroLoweringError::NonIntegerType(Ty::F64)),
            "a float operand type has no bit width"
        );
    }
}
