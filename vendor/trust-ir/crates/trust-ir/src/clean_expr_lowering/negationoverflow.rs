// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FUSION (design 2026-06-20-fusion-obligation-as-clean-expr), the
//! **NegationOverflow** obligation kind.
//!
//! Negating a signed integer overflows exactly when the operand is the type's
//! minimum value: for an N-bit signed type, `MIN = -2^(N-1)`, and `-MIN` is not
//! representable (it would be `+2^(N-1)`, one past `MAX = 2^(N-1) - 1`). The
//! obligation is therefore **`operand != type MIN`**.
//!
//! This file is the self-contained per-kind encoder, mirroring the OVERFLOW
//! pair in [`crate::clean_expr_lowering`]:
//!   - [`negation_overflow_goal`]  — builds the kernel-checkable proposition
//!     from the node's OWN fields (`UnOp::Neg`, the signed `ty`, the operand
//!     literal), using `clean_kernel` constructors only.
//!   - [`negation_overflow_obligation`] — wraps the goal in an
//!     [`crate::proof::ExprObligation`] with the node-sourced operand-fact
//!     hypothesis.
//!
//! Like the overflow encoder, the goal is the kernel-checkable *negation* of
//! the unsafe condition, in the same `@Eq Bool <decision-bool> Bool.false`
//! shape `trust-certify` accepts: here the decision bool is
//! `Nat.beq operand MIN`, which the kernel's native `Nat.beq` reducer evaluates.
//! When `operand != MIN` the bool δι-reduces to `Bool.false` and the
//! hand/ay-minted `@Eq.refl Bool Bool.false` term type-checks; when
//! `operand == MIN` it reduces to `Bool.true` and the kernel REFUSES the
//! proof (fail closed) — the verdict is intrinsic to the kernel, not a flag.
//!
//! NAMED TRUST BOUNDARY (ay BV decision, kept named): the operand is a *signed*
//! bit-vector value, but the goal encodes its and MIN's bit-patterns as `Nat`
//! (`MIN`'s magnitude `2^(N-1)`, and the operand's unsigned reinterpretation).
//! Equality of the unsigned reinterpretations is equivalent to equality of the
//! bit-patterns, so `operand != MIN` is faithful; the int-vs-BV modeling choice
//! that this is the right proposition for "signed negation does not overflow"
//! is the stated assumption, not silently absorbed by carrying an `Expr`.
//!
//! The whole module is gated on `clean-expr` so the default zero-dependency
//! trust-ir format build never references clean-kernel.

use crate::inst::UnOp;
use crate::proof::ExprObligation;
use crate::ty::Ty;
use crate::value::ValueId;
use clean_kernel::{BigNat, Expr, Level, Name};

/// Errors the NegationOverflow encoder can fail-closed with, rather than
/// minting a wrong or vacuous goal for an unsupported shape.
///
/// SELF-CONTAINED MIRROR of [`crate::clean_expr_lowering::LoweringError`]: this
/// file is written without editing the shared error enum (parallel-agent
/// conflict avoidance). The integrator should fold these into the shared
/// `LoweringError` — `NoBitWidth(Ty)` already exists there; only the two new
/// fail-closed cases below (`UnsupportedUnOp`, `UnsignedNegation`) are new and
/// must be added to the shared enum. See the kind report's `integrationNote`.
///
/// Manual `Display`/`Error` impls (not `thiserror`): the `trust-ir` crate keeps
/// zero required external dependencies, and the `clean-expr` feature only adds
/// `clean-kernel`, not an error-derive crate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NegationOverflowError {
    /// The instruction's type carries no bit width, so the signed `MIN` literal
    /// (`2^(bit_width-1)`) cannot be formed.
    NoBitWidth(Ty),
    /// The unary op is not `Neg`. NegationOverflow is a `UnOp::Neg`-only
    /// concern; a node edit (`Neg -> Not`) must re-shape the obligation rather
    /// than reuse the negation goal (the change-coupling discipline).
    UnsupportedUnOp(UnOp),
    /// The operand type is unsigned (or non-integer). Negation overflow is a
    /// *signed* phenomenon (unsigned `-x` wraps but is defined / has no `MIN`
    /// overflow obligation), so an unsigned/non-integer type fails closed
    /// instead of minting a goal about a non-existent signed `MIN`.
    UnsignedNegation(Ty),
}

impl core::fmt::Display for NegationOverflowError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            NegationOverflowError::NoBitWidth(ty) => {
                write!(
                    f,
                    "negation-overflow obligation: type {ty:?} has no bit width"
                )
            }
            NegationOverflowError::UnsupportedUnOp(op) => {
                write!(
                    f,
                    "negation-overflow obligation: unary op {op:?} is not Neg"
                )
            }
            NegationOverflowError::UnsignedNegation(ty) => {
                write!(
                    f,
                    "negation-overflow obligation: type {ty:?} is not signed; \
                     negation overflow is a signed-only concern"
                )
            }
        }
    }
}

impl std::error::Error for NegationOverflowError {}

/// `2^pow` as a Clean `Nat` literal. `pow` is the magnitude exponent of the
/// signed `MIN` (`bit_width - 1`), so for I8 `pow = 7` and `MIN`'s magnitude is
/// `2^7 = 128`; for I128 `pow = 127`, handled via `BigNat::from_limbs`.
///
/// Same construction as `clean_expr_lowering::modulus_lit`, generalized to an
/// arbitrary power so the negation encoder needs no shared-module change.
fn pow2_lit(pow: u32) -> Expr {
    if pow < 64 {
        Expr::nat_lit(1u64 << pow)
    } else {
        let whole = (pow / 64) as usize;
        let rem = pow % 64;
        let mut limbs = vec![0u64; whole];
        limbs.push(1u64 << rem);
        Expr::bignat_lit(BigNat::from_limbs(limbs))
    }
}

/// `Nat.beq a b` — the kernel's native decidable Nat-equality bool. The
/// `Nat.beq` reducer evaluates it on literal arguments (capped at the same
/// u128 / 2-limb-BigNat range that covers every signed `MIN` up to I128).
fn nat_beq(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.beq"), [a, b])
}

/// The "does NOT overflow" wrapper: `@Eq Bool decision Bool.false`.
///
/// Identical shape to `clean_expr_lowering::not_overflow_goal` — the
/// kernel-checkable assertion that the decision bool is `false`, the form
/// `trust-certify`'s gate accepts. Here `decision = Nat.beq operand MIN`, so the
/// goal reads "operand equals MIN is false", i.e. `operand != MIN`.
fn decision_is_false(decision: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            Expr::const_str("Bool"),
            decision,
            Expr::const_str("Bool.false"),
        ],
    )
}

/// The unsigned bit-pattern reinterpretation of a two's-complement signed value,
/// as the `Nat` the goal compares against `MIN`. For an N-bit signed value `v`,
/// the bit-pattern as an unsigned integer is `v` if `v >= 0` else `v + 2^N`.
/// This is the NAMED BV boundary: equality of these reinterpretations is
/// equality of bit-patterns, and `MIN`'s reinterpretation is `2^(N-1)`.
fn signed_bits_as_nat(operand: i128, bits: u32) -> u128 {
    if operand >= 0 {
        operand as u128
    } else if bits >= 128 {
        // 2^128 wraps u128; for I128 the reinterpretation is computed mod 2^128
        // via wrapping add, which is exactly two's-complement bit reinterpretation.
        (operand as u128).wrapping_add(0) // i128->u128 cast IS the bit pattern
    } else {
        (operand + (1i128 << bits)) as u128
    }
}

/// A `Nat` literal for a (possibly > u64) magnitude, choosing `nat_lit` or a
/// 2-limb `BigNat` so values up to `2^128 - 1` (the I128 range) are exact.
fn nat_lit_u128(v: u128) -> Expr {
    if v <= u64::MAX as u128 {
        Expr::nat_lit(v as u64)
    } else {
        let lo = (v & u64::MAX as u128) as u64;
        let hi = (v >> 64) as u64;
        Expr::bignat_lit(BigNat::from_limbs(vec![lo, hi]))
    }
}

/// Build the no-negation-overflow goal `Expr` for an `Inst::UnOp { op: Neg, .. }`
/// from its OWN fields. `MIN`'s magnitude comes from `ty` (`2^(bit_width-1)`);
/// the operand comes from the resolved operand literal the lowering context
/// carries (its two's-complement bit reinterpretation as a `Nat`).
///
/// The proposition is `@Eq Bool (Nat.beq operand_bits MIN_bits) Bool.false`,
/// i.e. "the operand is not the type minimum". Fails closed for non-`Neg` ops
/// and for unsigned/non-integer types so a node edit re-shapes the obligation
/// rather than reusing a stale negation goal.
///
/// `operand` is the concrete signed operand value the node implies; in the
/// lowering pipeline it is sourced from the resolved operand context.
pub fn negation_overflow_goal(
    op: UnOp,
    ty: Ty,
    operand: i128,
) -> Result<Expr, NegationOverflowError> {
    if op != UnOp::Neg {
        return Err(NegationOverflowError::UnsupportedUnOp(op));
    }
    if !ty.is_signed() {
        return Err(NegationOverflowError::UnsignedNegation(ty));
    }
    let bits = ty
        .bit_width()
        .ok_or_else(|| NegationOverflowError::NoBitWidth(ty.clone()))?;
    // MIN's bit-pattern reinterpretation is 2^(N-1).
    let min_lit = pow2_lit(bits - 1);
    let operand_lit = nat_lit_u128(signed_bits_as_nat(operand, bits));
    Ok(decision_is_false(nat_beq(operand_lit, min_lit)))
}

/// Build the full [`ExprObligation`] (goal + node-sourced operand hypothesis)
/// for an `Inst::UnOp { op: Neg, .. }`, ready to stamp as
/// [`crate::proof::ProofAnnotation::Goal`] in the lowering builder chain.
///
/// The hypothesis is the node's own operand fact: the operand value is a `Nat`
/// in the kernel context, sourced from the node, not an external model.
pub fn negation_overflow_obligation(
    op: UnOp,
    ty: Ty,
    operand_value: ValueId,
    operand: i128,
) -> Result<ExprObligation, NegationOverflowError> {
    let goal = negation_overflow_goal(op, ty, operand)?;
    Ok(ExprObligation::new(goal).with_hypothesis(
        format!("%{}", operand_value.index()),
        Expr::const_str("Nat"),
    ))
}

// ---------------------------------------------------------------------------
// Unit tests: the goal Expr is well-typed via clean_kernel check_type, plus a
// change-coupling assertion on a relevant field (the operand value).
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, LocalContext, TypeChecker};

    /// `@Eq.refl Bool Bool.false : @Eq Bool x Bool.false` whenever `x` δι-reduces
    /// to `Bool.false`. The kernel does the `Nat.beq` reduction itself, so this
    /// term type-checks against the goal exactly when `operand != MIN`.
    fn refl_false() -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [Expr::const_str("Bool"), Expr::const_str("Bool.false")],
        )
    }

    /// Kernel-discharge a goal: build the local context from the obligation's
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
    fn test_goal_shape_i8_min_is_128() {
        // I8: MIN = -128, bit-pattern reinterpretation 2^7 = 128. The goal is
        // @Eq Bool (Nat.beq operand 128) Bool.false.
        let goal = negation_overflow_goal(UnOp::Neg, Ty::I8, 5)
            .expect("signed Neg has a representable goal");
        let eq_args = goal.get_app_args();
        // @Eq Bool <decision> Bool.false
        assert_eq!(eq_args.len(), 3, "Eq takes (Bool, decision, false)");
        let decision = eq_args[1];
        let beq_args = decision.get_app_args();
        assert_eq!(beq_args.len(), 2, "Nat.beq takes (operand, MIN)");
        assert_eq!(
            beq_args[1],
            &Expr::nat_lit(128),
            "I8 MIN magnitude on the goal must be 2^7 = 128"
        );
    }

    #[test]
    fn test_goal_is_well_typed_via_check_type() {
        // The goal is a Prop (Eq @ Bool ...): it must itself type-check, and the
        // safe-case proof term must check against it.
        let ob = negation_overflow_obligation(UnOp::Neg, Ty::I8, ValueId::new(0), 5)
            .expect("safe operand has a goal");
        // Well-typedness: the goal Expr infers a sort (it is a Prop), and the
        // refl term checks against it (5 != 128 => Nat.beq reduces to false).
        let env = Environment::with_prelude();
        let tc = TypeChecker::new(&env);
        assert!(
            tc.infer_type(&ob.goal).is_ok(),
            "the negation-overflow goal Expr must be well-typed (a Prop)"
        );
        assert!(
            discharge(&ob, &refl_false()),
            "I8 operand 5 != MIN(-128): the kernel must discharge the goal"
        );
    }

    #[test]
    fn test_min_operand_is_unverified_fail_closed() {
        // I8 MIN = -128: negating it overflows. operand bit-pattern = 128 = MIN
        // bits, so Nat.beq 128 128 reduces to Bool.true, NOT false => REFUSED.
        let ob = negation_overflow_obligation(UnOp::Neg, Ty::I8, ValueId::new(0), -128)
            .expect("the goal is still formed; it is just not provable");
        assert!(
            !discharge(&ob, &refl_false()),
            "I8 -128 IS MIN: negation overflows, the kernel must REFUSE the goal"
        );
    }

    #[test]
    fn test_change_coupling_operand_flips_verdict_and_goal() {
        // CHANGE-COUPLING on the operand field: mutate the operand value, same
        // type I8. Both the goal Expr (its Nat.beq operand arg) AND the verdict
        // move, because the goal is materialized from the node's own operand.
        let safe =
            negation_overflow_obligation(UnOp::Neg, Ty::I8, ValueId::new(0), 5).expect("safe goal");
        let unsafe_ = negation_overflow_obligation(UnOp::Neg, Ty::I8, ValueId::new(0), -128)
            .expect("min goal");

        // The goal Expr differs in the operand argument of Nat.beq.
        assert_ne!(
            safe.goal, unsafe_.goal,
            "changing the operand changed the on-node goal Expr"
        );
        assert_eq!(
            safe.goal.get_app_args()[1].get_app_args()[0],
            &Expr::nat_lit(5),
            "safe goal compares operand 5"
        );
        assert_eq!(
            unsafe_.goal.get_app_args()[1].get_app_args()[0],
            &Expr::nat_lit(128),
            "unsafe goal compares operand bits 128 (== MIN bits)"
        );

        // And the verdict flips.
        assert!(discharge(&safe, &refl_false()), "5 != MIN => PROVEN");
        assert!(
            !discharge(&unsafe_, &refl_false()),
            "-128 == MIN => UNVERIFIED (fail closed)"
        );
    }

    #[test]
    fn test_change_coupling_widen_i8_to_i64() {
        // CHANGE-COUPLING on `ty`: the SAME operand value (-128) is MIN for I8
        // (overflow) but a perfectly representable interior value for I64
        // (MIN = -2^63), so the verdict flips with the type edit and the goal's
        // MIN literal changes from 2^7 to 2^63.
        let i8_min = negation_overflow_obligation(UnOp::Neg, Ty::I8, ValueId::new(0), -128)
            .expect("i8 goal");
        let i64_ok = negation_overflow_obligation(UnOp::Neg, Ty::I64, ValueId::new(0), -128)
            .expect("i64 goal");
        assert_ne!(
            i8_min.goal, i64_ok.goal,
            "widening the type changed the on-node goal Expr (MIN literal)"
        );
        assert!(!discharge(&i8_min, &refl_false()), "-128 IS I8 MIN");
        assert!(
            discharge(&i64_ok, &refl_false()),
            "-128 is interior for I64 => PROVEN; verdict flipped with the type edit"
        );
    }

    #[test]
    fn test_unsigned_fails_closed() {
        // Negation overflow is signed-only: an unsigned type fails closed rather
        // than minting a goal about a non-existent signed MIN.
        let r = negation_overflow_goal(UnOp::Neg, Ty::U8, 0);
        assert_eq!(r, Err(NegationOverflowError::UnsignedNegation(Ty::U8)));
    }

    #[test]
    fn test_non_neg_unop_fails_closed() {
        // op change Neg -> Not must re-shape, not reuse the negation goal.
        let r = negation_overflow_goal(UnOp::Not, Ty::I8, 5);
        assert_eq!(r, Err(NegationOverflowError::UnsupportedUnOp(UnOp::Not)));
    }
}
