// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FUSION (design 2026-06-20-fusion-obligation-as-clean-expr): the
//! per-kind `Expr` encoder for the **CastOverflow** obligation kind — a
//! narrowing integer cast must produce a value that FITS the destination
//! type's range.
//!
//! This file follows the OVERFLOW pattern byte-for-byte (see the sibling
//! `overflow_goal` / `overflow_obligation` in `clean_expr_lowering`):
//!
//! - [`cast_overflow_goal`] takes the node's OWN fields (`op`, `src_ty`,
//!   `dst_ty`, the concrete operand value) and returns the kernel-checkable
//!   proposition as a `clean_kernel::Expr`. The destination modulus
//!   `2^bit_width(dst_ty)` comes from `dst_ty` (a field of the OBJECT); the
//!   value comes from the node's resolved operand fact. Nothing is read from an
//!   external `.lean`.
//! - [`cast_overflow_obligation`] wraps the goal in an [`ExprObligation`] and
//!   adds the node-sourced operand hypothesis (`%operand : Nat`).
//!
//! ## The proposition
//!
//! A narrowing unsigned cast `Trunc : src_ty -> dst_ty` does NOT overflow iff
//! the source value `v` is below the destination modulus `M = 2^bit_width(dst)`:
//!
//! ```text
//! fits(v)  ==  NOT (M <= v)  ==  Nat.ble M v == Bool.false
//! ```
//!
//! So the goal is the same shape as the overflow kind's no-overflow goal — a
//! `Bool`-valued `Nat.ble` wrapped in `@Eq Bool _ Bool.false` — which means the
//! SAME hand-supplied `@Eq.refl Bool Bool.false` proof term discharges it, and
//! the kernel does the real reduction work (`Nat.ble M v -> Bool.false` exactly
//! when `v < M`). This is the de Bruijn criterion: the kernel proves the
//! object's own obligation; it is not told the answer.
//!
//! Fail-closed: [`cast_overflow_goal`] returns `Err` for any cast op / type
//! shape outside the supported narrowing-integer fragment, so a node edit
//! (e.g. `Trunc -> Bitcast`, or a non-narrowing dst) re-shapes the obligation
//! rather than silently reusing a stale "fits" goal. This mirrors
//! `overflow_goal`'s `UnsupportedOp` fail-closed behaviour.
//!
//! The whole module is gated on `clean-expr`; the default zero-dependency
//! trust-ir format build never references clean-kernel.

use crate::inst::CastOp;
use crate::proof::ExprObligation;
use crate::ty::Ty;
use crate::value::ValueId;
use clean_kernel::{BigNat, Expr, Level, Name};

/// Errors the cast-overflow encoder can fail-closed with, rather than minting a
/// wrong or vacuous "fits" goal for an unsupported shape.
///
/// Manual `Display`/`Error` impls (not `thiserror`): the `trust-ir` crate keeps
/// zero required external dependencies, and the `clean-expr` feature only adds
/// `clean-kernel`, not an error-derive crate. This mirrors the sibling
/// `clean_expr_lowering::LoweringError`; it is a SEPARATE type here only so this
/// file stays self-contained (the integrator may merge the two — see notes).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CastLoweringError {
    /// The destination type carries no bit width (e.g. an aggregate / pointer),
    /// so the modular "fits" goal cannot be formed.
    NoBitWidth(Ty),
    /// The cast op is outside the narrowing-integer fragment this encoder
    /// supports. The fits-shaped goal must not be silently reused for a
    /// float / pointer / widening / bitcast node.
    UnsupportedOp(CastOp),
    /// The cast is not narrowing (destination width >= source width), so there
    /// is no range obligation to discharge — fail closed rather than mint a
    /// vacuously-true goal (a widening `ZExt`/`SExt` always fits and carries no
    /// CastOverflow obligation; reusing the narrowing goal would be wrong).
    NotNarrowing { src: Ty, dst: Ty },
}

impl core::fmt::Display for CastLoweringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            CastLoweringError::NoBitWidth(ty) => {
                write!(f, "cast-overflow obligation: type {ty:?} has no bit width")
            }
            CastLoweringError::UnsupportedOp(op) => {
                write!(
                    f,
                    "cast-overflow obligation: op {op:?} not supported by this encoder"
                )
            }
            CastLoweringError::NotNarrowing { src, dst } => {
                write!(
                    f,
                    "cast-overflow obligation: cast {src:?} -> {dst:?} is not narrowing; \
                     no range obligation"
                )
            }
        }
    }
}

impl std::error::Error for CastLoweringError {}

/// `2^bits` as a Clean `Nat` literal.
///
/// `BigNat::from_limbs` handles widths at/past `u64` (e.g. `2^64 = [0, 1]`
/// little-endian). Identical to `clean_expr_lowering::modulus_lit` /
/// `fused_overflow.rs::modulus_lit`; duplicated locally so this file is
/// self-contained (the integrator may hoist it — see notes).
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

fn nat_ble(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.ble"), [a, b])
}

/// The "value FITS the destination range" goal: `@Eq Bool out_of_range Bool.false`.
///
/// Same wrapper as `overflow_goal`'s `not_overflow_goal`: the kernel-checkable
/// negation of the out-of-range claim, the shape `trust-certify`'s
/// "kernel proves the obligation" gate accepts.
fn fits_goal(out_of_range: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            Expr::const_str("Bool"),
            out_of_range,
            Expr::const_str("Bool.false"),
        ],
    )
}

/// Build the cast-overflow ("value fits the destination type") goal `Expr` for
/// an `Inst::Cast` from its OWN fields.
///
/// Supported fragment: a narrowing **unsigned** integer cast (`CastOp::Trunc`)
/// where both `src_ty` and `dst_ty` are integer types and the destination is
/// strictly narrower. The proposition is
/// `@Eq Bool (Nat.ble (2^bit_width(dst)) value) Bool.false`, i.e. "the value
/// does not reach the destination modulus" — it fits in `dst_ty`.
///
/// The modulus comes from `dst_ty` (the OBJECT); the `value` comes from the
/// node's resolved operand fact. Fails closed for any op / type shape outside
/// the fragment so a node edit re-shapes the obligation rather than reusing a
/// stale goal — exactly `overflow_goal`'s fail-closed contract.
pub fn cast_overflow_goal(
    op: CastOp,
    src_ty: Ty,
    dst_ty: Ty,
    value: u64,
) -> Result<Expr, CastLoweringError> {
    match op {
        // `Trunc` is the canonical narrowing integer cast. The range obligation
        // is "the source value is below the destination modulus".
        CastOp::Trunc => {
            if !src_ty.is_integer() || !dst_ty.is_integer() {
                return Err(CastLoweringError::UnsupportedOp(op));
            }
            let src_bits = src_ty
                .bit_width()
                .ok_or_else(|| CastLoweringError::NoBitWidth(src_ty.clone()))?;
            let dst_bits = dst_ty
                .bit_width()
                .ok_or_else(|| CastLoweringError::NoBitWidth(dst_ty.clone()))?;
            // Narrowing only: a widening/equal cast always fits, so there is no
            // obligation — fail closed rather than mint a vacuous goal.
            if dst_bits >= src_bits {
                return Err(CastLoweringError::NotNarrowing {
                    src: src_ty,
                    dst: dst_ty,
                });
            }
            let modulus = modulus_lit(dst_bits);
            // out_of_range  ==  modulus <= value  ==  Nat.ble modulus value
            Ok(fits_goal(nat_ble(modulus, Expr::nat_lit(value))))
        }
        // Float casts, pointer casts, bitcasts, transmutes, fn-pointer reify,
        // and the widening integer casts (ZExt/SExt) are outside this
        // narrowing-fits fragment. Fail closed.
        other => Err(CastLoweringError::UnsupportedOp(other)),
    }
}

/// Build the full [`ExprObligation`] (goal + node-sourced operand hypothesis)
/// for an `Inst::Cast`, ready to stamp as
/// [`crate::proof::ProofAnnotation::Goal`] in the lowering builder chain.
///
/// The hypothesis is the node's own operand fact: the cast operand is a `Nat`
/// in the kernel context, sourced from the node, not an external model.
pub fn cast_overflow_obligation(
    op: CastOp,
    src_ty: Ty,
    dst_ty: Ty,
    operand: ValueId,
    value: u64,
) -> Result<ExprObligation, CastLoweringError> {
    let goal = cast_overflow_goal(op, src_ty, dst_ty, value)?;
    Ok(ExprObligation::new(goal)
        .with_hypothesis(format!("%{}", operand.index()), Expr::const_str("Nat")))
}

// --- Unit tests: build the goal Expr + assert well-typed via check_type ------

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, Expr, Level, LocalContext, Name, TypeChecker};

    /// A hand-supplied proof term `@Eq.refl Bool Bool.false` — the same term
    /// fused_overflow uses. Proves the fits-goal exactly when its out-of-range
    /// `Bool` reduces to `Bool.false`; the kernel does the reduction itself.
    fn refl_false() -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [Expr::const_str("Bool"), Expr::const_str("Bool.false")],
        )
    }

    /// Kernel-discharge an obligation: push its node-sourced hypotheses into a
    /// `LocalContext`, then `check_type(term, &goal)` under
    /// `Environment::with_prelude()` ONLY — the same gate trust-certify uses.
    fn discharge(ob: &ExprObligation, term: &Expr) -> bool {
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
        tc.check_type(term, &ob.goal).is_ok()
    }

    #[test]
    fn test_goal_shape_u64_to_u8() {
        // Trunc U64 -> U8: dst modulus is 2^8 = 256. goal =
        // @Eq Bool (Nat.ble 256 value) Bool.false.
        let goal = cast_overflow_goal(CastOp::Trunc, Ty::U64, Ty::U8, 200)
            .expect("narrowing u64->u8 has a representable goal");
        let eq_args = goal.get_app_args();
        // @Eq Bool <out-of-range-bool> Bool.false
        assert_eq!(eq_args.len(), 3, "@Eq takes (ty, lhs, rhs)");
        let out_of_range = eq_args[1];
        let ble_args = out_of_range.get_app_args();
        assert_eq!(ble_args.len(), 2, "Nat.ble takes (modulus, value)");
        assert_eq!(
            ble_args[0],
            &Expr::nat_lit(256),
            "U8 destination modulus must be 2^8 = 256"
        );
    }

    #[test]
    fn test_goal_is_well_typed_and_proven_in_range() {
        // 200 fits in U8 (200 < 256): the goal is well-typed AND the kernel
        // reduces `Nat.ble 256 200` to `Bool.false` and accepts `rfl`.
        let ob = cast_overflow_obligation(CastOp::Trunc, Ty::U64, Ty::U8, ValueId::new(0), 200)
            .expect("narrowing u64->u8 has a representable obligation");
        assert!(
            discharge(&ob, &refl_false()),
            "200 fits in U8 => the kernel must discharge the fits-goal (well-typed + PROVEN)"
        );
    }

    #[test]
    fn test_out_of_range_is_unverified_fail_closed() {
        // 300 does NOT fit in U8 (300 >= 256): the kernel reduces the
        // out-of-range Bool to `Bool.true`, so the fits-goal becomes
        // `Eq Bool Bool.true Bool.false` and `rfl` is REFUSED.
        let ob = cast_overflow_obligation(CastOp::Trunc, Ty::U64, Ty::U8, ValueId::new(0), 300)
            .expect("narrowing u64->u8 has a representable obligation");
        assert!(
            !discharge(&ob, &refl_false()),
            "300 does not fit in U8 => the kernel must REFUSE the fits-goal (fail closed)"
        );
    }

    #[test]
    fn test_change_coupling_dst_ty_u8_to_u16() {
        // CHANGE-COUPLING on the `dst_ty` field: widen the destination U8 -> U16
        // with a FIXED value 300. Both the goal Expr (its modulus argument) AND
        // the verdict move, because the modulus is read off `dst_ty`.
        let value = 300;

        // dst = U8: modulus 256; 300 >= 256 => out of range => UNVERIFIED.
        let ob_u8 =
            cast_overflow_obligation(CastOp::Trunc, Ty::U64, Ty::U8, ValueId::new(0), value)
                .expect("u64->u8 obligation");
        assert_eq!(
            ob_u8.goal.get_app_args()[1].get_app_args()[0],
            &Expr::nat_lit(256),
            "U8 fits-goal modulus is 2^8"
        );
        assert!(!discharge(&ob_u8, &refl_false()), "300 does not fit U8");

        // dst = U16: modulus 65536; 300 < 65536 => fits => PROVEN.
        let ob_u16 =
            cast_overflow_obligation(CastOp::Trunc, Ty::U64, Ty::U16, ValueId::new(0), value)
                .expect("u64->u16 obligation");
        assert_ne!(
            ob_u8.goal, ob_u16.goal,
            "the goal Expr is change-coupled: widening `dst_ty` changed the modulus"
        );
        assert_eq!(
            ob_u16.goal.get_app_args()[1].get_app_args()[0],
            &Expr::nat_lit(65536),
            "U16 fits-goal modulus is 2^16"
        );
        assert!(
            discharge(&ob_u16, &refl_false()),
            "300 fits in U16 => PROVEN: verdict flipped with the dst_ty edit"
        );
    }

    #[test]
    fn test_widening_fails_closed() {
        // ZExt is a widening cast — outside the narrowing fragment. Fail closed
        // rather than mint a fits-goal.
        assert!(matches!(
            cast_overflow_goal(CastOp::ZExt, Ty::U8, Ty::U64, 5),
            Err(CastLoweringError::UnsupportedOp(CastOp::ZExt))
        ));

        // A `Trunc` whose dst is not narrower is also fail-closed.
        assert!(matches!(
            cast_overflow_goal(CastOp::Trunc, Ty::U8, Ty::U16, 5),
            Err(CastLoweringError::NotNarrowing { .. })
        ));
    }

    #[test]
    fn test_change_coupling_op_trunc_to_bitcast_fails_closed() {
        // CHANGE-COUPLING on `op`: a Trunc node has a goal; mutating op to
        // Bitcast re-shapes (fail closed) — the narrowing goal is NOT reused.
        let trunc = cast_overflow_goal(CastOp::Trunc, Ty::U64, Ty::U8, 200);
        assert!(trunc.is_ok(), "trunc has a representable goal");
        let bitcast = cast_overflow_goal(CastOp::Bitcast, Ty::U64, Ty::U8, 200);
        assert!(
            matches!(
                bitcast,
                Err(CastLoweringError::UnsupportedOp(CastOp::Bitcast))
            ),
            "changing op Trunc -> Bitcast must re-shape, not reuse the narrowing goal"
        );
    }
}
