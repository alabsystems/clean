// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native reducers for Lean `Int` (signed integer) primitives.
//!
//! Lean 4's `Int` is an inductive with two constructors:
//! - `Int.ofNat (n : Nat)` for non-negative integers (represents n)
//! - `Int.negSucc (n : Nat)` for negative integers (represents -(n+1))
//!
//! Native reducers extract the signed value from constructor applications,
//! compute the result, and wrap it back in the appropriate constructor form.
//!
//! Part of #3210: reduce heartbeat usage for Init .olean type-checking.

use crate::env::native_reducers_arith::get_bignat_val;
use crate::env::Environment;
use crate::expr::{BigNat, Expr, ExprKind, Literal};
use crate::level::Level;
use crate::name::Name;

/// Matches the native reducer signature used by `env::native_reducers`.
type NativeReducerFn = fn(args: &[&Expr]) -> Option<Expr>;

pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    macro_rules! name {
        ($vis:vis $ident:ident = $value:literal) => {
            $vis static $ident: LazyLock<Name> = LazyLock::new(|| Name::from_string($value));
        };
    }

    // Int constructors
    name!(pub(crate) INT_OF_NAT = "Int.ofNat");
    name!(pub(crate) INT_NEG_SUCC = "Int.negSucc");

    // Int type name (for decidable equality)
    name!(pub(crate) INT = "Int");

    // Int operations
    name!(pub(crate) INT_ADD = "Int.add");
    name!(pub(crate) INT_SUB = "Int.sub");
    name!(pub(crate) INT_MUL = "Int.mul");
    name!(pub(crate) INT_DIV = "Int.div");
    name!(pub(crate) INT_MOD = "Int.mod");
    name!(pub(crate) INT_NEG = "Int.neg");
    name!(pub(crate) INT_NAT_ABS = "Int.natAbs");
    name!(pub(crate) INT_TO_NAT = "Int.toNat");
    name!(pub(crate) INT_BEQ = "Int.beq");
    name!(pub(crate) INT_BLT = "Int.blt");
    name!(pub(crate) INT_BLE = "Int.ble");
    name!(pub(crate) INT_DEC_EQ = "Int.decEq");

    // Decidable constructors
    name!(pub(crate) DECIDABLE_IS_TRUE = "Decidable.isTrue");
    name!(pub(crate) DECIDABLE_IS_FALSE = "Decidable.isFalse");
    name!(pub(crate) EQ_REFL = "Eq.refl");
}

/// Extract a Nat value from a literal expression.
pub(crate) fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

/// The non-negative value of a `BigNat` as `u128`, or `None` if it exceeds
/// `2^128 - 1` (more than two 64-bit limbs). `from_limbs` normalizes a `Big` to ≥2
/// limbs (a 1-limb value collapses to `Small`), so the `Big` arm only sees ≥2 limbs.
fn bignat_to_u128(n: &BigNat) -> Option<u128> {
    match n {
        BigNat::Small(v) => Some(u128::from(*v)),
        BigNat::Big(limbs) => match limbs.len() {
            0 => Some(0),
            1 => Some(u128::from(limbs[0])),
            2 => Some(u128::from(limbs[0]) | (u128::from(limbs[1]) << 64)),
            _ => None,
        },
    }
}

/// `-(mag)` as `i128`, or `None` if `mag` exceeds the i128 negative range
/// (`mag > 2^127 = |i128::MIN|`). The `mag == 2^127` case is exactly `i128::MIN`,
/// which `-(mag as i128)` cannot express (it would overflow `i128`).
fn int_from_neg_magnitude(mag: u128) -> Option<i128> {
    const TWO_POW_127: u128 = 1u128 << 127;
    if mag < TWO_POW_127 {
        Some(-(mag as i128))
    } else if mag == TWO_POW_127 {
        Some(i128::MIN)
    } else {
        None
    }
}

/// Extract a signed `i128` value from an `Int` constructor application.
///
/// - `Int.ofNat n`   -> `n`         (`None` if `n > i128::MAX`)
/// - `Int.negSucc n` -> `-(n+1)`    (`None` if `n+1 > 2^127`)
///
/// Trust (arbitrary-magnitude read): the Nat operand is read via the multi-limb
/// `get_bignat_val`/`bignat_to_u128` path, NOT the former `u64`-capped `get_nat_val`.
/// So overflow-check thresholds whose magnitude exceeds `2^64` (e.g. `i128::MAX`,
/// `i128::MIN`, and widened-`i128` sum bounds) now reduce natively instead of
/// stalling in the slow δι reduction of `Int.subNatNat`. The result is still an
/// `i128` — the widest Rust integer type — so a magnitude beyond `i128` declines
/// (sound: the kernel falls back to δι reduction rather than truncating).
pub(crate) fn get_int_val(e: &Expr) -> Option<i128> {
    match e.kind() {
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, levels) = f.kind() {
                if !levels.is_empty() {
                    return None;
                }
                let n = bignat_to_u128(get_bignat_val(arg)?)?;
                if *name == *names::INT_OF_NAT {
                    return i128::try_from(n).ok();
                }
                if *name == *names::INT_NEG_SUCC {
                    // negSucc n represents -(n+1); magnitude is n+1.
                    return int_from_neg_magnitude(n.checked_add(1)?);
                }
            }
            None
        }
        // A bare Nat literal can appear if the kernel hasn't normalized;
        // treat it as Int.ofNat n.
        ExprKind::Lit(Literal::Nat(n)) => i128::try_from(bignat_to_u128(n)?).ok(),
        _ => None,
    }
}

/// Construct an `Int` expression from a signed `i128` value.
///
/// Non-negative values produce `Int.ofNat n`; negative values produce
/// `Int.negSucc (|v|-1)`. The Nat magnitude is encoded via the arbitrary-precision
/// `Expr::nat_lit_u128` (NOT the former `u64`-capped `Expr::nat_lit`), so the full
/// `i128` range — including magnitudes up to `2^127` (`i128::MIN`) — encodes without
/// truncation. Always `Some` for any `i128` input; the `Option` is kept so callers
/// can chain `?` after the `checked_*` arithmetic that feeds it.
pub(crate) fn mk_int(v: i128) -> Option<Expr> {
    if v >= 0 {
        Some(Expr::app(
            Expr::const_(names::INT_OF_NAT.clone(), vec![]),
            Expr::nat_lit_u128(v as u128),
        ))
    } else {
        // v < 0: -(n+1) where n = |v| - 1. `unsigned_abs` gives |v| as u128 (so
        // `i128::MIN` maps to `2^127`), and `|v| ≥ 1`, so `|v| - 1` never underflows.
        let n = v.unsigned_abs() - 1;
        Some(Expr::app(
            Expr::const_(names::INT_NEG_SUCC.clone(), vec![]),
            Expr::nat_lit_u128(n),
        ))
    }
}

pub(crate) fn mk_bool(value: bool) -> Expr {
    let name = if value { "Bool.true" } else { "Bool.false" };
    Expr::const_(Name::from_string(name), vec![])
}

// === arbitrary-precision (BigInt) Int support ===
//
// The i128 path above (`get_int_val` / `mk_int`) covers the hot `u64`/`i64`
// literal range. It CANNOT, however, represent the operands that the `Rat.le`
// lift produces at the binary64 floored-ulp / `(1+u)^n` scales: `Rat.le a b ≡
// Int.le (na · ofNat(effDenom b)) (nb · ofNat(effDenom a))` and
// `Int.le x y := Int.NonNeg (Int.sub y x)`. With a `2^1074`-scale denominator
// (or a `2^53 − n` γ_n denominator), `na · effDenom` and the difference exceed
// `i128`, so the i128 reducers DECLINE and the kernel δ-unfolds the recursive
// `Int.mul` / `Int.sub` definitions — a heartbeat blowup (the SECOND wall, past
// the `Nat.pred` OOM wall closed in tc/reduction/nat.rs). The BigInt-aware
// `Int.add/sub/mul` below close it: they extract a sign-magnitude `(neg, BigNat)`
// and compute with multi-limb arithmetic, emitting `Int.ofNat`/`Int.negSucc`
// over a `BigNat`. They strictly SUPERSEDE the i128 versions (small values are
// `BigNat::Small`), so registering them loses no existing reduction.

/// A sign-magnitude arbitrary-precision integer: value `(-1)^neg · mag`.
/// `neg = true` with `mag = 0` is normalized to `+0` on emit.
struct BigIntVal {
    neg: bool,
    mag: BigNat,
}

/// Limb cap for BigInt products / results (≈5120 bits). `Rat.le` cross-products
/// at the `2^1074` scale are ≈34 limbs (two ≈17-limb operands); 80 limbs leaves
/// generous headroom while keeping allocation strictly bounded (parity intent
/// with the Nat path's `checked_mul_big` guard, just a wider bound for the
/// signed cross-multiply lane).
const BIGINT_LIMB_CAP: usize = 80;

/// Extract a sign-magnitude BigInt from an `Int` constructor application.
///
/// - `Int.ofNat n`   → `(+, n)`         (`n` any closed Nat literal, no u64 cap)
/// - `Int.negSucc n` → `(−, n+1)`
/// - bare `Nat` literal → `(+, n)`      (un-normalized `Int.ofNat`)
fn get_bigint_val(e: &Expr) -> Option<BigIntVal> {
    match e.kind() {
        ExprKind::App(f, arg) => {
            let ExprKind::Const(name, levels) = f.kind() else {
                return None;
            };
            if !levels.is_empty() {
                return None;
            }
            let ExprKind::Lit(Literal::Nat(n)) = arg.kind() else {
                return None;
            };
            if *name == *names::INT_OF_NAT {
                Some(BigIntVal {
                    neg: false,
                    mag: n.clone(),
                })
            } else if *name == *names::INT_NEG_SUCC {
                // negSucc n = −(n+1).
                Some(BigIntVal {
                    neg: true,
                    mag: n.checked_add_big(&BigNat::Small(1)),
                })
            } else {
                None
            }
        }
        ExprKind::Lit(Literal::Nat(n)) => Some(BigIntVal {
            neg: false,
            mag: n.clone(),
        }),
        _ => None,
    }
}

/// Emit a sign-magnitude BigInt as an `Int` constructor application:
/// non-negative → `Int.ofNat mag`; negative → `Int.negSucc (mag − 1)`.
fn mk_bigint(v: BigIntVal) -> Expr {
    if v.neg && !v.mag.is_zero() {
        // value = −mag (mag > 0) = negSucc (mag − 1).
        let pred = v.mag.pred().unwrap_or(BigNat::Small(0));
        Expr::app(
            Expr::const_(names::INT_NEG_SUCC.clone(), vec![]),
            Expr::bignat_lit(pred),
        )
    } else {
        // non-negative (or −0): ofNat mag.
        Expr::app(
            Expr::const_(names::INT_OF_NAT.clone(), vec![]),
            Expr::bignat_lit(v.mag),
        )
    }
}

/// `a + b` over sign-magnitude BigInts.
fn bigint_add(a: &BigIntVal, b: &BigIntVal) -> BigIntVal {
    if a.neg == b.neg {
        // same sign: magnitudes add, sign preserved.
        BigIntVal {
            neg: a.neg,
            mag: a.mag.checked_add_big(&b.mag),
        }
    } else {
        // opposite signs: subtract smaller magnitude from larger; sign of larger.
        match a.mag.cmp(&b.mag) {
            std::cmp::Ordering::Equal => BigIntVal {
                neg: false,
                mag: BigNat::Small(0),
            },
            std::cmp::Ordering::Greater => BigIntVal {
                neg: a.neg,
                mag: a.mag.saturating_sub_big(&b.mag),
            },
            std::cmp::Ordering::Less => BigIntVal {
                neg: b.neg,
                mag: b.mag.saturating_sub_big(&a.mag),
            },
        }
    }
}

/// `a − b` over sign-magnitude BigInts (= `a + (−b)`).
fn bigint_sub(a: &BigIntVal, b: &BigIntVal) -> BigIntVal {
    let neg_b = BigIntVal {
        neg: !b.neg,
        mag: b.mag.clone(),
    };
    bigint_add(a, &neg_b)
}

/// `a · b` over sign-magnitude BigInts; `None` past the limb cap.
fn bigint_mul(a: &BigIntVal, b: &BigIntVal) -> Option<BigIntVal> {
    let mag = a.mag.mul_big_capped(&b.mag, BIGINT_LIMB_CAP)?;
    let neg = (a.neg != b.neg) && !mag.is_zero();
    Some(BigIntVal { neg, mag })
}

// --- Int arithmetic reducers ---

pub(crate) fn reduce_int_add(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    // Arbitrary-precision: extracts a sign-magnitude BigInt (no u64/i128 cap),
    // so closed `Int.add` over large `Rat.le`-lift operands reduces in O(limbs)
    // rather than δ-unfolding the recursive `Int.add` definition.
    let a = get_bigint_val(args[0])?;
    let b = get_bigint_val(args[1])?;
    Some(mk_bigint(bigint_add(&a, &b)))
}

pub(crate) fn reduce_int_sub(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    // Arbitrary-precision (see `reduce_int_add`). The `Rat.le` lift's
    // `Int.NonNeg (Int.sub y x)` difference is computed here without blowup.
    let a = get_bigint_val(args[0])?;
    let b = get_bigint_val(args[1])?;
    Some(mk_bigint(bigint_sub(&a, &b)))
}

pub(crate) fn reduce_int_mul(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    // Arbitrary-precision, bounded at `BIGINT_LIMB_CAP` limbs. The `Rat.le`
    // lift's `na · ofNat(effDenom)` cross-products at the `2^1074` scale reduce
    // here (≈34-limb products) instead of δ-unfolding the recursive `Int.mul`.
    let a = get_bigint_val(args[0])?;
    let b = get_bigint_val(args[1])?;
    Some(mk_bigint(bigint_mul(&a, &b)?))
}

/// Lean 4 Int.div uses T-division (truncation toward zero).
pub(crate) fn reduce_int_div(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_int_val(args[0])?;
    let b = get_int_val(args[1])?;
    if b == 0 {
        mk_int(0)
    } else {
        mk_int(a.checked_div(b)?)
    }
}

/// Lean 4 Int.mod uses T-remainder (sign follows dividend).
pub(crate) fn reduce_int_mod(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_int_val(args[0])?;
    let b = get_int_val(args[1])?;
    if b == 0 {
        mk_int(a)
    } else {
        mk_int(a.checked_rem(b)?)
    }
}

/// Int.neg : Int -> Int
pub(crate) fn reduce_int_neg(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let a = get_int_val(args[0])?;
    mk_int(a.checked_neg()?)
}

/// Int.natAbs : Int -> Nat
pub(crate) fn reduce_int_nat_abs(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let a = get_int_val(args[0])?;
    Some(Expr::nat_lit_u128(a.unsigned_abs()))
}

/// Int.toNat : Int -> Nat (clamps negative to 0)
pub(crate) fn reduce_int_to_nat(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let a = get_int_val(args[0])?;
    if a < 0 {
        Some(Expr::nat_lit(0))
    } else {
        Some(Expr::nat_lit_u128(a as u128))
    }
}

// --- Int comparison reducers ---

/// Total order on sign-magnitude BigInts: negatives < non-negatives; among
/// non-negatives compare magnitudes; among negatives reverse-compare magnitudes.
fn bigint_cmp(a: &BigIntVal, b: &BigIntVal) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let a_neg = a.neg && !a.mag.is_zero();
    let b_neg = b.neg && !b.mag.is_zero();
    match (a_neg, b_neg) {
        (false, false) => a.mag.cmp(&b.mag),
        (true, true) => b.mag.cmp(&a.mag), // more-negative magnitude is smaller
        (true, false) => Ordering::Less,
        (false, true) => Ordering::Greater,
    }
}

pub(crate) fn reduce_int_beq(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    // Arbitrary-precision comparison (no i128 cap).
    let a = get_bigint_val(args[0])?;
    let b = get_bigint_val(args[1])?;
    Some(mk_bool(bigint_cmp(&a, &b) == std::cmp::Ordering::Equal))
}

pub(crate) fn reduce_int_blt(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bigint_val(args[0])?;
    let b = get_bigint_val(args[1])?;
    Some(mk_bool(bigint_cmp(&a, &b) == std::cmp::Ordering::Less))
}

pub(crate) fn reduce_int_ble(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bigint_val(args[0])?;
    let b = get_bigint_val(args[1])?;
    Some(mk_bool(bigint_cmp(&a, &b) != std::cmp::Ordering::Greater))
}

// `Int.decEq` delegates to the single sound implementation in
// `native_reducers_decidable_ext` so that both registrations of `Int.decEq`
// resolve to an axiom-free, kernel-type-checked disproof regardless of init
// order. (The previous local body emitted `Decidable.isFalse sorryAx`.)
pub(crate) fn reduce_int_dec_eq(args: &[&Expr]) -> Option<Expr> {
    super::native_reducers_decidable_ext::reduce_int_dec_eq(args)
}

// --- Registration ---

impl Environment {
    /// Register all Int native reducers (12 operations).
    pub(crate) fn init_int_native_reducers(&mut self) {
        self.register_native_reducer(names::INT_ADD.clone(), reduce_int_add as NativeReducerFn);
        self.register_native_reducer(names::INT_SUB.clone(), reduce_int_sub as NativeReducerFn);
        self.register_native_reducer(names::INT_MUL.clone(), reduce_int_mul as NativeReducerFn);
        self.register_native_reducer(names::INT_DIV.clone(), reduce_int_div as NativeReducerFn);
        self.register_native_reducer(names::INT_MOD.clone(), reduce_int_mod as NativeReducerFn);
        self.register_native_reducer(names::INT_NEG.clone(), reduce_int_neg as NativeReducerFn);
        self.register_native_reducer(
            names::INT_NAT_ABS.clone(),
            reduce_int_nat_abs as NativeReducerFn,
        );
        self.register_native_reducer(
            names::INT_TO_NAT.clone(),
            reduce_int_to_nat as NativeReducerFn,
        );
        self.register_native_reducer(names::INT_BEQ.clone(), reduce_int_beq as NativeReducerFn);
        self.register_native_reducer(names::INT_BLT.clone(), reduce_int_blt as NativeReducerFn);
        self.register_native_reducer(names::INT_BLE.clone(), reduce_int_ble as NativeReducerFn);
        self.register_native_reducer(
            names::INT_DEC_EQ.clone(),
            reduce_int_dec_eq as NativeReducerFn,
        );
    }
}

#[cfg(test)]
#[path = "native_reducers_int_tests.rs"]
mod edge_tests;

#[cfg(test)]
mod tests {
    use super::*;

    fn int_of_nat(n: u64) -> Expr {
        Expr::app(
            Expr::const_(names::INT_OF_NAT.clone(), vec![]),
            Expr::nat_lit(n),
        )
    }

    fn int_neg_succ(n: u64) -> Expr {
        Expr::app(
            Expr::const_(names::INT_NEG_SUCC.clone(), vec![]),
            Expr::nat_lit(n),
        )
    }

    #[test]
    fn test_get_int_val_of_nat() {
        let e = int_of_nat(42);
        assert_eq!(get_int_val(&e), Some(42));
    }

    #[test]
    fn test_get_int_val_neg_succ() {
        // negSucc 0 = -1, negSucc 4 = -5
        let e = int_neg_succ(0);
        assert_eq!(get_int_val(&e), Some(-1));
        let e = int_neg_succ(4);
        assert_eq!(get_int_val(&e), Some(-5));
    }

    #[test]
    fn test_int_add_positive() {
        let a = int_of_nat(3);
        let b = int_of_nat(5);
        let result = reduce_int_add(&[&a, &b]).expect("should reduce");
        assert_eq!(get_int_val(&result), Some(8));
    }

    #[test]
    fn test_int_add_mixed_sign() {
        let a = int_of_nat(10);
        let b = int_neg_succ(4); // -5
        let result = reduce_int_add(&[&a, &b]).expect("should reduce");
        assert_eq!(get_int_val(&result), Some(5));
    }

    #[test]
    fn test_int_sub_result_negative() {
        let a = int_of_nat(3);
        let b = int_of_nat(10);
        let result = reduce_int_sub(&[&a, &b]).expect("should reduce");
        assert_eq!(get_int_val(&result), Some(-7));
    }

    #[test]
    fn test_int_mul_negative() {
        let a = int_neg_succ(2); // -3
        let b = int_of_nat(4);
        let result = reduce_int_mul(&[&a, &b]).expect("should reduce");
        assert_eq!(get_int_val(&result), Some(-12));
    }

    #[test]
    fn test_int_div_truncates_toward_zero() {
        let a = int_neg_succ(6); // -7
        let b = int_of_nat(2);
        let result = reduce_int_div(&[&a, &b]).expect("should reduce");
        assert_eq!(get_int_val(&result), Some(-3)); // T-division
    }

    #[test]
    fn test_int_div_by_zero() {
        let a = int_of_nat(5);
        let b = int_of_nat(0);
        let result = reduce_int_div(&[&a, &b]).expect("should reduce");
        assert_eq!(get_int_val(&result), Some(0));
    }

    #[test]
    fn test_int_neg() {
        let a = int_of_nat(5);
        let result = reduce_int_neg(&[&a]).expect("should reduce");
        assert_eq!(get_int_val(&result), Some(-5));

        let b = int_neg_succ(3); // -4
        let result = reduce_int_neg(&[&b]).expect("should reduce");
        assert_eq!(get_int_val(&result), Some(4));
    }

    #[test]
    fn test_int_nat_abs() {
        let a = int_neg_succ(4); // -5
        let result = reduce_int_nat_abs(&[&a]).expect("should reduce");
        assert_eq!(get_nat_val(&result), Some(5));
    }

    #[test]
    fn test_int_to_nat_clamps() {
        let a = int_neg_succ(0); // -1
        let result = reduce_int_to_nat(&[&a]).expect("should reduce");
        assert_eq!(get_nat_val(&result), Some(0));

        let b = int_of_nat(7);
        let result = reduce_int_to_nat(&[&b]).expect("should reduce");
        assert_eq!(get_nat_val(&result), Some(7));
    }

    fn is_bool_true(e: &Expr) -> bool {
        matches!(e.kind(), ExprKind::Const(name, levels)
            if levels.is_empty() && *name == Name::from_string("Bool.true"))
    }

    fn is_bool_false(e: &Expr) -> bool {
        matches!(e.kind(), ExprKind::Const(name, levels)
            if levels.is_empty() && *name == Name::from_string("Bool.false"))
    }

    #[test]
    fn test_int_beq() {
        let a = int_of_nat(3);
        let b = int_of_nat(3);
        let result = reduce_int_beq(&[&a, &b]).expect("should reduce");
        assert!(is_bool_true(&result));

        let c = int_of_nat(3);
        let d = int_of_nat(4);
        let result = reduce_int_beq(&[&c, &d]).expect("should reduce");
        assert!(is_bool_false(&result));
    }

    #[test]
    fn test_int_blt() {
        let a = int_neg_succ(0); // -1
        let b = int_of_nat(0);
        let result = reduce_int_blt(&[&a, &b]).expect("should reduce");
        assert!(is_bool_true(&result));

        let result = reduce_int_blt(&[&b, &a]).expect("should reduce");
        assert!(is_bool_false(&result));
    }

    #[test]
    fn test_int_too_few_args() {
        let a = int_of_nat(3);
        assert!(reduce_int_add(&[&a]).is_none());
        assert!(reduce_int_add(&[]).is_none());
    }
}
