// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native reducers for BitVec and UInt/Int BitVec conversion operations.
//!
//! Lean 4.15+ changed UInt types from Fin-based to BitVec-based:
//! - `structure UInt8 where ofBitVec :: toBitVec : BitVec 8`
//! - `structure BitVec (w : Nat) where ofFin :: toFin : Fin (2^w)`
//!
//! The kernel internally represents UInt values as Nat literals. These
//! native reducers handle the conversion functions that the type checker
//! encounters when validating .olean constants:
//!
//! - `UIntN.toBitVec` / `UIntN.ofBitVec`: structure field projection/constructor
//! - `BitVec.ofNat n v`: create BitVec from width and value (v % 2^n)
//! - `BitVec.toNat`: extract underlying Nat from BitVec
//! - `BitVec.toFin` / `Fin.val`: identity on Nat literals
//!
//! Signed integer types (Int8/Int16/Int32/Int64/ISize) are defined as:
//! - `structure Int8 where ofUInt8 :: toUInt8 : UInt8`
//!   Their toBitVec/ofBitVec reducers delegate to the underlying UInt type.
//!
//! Part of #3232: fix 244 of 295 check_type failures in Init .olean validation.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};

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

    // BitVec core operations
    name!(pub(crate) BITVEC_OF_NAT = "BitVec.ofNat");
    name!(pub(crate) BITVEC_TO_NAT = "BitVec.toNat");
    name!(pub(crate) BITVEC_TO_FIN = "BitVec.toFin");
    name!(pub(crate) BITVEC_OF_FIN = "BitVec.ofFin");
    name!(pub(crate) BITVEC_OF_NAT_LT = "BitVec.ofNatLT");
    name!(pub(crate) FIN_MK = "Fin.mk");

    // BitVec arithmetic / logic / shift / comparison operations. These compute
    // directly on the width (`args[0]`) + Nat payloads, matching Lean v4.30
    // `#eval` semantics EXACTLY (verified against `#print BitVec.*` on the
    // pinned toolchain leanprover--lean4---v4.30.0-rc2). Registering them stops
    // the kernel from unfolding the full BitVec→Fin→Nat tower on every carrier
    // reduction (the 2M-heartbeat blowup fixed by this change).
    name!(pub(crate) BITVEC_ADD = "BitVec.add");
    name!(pub(crate) BITVEC_SUB = "BitVec.sub");
    name!(pub(crate) BITVEC_MUL = "BitVec.mul");
    name!(pub(crate) BITVEC_NEG = "BitVec.neg");
    name!(pub(crate) BITVEC_AND = "BitVec.and");
    name!(pub(crate) BITVEC_OR = "BitVec.or");
    name!(pub(crate) BITVEC_XOR = "BitVec.xor");
    name!(pub(crate) BITVEC_NOT = "BitVec.not");
    name!(pub(crate) BITVEC_SHIFT_LEFT = "BitVec.shiftLeft");
    name!(pub(crate) BITVEC_USHIFT_RIGHT = "BitVec.ushiftRight");
    name!(pub(crate) BITVEC_UDIV = "BitVec.udiv");
    name!(pub(crate) BITVEC_UMOD = "BitVec.umod");
    name!(pub(crate) BITVEC_ULT = "BitVec.ult");
    name!(pub(crate) BITVEC_ULE = "BitVec.ule");
    name!(pub(crate) BITVEC_SLT = "BitVec.slt");
    name!(pub(crate) BITVEC_SLE = "BitVec.sle");

    // UInt toBitVec (structure field projection)
    name!(pub(crate) UINT8_TO_BITVEC = "UInt8.toBitVec");
    name!(pub(crate) UINT16_TO_BITVEC = "UInt16.toBitVec");
    name!(pub(crate) UINT32_TO_BITVEC = "UInt32.toBitVec");
    name!(pub(crate) UINT64_TO_BITVEC = "UInt64.toBitVec");
    name!(pub(crate) USIZE_TO_BITVEC = "USize.toBitVec");

    // UInt ofBitVec (structure constructor)
    name!(pub(crate) UINT8_OF_BITVEC = "UInt8.ofBitVec");
    name!(pub(crate) UINT16_OF_BITVEC = "UInt16.ofBitVec");
    name!(pub(crate) UINT32_OF_BITVEC = "UInt32.ofBitVec");
    name!(pub(crate) UINT64_OF_BITVEC = "UInt64.ofBitVec");
    name!(pub(crate) USIZE_OF_BITVEC = "USize.ofBitVec");

    // Signed integer toBitVec/ofBitVec
    // Int8 wraps UInt8, etc. -- these are composition of two projections
    // but the kernel still needs native reducers for them.
    name!(pub(crate) INT8_TO_BITVEC = "Int8.toBitVec");
    name!(pub(crate) INT16_TO_BITVEC = "Int16.toBitVec");
    name!(pub(crate) INT32_TO_BITVEC = "Int32.toBitVec");
    name!(pub(crate) INT64_TO_BITVEC = "Int64.toBitVec");
    name!(pub(crate) ISIZE_TO_BITVEC = "ISize.toBitVec");

    // Signed integer toUInt / ofUInt (structure field projection/constructor)
    name!(pub(crate) INT8_TO_UINT8 = "Int8.toUInt8");
    name!(pub(crate) INT16_TO_UINT16 = "Int16.toUInt16");
    name!(pub(crate) INT32_TO_UINT32 = "Int32.toUInt32");
    name!(pub(crate) INT64_TO_UINT64 = "Int64.toUInt64");
    name!(pub(crate) ISIZE_TO_USIZE = "ISize.toUSize");
    name!(pub(crate) INT8_OF_UINT8 = "Int8.ofUInt8");
    name!(pub(crate) INT16_OF_UINT16 = "Int16.ofUInt16");
    name!(pub(crate) INT32_OF_UINT32 = "Int32.ofUInt32");
    name!(pub(crate) INT64_OF_UINT64 = "Int64.ofUInt64");
    name!(pub(crate) ISIZE_OF_USIZE = "ISize.ofUSize");
}

/// Extract a Nat value from a literal expression.
fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

// --- BitVec core operations ---

/// Native reducer for `BitVec.ofNat (n : Nat) (i : Nat) : BitVec n`.
///
/// Computes `i % 2^n`. The kernel passes the width `n` and value `i` as
/// arguments after the expression is partially applied.
///
/// Argument layout: BitVec.ofNat takes 2 explicit args: n (width), i (value).
pub(crate) fn reduce_bitvec_of_nat(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let width = get_nat_val(args[0])?;
    let value = get_nat_val(args[1])?;
    // BitVec.ofNat n i = i % 2^n
    if width >= 64 {
        // For width >= 64, no truncation needed for values that fit u64
        Some(Expr::nat_lit(value))
    } else {
        let modulus = 1u64 << width;
        Some(Expr::nat_lit(value % modulus))
    }
}

/// Native reducer for `BitVec.toNat (x : BitVec w) : Nat`.
///
/// Identity on Nat literals -- the BitVec value IS a Nat internally.
/// Takes 1 implicit arg (w) + 1 explicit arg (the BitVec value).
pub(crate) fn reduce_bitvec_to_nat(args: &[&Expr]) -> Option<Expr> {
    // The last argument is the actual value; earlier args are implicit (width).
    let arg = args.last().copied()?;
    get_nat_val(arg)?;
    Some(arg.clone())
}

/// Native reducer for `BitVec.toFin (x : BitVec w) : Fin (2^w)`.
///
/// Identity on Nat literals.
pub(crate) fn reduce_bitvec_to_fin(args: &[&Expr]) -> Option<Expr> {
    let arg = args.last().copied()?;
    get_nat_val(arg)?;
    Some(arg.clone())
}

/// Native reducer for `BitVec.ofFin (x : Fin (2^w)) : BitVec w`.
///
/// Identity on Nat literals.
pub(crate) fn reduce_bitvec_of_fin(args: &[&Expr]) -> Option<Expr> {
    let arg = args.last().copied()?;
    get_nat_val(arg)?;
    Some(arg.clone())
}

// --- UInt toBitVec (structure field projection, identity on Nat) ---

/// `UIntN.toBitVec` is a structure field projection. Since UInt values
/// are represented as Nat literals internally, this is identity.
fn reduce_identity_last(args: &[&Expr]) -> Option<Expr> {
    let arg = args.last().copied()?;
    get_nat_val(arg)?;
    Some(arg.clone())
}

pub(crate) fn reduce_uint8_to_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_uint16_to_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_uint32_to_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_uint64_to_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_usize_to_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

// --- UInt ofBitVec (structure constructor, identity on Nat) ---

pub(crate) fn reduce_uint8_of_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_uint16_of_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_uint32_of_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_uint64_of_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_usize_of_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

// --- Signed integer toUInt/ofUInt (identity on Nat) ---

pub(crate) fn reduce_int8_to_uint8(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_int16_to_uint16(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_int32_to_uint32(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_int64_to_uint64(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_isize_to_usize(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_int8_of_uint8(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_int16_of_uint16(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_int32_of_uint32(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_int64_of_uint64(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_isize_of_usize(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

// --- Signed integer toBitVec (composition: IntN -> UIntN -> BitVec) ---

pub(crate) fn reduce_int8_to_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_int16_to_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_int32_to_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_int64_to_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

pub(crate) fn reduce_isize_to_bitvec(args: &[&Expr]) -> Option<Expr> {
    reduce_identity_last(args)
}

// --- BitVec arithmetic / logic / shift / comparison ---
//
// Genuine v4.30 semantics (from `#print BitVec.*`, all `#eval`-verified):
//   BitVec.add  n x y = ofNat n (x.toNat + y.toNat)          = (a+b) mod 2^n
//   BitVec.sub  n x y = ofNat n (2^n - y.toNat + x.toNat)    = (a-b) mod 2^n
//   BitVec.mul  n x y = ofNat n (x.toNat * y.toNat)          = (a*b) mod 2^n
//   BitVec.neg  n x   = ofNat n (2^n - x.toNat)              = (2^n - a) mod 2^n
//   BitVec.and  n x y = (x.toNat &&& y.toNat)                = a & b
//   BitVec.or   n x y = (x.toNat ||| y.toNat)                = a | b
//   BitVec.xor  n x y = (x.toNat ^^^ y.toNat)                = a ^ b
//   BitVec.not  n x   = allOnes n ^^^ x                      = (!a) & (2^n-1)
//   BitVec.shiftLeft    n x s = ofNat n (x.toNat <<< s)      = (a << s) mod 2^n
//   BitVec.ushiftRight  n x s = (x.toNat >>> s)              = a >> s
//   BitVec.udiv n x y = (x.toNat / y.toNat)                  = a / b  (b=0 → 0)
//   BitVec.umod n x y = (x.toNat % y.toNat)                  = a % b  (b=0 → a)
//   BitVec.ult  n x y = decide (x.toNat < y.toNat)           = a <  b  (unsigned)
//   BitVec.ule  n x y = decide (x.toNat ≤ y.toNat)           = a <= b  (unsigned)
//   BitVec.slt  n x y = decide (x.toInt < y.toInt)           = a <  b  (2's-comp)
//   BitVec.sle  n x y = decide (x.toInt ≤ y.toInt)           = a <= b  (2's-comp)
//
// NOTE the shift amount `s` for shiftLeft/ushiftRight is a RAW `Nat` — it is
// NOT taken mod width at the BitVec layer (the mod-width step lives one level
// up in `UInt*.shiftLeft`). So an over-width shift genuinely zeroes/clears.
//
// All values are the BitVec's canonical `Nat` payload (`< 2^n`), the same
// representation `reduce_bitvec_of_nat` already produces, so returning a raw
// `Nat` literal is consistent with the existing carrier convention and sound:
// `BitVec.add x y` is def-eq to `BitVec.ofNat n (x.toNat+y.toNat)`, which
// `reduce_bitvec_of_nat` reduces to the identical literal.

/// `2^w - 1` as a `u64` mask for width `w`, or `None` for `w > 64` (the payload
/// cannot fit a `u64`; decline and let the kernel fall back to structural δι).
fn width_mask(w: u64) -> Option<u64> {
    match w {
        0 => Some(0),
        1..=63 => Some((1u64 << w) - 1),
        64 => Some(u64::MAX),
        _ => None,
    }
}

/// Extract `(width, mask)` from `args[0]` (the implicit `{n : Nat}` width).
fn bv_width(args: &[&Expr]) -> Option<(u64, u64)> {
    let w = get_nat_val(args.first().copied()?)?;
    Some((w, width_mask(w)?))
}

/// Extract a BitVec operand's canonical `Nat` payload (`value & mask`).
///
/// Recognises the shapes a BitVec value takes after (pre-)WHNF:
///   - a raw `Nat` literal (the canonical payload `reduce_bitvec_of_nat` emits);
///   - `BitVec.ofNat  w v`        → `v mod 2^w`;
///   - `BitVec.ofNatLT w v proof` → `v` (already in range);
///   - `BitVec.ofFin  w (Fin.mk _ v _)` → `v`.
///
/// Masking by `mask` (= `2^w-1`) normalises any over-range literal to the
/// canonical payload, matching Lean's `BitVec.ofNat` truncation.
fn get_bitvec_operand(e: &Expr, mask: u64) -> Option<u64> {
    if let ExprKind::Lit(Literal::Nat(n)) = e.kind() {
        return n.to_u64().map(|v| v & mask);
    }
    let ExprKind::Const(name, _) = e.get_app_fn().kind() else {
        return None;
    };
    let args = e.get_app_args();
    if *name == *names::BITVEC_OF_NAT || *name == *names::BITVEC_OF_NAT_LT {
        // BitVec.ofNat w v / BitVec.ofNatLT w v proof — payload is arg index 1.
        return args.get(1).and_then(|a| get_nat_val(a)).map(|v| v & mask);
    }
    if *name == *names::BITVEC_OF_FIN {
        // BitVec.ofFin w (Fin.mk _ v _) — payload is Fin.mk's arg index 1.
        let fin = args.get(1)?;
        if let ExprKind::Const(fname, _) = fin.get_app_fn().kind() {
            if *fname == *names::FIN_MK {
                return fin
                    .get_app_args()
                    .get(1)
                    .and_then(|a| get_nat_val(a))
                    .map(|v| v & mask);
            }
        }
    }
    None
}

/// Both BitVec value operands (`args[1]`, `args[2]`) as canonical payloads.
fn bv_two_operands(args: &[&Expr], mask: u64) -> Option<(u64, u64)> {
    let a = get_bitvec_operand(args.get(1).copied()?, mask)?;
    let b = get_bitvec_operand(args.get(2).copied()?, mask)?;
    Some((a, b))
}

/// A `Bool` constructor for the comparison reducers.
fn mk_bool(value: bool) -> Expr {
    Expr::const_(
        crate::name::Name::from_string(if value { "Bool.true" } else { "Bool.false" }),
        vec![],
    )
}

/// Two's-complement interpretation of an `n`-bit payload `v` (`< 2^n`).
fn to_signed(v: u64, w: u64) -> i128 {
    if w == 0 {
        return 0;
    }
    let half = 1u128 << (w - 1);
    if (v as u128) < half {
        v as i128
    } else {
        v as i128 - (1i128 << w)
    }
}

pub(crate) fn reduce_bitvec_add(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let (a, b) = bv_two_operands(args, mask)?;
    Some(Expr::nat_lit(
        ((a as u128 + b as u128) & mask as u128) as u64,
    ))
}

pub(crate) fn reduce_bitvec_sub(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let (a, b) = bv_two_operands(args, mask)?;
    let modulus = mask as u128 + 1; // 2^w
    Some(Expr::nat_lit(
        ((a as u128 + modulus - b as u128) & mask as u128) as u64,
    ))
}

pub(crate) fn reduce_bitvec_mul(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let (a, b) = bv_two_operands(args, mask)?;
    Some(Expr::nat_lit(
        ((a as u128 * b as u128) & mask as u128) as u64,
    ))
}

pub(crate) fn reduce_bitvec_neg(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let a = get_bitvec_operand(args.get(1).copied()?, mask)?;
    let modulus = mask as u128 + 1; // 2^w
    Some(Expr::nat_lit(((modulus - a as u128) & mask as u128) as u64))
}

pub(crate) fn reduce_bitvec_and(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let (a, b) = bv_two_operands(args, mask)?;
    Some(Expr::nat_lit(a & b))
}

pub(crate) fn reduce_bitvec_or(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let (a, b) = bv_two_operands(args, mask)?;
    Some(Expr::nat_lit(a | b))
}

pub(crate) fn reduce_bitvec_xor(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let (a, b) = bv_two_operands(args, mask)?;
    Some(Expr::nat_lit(a ^ b))
}

pub(crate) fn reduce_bitvec_not(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let a = get_bitvec_operand(args.get(1).copied()?, mask)?;
    Some(Expr::nat_lit((!a) & mask))
}

pub(crate) fn reduce_bitvec_shift_left(args: &[&Expr]) -> Option<Expr> {
    let (w, mask) = bv_width(args)?;
    let a = get_bitvec_operand(args.get(1).copied()?, mask)?;
    // Shift amount is a RAW Nat (no mod-width at the BitVec layer).
    let s = get_nat_val(args.get(2).copied()?)?;
    // (a << s) mod 2^w: when s ≥ w every set bit is shifted past bit w.
    let result = if s >= w {
        0
    } else {
        (((a as u128) << s) & mask as u128) as u64
    };
    Some(Expr::nat_lit(result))
}

pub(crate) fn reduce_bitvec_ushift_right(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let a = get_bitvec_operand(args.get(1).copied()?, mask)?;
    let s = get_nat_val(args.get(2).copied()?)?;
    // a fits u64, so any shift ≥ 64 yields 0; smaller shifts stay in range.
    let result = if s >= 64 { 0 } else { a >> s };
    Some(Expr::nat_lit(result))
}

pub(crate) fn reduce_bitvec_udiv(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let (a, b) = bv_two_operands(args, mask)?;
    // Lean: x / 0 = 0.
    Some(Expr::nat_lit(a.checked_div(b).unwrap_or(0)))
}

pub(crate) fn reduce_bitvec_umod(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let (a, b) = bv_two_operands(args, mask)?;
    // Lean: x % 0 = x.
    Some(Expr::nat_lit(if b == 0 { a } else { a % b }))
}

pub(crate) fn reduce_bitvec_ult(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let (a, b) = bv_two_operands(args, mask)?;
    Some(mk_bool(a < b))
}

pub(crate) fn reduce_bitvec_ule(args: &[&Expr]) -> Option<Expr> {
    let (_, mask) = bv_width(args)?;
    let (a, b) = bv_two_operands(args, mask)?;
    Some(mk_bool(a <= b))
}

pub(crate) fn reduce_bitvec_slt(args: &[&Expr]) -> Option<Expr> {
    let (w, mask) = bv_width(args)?;
    let (a, b) = bv_two_operands(args, mask)?;
    Some(mk_bool(to_signed(a, w) < to_signed(b, w)))
}

pub(crate) fn reduce_bitvec_sle(args: &[&Expr]) -> Option<Expr> {
    let (w, mask) = bv_width(args)?;
    let (a, b) = bv_two_operands(args, mask)?;
    Some(mk_bool(to_signed(a, w) <= to_signed(b, w)))
}

// --- Registration ---

macro_rules! register_all {
    ($env:expr, $( $name:expr => $reducer:ident ),+ $(,)?) => {
        $($env.register_native_reducer($name.clone(), $reducer as NativeReducerFn);)+
    };
}

impl Environment {
    /// Register all BitVec and UInt/Int BitVec conversion native reducers.
    /// 45 reducers total: 4 BitVec core + 16 BitVec arith/logic/shift/cmp +
    /// 10 UInt + 10 signed toUInt/ofUInt + 5 signed toBitVec.
    pub(crate) fn init_bitvec_native_reducers(&mut self) {
        self.register_bitvec_core_reducers();
        self.register_bitvec_arith_reducers();
        self.register_uint_bitvec_reducers();
        self.register_sint_bitvec_reducers();
    }

    fn register_bitvec_core_reducers(&mut self) {
        register_all!(self,
            names::BITVEC_OF_NAT => reduce_bitvec_of_nat,
            names::BITVEC_TO_NAT => reduce_bitvec_to_nat,
            names::BITVEC_TO_FIN => reduce_bitvec_to_fin,
            names::BITVEC_OF_FIN => reduce_bitvec_of_fin,
        );
    }

    /// BitVec arithmetic / logic / shift / comparison — the fast path that
    /// short-circuits the BitVec→Fin→Nat tower (fixes the 2M-heartbeat blowup
    /// on the carrier reduction paths, e.g. Char.Ordinal / utf8DecodeChar?).
    fn register_bitvec_arith_reducers(&mut self) {
        register_all!(self,
            names::BITVEC_ADD => reduce_bitvec_add,
            names::BITVEC_SUB => reduce_bitvec_sub,
            names::BITVEC_MUL => reduce_bitvec_mul,
            names::BITVEC_NEG => reduce_bitvec_neg,
            names::BITVEC_AND => reduce_bitvec_and,
            names::BITVEC_OR => reduce_bitvec_or,
            names::BITVEC_XOR => reduce_bitvec_xor,
            names::BITVEC_NOT => reduce_bitvec_not,
            names::BITVEC_SHIFT_LEFT => reduce_bitvec_shift_left,
            names::BITVEC_USHIFT_RIGHT => reduce_bitvec_ushift_right,
            names::BITVEC_UDIV => reduce_bitvec_udiv,
            names::BITVEC_UMOD => reduce_bitvec_umod,
            names::BITVEC_ULT => reduce_bitvec_ult,
            names::BITVEC_ULE => reduce_bitvec_ule,
            names::BITVEC_SLT => reduce_bitvec_slt,
            names::BITVEC_SLE => reduce_bitvec_sle,
        );
    }

    fn register_uint_bitvec_reducers(&mut self) {
        register_all!(self,
            names::UINT8_TO_BITVEC => reduce_uint8_to_bitvec,
            names::UINT16_TO_BITVEC => reduce_uint16_to_bitvec,
            names::UINT32_TO_BITVEC => reduce_uint32_to_bitvec,
            names::UINT64_TO_BITVEC => reduce_uint64_to_bitvec,
            names::USIZE_TO_BITVEC => reduce_usize_to_bitvec,
            names::UINT8_OF_BITVEC => reduce_uint8_of_bitvec,
            names::UINT16_OF_BITVEC => reduce_uint16_of_bitvec,
            names::UINT32_OF_BITVEC => reduce_uint32_of_bitvec,
            names::UINT64_OF_BITVEC => reduce_uint64_of_bitvec,
            names::USIZE_OF_BITVEC => reduce_usize_of_bitvec,
        );
    }

    fn register_sint_bitvec_reducers(&mut self) {
        register_all!(self,
            names::INT8_TO_UINT8 => reduce_int8_to_uint8,
            names::INT16_TO_UINT16 => reduce_int16_to_uint16,
            names::INT32_TO_UINT32 => reduce_int32_to_uint32,
            names::INT64_TO_UINT64 => reduce_int64_to_uint64,
            names::ISIZE_TO_USIZE => reduce_isize_to_usize,
            names::INT8_OF_UINT8 => reduce_int8_of_uint8,
            names::INT16_OF_UINT16 => reduce_int16_of_uint16,
            names::INT32_OF_UINT32 => reduce_int32_of_uint32,
            names::INT64_OF_UINT64 => reduce_int64_of_uint64,
            names::ISIZE_OF_USIZE => reduce_isize_of_usize,
            names::INT8_TO_BITVEC => reduce_int8_to_bitvec,
            names::INT16_TO_BITVEC => reduce_int16_to_bitvec,
            names::INT32_TO_BITVEC => reduce_int32_to_bitvec,
            names::INT64_TO_BITVEC => reduce_int64_to_bitvec,
            names::ISIZE_TO_BITVEC => reduce_isize_to_bitvec,
        );
    }
}

#[cfg(test)]
#[path = "native_reducers_bitvec_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "native_reducers_bitvec_crosswidth_tests.rs"]
mod crosswidth_tests;

#[cfg(test)]
#[path = "native_reducers_bitvec_arith_tests.rs"]
mod arith_tests;
