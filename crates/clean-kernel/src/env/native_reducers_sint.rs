// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native reducers for Lean signed fixed-width integer types.
//!
//! Provides fast-path computation for `Int8`, `Int16`, `Int32`, `Int64`,
//! and `ISize` decidable equality, arithmetic, and comparisons.
//!
//! In Lean 4, signed integers wrap unsigned integers:
//! - `structure Int8 where ofUInt8 :: toUInt8 : UInt8`
//! - `structure Int16 where ofUInt16 :: toUInt16 : UInt16`
//! - etc.
//!
//! Internally, the kernel represents both signed and unsigned values as
//! `Expr::Lit(Literal::Nat(_))`. Arithmetic operations (add, sub, mul) use
//! the same modular semantics as the unsigned counterparts (two's complement).
//! Comparisons (blt, ble) need signed interpretation.
//!
//! Part of #3210: reduce heartbeat usage for Init .olean type-checking.

use crate::env::native_reducers_uint::{
    mk_bool, reduce_small_add, reduce_small_mul, reduce_small_sub, reduce_u64_add, reduce_u64_mul,
    reduce_u64_sub, reduce_uint_beq, with_binary_nat_args,
};
use crate::env::Environment;
use crate::expr::Expr;

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

    // Type names (for decidable equality proof terms)
    name!(pub(crate) INT8 = "Int8");
    name!(pub(crate) INT16 = "Int16");
    name!(pub(crate) INT32 = "Int32");
    name!(pub(crate) INT64 = "Int64");
    name!(pub(crate) ISIZE = "ISize");

    // Int8 operations
    name!(pub(crate) INT8_ADD = "Int8.add");
    name!(pub(crate) INT8_SUB = "Int8.sub");
    name!(pub(crate) INT8_MUL = "Int8.mul");
    name!(pub(crate) INT8_DIV = "Int8.div");
    name!(pub(crate) INT8_MOD = "Int8.mod");
    name!(pub(crate) INT8_BEQ = "Int8.beq");
    name!(pub(crate) INT8_BLT = "Int8.blt");
    name!(pub(crate) INT8_BLE = "Int8.ble");
    name!(pub(crate) INT8_DEC_EQ = "Int8.decEq");
    name!(pub(crate) INT8_DEC_LT = "Int8.decLt");
    name!(pub(crate) INT8_DEC_LE = "Int8.decLe");

    // Int16 operations
    name!(pub(crate) INT16_ADD = "Int16.add");
    name!(pub(crate) INT16_SUB = "Int16.sub");
    name!(pub(crate) INT16_MUL = "Int16.mul");
    name!(pub(crate) INT16_DIV = "Int16.div");
    name!(pub(crate) INT16_MOD = "Int16.mod");
    name!(pub(crate) INT16_BEQ = "Int16.beq");
    name!(pub(crate) INT16_BLT = "Int16.blt");
    name!(pub(crate) INT16_BLE = "Int16.ble");
    name!(pub(crate) INT16_DEC_EQ = "Int16.decEq");
    name!(pub(crate) INT16_DEC_LT = "Int16.decLt");
    name!(pub(crate) INT16_DEC_LE = "Int16.decLe");

    // Int32 operations
    name!(pub(crate) INT32_ADD = "Int32.add");
    name!(pub(crate) INT32_SUB = "Int32.sub");
    name!(pub(crate) INT32_MUL = "Int32.mul");
    name!(pub(crate) INT32_DIV = "Int32.div");
    name!(pub(crate) INT32_MOD = "Int32.mod");
    name!(pub(crate) INT32_BEQ = "Int32.beq");
    name!(pub(crate) INT32_BLT = "Int32.blt");
    name!(pub(crate) INT32_BLE = "Int32.ble");
    name!(pub(crate) INT32_DEC_EQ = "Int32.decEq");
    name!(pub(crate) INT32_DEC_LT = "Int32.decLt");
    name!(pub(crate) INT32_DEC_LE = "Int32.decLe");

    // Int64 operations
    name!(pub(crate) INT64_ADD = "Int64.add");
    name!(pub(crate) INT64_SUB = "Int64.sub");
    name!(pub(crate) INT64_MUL = "Int64.mul");
    name!(pub(crate) INT64_DIV = "Int64.div");
    name!(pub(crate) INT64_MOD = "Int64.mod");
    name!(pub(crate) INT64_BEQ = "Int64.beq");
    name!(pub(crate) INT64_BLT = "Int64.blt");
    name!(pub(crate) INT64_BLE = "Int64.ble");
    name!(pub(crate) INT64_DEC_EQ = "Int64.decEq");
    name!(pub(crate) INT64_DEC_LT = "Int64.decLt");
    name!(pub(crate) INT64_DEC_LE = "Int64.decLe");

    // ISize operations
    name!(pub(crate) ISIZE_ADD = "ISize.add");
    name!(pub(crate) ISIZE_SUB = "ISize.sub");
    name!(pub(crate) ISIZE_MUL = "ISize.mul");
    name!(pub(crate) ISIZE_DIV = "ISize.div");
    name!(pub(crate) ISIZE_MOD = "ISize.mod");
    name!(pub(crate) ISIZE_BEQ = "ISize.beq");
    name!(pub(crate) ISIZE_BLT = "ISize.blt");
    name!(pub(crate) ISIZE_BLE = "ISize.ble");
    name!(pub(crate) ISIZE_DEC_EQ = "ISize.decEq");
    name!(pub(crate) ISIZE_DEC_LT = "ISize.decLt");
    name!(pub(crate) ISIZE_DEC_LE = "ISize.decLe");

    // Instance name aliases for decidable equality
    name!(pub(crate) INST_DEC_EQ_INT8 = "instDecidableEqInt8");
    name!(pub(crate) INST_DEC_EQ_INT16 = "instDecidableEqInt16");
    name!(pub(crate) INST_DEC_EQ_INT32 = "instDecidableEqInt32");
    name!(pub(crate) INST_DEC_EQ_INT64 = "instDecidableEqInt64");
    name!(pub(crate) INST_DEC_EQ_ISIZE = "instDecidableEqISize");
}

// Modulus constants (same as unsigned: two's complement arithmetic is identical)
const INT8_MODULUS: u64 = 1u64 << 8;
const INT16_MODULUS: u64 = 1u64 << 16;
const INT32_MODULUS: u64 = 1u64 << 32;

// --- Signed interpretation helpers ---

/// Interpret a Nat value as a signed value in two's complement with given bit width.
fn to_signed(val: u64, bits: u32) -> i64 {
    if bits == 64 {
        // For 64-bit, u64 reinterpretation as i64 is exactly two's complement.
        return val as i64;
    }
    let sign_bit = 1u64 << (bits - 1);
    if val & sign_bit != 0 {
        // Negative: extend sign. For n-bit, val - 2^n gives the signed value.
        val as i64 - (1i64 << bits)
    } else {
        val as i64
    }
}

/// Signed decidable less-than for fixed-width types.
///
/// Signed two's-complement ordering is not yet backed by an in-kernel order
/// proof, so this reducer *declines* (returns `None`) rather than laundering a
/// `Decidable.isTrue/isFalse sorryAx` witness through the trusted kernel. The
/// kernel then falls back to ordinary iota reduction of the real `Decidable`
/// instance. (Sound by omission — never emits an axiom-typed term.)
fn reduce_signed_dec_lt(_args: &[&Expr], _bits: u32) -> Option<Expr> {
    None
}

/// Signed decidable less-than-or-equal for fixed-width types. Declines for the
/// same soundness reason as [`reduce_signed_dec_lt`].
fn reduce_signed_dec_le(_args: &[&Expr], _bits: u32) -> Option<Expr> {
    None
}

/// Signed less-than comparison for fixed-width types.
fn reduce_signed_blt(args: &[&Expr], bits: u32) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| {
        mk_bool(to_signed(a, bits) < to_signed(b, bits))
    })
}

/// Signed less-than-or-equal comparison for fixed-width types.
fn reduce_signed_ble(args: &[&Expr], bits: u32) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| {
        mk_bool(to_signed(a, bits) <= to_signed(b, bits))
    })
}

/// Signed division (T-division: truncation toward zero) for fixed-width types.
fn reduce_signed_div(args: &[&Expr], bits: u32, modulus: u64) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| {
        if b == 0 {
            return Expr::nat_lit(0);
        }
        let sa = to_signed(a, bits);
        let sb = to_signed(b, bits);
        // Handle overflow: MIN / -1 = MIN in two's complement
        let result = sa.checked_div(sb).unwrap_or(sa);
        // Wrap back to unsigned representation
        Expr::nat_lit((result as u64) & (modulus - 1))
    })
}

/// Signed remainder (sign follows dividend) for fixed-width types.
fn reduce_signed_mod(args: &[&Expr], bits: u32, modulus: u64) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| {
        if b == 0 {
            return Expr::nat_lit(a);
        }
        let sa = to_signed(a, bits);
        let sb = to_signed(b, bits);
        let result = sa.checked_rem(sb).unwrap_or(0);
        Expr::nat_lit((result as u64) & (modulus - 1))
    })
}

// --- Per-width reducer functions (small types: 8, 16, 32 bit) ---

macro_rules! define_small_sint_reducers {
    (
        $add:ident, $sub:ident, $mul:ident, $div:ident, $mod_:ident,
        $beq:ident, $blt:ident, $ble:ident,
        $dec_eq:ident, $dec_lt:ident, $dec_le:ident,
        $modulus:expr, $bits:expr, $type_name:expr
    ) => {
        pub(crate) fn $add(args: &[&Expr]) -> Option<Expr> {
            reduce_small_add(args, $modulus)
        }
        pub(crate) fn $sub(args: &[&Expr]) -> Option<Expr> {
            reduce_small_sub(args, $modulus)
        }
        pub(crate) fn $mul(args: &[&Expr]) -> Option<Expr> {
            reduce_small_mul(args, $modulus)
        }
        pub(crate) fn $div(args: &[&Expr]) -> Option<Expr> {
            reduce_signed_div(args, $bits, $modulus)
        }
        pub(crate) fn $mod_(args: &[&Expr]) -> Option<Expr> {
            reduce_signed_mod(args, $bits, $modulus)
        }
        pub(crate) fn $beq(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_beq(args)
        }
        pub(crate) fn $blt(args: &[&Expr]) -> Option<Expr> {
            reduce_signed_blt(args, $bits)
        }
        pub(crate) fn $ble(args: &[&Expr]) -> Option<Expr> {
            reduce_signed_ble(args, $bits)
        }
        pub(crate) fn $dec_eq(_args: &[&Expr]) -> Option<Expr> {
            // DECLINE. Unlike the UInt widths, the signed types (`Int8`..`ISize`)
            // are NOT registered in any Clean environment — there is no
            // `add_inductive` for them and no `<T>.val : <T> → Nat` projection.
            // A wrapper disproof would emit `<T>.val`-referencing output that
            // (a) we cannot type-check (the type is absent from `with_prelude`)
            // and (b) the kernel trusts without re-checking (`reduce_native`).
            // Rather than ship a trusted-but-unverified reducer resting on a
            // guess about `<T>.val`'s type, we decline (sound: the kernel falls
            // back to iota). Re-enable with a real wrapper disproof only once the
            // signed types + a `<T>.val : <T> → Nat` projection live in a prelude
            // we can type-check the output against.
            None
        }
        pub(crate) fn $dec_lt(args: &[&Expr]) -> Option<Expr> {
            reduce_signed_dec_lt(args, $bits)
        }
        pub(crate) fn $dec_le(args: &[&Expr]) -> Option<Expr> {
            reduce_signed_dec_le(args, $bits)
        }
    };
}

// 64-bit signed uses wrapping u64 ops (same as UInt64)
// 64-bit signed uses wrapping u64 ops (same as UInt64)
macro_rules! define_u64_sint_reducers {
    (
        $add:ident, $sub:ident, $mul:ident, $div:ident, $mod_:ident,
        $beq:ident, $blt:ident, $ble:ident,
        $dec_eq:ident, $dec_lt:ident, $dec_le:ident,
        $bits:expr, $type_name:expr
    ) => {
        pub(crate) fn $add(args: &[&Expr]) -> Option<Expr> {
            reduce_u64_add(args)
        }
        pub(crate) fn $sub(args: &[&Expr]) -> Option<Expr> {
            reduce_u64_sub(args)
        }
        pub(crate) fn $mul(args: &[&Expr]) -> Option<Expr> {
            reduce_u64_mul(args)
        }
        pub(crate) fn $div(args: &[&Expr]) -> Option<Expr> {
            with_binary_nat_args(args, |a, b| {
                if b == 0 {
                    return Expr::nat_lit(0);
                }
                let sa = a as i64;
                let sb = b as i64;
                let result = sa.checked_div(sb).unwrap_or(sa);
                Expr::nat_lit(result as u64)
            })
        }
        pub(crate) fn $mod_(args: &[&Expr]) -> Option<Expr> {
            with_binary_nat_args(args, |a, b| {
                if b == 0 {
                    return Expr::nat_lit(a);
                }
                let sa = a as i64;
                let sb = b as i64;
                let result = sa.checked_rem(sb).unwrap_or(0);
                Expr::nat_lit(result as u64)
            })
        }
        pub(crate) fn $beq(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_beq(args)
        }
        pub(crate) fn $blt(args: &[&Expr]) -> Option<Expr> {
            reduce_signed_blt(args, $bits)
        }
        pub(crate) fn $ble(args: &[&Expr]) -> Option<Expr> {
            reduce_signed_ble(args, $bits)
        }
        pub(crate) fn $dec_eq(_args: &[&Expr]) -> Option<Expr> {
            // DECLINE. Unlike the UInt widths, the signed types (`Int8`..`ISize`)
            // are NOT registered in any Clean environment — there is no
            // `add_inductive` for them and no `<T>.val : <T> → Nat` projection.
            // A wrapper disproof would emit `<T>.val`-referencing output that
            // (a) we cannot type-check (the type is absent from `with_prelude`)
            // and (b) the kernel trusts without re-checking (`reduce_native`).
            // Rather than ship a trusted-but-unverified reducer resting on a
            // guess about `<T>.val`'s type, we decline (sound: the kernel falls
            // back to iota). Re-enable with a real wrapper disproof only once the
            // signed types + a `<T>.val : <T> → Nat` projection live in a prelude
            // we can type-check the output against.
            None
        }
        pub(crate) fn $dec_lt(args: &[&Expr]) -> Option<Expr> {
            reduce_signed_dec_lt(args, $bits)
        }
        pub(crate) fn $dec_le(args: &[&Expr]) -> Option<Expr> {
            reduce_signed_dec_le(args, $bits)
        }
    };
}

define_small_sint_reducers!(
    reduce_int8_add,
    reduce_int8_sub,
    reduce_int8_mul,
    reduce_int8_div,
    reduce_int8_mod,
    reduce_int8_beq,
    reduce_int8_blt,
    reduce_int8_ble,
    reduce_int8_dec_eq,
    reduce_int8_dec_lt,
    reduce_int8_dec_le,
    INT8_MODULUS,
    8,
    &*names::INT8
);

define_small_sint_reducers!(
    reduce_int16_add,
    reduce_int16_sub,
    reduce_int16_mul,
    reduce_int16_div,
    reduce_int16_mod,
    reduce_int16_beq,
    reduce_int16_blt,
    reduce_int16_ble,
    reduce_int16_dec_eq,
    reduce_int16_dec_lt,
    reduce_int16_dec_le,
    INT16_MODULUS,
    16,
    &*names::INT16
);

define_small_sint_reducers!(
    reduce_int32_add,
    reduce_int32_sub,
    reduce_int32_mul,
    reduce_int32_div,
    reduce_int32_mod,
    reduce_int32_beq,
    reduce_int32_blt,
    reduce_int32_ble,
    reduce_int32_dec_eq,
    reduce_int32_dec_lt,
    reduce_int32_dec_le,
    INT32_MODULUS,
    32,
    &*names::INT32
);

define_u64_sint_reducers!(
    reduce_int64_add,
    reduce_int64_sub,
    reduce_int64_mul,
    reduce_int64_div,
    reduce_int64_mod,
    reduce_int64_beq,
    reduce_int64_blt,
    reduce_int64_ble,
    reduce_int64_dec_eq,
    reduce_int64_dec_lt,
    reduce_int64_dec_le,
    64,
    &*names::INT64
);

define_u64_sint_reducers!(
    reduce_isize_add,
    reduce_isize_sub,
    reduce_isize_mul,
    reduce_isize_div,
    reduce_isize_mod,
    reduce_isize_beq,
    reduce_isize_blt,
    reduce_isize_ble,
    reduce_isize_dec_eq,
    reduce_isize_dec_lt,
    reduce_isize_dec_le,
    64,
    &*names::ISIZE
);

// --- Registration ---

// Registration split to separate file for file size management.
#[path = "native_reducers_sint_reg.rs"]
mod registration;

#[cfg(test)]
#[path = "native_reducers_sint_tests.rs"]
mod tests;
