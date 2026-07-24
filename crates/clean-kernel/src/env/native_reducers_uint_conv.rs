// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native reducers for UInt/USize type conversion operations.
//!
//! Provides fast-path computation for:
//! - ofNat (Nat → UIntN): computes n % modulus
//! - Cross-width conversions (UIntN → UIntM): narrowing with modulus, widening identity
//! - Fin.val (identity on Nat literals)

use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;

pub(crate) type NativeReducerFn = fn(args: &[&Expr]) -> Option<Expr>;

pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    macro_rules! name {
        ($vis:vis $ident:ident = $value:literal) => {
            $vis static $ident: LazyLock<Name> = LazyLock::new(|| Name::from_string($value));
        };
    }

    // narrowing conversions
    name!(pub(crate) UINT16_TO_UINT8 = "UInt16.toUInt8");
    name!(pub(crate) UINT32_TO_UINT8 = "UInt32.toUInt8");
    name!(pub(crate) UINT32_TO_UINT16 = "UInt32.toUInt16");
    name!(pub(crate) UINT64_TO_UINT8 = "UInt64.toUInt8");
    name!(pub(crate) UINT64_TO_UINT16 = "UInt64.toUInt16");
    name!(pub(crate) UINT64_TO_UINT32 = "UInt64.toUInt32");
    name!(pub(crate) USIZE_TO_UINT8 = "USize.toUInt8");
    name!(pub(crate) USIZE_TO_UINT16 = "USize.toUInt16");
    name!(pub(crate) USIZE_TO_UINT32 = "USize.toUInt32");

    // widening conversions (identity for 64-bit platform)
    name!(pub(crate) UINT8_TO_UINT16 = "UInt8.toUInt16");
    name!(pub(crate) UINT8_TO_UINT32 = "UInt8.toUInt32");
    name!(pub(crate) UINT8_TO_UINT64 = "UInt8.toUInt64");
    name!(pub(crate) UINT16_TO_UINT32 = "UInt16.toUInt32");
    name!(pub(crate) UINT16_TO_UINT64 = "UInt16.toUInt64");
    name!(pub(crate) UINT32_TO_UINT64 = "UInt32.toUInt64");
    name!(pub(crate) UINT8_TO_USIZE = "UInt8.toUSize");
    name!(pub(crate) UINT16_TO_USIZE = "UInt16.toUSize");
    name!(pub(crate) UINT32_TO_USIZE = "UInt32.toUSize");
    name!(pub(crate) UINT64_TO_USIZE = "UInt64.toUSize");
    name!(pub(crate) USIZE_TO_UINT64 = "USize.toUInt64");

    // Fin.val
    name!(pub(crate) FIN_VAL = "Fin.val");
}

const UINT8_MOD: u64 = 256;
const UINT16_MOD: u64 = 65_536;
const UINT32_MOD: u64 = 4_294_967_296;

pub(crate) fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

pub(crate) fn reduce_mod(args: &[&Expr], modulus: u64) -> Option<Expr> {
    Some(Expr::nat_lit(
        get_nat_val(args.first().copied()?)? % modulus,
    ))
}

pub(crate) fn reduce_identity(args: &[&Expr]) -> Option<Expr> {
    let arg = args.last().copied()?;
    get_nat_val(arg)?;
    Some(arg.clone())
}

pub(crate) fn register(env: &mut Environment, name: &Name, reducer: NativeReducerFn) {
    env.register_native_reducer(name.clone(), reducer);
}

macro_rules! mod_reducer {
    ($fn:ident, $modulus:expr) => {
        pub(crate) fn $fn(args: &[&Expr]) -> Option<Expr> {
            reduce_mod(args, $modulus)
        }
    };
}

// NOTE — `<Name>.ofNat` has NO native reducer (deliberately removed).
//
// `<Name>.ofNat` is a genuine `Definition : Nat → <Name>` in BOTH environments
// clean runs in, but with DIFFERENT genuine constructors:
//   * pure-clean `init_uint_type`: `<Name>.ofNat n := <Name>.mk n`
//     (the Nat-wrapper carrier whose constructor is `<Name>.mk : Nat → <Name>`)
//   * real Lean 4 olean (BitVec-based): `<Name>.ofNat n :=
//     <Name>.ofBitVec (BitVec.ofNat w n)` (constructor `<Name>.ofBitVec`).
//
// A native reducer cannot see the environment (`fn(args) -> Option<Expr>`), so a
// hard-coded constructor name (`<Name>.mk`) is *fictional* in the olean env —
// there the real constructor is `<Name>.ofBitVec`. Producing `<Name>.mk k` left
// `<Name>.toBitVec (<Name>.mk k)` STUCK at `Proj(<Name>, 0, <Name>.mk k)`
// because `get_constructor("<Name>.mk")` fails (the registered ctor is
// `<Name>.ofBitVec`). That stuck projection is exactly what blocked the
// `UInt*/USize` coercion-arith lemmas (`UInt16.zero_mul`, …) from
// re-converging `<Name>.toBitVec (a * b)` with `BitVec.mul (toBitVec a)
// (toBitVec b)` during `is_def_eq`.
//
// SOUND FIX: decline the fast-path entirely (no `ofNat` reducer is registered)
// and let ordinary δ-reduction unfold the *real* `<Name>.ofNat` definition.
// That always yields the genuine constructor form for whichever environment is
// loaded — `<Name>.mk n` in pure-clean, `<Name>.ofBitVec (BitVec.ofNat w n)` in
// olean — so the projection `<Name>.toBitVec (…)` fires via the EXISTING generic
// proj-through-ctor with no new allowlist shortcut. The width modulus is applied
// by those real definitions (`BitVec.ofNat` carries the width intrinsically), so
// no width-blind, type-erased-`Nat` step can conflate distinct widths or values.

macro_rules! id_reducer {
    ($fn:ident) => {
        pub(crate) fn $fn(args: &[&Expr]) -> Option<Expr> {
            reduce_identity(args)
        }
    };
}

mod_reducer!(reduce_uint16_to_uint8, UINT8_MOD);
mod_reducer!(reduce_uint32_to_uint8, UINT8_MOD);
mod_reducer!(reduce_uint32_to_uint16, UINT16_MOD);
mod_reducer!(reduce_uint64_to_uint8, UINT8_MOD);
mod_reducer!(reduce_uint64_to_uint16, UINT16_MOD);
mod_reducer!(reduce_uint64_to_uint32, UINT32_MOD);
mod_reducer!(reduce_usize_to_uint8, UINT8_MOD);
mod_reducer!(reduce_usize_to_uint16, UINT16_MOD);
mod_reducer!(reduce_usize_to_uint32, UINT32_MOD);
id_reducer!(reduce_uint8_to_uint16);
id_reducer!(reduce_uint8_to_uint32);
id_reducer!(reduce_uint8_to_uint64);
id_reducer!(reduce_uint16_to_uint32);
id_reducer!(reduce_uint16_to_uint64);
id_reducer!(reduce_uint32_to_uint64);
id_reducer!(reduce_uint8_to_usize);
id_reducer!(reduce_uint16_to_usize);
id_reducer!(reduce_uint32_to_usize);
id_reducer!(reduce_uint64_to_usize);
id_reducer!(reduce_usize_to_uint64);
id_reducer!(reduce_fin_val);

macro_rules! register_all {
    ($env:expr, $( $name:expr => $reducer:ident ),+ $(,)?) => {
        $(register($env, &$name, $reducer as NativeReducerFn);)+
    };
}

impl Environment {
    pub(crate) fn init_uint_conv_native_reducers(&mut self) {
        // NOTE: `<Name>.ofNat` reducers are intentionally NOT registered — see
        // the comment above. They δ-unfold the real definition for env-correct,
        // genuine-constructor reduction (sound in both pure-clean and olean envs).
        register_all!(self,
            names::UINT16_TO_UINT8 => reduce_uint16_to_uint8,
            names::UINT32_TO_UINT8 => reduce_uint32_to_uint8,
            names::UINT32_TO_UINT16 => reduce_uint32_to_uint16,
            names::UINT64_TO_UINT8 => reduce_uint64_to_uint8,
            names::UINT64_TO_UINT16 => reduce_uint64_to_uint16,
            names::UINT64_TO_UINT32 => reduce_uint64_to_uint32,
            names::USIZE_TO_UINT8 => reduce_usize_to_uint8,
            names::USIZE_TO_UINT16 => reduce_usize_to_uint16,
            names::USIZE_TO_UINT32 => reduce_usize_to_uint32,
            names::UINT8_TO_UINT16 => reduce_uint8_to_uint16,
            names::UINT8_TO_UINT32 => reduce_uint8_to_uint32,
            names::UINT8_TO_UINT64 => reduce_uint8_to_uint64,
            names::UINT16_TO_UINT32 => reduce_uint16_to_uint32,
            names::UINT16_TO_UINT64 => reduce_uint16_to_uint64,
            names::UINT32_TO_UINT64 => reduce_uint32_to_uint64,
            names::UINT8_TO_USIZE => reduce_uint8_to_usize,
            names::UINT16_TO_USIZE => reduce_uint16_to_usize,
            names::UINT32_TO_USIZE => reduce_uint32_to_usize,
            names::UINT64_TO_USIZE => reduce_uint64_to_usize,
            names::USIZE_TO_UINT64 => reduce_usize_to_uint64,
            names::FIN_VAL => reduce_fin_val,
        );
    }
}

#[cfg(test)]
#[path = "native_reducers_uint_conv_tests.rs"]
mod tests;
