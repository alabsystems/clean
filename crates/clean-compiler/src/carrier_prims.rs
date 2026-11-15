// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The native carrier primitives of the Rust ABI (Trust plan step 3.2, C1 and C3).
//!
//! A Lean function a Rust function calls is compiled at its CARRIER types —
//! `UInt8`/`16`/`32`/`64` at `u8`..`u64`, `Bool` at `bool`, `Nat` at the pinned
//! `trust_bignum::Nat` handle (Trust design
//! `docs/design/2026-10-02-step3-lean-through-trust-ir.md` §2.2). Inside such a
//! closure the prelude operations on those types are not compiled from their
//! Lean bodies: `UInt64.add` is defined through `Nat` and `UInt64.decLe` through
//! `Nat.decLe`, so compiling the body is the boxed `Nat` round trip the design
//! measured (§1.5). This table is what replaces them, one machine operation
//! each — the same role Lean 4's `@[extern "lean_uint64_add"]` attribute plays
//! for its own compiler, and keyed the same way: by the exact prelude name.
//!
//! # What makes a name-keyed table acceptable here
//!
//! * Each row is EXACT, not an approximation: the kernel's `UIntW` arithmetic
//!   is modulo `2^W` and trust-ir's integer `add`/`sub`/`mul` wrap at the
//!   operand width (`docs/ub-numerics-policy.md` in trust-ir); `UIntW.decLt`
//!   is `Nat.decLt a.toNat b.toNat`, which is the unsigned machine compare;
//!   the `Bool` operations are total two-valued functions; after `to_mono` a
//!   `Decidable` IS its `Bool`, so `Decidable.decide p d` is `d`.
//! * Aliases are NOT in the table. `instDecidableUInt64Le`, `and`, `decide`
//!   and `instDecidableEqUInt32` reach a row only through
//!   `opt::resolve_carrier_prims`, which reads each alias's kernel VALUE.
//! * Nothing here is authority. The Function the core emits is gated by Trust
//!   (`trust-clean-ir-gate`, kernel definitional equality at the carrier),
//!   never by this table; a wrong row is a gate refusal, not a wrong binary.
//!
//! # `Nat` (C3)
//!
//! The `Nat` rows are used only when the closure is compiled with `Nat` at the
//! pinned handle. Only the five entry points `trust-bignum` exports today are
//! reachable (`from_u64`, `add`, `sub`, `is_zero`, `drop`); the comparisons are
//! spelled with them — `a ≤ b` is `is_zero(a - b)` under truncated
//! subtraction — so a module never calls a pinned symbol nothing links.

use crate::ir::IRType;
use clean_kernel::Name;

/// A fixed unsigned machine width.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum UIntWidth {
    /// `UInt8` / `u8`.
    W8,
    /// `UInt16` / `u16`.
    W16,
    /// `UInt32` / `u32`.
    W32,
    /// `UInt64` / `u64`.
    W64,
}

impl UIntWidth {
    /// The L5IR scalar type of this width.
    pub(crate) fn ir_type(self) -> IRType {
        match self {
            Self::W8 => IRType::UInt8,
            Self::W16 => IRType::UInt16,
            Self::W32 => IRType::UInt32,
            Self::W64 => IRType::UInt64,
        }
    }

    /// The width of the Lean carrier named `name` (`UInt8` .. `UInt64`).
    pub(crate) fn of_carrier_name(name: &str) -> Option<Self> {
        Some(match name {
            "UInt8" => Self::W8,
            "UInt16" => Self::W16,
            "UInt32" => Self::W32,
            "UInt64" => Self::W64,
            _ => return None,
        })
    }
}

/// A wrapping binary operation at one width.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ScalarBin {
    /// `UIntW.add`.
    Add,
    /// `UIntW.sub`.
    Sub,
    /// `UIntW.mul`.
    Mul,
    /// `UIntW.land`.
    And,
    /// `UIntW.lor`.
    Or,
    /// `UIntW.xor`.
    Xor,
    /// `UIntW.shiftLeft`, with the amount reduced modulo the word width.
    Shl,
    /// `UIntW.shiftRight`, with the amount reduced modulo the word width.
    LShr,
}

/// An unsigned comparison producing a `Bool`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ScalarCmp {
    /// `UIntW.decEq`.
    Eq,
    /// `UIntW.decLt`.
    Ult,
    /// `UIntW.decLe`.
    Ule,
}

/// A `Bool` operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum BoolOp {
    /// `Bool.not`.
    Not,
    /// `Bool.and`.
    And,
    /// `Bool.or`.
    Or,
    /// `Bool.xor`.
    Xor,
    /// `Bool.decEq`.
    Eq,
}

/// A `Nat` operation over the pinned `trust_bignum::Nat` handle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum NatOp {
    /// `Nat.add` — the pinned `add`.
    Add,
    /// `Nat.sub` — the pinned `sub`, Lean's truncated subtraction.
    Sub,
    /// `Nat.decEq` / `Nat.beq` — `is_zero(a - b) && is_zero(b - a)`.
    Eq,
    /// `Nat.decLe` / `Nat.ble` — `is_zero(a - b)`.
    Le,
    /// `Nat.decLt` / `Nat.blt` — `!is_zero(b - a)`.
    Lt,
    /// `UIntW.toNat` — `from_u64` of the zero-extended value.
    OfUInt(UIntWidth),
}

/// One native carrier primitive.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CarrierPrim {
    /// A wrapping binary operation.
    Bin(ScalarBin, UIntWidth),
    /// An unsigned comparison.
    Cmp(ScalarCmp, UIntWidth),
    /// A `Bool` operation.
    Bool(BoolOp),
    /// `Decidable.decide p d` — `d` (its first argument is the erased `p`).
    Decide,
    /// A `Nat` operation (only when `Nat` is carried by the pinned handle).
    Nat(NatOp),
}

impl CarrierPrim {
    /// The L5IR parameter types, one per call-site argument.
    pub(crate) fn params(self) -> Vec<IRType> {
        match self {
            Self::Bin(_, w) | Self::Cmp(_, w) => vec![w.ir_type(), w.ir_type()],
            Self::Bool(BoolOp::Not) => vec![IRType::Bool],
            Self::Bool(_) => vec![IRType::Bool, IRType::Bool],
            Self::Decide => vec![IRType::Erased, IRType::Bool],
            Self::Nat(NatOp::OfUInt(w)) => vec![w.ir_type()],
            Self::Nat(_) => vec![IRType::Object, IRType::Object],
        }
    }

    /// The L5IR result type.
    pub(crate) fn ret(self) -> IRType {
        match self {
            Self::Bin(_, w) => w.ir_type(),
            Self::Cmp(..) | Self::Bool(_) | Self::Decide => IRType::Bool,
            Self::Nat(NatOp::Add | NatOp::Sub | NatOp::OfUInt(_)) => IRType::Object,
            Self::Nat(NatOp::Eq | NatOp::Le | NatOp::Lt) => IRType::Bool,
        }
    }
}

/// The native primitive `name` denotes, if any.
///
/// `nat_handles` selects whether the `Nat` rows exist: they are faithful only
/// where every `Nat` of the closure is the pinned handle.
pub(crate) fn carrier_prim(name: &Name, nat_handles: bool) -> Option<CarrierPrim> {
    let text = name.to_string();
    // Pretty spelling is not the typed identity: an escaped single segment
    // named `UInt8.decLt` is an ordinary user constant, not the namespace op.
    if *name != Name::from_string(&text) {
        return None;
    }
    let fixed = match text.as_str() {
        "Bool.not" => Some(CarrierPrim::Bool(BoolOp::Not)),
        "Bool.and" => Some(CarrierPrim::Bool(BoolOp::And)),
        "Bool.or" => Some(CarrierPrim::Bool(BoolOp::Or)),
        "Bool.xor" => Some(CarrierPrim::Bool(BoolOp::Xor)),
        "Bool.decEq" => Some(CarrierPrim::Bool(BoolOp::Eq)),
        "Decidable.decide" => Some(CarrierPrim::Decide),
        "Nat.add" => Some(CarrierPrim::Nat(NatOp::Add)),
        "Nat.sub" => Some(CarrierPrim::Nat(NatOp::Sub)),
        "Nat.decEq" | "Nat.beq" => Some(CarrierPrim::Nat(NatOp::Eq)),
        "Nat.decLe" | "Nat.ble" => Some(CarrierPrim::Nat(NatOp::Le)),
        "Nat.decLt" | "Nat.blt" => Some(CarrierPrim::Nat(NatOp::Lt)),
        _ => None,
    };
    let prim = match fixed {
        Some(prim) => prim,
        None => {
            let (carrier, op) = text.rsplit_once('.')?;
            let width = UIntWidth::of_carrier_name(carrier)?;
            match op {
                "add" => CarrierPrim::Bin(ScalarBin::Add, width),
                "sub" => CarrierPrim::Bin(ScalarBin::Sub, width),
                "mul" => CarrierPrim::Bin(ScalarBin::Mul, width),
                "land" => CarrierPrim::Bin(ScalarBin::And, width),
                "lor" => CarrierPrim::Bin(ScalarBin::Or, width),
                "xor" => CarrierPrim::Bin(ScalarBin::Xor, width),
                "shiftLeft" => CarrierPrim::Bin(ScalarBin::Shl, width),
                "shiftRight" => CarrierPrim::Bin(ScalarBin::LShr, width),
                "decEq" => CarrierPrim::Cmp(ScalarCmp::Eq, width),
                "decLt" => CarrierPrim::Cmp(ScalarCmp::Ult, width),
                "decLe" => CarrierPrim::Cmp(ScalarCmp::Ule, width),
                "toNat" => CarrierPrim::Nat(NatOp::OfUInt(width)),
                _ => return None,
            }
        }
    };
    if matches!(prim, CarrierPrim::Nat(_)) && !nat_handles {
        return None;
    }
    Some(prim)
}
