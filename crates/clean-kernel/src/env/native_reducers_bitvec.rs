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
use crate::expr::{BigNat, Expr, ExprKind, Literal};

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

    // Numeral-literal wrapper the island parser / v4.30 use for a `Nat` numeral:
    // `@OfNat.ofNat Nat n (instOfNatNat n)`. `reduce_bitvec_of_nat` peels this
    // exact shape (a pure delta/projection step — `instOfNatNat n = ⟨n⟩`) so a
    // wrapped operand reads the same as a bare `Nat` literal.
    name!(pub(crate) OF_NAT_OF_NAT = "OfNat.ofNat");
    name!(pub(crate) INST_OF_NAT_NAT = "instOfNatNat");
    name!(pub(crate) NAT = "Nat");
    name!(pub(crate) BITVEC_TO_FIN = "BitVec.toFin");
    name!(pub(crate) BITVEC_OF_FIN = "BitVec.ofFin");
    name!(pub(crate) BITVEC_OF_NAT_LT = "BitVec.ofNatLT");
    name!(pub(crate) INST_OF_NAT_BITVEC = "instOfNatBitVec");
    name!(pub(crate) BITVEC = "BitVec");
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

/// The non-negative value of a closed `Nat` literal as `u128`, or `None` if it
/// exceeds `2^128 - 1` (more than two 64-bit limbs). `BigNat::from_limbs` keeps
/// `Big` at ≥2 significant limbs, so the two-limb arm only fires past `2^64`.
/// Mirrors the `Int` path's `bignat_to_u128` (`native_reducers_int.rs`).
fn bignat_to_u128(n: &BigNat) -> Option<u128> {
    match n.limbs() {
        [] => Some(0),
        [lo] => Some(u128::from(*lo)),
        [lo, hi] => Some(u128::from(*lo) | (u128::from(*hi) << 64)),
        _ => None,
    }
}

/// True iff the head of `e`'s application spine is the constant `target`.
fn head_const_is(e: &Expr, target: &crate::name::Name) -> bool {
    matches!(e.get_app_fn().kind(), ExprKind::Const(n, _) if *n == *target)
}

/// Peel the `@OfNat.ofNat Nat n (instOfNatNat n)` numeral-literal wrapper to the
/// underlying bare `Nat` literal `n`.
///
/// This is the wrapped spelling the island parser / v4.30 emit for a `Nat`
/// numeral. `instOfNatNat n = ⟨n⟩` and `OfNat.ofNat` projects that single field,
/// so the wrapper is *definitionally* `n` — peeling it is exactly the kernel's
/// own delta/beta/projection WHNF of this one numeral constructor, NOT a general
/// operand WHNF (which the BitVec reducers deliberately avoid; see
/// `tc/def_eq/delta_helpers.rs`). The instance head is checked to be
/// `instOfNatNat` and the carrier to be `Nat`, so no other `OfNat` instance
/// (whose field need not equal `n`) is ever peeled.
///
/// The value returned is the INSTANCE's own argument — the field the genuine
/// projection chain `OfNat.ofNat → proj(OfNat, 0, instOfNatNat K) → K` would
/// produce — and the peel additionally requires the `OfNat` index argument to
/// be the syntactically identical literal. On every well-typed term the two
/// agree (the instance's class index is defeq to the value argument), so this
/// costs nothing; on an ill-typed term (which the kernel's discipline should
/// never reduce, but which a buggy caller might) the two could differ, and
/// trusting the index would return a value the term does not definitionally
/// denote. Reading the instance argument makes the reducer locally faithful
/// regardless of caller discipline. Returns `None` for any shape other than
/// this exact, internally consistent numeral wrapper.
fn peel_ofnat_nat_lit(e: &Expr) -> Option<&Expr> {
    if !head_const_is(e, &names::OF_NAT_OF_NAT) {
        return None;
    }
    let args = e.get_app_args();
    // args = [carrier, value, instance]
    if args.len() != 3 {
        return None;
    }
    if !head_const_is(args[0], &names::NAT) || !head_const_is(args[2], &names::INST_OF_NAT_NAT) {
        return None;
    }
    // The genuine definitional value is the instance's stored field, i.e. the
    // argument of `instOfNatNat` — read THAT, and require the `OfNat` index
    // (args[1]) to be the same literal, so an internally inconsistent
    // (ill-typed) wrapper parks instead of reducing to either half.
    let inst_args = args[2].get_app_args();
    if inst_args.len() != 1 {
        return None;
    }
    let (ExprKind::Lit(Literal::Nat(inst_lit)), ExprKind::Lit(Literal::Nat(idx_lit))) =
        (inst_args[0].kind(), args[1].kind())
    else {
        return None;
    };
    if inst_lit != idx_lit {
        return None;
    }
    Some(inst_args[0])
}

/// Read a closed `Nat` literal from `e`, transparently peeling the OfNat numeral
/// wrapper. Recognises a bare `Lit(Nat)` (small or multi-limb) and the
/// `@OfNat.ofNat Nat n (instOfNatNat n)` wrapper (via [`peel_ofnat_nat_lit`]).
/// NOT a general WHNF: only the one numeral-constructor shape is peeled.
fn get_nat_lit(e: &Expr) -> Option<&BigNat> {
    if let ExprKind::Lit(Literal::Nat(n)) = e.kind() {
        return Some(n);
    }
    match peel_ofnat_nat_lit(e)?.kind() {
        ExprKind::Lit(Literal::Nat(n)) => Some(n),
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
///
/// Trust (robust, arbitrary-magnitude read): both operands are read via
/// [`get_nat_lit`], which recognises a bare `Nat` literal (small OR multi-limb)
/// AND the `@OfNat.ofNat Nat k (instOfNatNat k)` numeral wrapper the island
/// parser emits. The value is taken up to `2^128 - 1` (mirroring the `Int`
/// path's `bignat_to_u128`) and the result is emitted via the multi-limb-capable
/// `Expr::nat_lit_u128`. So `BitVec.ofNat w N` now reduces to the canonical
/// payload `N mod 2^w` for the whole `0 ≤ N < 2^128` range regardless of which
/// literal spelling the operand takes, instead of PARKING whenever the value is
/// `≥ 2^64` or OfNat-wrapped. `BitVec.ofNat w N` is DEFINED as `N mod 2^w`
/// (`env/data_types_bitvec.rs`), so this is pure evaluation of the constructor
/// semantics: it can only reduce a term to the literal it already denotes, never
/// equate two distinct BitVec values. Values `≥ 2^128` still decline and fall
/// back to δι, exactly as before.
pub(crate) fn reduce_bitvec_of_nat(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    // BARE literals only — deliberately NOT `get_nat_lit`'s OfNat-wrapped
    // read. The payload world (raw `Lit` operands, produced and consumed by
    // the sibling native reducers) is closed under this reducer; an
    // OfNat-WRAPPED operand is a structural-world term, and firing on it
    // injects a raw payload into a δι spine mid-reduction, where `Fin.rec`
    // needs a constructor and wedges (measured: b125's direct-const
    // `def bx := BitVec.ofNat 8 5; bx.toNat = 5 := rfl`, red from e9a172f67
    // — the commit that widened these reads — until this narrowing).
    // Wrapped shapes are served at the CONSUMER boundary instead, where
    // peeling is sound: `reduce_bitvec_to_nat`'s structural
    // ofNat/ofNatLT/OfNat-instance peel reads them via [`get_nat_lit`].
    // Multi-limb bare literals keep reducing (that read stays `BigNat`-wide).
    let ExprKind::Lit(Literal::Nat(width_lit)) = args[0].kind() else {
        return None;
    };
    let width = width_lit.to_u64()?;
    let ExprKind::Lit(Literal::Nat(value_lit)) = args[1].kind() else {
        return None;
    };
    let value = bignat_to_u128(value_lit)?;
    // BitVec.ofNat w i = i % 2^w. `value < 2^128` (read cap), so for w ≥ 128 no
    // truncation is needed; for w < 128 keep the low w bits (= i mod 2^w).
    let result = if width >= 128 {
        value
    } else {
        value & ((1u128 << width) - 1)
    };
    Some(Expr::nat_lit_u128(result))
}

/// Native reducer for `BitVec.toNat (x : BitVec w) : Nat`.
///
/// Identity on Nat literals -- the BitVec value IS a Nat internally -- at ANY
/// magnitude (the former u64 cap is lifted, mirroring `reduce_bitvec_of_nat`).
/// Takes 1 implicit arg (w) + 1 explicit arg (the BitVec value).
///
/// Trust (structural `ofNat` peel): when the operand is a stuck
/// `BitVec.ofNat w n` / `BitVec.ofNatLT w n pf` application with literal
/// arguments (bare or OfNat-wrapped, via [`get_nat_lit`]), the reducer
/// computes `n mod 2^w` directly -- byte-for-byte the computation
/// [`reduce_bitvec_of_nat`] performs when IT fires -- so
/// `BitVec.toNat (BitVec.ofNat w n)` reduces to the literal the composed
/// definition denotes. This is a STRUCTURAL peel of the operand expression,
/// exactly like [`get_bitvec_operand`]'s, NOT an operand pre-WHNF pass (the
/// no-pre-WHNF invariant in `tc/def_eq/delta_helpers.rs` guards a measured
/// `Init.Data.Char.Basic` regression and is preserved). For `ofNatLT` the
/// payload is already proved `< 2^w`, so the mask is the identity on it;
/// applying it anyway keeps the two arms one computation. Anything else --
/// `ofFin`, open operands, non-literal args -- parks and falls back to the
/// sound delta-iota tower, exactly as before.
pub(crate) fn reduce_bitvec_to_nat(args: &[&Expr]) -> Option<Expr> {
    // The last argument is the actual value; earlier args are implicit (width).
    let arg = args.last().copied()?;
    // Raw payload literal: identity, any magnitude.
    if let ExprKind::Lit(Literal::Nat(_)) = arg.kind() {
        return Some(arg.clone());
    }
    // Stuck `BitVec.ofNat w n` / `BitVec.ofNatLT w n pf`: compute `n mod 2^w`.
    // The instance spelling `@OfNat.ofNat (BitVec w) i (@instOfNatBitVec w i)`
    // is the SAME value one wrapper out (`instOfNatBitVec` is defined as
    // `OfNat.mk (BitVec.ofNat w i)`, `env/data_types_bitvec.rs`), and it is
    // what the elaborator emits for a `(i : BitVec w)` literal — without this
    // arm the δι fallback unfolds `toNat` to its `Fin.rec` spine FIRST, the
    // inner `ofNat` then native-reduces to the raw payload literal mid-spine,
    // and the recursor wedges on a payload where it needs a constructor
    // (measured: b125_c5, red from e9a172f67 — the commit that made `ofNat`
    // fire on OfNat-wrapped operands — until this arm). Same discipline as
    // the Nat-level peel: read the INSTANCE's own argument, and require the
    // `OfNat` index to agree so an ill-typed wrapper parks.
    let peeled = peel_ofnat_bitvec(arg).unwrap_or(arg);
    let ExprKind::Const(name, _) = peeled.get_app_fn().kind() else {
        return None;
    };
    // `instOfNatBitVec w i` (the peel's result) carries the same `[w, i]`
    // argument layout as `BitVec.ofNat w i` — `instOfNatBitVec` is DEFINED as
    // `OfNat.mk (BitVec.ofNat w i)` — so the three heads share one read.
    if *name != *names::BITVEC_OF_NAT
        && *name != *names::BITVEC_OF_NAT_LT
        && *name != *names::INST_OF_NAT_BITVEC
    {
        return None;
    }
    let inner = peeled.get_app_args();
    let width = get_nat_lit(inner.first()?)?.to_u64()?;
    let value = bignat_to_u128(get_nat_lit(inner.get(1)?)?)?;
    let result = if width >= 128 {
        value
    } else {
        value & ((1u128 << width) - 1)
    };
    Some(Expr::nat_lit_u128(result))
}

/// Peel `@OfNat.ofNat (BitVec w) i (@instOfNatBitVec w i)` to the
/// `BitVec.ofNat w i` application the instance's stored field denotes —
/// returned as the SYNTHESIZED view of the instance's own arguments, i.e. the
/// peel yields the instance application `@instOfNatBitVec w i`'s payload
/// shape by re-reading `(w, i)` from the instance and requiring the `OfNat`
/// index to be the same literal (the exact discipline of
/// [`peel_ofnat_nat_lit`]). Returns the INSTANCE application itself, whose
/// argument list `[w, i]` matches `BitVec.ofNat`'s `[w, i]` — the caller
/// reads `inner[0]`/`inner[1]` identically for both shapes. `None` for any
/// other shape; parking is always sound.
fn peel_ofnat_bitvec(e: &Expr) -> Option<&Expr> {
    if !head_const_is(e, &names::OF_NAT_OF_NAT) {
        return None;
    }
    let args = e.get_app_args();
    // args = [carrier `BitVec w`, index i, instance `@instOfNatBitVec w i`]
    if args.len() != 3 {
        return None;
    }
    if !head_const_is(args[0], &names::BITVEC) {
        return None;
    }
    let inst = args[2];
    if !head_const_is(inst, &names::INST_OF_NAT_BITVEC) {
        return None;
    }
    let inst_args = inst.get_app_args();
    if inst_args.len() != 2 {
        return None;
    }
    // The index and the instance's value argument must be the SAME literal
    // (bare or Nat-OfNat-wrapped), so an internally inconsistent wrapper
    // parks instead of reducing to either half.
    let idx = get_nat_lit(args[1])?;
    let inst_val = get_nat_lit(inst_args[1])?;
    if idx != inst_val {
        return None;
    }
    Some(inst)
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
