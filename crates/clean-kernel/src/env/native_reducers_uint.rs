// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native reducers for Lean unsigned integer primitives.
//!
//! Provides fast-path computation for `UInt8`, `UInt16`, `UInt32`, `UInt64`,
//! and `USize` arithmetic, comparisons, bitwise ops, and decidable equality.
//!
//! Like the existing arithmetic reducers, these reducers operate directly on
//! `Expr::Lit(Literal::Nat(_))` values. The kernel passes the underlying Nat
//! payloads of the UInt values, not `UInt*.mk` constructor wrappers.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::level::Level;
use crate::name::Name;

/// Matches the native reducer signature used by `env::native_reducers`.
pub(crate) type NativeReducerFn = fn(args: &[&Expr]) -> Option<Expr>;

/// Well-known names used by UInt native reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    macro_rules! name {
        ($vis:vis $ident:ident = $value:literal) => {
            $vis static $ident: LazyLock<Name> = LazyLock::new(|| Name::from_string($value));
        };
    }

    name!(pub(crate) DECIDABLE_IS_TRUE = "Decidable.isTrue");
    #[cfg(test)]
    name!(pub(crate) DECIDABLE_IS_FALSE = "Decidable.isFalse");
    name!(pub(crate) EQ_REFL = "Eq.refl");

    name!(pub(crate) UINT8 = "UInt8");
    name!(pub(crate) UINT16 = "UInt16");
    name!(pub(crate) UINT32 = "UInt32");
    name!(pub(crate) UINT64 = "UInt64");

    // UInt8 operations
    name!(pub(crate) UINT8_ADD = "UInt8.add");
    name!(pub(crate) UINT8_SUB = "UInt8.sub");
    name!(pub(crate) UINT8_MUL = "UInt8.mul");
    name!(pub(crate) UINT8_DIV = "UInt8.div");
    name!(pub(crate) UINT8_MOD = "UInt8.mod");
    name!(pub(crate) UINT8_BEQ = "UInt8.beq");
    name!(pub(crate) UINT8_BLT = "UInt8.blt");
    name!(pub(crate) UINT8_BLE = "UInt8.ble");
    name!(pub(crate) UINT8_DEC_EQ = "UInt8.decEq");
    name!(pub(crate) UINT8_DEC_LT = "UInt8.decLt");
    name!(pub(crate) UINT8_LAND = "UInt8.land");
    name!(pub(crate) UINT8_LOR = "UInt8.lor");
    name!(pub(crate) UINT8_XOR = "UInt8.xor");
    name!(pub(crate) UINT8_SHIFT_LEFT = "UInt8.shiftLeft");
    name!(pub(crate) UINT8_SHIFT_RIGHT = "UInt8.shiftRight");
    name!(pub(crate) UINT8_COMPLEMENT = "UInt8.complement");
    name!(pub(crate) UINT8_TO_NAT = "UInt8.toNat");

    // UInt16 operations
    name!(pub(crate) UINT16_ADD = "UInt16.add");
    name!(pub(crate) UINT16_SUB = "UInt16.sub");
    name!(pub(crate) UINT16_MUL = "UInt16.mul");
    name!(pub(crate) UINT16_DIV = "UInt16.div");
    name!(pub(crate) UINT16_MOD = "UInt16.mod");
    name!(pub(crate) UINT16_BEQ = "UInt16.beq");
    name!(pub(crate) UINT16_BLT = "UInt16.blt");
    name!(pub(crate) UINT16_BLE = "UInt16.ble");
    name!(pub(crate) UINT16_DEC_EQ = "UInt16.decEq");
    name!(pub(crate) UINT16_DEC_LT = "UInt16.decLt");
    name!(pub(crate) UINT16_LAND = "UInt16.land");
    name!(pub(crate) UINT16_LOR = "UInt16.lor");
    name!(pub(crate) UINT16_XOR = "UInt16.xor");
    name!(pub(crate) UINT16_SHIFT_LEFT = "UInt16.shiftLeft");
    name!(pub(crate) UINT16_SHIFT_RIGHT = "UInt16.shiftRight");
    name!(pub(crate) UINT16_COMPLEMENT = "UInt16.complement");
    name!(pub(crate) UINT16_TO_NAT = "UInt16.toNat");

    // UInt32 operations
    name!(pub(crate) UINT32_ADD = "UInt32.add");
    name!(pub(crate) UINT32_SUB = "UInt32.sub");
    name!(pub(crate) UINT32_MUL = "UInt32.mul");
    name!(pub(crate) UINT32_DIV = "UInt32.div");
    name!(pub(crate) UINT32_MOD = "UInt32.mod");
    name!(pub(crate) UINT32_BEQ = "UInt32.beq");
    name!(pub(crate) UINT32_BLT = "UInt32.blt");
    name!(pub(crate) UINT32_BLE = "UInt32.ble");
    name!(pub(crate) UINT32_DEC_EQ = "UInt32.decEq");
    name!(pub(crate) UINT32_DEC_LT = "UInt32.decLt");
    name!(pub(crate) UINT32_LAND = "UInt32.land");
    name!(pub(crate) UINT32_LOR = "UInt32.lor");
    name!(pub(crate) UINT32_XOR = "UInt32.xor");
    name!(pub(crate) UINT32_SHIFT_LEFT = "UInt32.shiftLeft");
    name!(pub(crate) UINT32_SHIFT_RIGHT = "UInt32.shiftRight");
    name!(pub(crate) UINT32_COMPLEMENT = "UInt32.complement");
    name!(pub(crate) UINT32_TO_NAT = "UInt32.toNat");

    // UInt64 operations
    name!(pub(crate) UINT64_ADD = "UInt64.add");
    name!(pub(crate) UINT64_SUB = "UInt64.sub");
    name!(pub(crate) UINT64_MUL = "UInt64.mul");
    name!(pub(crate) UINT64_DIV = "UInt64.div");
    name!(pub(crate) UINT64_MOD = "UInt64.mod");
    name!(pub(crate) UINT64_BEQ = "UInt64.beq");
    name!(pub(crate) UINT64_BLT = "UInt64.blt");
    name!(pub(crate) UINT64_BLE = "UInt64.ble");
    name!(pub(crate) UINT64_DEC_EQ = "UInt64.decEq");
    name!(pub(crate) UINT64_DEC_LT = "UInt64.decLt");
    name!(pub(crate) UINT64_LAND = "UInt64.land");
    name!(pub(crate) UINT64_LOR = "UInt64.lor");
    name!(pub(crate) UINT64_XOR = "UInt64.xor");
    name!(pub(crate) UINT64_SHIFT_LEFT = "UInt64.shiftLeft");
    name!(pub(crate) UINT64_SHIFT_RIGHT = "UInt64.shiftRight");
    name!(pub(crate) UINT64_COMPLEMENT = "UInt64.complement");
    name!(pub(crate) UINT64_TO_NAT = "UInt64.toNat");

    // USize native computation is intentionally absent while the carrier width
    // is platform-abstract. Tests keep the names to assert that no reducer is
    // registered for any of these operations.
    #[cfg(test)]
    name!(pub(crate) USIZE_ADD = "USize.add");
    #[cfg(test)]
    name!(pub(crate) USIZE_SUB = "USize.sub");
    #[cfg(test)]
    name!(pub(crate) USIZE_MUL = "USize.mul");
    #[cfg(test)]
    name!(pub(crate) USIZE_DIV = "USize.div");
    #[cfg(test)]
    name!(pub(crate) USIZE_MOD = "USize.mod");
    #[cfg(test)]
    name!(pub(crate) USIZE_BEQ = "USize.beq");
    #[cfg(test)]
    name!(pub(crate) USIZE_BLT = "USize.blt");
    #[cfg(test)]
    name!(pub(crate) USIZE_BLE = "USize.ble");
    #[cfg(test)]
    name!(pub(crate) USIZE_DEC_EQ = "USize.decEq");
    #[cfg(test)]
    name!(pub(crate) USIZE_LAND = "USize.land");
    #[cfg(test)]
    name!(pub(crate) USIZE_LOR = "USize.lor");
    #[cfg(test)]
    name!(pub(crate) USIZE_XOR = "USize.xor");
    #[cfg(test)]
    name!(pub(crate) USIZE_SHIFT_LEFT = "USize.shiftLeft");
    #[cfg(test)]
    name!(pub(crate) USIZE_SHIFT_RIGHT = "USize.shiftRight");
    #[cfg(test)]
    name!(pub(crate) USIZE_COMPLEMENT = "USize.complement");
    #[cfg(test)]
    name!(pub(crate) USIZE_TO_NAT = "USize.toNat");
}

const UINT8_MODULUS: u64 = 1u64 << 8;
const UINT16_MODULUS: u64 = 1u64 << 16;
const UINT32_MODULUS: u64 = 1u64 << 32;

/// Extract a Nat value from a literal expression.
pub(crate) fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

pub(crate) fn with_binary_nat_args<R>(args: &[&Expr], f: impl FnOnce(u64, u64) -> R) -> Option<R> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_val(args[0])?;
    let b = get_nat_val(args[1])?;
    Some(f(a, b))
}

pub(crate) fn mk_bool(value: bool) -> Expr {
    let name = if value { "Bool.true" } else { "Bool.false" };
    Expr::const_(Name::from_string(name), vec![])
}

pub(crate) fn mk_dec_is_true(type_name: &Name, val: &Expr) -> Expr {
    let eq_refl = Expr::app(
        Expr::app(
            Expr::const_(names::EQ_REFL.clone(), vec![Level::succ(Level::zero())]),
            Expr::const_(type_name.clone(), vec![]),
        ),
        val.clone(),
    );
    Expr::app(
        Expr::const_(names::DECIDABLE_IS_TRUE.clone(), vec![]),
        eq_refl,
    )
}

// --- Shared arithmetic helpers ---

pub(crate) fn reduce_small_add(args: &[&Expr], modulus: u64) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a.wrapping_add(b) % modulus))
}

pub(crate) fn reduce_small_sub(args: &[&Expr], modulus: u64) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a.wrapping_sub(b) % modulus))
}

pub(crate) fn reduce_small_mul(args: &[&Expr], modulus: u64) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a.wrapping_mul(b) % modulus))
}

pub(crate) fn reduce_u64_add(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a.wrapping_add(b)))
}

pub(crate) fn reduce_u64_sub(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a.wrapping_sub(b)))
}

pub(crate) fn reduce_u64_mul(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a.wrapping_mul(b)))
}

pub(crate) fn reduce_uint_div(args: &[&Expr]) -> Option<Expr> {
    // Lean semantics: n / 0 = 0.
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a.checked_div(b).unwrap_or(0)))
}

pub(crate) fn reduce_uint_mod(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| {
        if b == 0 {
            Expr::nat_lit(a)
        } else {
            Expr::nat_lit(a % b)
        }
    })
}

pub(crate) fn reduce_uint_beq(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| mk_bool(a == b))
}

pub(crate) fn reduce_uint_blt(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| mk_bool(a < b))
}

pub(crate) fn reduce_uint_ble(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| mk_bool(a <= b))
}

/// Extract the underlying `Nat` from a concrete UInt value.
///
/// GENUINE v4.30 CARRIER: `<T>.ofBitVec : BitVec <width> → <T>`, so a concrete
/// UInt after WHNF is `<T>.ofBitVec <bv>` where `<bv>` is one of:
///   - `BitVec.ofFin <w> (Fin.mk <2^w> <nat-lit> <proof>)` — payload Nat is
///     `Fin.mk`'s 2nd explicit arg (index 1);
///   - `BitVec.ofNat <w> <nat-lit>` — value is `<nat-lit> mod 2^width`;
///   - `BitVec.ofNatLT <w> <nat-lit> <proof>` — value is `<nat-lit>` (already
///     in range).
/// The literal `<T>.ofNat <nat-lit>` form is also recognised directly (its
/// value is `<nat-lit> mod 2^width`) so pre-WHNF operands still reduce. In a
/// *well-typed* `Decidable (@Eq <T> a b)` the operands have type `<T>`, so after
/// WHNF they are such applications; anything else makes the reducer decline.
///
/// `modulus` is `2^width` (or `None` for width-abstract USize — no compute).
fn get_uint_ctor_val(e: &Expr, type_name: &Name, modulus: Option<u64>) -> Option<u64> {
    let head = e.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    // `<T>.ofNat <lit>` — value is `<lit> mod 2^width`.
    if *name == Name::from_string(&format!("{type_name}.ofNat")) {
        let arg = e.get_app_args().into_iter().next()?;
        let v = get_nat_val(arg)?;
        return Some(modulus.map_or(v, |m| v % m));
    }
    // `<T>.ofBitVec <bv>` — peel the BitVec payload.
    if *name == Name::from_string(&format!("{type_name}.ofBitVec")) {
        let bv = e.get_app_args().into_iter().next()?;
        let bv_head = bv.get_app_fn();
        let ExprKind::Const(bv_name, _) = bv_head.kind() else {
            return None;
        };
        let bv_args = bv.get_app_args();
        if *bv_name == Name::from_string("BitVec.ofFin") {
            // BitVec.ofFin <w> (Fin.mk <2^w> <val-lit> <proof>)
            let fin = bv_args.get(1)?;
            let fin_head = fin.get_app_fn();
            if let ExprKind::Const(fname, _) = fin_head.kind() {
                if *fname == Name::from_string("Fin.mk") {
                    return fin.get_app_args().get(1).and_then(|a| get_nat_val(a));
                }
            }
            return None;
        }
        if *bv_name == Name::from_string("BitVec.ofNat") {
            // BitVec.ofNat <w> <lit>  — value is <lit> mod 2^width
            let v = bv_args.get(1).and_then(|a| get_nat_val(a))?;
            return Some(modulus.map_or(v, |m| v % m));
        }
        if *bv_name == Name::from_string("BitVec.ofNatLT") {
            // BitVec.ofNatLT <w> <lit> <proof>  — value is <lit> (in range)
            return bv_args.get(1).and_then(|a| get_nat_val(a));
        }
    }
    None
}

/// `2^width` for the fixed widths, or `None` for UInt64/USize (any `u64` value
/// is already `< 2^64`, and width-abstract USize has no concrete modulus).
fn uint_modulus(type_name: &Name) -> Option<u64> {
    if *type_name == *names::UINT8 {
        Some(UINT8_MODULUS)
    } else if *type_name == *names::UINT16 {
        Some(UINT16_MODULUS)
    } else if *type_name == *names::UINT32 {
        Some(UINT32_MODULUS)
    } else {
        None
    }
}

pub(crate) fn reduce_uint_dec_eq(args: &[&Expr], type_name: &Name) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let m = uint_modulus(type_name);
    let a = get_uint_ctor_val(args[0], type_name, m)?;
    let b = get_uint_ctor_val(args[1], type_name, m)?;
    if a == b {
        // `@Eq.refl <T> (<T>.mk n) : @Eq <T> (<T>.mk n) (<T>.mk n)` — well-typed.
        Some(mk_dec_is_true(type_name, args[0]))
    } else {
        // Sound disproof via the `<T>.toNat` projection (`: <T> → Nat`, carrier-
        // agnostic — for the Fin carrier `<T>.toNat = Fin.val ∘ <T>.val`):
        // `<T>.toNat (<T>.mk ⟨n,h⟩)` ι-reduces to `n`, so
        // `Nat.beq (<T>.toNat a) (<T>.toNat b)` δι-reduces to `false` and
        // `Nat.ne_of_beq_false` turns `Eq Nat` of the projections into `False`;
        // `congrArg <T>.toNat` lifts `@Eq <T> a b` to that. No sorry.
        let ty = Expr::const_(type_name.clone(), vec![]);
        let to_nat_fn = Expr::const_(Name::from_string(&format!("{type_name}.toNat")), vec![]);
        Some(super::native_reducers::mk_wrapper_dec_is_false(
            &ty, &to_nat_fn, args[0], args[1],
        ))
    }
}

/// Native reducer for `<T>.decLt : (a b : <T>) → Decidable (<T>.lt a b)`.
///
/// `<T>.lt a b` is the reducible `Nat.lt (<T>.val a) (<T>.val b)`
/// (`algebra_uint_dec_le_proof.rs`); ordering on the single-constructor
/// `Nat`-wrapper `<T>` is exactly ordering on the underlying value, taken mod
/// `2^n` — i.e. the value the canonical literal `<T>.mk k` already carries
/// (`0 ≤ k < 2^n`). So the CORRECT comparison is `va < vb` on the constructor
/// payloads `va`/`vb`, and the witness is built from the axiom-free `Nat.ble`
/// bridge lemmas on `<T>.val a` / `<T>.val b` — never a `sorry`, never a flipped
/// comparison. Only fires for concrete `<T>.mk <nat-lit>` operands (well-typed
/// `Decidable (@<T>.lt a b)` operands are constructor applications after WHNF);
/// otherwise declines and the kernel falls back to ordinary δι reduction of the
/// real `<T>.decLt` definition.
pub(crate) fn reduce_uint_dec_lt(args: &[&Expr], type_name: &Name) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let m = uint_modulus(type_name);
    let a = get_uint_ctor_val(args[0], type_name, m)?;
    let b = get_uint_ctor_val(args[1], type_name, m)?;
    let ty = Expr::const_(type_name.clone(), vec![]);
    // `<T>.lt a b := Nat.lt (<T>.toNat a) (<T>.toNat b)` (carrier-agnostic
    // underlying Nat projection), so build the `Nat.ble` witness on `<T>.toNat`.
    let val_fn = Expr::const_(Name::from_string(&format!("{type_name}.toNat")), vec![]);
    Some(super::native_reducers::mk_wrapper_lt_dec(
        &ty,
        &val_fn,
        args[0],
        args[1],
        a < b,
    ))
}

// --- Shared bitwise helpers ---

pub(crate) fn reduce_small_land(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a & b))
}

pub(crate) fn reduce_small_lor(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a | b))
}

pub(crate) fn reduce_small_xor(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a ^ b))
}

pub(crate) fn reduce_small_shift_left(args: &[&Expr], modulus: u64) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| {
        // Lean v4.30 semantics: the shift amount is taken MOD the bit width
        // (`UInt8.shiftLeft a b = ⟨a.toBitVec <<< (b.toBitVec % 8)⟩`), NOT
        // saturating-to-zero. Pinned by the carrier differential harness
        // (`carrier_differential_tests.rs`) against `#eval` ground truth:
        // (1 : UInt8) <<< 254 = 64 (shift by 254 % 8 = 6).
        let bits = modulus.trailing_zeros() as u64;
        Expr::nat_lit((a << (b % bits)) % modulus)
    })
}

pub(crate) fn reduce_small_shift_right(args: &[&Expr], modulus: u64) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| {
        // Lean v4.30 semantics: shift amount mod bit width (see shift_left).
        let bits = modulus.trailing_zeros() as u64;
        Expr::nat_lit(a >> (b % bits))
    })
}

pub(crate) fn reduce_small_complement(args: &[&Expr], modulus: u64) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let a = get_nat_val(args[0])?;
    Some(Expr::nat_lit((!a) & (modulus - 1)))
}

pub(crate) fn reduce_u64_land(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a & b))
}

pub(crate) fn reduce_u64_lor(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a | b))
}

pub(crate) fn reduce_u64_xor(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| Expr::nat_lit(a ^ b))
}

pub(crate) fn reduce_u64_shift_left(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| {
        // Lean v4.30 semantics: shift amount mod 64 (see
        // reduce_small_shift_left; pinned by the carrier differential
        // harness against `#eval` ground truth).
        Expr::nat_lit(a.wrapping_shl((b % 64) as u32))
    })
}

pub(crate) fn reduce_u64_shift_right(args: &[&Expr]) -> Option<Expr> {
    with_binary_nat_args(args, |a, b| {
        // Lean v4.30 semantics: shift amount mod 64 (see shift_left).
        Expr::nat_lit(a >> (b % 64))
    })
}

pub(crate) fn reduce_u64_complement(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let a = get_nat_val(args[0])?;
    Some(Expr::nat_lit(!a))
}

/// toNat is identity: UInt values are already represented as Nat literals.
pub(crate) fn reduce_uint_to_nat(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    get_nat_val(args[0])?;
    Some(args[0].clone())
}

// --- Per-width reducer functions (small types) ---

macro_rules! define_small_uint_reducers {
    (
        $add:ident, $sub:ident, $mul:ident, $div:ident, $mod_:ident,
        $beq:ident, $blt:ident, $ble:ident, $dec_eq:ident, $dec_lt:ident,
        $land:ident, $lor:ident, $xor:ident,
        $shl:ident, $shr:ident, $compl:ident, $to_nat:ident,
        $modulus:expr, $type_name:expr
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
            reduce_uint_div(args)
        }
        pub(crate) fn $mod_(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_mod(args)
        }
        pub(crate) fn $beq(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_beq(args)
        }
        pub(crate) fn $blt(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_blt(args)
        }
        pub(crate) fn $ble(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_ble(args)
        }
        pub(crate) fn $dec_eq(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_dec_eq(args, $type_name)
        }
        pub(crate) fn $dec_lt(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_dec_lt(args, $type_name)
        }
        pub(crate) fn $land(args: &[&Expr]) -> Option<Expr> {
            reduce_small_land(args)
        }
        pub(crate) fn $lor(args: &[&Expr]) -> Option<Expr> {
            reduce_small_lor(args)
        }
        pub(crate) fn $xor(args: &[&Expr]) -> Option<Expr> {
            reduce_small_xor(args)
        }
        pub(crate) fn $shl(args: &[&Expr]) -> Option<Expr> {
            reduce_small_shift_left(args, $modulus)
        }
        pub(crate) fn $shr(args: &[&Expr]) -> Option<Expr> {
            reduce_small_shift_right(args, $modulus)
        }
        pub(crate) fn $compl(args: &[&Expr]) -> Option<Expr> {
            reduce_small_complement(args, $modulus)
        }
        pub(crate) fn $to_nat(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_to_nat(args)
        }
    };
}

macro_rules! define_u64_uint_reducers {
    (
        $add:ident, $sub:ident, $mul:ident, $div:ident, $mod_:ident,
        $beq:ident, $blt:ident, $ble:ident, $dec_eq:ident, $dec_lt:ident,
        $land:ident, $lor:ident, $xor:ident,
        $shl:ident, $shr:ident, $compl:ident, $to_nat:ident,
        $type_name:expr
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
            reduce_uint_div(args)
        }
        pub(crate) fn $mod_(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_mod(args)
        }
        pub(crate) fn $beq(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_beq(args)
        }
        pub(crate) fn $blt(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_blt(args)
        }
        pub(crate) fn $ble(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_ble(args)
        }
        pub(crate) fn $dec_eq(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_dec_eq(args, $type_name)
        }
        pub(crate) fn $dec_lt(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_dec_lt(args, $type_name)
        }
        pub(crate) fn $land(args: &[&Expr]) -> Option<Expr> {
            reduce_u64_land(args)
        }
        pub(crate) fn $lor(args: &[&Expr]) -> Option<Expr> {
            reduce_u64_lor(args)
        }
        pub(crate) fn $xor(args: &[&Expr]) -> Option<Expr> {
            reduce_u64_xor(args)
        }
        pub(crate) fn $shl(args: &[&Expr]) -> Option<Expr> {
            reduce_u64_shift_left(args)
        }
        pub(crate) fn $shr(args: &[&Expr]) -> Option<Expr> {
            reduce_u64_shift_right(args)
        }
        pub(crate) fn $compl(args: &[&Expr]) -> Option<Expr> {
            reduce_u64_complement(args)
        }
        pub(crate) fn $to_nat(args: &[&Expr]) -> Option<Expr> {
            reduce_uint_to_nat(args)
        }
    };
}

define_small_uint_reducers!(
    reduce_uint8_add,
    reduce_uint8_sub,
    reduce_uint8_mul,
    reduce_uint8_div,
    reduce_uint8_mod,
    reduce_uint8_beq,
    reduce_uint8_blt,
    reduce_uint8_ble,
    reduce_uint8_dec_eq,
    reduce_uint8_dec_lt,
    reduce_uint8_land,
    reduce_uint8_lor,
    reduce_uint8_xor,
    reduce_uint8_shl,
    reduce_uint8_shr,
    reduce_uint8_compl,
    reduce_uint8_to_nat,
    UINT8_MODULUS,
    &*names::UINT8
);

define_small_uint_reducers!(
    reduce_uint16_add,
    reduce_uint16_sub,
    reduce_uint16_mul,
    reduce_uint16_div,
    reduce_uint16_mod,
    reduce_uint16_beq,
    reduce_uint16_blt,
    reduce_uint16_ble,
    reduce_uint16_dec_eq,
    reduce_uint16_dec_lt,
    reduce_uint16_land,
    reduce_uint16_lor,
    reduce_uint16_xor,
    reduce_uint16_shl,
    reduce_uint16_shr,
    reduce_uint16_compl,
    reduce_uint16_to_nat,
    UINT16_MODULUS,
    &*names::UINT16
);

define_small_uint_reducers!(
    reduce_uint32_add,
    reduce_uint32_sub,
    reduce_uint32_mul,
    reduce_uint32_div,
    reduce_uint32_mod,
    reduce_uint32_beq,
    reduce_uint32_blt,
    reduce_uint32_ble,
    reduce_uint32_dec_eq,
    reduce_uint32_dec_lt,
    reduce_uint32_land,
    reduce_uint32_lor,
    reduce_uint32_xor,
    reduce_uint32_shl,
    reduce_uint32_shr,
    reduce_uint32_compl,
    reduce_uint32_to_nat,
    UINT32_MODULUS,
    &*names::UINT32
);

define_u64_uint_reducers!(
    reduce_uint64_add,
    reduce_uint64_sub,
    reduce_uint64_mul,
    reduce_uint64_div,
    reduce_uint64_mod,
    reduce_uint64_beq,
    reduce_uint64_blt,
    reduce_uint64_ble,
    reduce_uint64_dec_eq,
    reduce_uint64_dec_lt,
    reduce_uint64_land,
    reduce_uint64_lor,
    reduce_uint64_xor,
    reduce_uint64_shl,
    reduce_uint64_shr,
    reduce_uint64_compl,
    reduce_uint64_to_nat,
    &*names::UINT64
);

// USize reducers DELETED (carrier-parity Phase 1, §7.4): genuine v4.30 USize is
// width-abstract, so width-dependent USize ops are kernel-stuck in Lean. The
// `USIZE_*` reducer-name constants are retained (still referenced by removed-
// entry doc comments and cross-width tables) but no USize reducer is registered.

// Registration split to native_reducers_uint_reg.rs for file size.
#[path = "native_reducers_uint_reg.rs"]
mod registration;

#[cfg(test)]
#[path = "native_reducers_uint_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "native_reducers_uint_bitwise_tests.rs"]
mod bitwise_tests;
