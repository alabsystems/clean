// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native arithmetic reducers for Nat and UInt32 operations.
//!
//! Provides fast-path computation for core arithmetic primitives:
//! - `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.decEq`, `Nat.blt`
//! - `UInt32.add`, `UInt32.sub`, `UInt32.mul`
//!
//! These reducers operate on `Expr::Lit(Literal::Nat(_))` values and return
//! reduced literal expressions, enabling the kernel to evaluate arithmetic
//! without delta-unfolding recursive definitions.
//!
//! Reference: Lean 4 kernel/type_checker.cpp native reduction infrastructure.

use crate::env::Environment;
use crate::expr::{BigNat, Expr, ExprKind, Literal};
use crate::name::Name;

/// Well-known names for arithmetic native reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static NAT_PRED: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.pred"));
    pub(crate) static NAT_ADD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.add"));
    pub(crate) static NAT_SUB: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.sub"));
    pub(crate) static NAT_MUL: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.mul"));
    pub(crate) static NAT_DIV: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.div"));
    pub(crate) static NAT_MOD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.mod"));
    pub(crate) static NAT_POW: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.pow"));
    pub(crate) static NAT_BLT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.blt"));
    pub(crate) static NAT_BLE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.ble"));
    pub(crate) static NAT_BEQ: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.beq"));
    pub(crate) static NAT_LAND: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.land"));
    pub(crate) static NAT_LOR: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.lor"));
    pub(crate) static NAT_LXOR: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.xor"));
    pub(crate) static NAT_SHIFT_LEFT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Nat.shiftLeft"));
    pub(crate) static NAT_SHIFT_RIGHT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Nat.shiftRight"));
    pub(crate) static UINT32_ADD: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("UInt32.add"));
    pub(crate) static UINT32_SUB: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("UInt32.sub"));
    pub(crate) static UINT32_MUL: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("UInt32.mul"));
}

/// UInt32 modulus (2^32).
const UINT32_MOD: u64 = 1u64 << 32;

/// Extract a Nat value from an expression (literal form).
///
/// Returns `Some(n)` for `Expr::Lit(Literal::Nat(BigNat::Small(n)))`,
/// `None` for non-literal expressions or big naturals that exceed u64.
pub(crate) fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

/// Extract a BigNat reference from an expression.
///
/// Returns `Some(&bignat)` for any `Expr::Lit(Literal::Nat(_))`,
/// handling both `BigNat::Small` and `BigNat::Big` variants.
/// This enables native reducers to operate on values exceeding u64.
pub(crate) fn get_bignat_val(e: &Expr) -> Option<&BigNat> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => Some(n),
        _ => None,
    }
}

/// Extract a Nat literal that fits within the tc reducer's comparison range.
///
/// clean's tc-side closed Nat predicate reduction currently caps comparisons
/// at values representable in `u128` (small literals and 2-limb `BigNat`s).
/// Native reducers must preserve that same boundary so WHNF does not reduce
/// `Nat.ble`/`Nat.blt`/`Nat.beq` on larger closed values that Lean 4 leaves
/// stuck in this lane.
pub(crate) fn get_nat_pred_val(e: &Expr) -> Option<&BigNat> {
    let n = get_bignat_val(e)?;
    match n {
        BigNat::Small(_) => Some(n),
        BigNat::Big(limbs) if limbs.len() <= 2 => Some(n),
        BigNat::Big(_) => None,
    }
}

/// Native reducer for `Nat.pred : Nat -> Nat`.
///
/// Computes `a - 1`, truncated at zero (Lean floored semantics:
/// `Nat.pred 0 = 0`, `Nat.pred (n+1) = n`). `BigNat::pred()` returns `None`
/// for zero, which maps to `0`. Pure and O(1) on the literal — no `Nat.rec`
/// `succ∘pred` unfolding (which OOMs past ~2^16). This is what lets
/// `Rat.Raw.effDenom` (syntactically `Nat.succ (Nat.pred (Rat.denom x))`)
/// native-reduce on large literal denominators such as `2^1074`.
pub(crate) fn reduce_nat_pred(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let a = get_bignat_val(args[0])?;
    Some(Expr::bignat_lit(a.pred().unwrap_or(BigNat::Small(0))))
}

/// Native reducer for `Nat.add : Nat -> Nat -> Nat`.
///
/// Computes `a + b` for two Nat literals. Handles both Small and Big
/// values via multi-limb addition.
pub(crate) fn reduce_nat_add(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bignat_val(args[0])?;
    let b = get_bignat_val(args[1])?;
    Some(Expr::bignat_lit(a.checked_add_big(b)))
}

/// Native reducer for `Nat.sub : Nat -> Nat -> Nat`.
///
/// Computes `a - b` with truncation to zero (Nat subtraction is floored).
/// Handles both Small and Big values via multi-limb subtraction.
pub(crate) fn reduce_nat_sub(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bignat_val(args[0])?;
    let b = get_bignat_val(args[1])?;
    Some(Expr::bignat_lit(a.saturating_sub_big(b)))
}

/// Native reducer for `Nat.mul : Nat -> Nat -> Nat`.
///
/// Computes `a * b` for two Nat literals. Returns `None` if the result
/// would exceed 1024 bits (16 limbs) to bound allocation.
pub(crate) fn reduce_nat_mul(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bignat_val(args[0])?;
    let b = get_bignat_val(args[1])?;
    Some(Expr::bignat_lit(a.checked_mul_big(b)?))
}

/// Native reducer for `Nat.div : Nat -> Nat -> Nat`.
///
/// Computes `a / b` (floored division). Returns 0 when b == 0.
/// Handles both Small and Big values via multi-limb division.
pub(crate) fn reduce_nat_div(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bignat_val(args[0])?;
    let b = get_bignat_val(args[1])?;
    Some(Expr::bignat_lit(a.checked_div_big(b)))
}

/// Native reducer for `Nat.mod : Nat -> Nat -> Nat`.
///
/// Computes `a % b`. Returns `a` when b == 0 (Lean 4 semantics).
/// Handles both Small and Big values via multi-limb modulo.
pub(crate) fn reduce_nat_mod(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bignat_val(args[0])?;
    let b = get_bignat_val(args[1])?;
    Some(Expr::bignat_lit(a.checked_mod_big(b)))
}

/// Native reducer for `Nat.pow : Nat -> Nat -> Nat`.
///
/// Computes `a ^ b`. Returns `None` if the result would exceed
/// 1024 bits (16 limbs) to bound allocation.
/// Handles both Small and Big values via multi-limb exponentiation.
pub(crate) fn reduce_nat_pow(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bignat_val(args[0])?;
    let b = get_bignat_val(args[1])?;
    Some(Expr::bignat_lit(a.checked_pow_big(b)?))
}

/// Cached `Bool.true` / `Bool.false` constants. The comparison reducers
/// (`Nat.beq`/`ble`/`blt`) return one of these on every call on the hot WHNF
/// arithmetic path; caching the full `Expr` avoids re-interning the name and
/// re-allocating the `Const` node each time. `Expr::clone` is a shallow `Arc`
/// bump, and the returned `Const(Bool.true|false, [])` is structurally identical
/// to a freshly built one, so every kernel verdict is unchanged.
#[inline]
fn bool_const(value: bool) -> Expr {
    use std::sync::LazyLock;
    static BOOL_TRUE: LazyLock<Expr> =
        LazyLock::new(|| Expr::const_(Name::from_string("Bool.true"), vec![]));
    static BOOL_FALSE: LazyLock<Expr> =
        LazyLock::new(|| Expr::const_(Name::from_string("Bool.false"), vec![]));
    if value {
        BOOL_TRUE.clone()
    } else {
        BOOL_FALSE.clone()
    }
}

/// Native reducer for `Nat.beq : Nat -> Nat -> Bool`.
///
/// Computes `a == b` and returns `Bool.true` or `Bool.false`.
/// Handles both Small and Big values via BigNat's PartialEq.
pub(crate) fn reduce_nat_beq(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_pred_val(args[0])?;
    let b = get_nat_pred_val(args[1])?;
    Some(bool_const(a == b))
}

/// Native reducer for `Nat.ble : Nat -> Nat -> Bool`.
///
/// Computes `a <= b` and returns `Bool.true` or `Bool.false`.
/// Handles both Small and Big values via BigNat's Ord.
pub(crate) fn reduce_nat_ble(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_pred_val(args[0])?;
    let b = get_nat_pred_val(args[1])?;
    Some(bool_const(a <= b))
}

/// Native reducer for `Nat.blt : Nat -> Nat -> Bool`.
///
/// Computes `a < b` and returns `Bool.true` or `Bool.false`.
/// Handles both Small and Big values via BigNat's Ord.
pub(crate) fn reduce_nat_blt(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_pred_val(args[0])?;
    let b = get_nat_pred_val(args[1])?;
    Some(bool_const(a < b))
}

/// Native reducer for `Nat.land : Nat -> Nat -> Nat`.
///
/// Bitwise AND. Handles both Small and Big values.
pub(crate) fn reduce_nat_land(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bignat_val(args[0])?;
    let b = get_bignat_val(args[1])?;
    Some(Expr::bignat_lit(a.bitand_big(b)))
}

/// Native reducer for `Nat.lor : Nat -> Nat -> Nat`.
///
/// Bitwise OR. Handles both Small and Big values.
pub(crate) fn reduce_nat_lor(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bignat_val(args[0])?;
    let b = get_bignat_val(args[1])?;
    Some(Expr::bignat_lit(a.bitor_big(b)))
}

/// Native reducer for `Nat.xor : Nat -> Nat -> Nat`.
///
/// Bitwise XOR. Handles both Small and Big values.
pub(crate) fn reduce_nat_lxor(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bignat_val(args[0])?;
    let b = get_bignat_val(args[1])?;
    Some(Expr::bignat_lit(a.bitxor_big(b)))
}

/// Native reducer for `Nat.shiftLeft : Nat -> Nat -> Nat`.
///
/// Left shift. Returns `None` if result would exceed 1024 bits.
/// Handles both Small and Big values.
pub(crate) fn reduce_nat_shift_left(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bignat_val(args[0])?;
    let b = get_bignat_val(args[1])?;
    if a.is_zero() {
        return Some(Expr::nat_lit(0));
    }
    // Cap shift amount to prevent unreasonable allocation
    let shift = b.to_u64()?;
    if shift > 1024 {
        return None; // Result would exceed 1024 bits
    }
    let result = a.checked_shl_big(shift as usize);
    // Verify result doesn't exceed 16 limbs
    if result.limbs().len() > 16 {
        return None;
    }
    Some(Expr::bignat_lit(result))
}

/// Native reducer for `Nat.shiftRight : Nat -> Nat -> Nat`.
///
/// Right shift. Handles both Small and Big values.
pub(crate) fn reduce_nat_shift_right(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bignat_val(args[0])?;
    let b = get_bignat_val(args[1])?;
    let shift = b.to_u64()?;
    if shift > u64::MAX / 2 {
        // Shift larger than any representable value
        return Some(Expr::nat_lit(0));
    }
    Some(Expr::bignat_lit(a.shr_big(shift as usize)))
}

/// Native reducer for `UInt32.add : UInt32 -> UInt32 -> UInt32`.
///
/// UInt32 values are represented as `UInt32.mk n` where `n` is a Nat literal.
/// Addition wraps modulo 2^32. The result is a bare Nat literal (the kernel
/// reconstructs the `UInt32.mk` wrapper during type checking if needed).
pub(crate) fn reduce_uint32_add(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_val(args[0])?;
    let b = get_nat_val(args[1])?;
    let sum = (a.wrapping_add(b)) % UINT32_MOD;
    Some(Expr::nat_lit(sum))
}

/// Native reducer for `UInt32.sub : UInt32 -> UInt32 -> UInt32`.
///
/// Wrapping subtraction modulo 2^32.
pub(crate) fn reduce_uint32_sub(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_val(args[0])?;
    let b = get_nat_val(args[1])?;
    let diff = (a.wrapping_sub(b)) % UINT32_MOD;
    Some(Expr::nat_lit(diff))
}

/// Native reducer for `UInt32.mul : UInt32 -> UInt32 -> UInt32`.
///
/// Wrapping multiplication modulo 2^32.
pub(crate) fn reduce_uint32_mul(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_val(args[0])?;
    let b = get_nat_val(args[1])?;
    let product = (a.wrapping_mul(b)) % UINT32_MOD;
    Some(Expr::nat_lit(product))
}

/// Register all arithmetic native reducers on the environment.
///
/// Called from `init_native_reducers` to add Nat and UInt32 arithmetic
/// fast paths alongside the existing decEq/String reducers.
impl Environment {
    pub(crate) fn init_arith_native_reducers(&mut self) {
        self.register_native_reducer(names::NAT_PRED.clone(), reduce_nat_pred);
        self.register_native_reducer(names::NAT_ADD.clone(), reduce_nat_add);
        self.register_native_reducer(names::NAT_SUB.clone(), reduce_nat_sub);
        self.register_native_reducer(names::NAT_MUL.clone(), reduce_nat_mul);
        self.register_native_reducer(names::NAT_DIV.clone(), reduce_nat_div);
        self.register_native_reducer(names::NAT_MOD.clone(), reduce_nat_mod);
        self.register_native_reducer(names::NAT_POW.clone(), reduce_nat_pow);
        self.register_native_reducer(names::NAT_BLT.clone(), reduce_nat_blt);
        self.register_native_reducer(names::NAT_BLE.clone(), reduce_nat_ble);
        self.register_native_reducer(names::NAT_BEQ.clone(), reduce_nat_beq);
        self.register_native_reducer(names::NAT_LAND.clone(), reduce_nat_land);
        self.register_native_reducer(names::NAT_LOR.clone(), reduce_nat_lor);
        self.register_native_reducer(names::NAT_LXOR.clone(), reduce_nat_lxor);
        self.register_native_reducer(names::NAT_SHIFT_LEFT.clone(), reduce_nat_shift_left);
        self.register_native_reducer(names::NAT_SHIFT_RIGHT.clone(), reduce_nat_shift_right);
        self.register_native_reducer(names::UINT32_ADD.clone(), reduce_uint32_add);
        self.register_native_reducer(names::UINT32_SUB.clone(), reduce_uint32_sub);
        self.register_native_reducer(names::UINT32_MUL.clone(), reduce_uint32_mul);
    }
}
