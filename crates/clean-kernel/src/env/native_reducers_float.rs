// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native reducers for Float operations.
//!
//! In Lean 4, `Float` is `structure Float where mk :: val : UInt64`. Float
//! operations like `Float.add`, `Float.sub`, etc. are `@[extern]` opaque
//! functions with no computational body. Without native reducers, any
//! type-checking that needs to evaluate Float arithmetic gets stuck.
//!
//! This module provides native reducers that interpret the underlying Nat
//! value as IEEE 754 f64 bit patterns, compute the operation, and return
//! the result wrapped in `Float.mk`.
//!
//! Float values flow through the kernel as `Float.mk (UInt64.mk n)` where
//! `n` is a Nat literal representing the f64 bit pattern. After WHNF
//! reduction strips the structure wrappers, the native reducer receives the
//! bare Nat literal argument(s).
//!
//! Reference: Lean 4 Init/Prelude.lean Float definition and
//! runtime/lean_float.h for the C implementations.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;
use std::sync::LazyLock;

/// Well-known names for Float native reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    macro_rules! name {
        ($vis:vis $ident:ident = $value:literal) => {
            $vis static $ident: LazyLock<Name> = LazyLock::new(|| Name::from_string($value));
        };
    }

    // Float arithmetic
    name!(pub(crate) FLOAT_ADD = "Float.add");
    name!(pub(crate) FLOAT_SUB = "Float.sub");
    name!(pub(crate) FLOAT_MUL = "Float.mul");
    name!(pub(crate) FLOAT_DIV = "Float.div");
    name!(pub(crate) FLOAT_NEG = "Float.neg");

    // Float comparison
    name!(pub(crate) FLOAT_BEQ = "Float.beq");
    name!(pub(crate) FLOAT_BLT = "Float.blt");
    name!(pub(crate) FLOAT_BLE = "Float.ble");
    name!(pub(crate) FLOAT_DEC_EQ = "Float.decEq");
    name!(pub(crate) FLOAT_DEC_LT = "Float.decLt");
    name!(pub(crate) FLOAT_DEC_LE = "Float.decLe");

    // Float conversion
    name!(pub(crate) FLOAT_OF_NAT = "Float.ofNat");
    name!(pub(crate) FLOAT_OF_INT = "Float.ofInt");
    name!(pub(crate) FLOAT_OF_SCIENTIFIC = "Float.ofScientific");
    name!(pub(crate) FLOAT_TO_STRING = "Float.toString");
    name!(pub(crate) FLOAT_TO_UINT8 = "Float.toUInt8");
    name!(pub(crate) FLOAT_TO_UINT16 = "Float.toUInt16");
    name!(pub(crate) FLOAT_TO_UINT32 = "Float.toUInt32");
    name!(pub(crate) FLOAT_TO_UINT64 = "Float.toUInt64");

    // Float functions
    name!(pub(crate) FLOAT_SQRT = "Float.sqrt");
    name!(pub(crate) FLOAT_ABS = "Float.abs");
    name!(pub(crate) FLOAT_CEIL = "Float.ceil");
    name!(pub(crate) FLOAT_FLOOR = "Float.floor");
    name!(pub(crate) FLOAT_ROUND = "Float.round");
    name!(pub(crate) FLOAT_IS_NAN = "Float.isNaN");
    name!(pub(crate) FLOAT_IS_INF = "Float.isInf");
    name!(pub(crate) FLOAT_IS_FINITE = "Float.isFinite");

    // Decidable names
    name!(pub(crate) FLOAT = "Float");
    name!(pub(crate) FLOAT_MK = "Float.mk");
    name!(pub(crate) DECIDABLE_IS_TRUE = "Decidable.isTrue");
    name!(pub(crate) EQ_REFL = "Eq.refl");
}

/// Extract the underlying `Nat` bit-pattern of a `Float` argument.
///
/// Accepts both forms a `Float` value can take during reduction:
/// - a bare `Lit(Nat)` — the result of a prior Float arith reducer
///   (`float_binary_op`/`float_unary_op` emit `Expr::nat_lit(bits)`), and
/// - `Float.mk (Lit Nat)` — the surface constructor form. `Float` is the
///   single-field structure `Float.mk :: val : Nat`, so unwrapping `Float.mk n`
///   to its argument `n` is exactly ι-reduction of the `val` projection and is
///   sound. This lets `Float.isNaN (Float.mk bits)` (and the other classifiers
///   / arith ops) reduce on ground constructor inputs, not just on the bare-Nat
///   intermediate form.
pub(crate) fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                if *name == *names::FLOAT_MK {
                    if let ExprKind::Lit(Literal::Nat(n)) = arg.kind() {
                        return n.to_u64();
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Interpret a Nat as the bit pattern of an f64.
fn nat_to_f64(n: u64) -> f64 {
    f64::from_bits(n)
}

/// Convert an f64 to its bit pattern as a Nat.
fn f64_to_nat(f: f64) -> u64 {
    f.to_bits()
}

/// Build a `Float` value expression `Float.mk <bits>` from an f64 bit pattern.
///
/// Every native reducer that yields a `Float` returns it in this canonical
/// constructor form (NOT a bare `Nat` literal). A reduced `Float` must have type
/// `Float` so it is well-typed wherever a `Float` is expected — the operands of
/// `@Eq Float _ _`, the argument of a further `Float` op, a `Float`-typed def
/// body reduced during a `rfl` defeq check, etc. Returning a bare `Nat` here (the
/// prior behavior, which contradicted this module's own doc contract on lines
/// 14/16) made `(1.5 : Float) = (1.5 : Float) := rfl` reduce both sides to a
/// `Nat` literal, after which the kernel rejected the `Eq` with "expected Float,
/// got Nat": a Float value silently collapsing to a `Nat`. `get_nat_val` accepts
/// both `Float.mk n` and the bare-`Nat` intermediate form, so chaining Float ops
/// is unaffected.
fn mk_float(bits: u64) -> Expr {
    Expr::app(
        Expr::const_(names::FLOAT_MK.clone(), vec![]),
        Expr::nat_lit(bits),
    )
}

/// Build a Bool constant expression.
fn mk_bool(val: bool) -> Expr {
    static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
    static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
    if val {
        Expr::const_(BOOL_TRUE.clone(), vec![])
    } else {
        Expr::const_(BOOL_FALSE.clone(), vec![])
    }
}

/// Build a `Decidable.isTrue` proof term for Float equality.
fn mk_float_dec_is_true(val: &Expr) -> Expr {
    let eq_refl = Expr::app(
        Expr::app(
            Expr::const_(
                names::EQ_REFL.clone(),
                vec![crate::level::Level::succ(crate::level::Level::zero())],
            ),
            Expr::const_(names::FLOAT.clone(), vec![]),
        ),
        val.clone(),
    );
    Expr::app(
        Expr::const_(names::DECIDABLE_IS_TRUE.clone(), vec![]),
        eq_refl,
    )
}

/// Apply a binary f64 operation: (Nat, Nat) -> Nat
fn float_binary_op(args: &[&Expr], op: fn(f64, f64) -> f64) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = nat_to_f64(get_nat_val(args[0])?);
    let b = nat_to_f64(get_nat_val(args[1])?);
    Some(mk_float(f64_to_nat(op(a, b))))
}

/// Apply a binary f64 comparison: (Nat, Nat) -> Bool
fn float_binary_cmp(args: &[&Expr], cmp: fn(f64, f64) -> bool) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = nat_to_f64(get_nat_val(args[0])?);
    let b = nat_to_f64(get_nat_val(args[1])?);
    Some(mk_bool(cmp(a, b)))
}

/// Apply a unary f64 operation: Nat -> Nat
fn float_unary_op(args: &[&Expr], op: fn(f64) -> f64) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let a = nat_to_f64(get_nat_val(args[0])?);
    Some(mk_float(f64_to_nat(op(a))))
}

/// Apply a unary f64 predicate: Nat -> Bool
fn float_unary_pred(args: &[&Expr], pred: fn(f64) -> bool) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let a = nat_to_f64(get_nat_val(args[0])?);
    Some(mk_bool(pred(a)))
}

// === Float arithmetic ===

pub(crate) fn reduce_float_add(args: &[&Expr]) -> Option<Expr> {
    float_binary_op(args, |a, b| a + b)
}

pub(crate) fn reduce_float_sub(args: &[&Expr]) -> Option<Expr> {
    float_binary_op(args, |a, b| a - b)
}

pub(crate) fn reduce_float_mul(args: &[&Expr]) -> Option<Expr> {
    float_binary_op(args, |a, b| a * b)
}

pub(crate) fn reduce_float_div(args: &[&Expr]) -> Option<Expr> {
    float_binary_op(args, |a, b| a / b)
}

pub(crate) fn reduce_float_neg(args: &[&Expr]) -> Option<Expr> {
    float_unary_op(args, |a| -a)
}

// === Float comparison ===

pub(crate) fn reduce_float_beq(args: &[&Expr]) -> Option<Expr> {
    float_binary_cmp(args, |a, b| a == b)
}

pub(crate) fn reduce_float_blt(args: &[&Expr]) -> Option<Expr> {
    float_binary_cmp(args, |a, b| a < b)
}

pub(crate) fn reduce_float_ble(args: &[&Expr]) -> Option<Expr> {
    float_binary_cmp(args, |a, b| a <= b)
}

/// Extract the underlying bit-pattern `Nat` from a concrete `Float.mk <nat>`.
///
/// In a well-typed `Decidable (@Eq Float a b)` the operands have type `Float`,
/// so they are constructor applications `Float.mk <nat>`. We only recognise that
/// form (bare operands would be ill-typed for `@Eq Float`), declining otherwise.
fn get_float_ctor_val(e: &Expr) -> Option<u64> {
    let head = e.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        if *name == *names::FLOAT_MK {
            return e.get_app_args().first().and_then(|a| get_nat_val(a));
        }
    }
    None
}

/// Native reducer for `Float.decEq : (a b : Float) → Decidable (a = b)`.
///
/// Propositional equality on `Float` is **structural on the bit pattern** — it
/// is *not* IEEE `==` (which is `Float.beq`). So `+0.0 ≠ -0.0` and `NaN = NaN`
/// when the bits coincide, exactly matching `@Eq Float (Float.mk x) (Float.mk
/// y) ↔ x = y`. The previous reducer compared reinterpreted `f64` values, which
/// is *unsound* for `Eq Float` (it wrongly equates `±0.0` and disequates equal
/// NaNs). We compare bit-`Nat`s and build a sorry-free disproof via the
/// `Float.val` projection (`Float.val (Float.mk n) ι→ n`).
pub(crate) fn reduce_float_dec_eq(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_float_ctor_val(args[0])?;
    let b = get_float_ctor_val(args[1])?;
    if a == b {
        Some(mk_float_dec_is_true(args[0]))
    } else {
        let ty = Expr::const_(names::FLOAT.clone(), vec![]);
        let val_fn = Expr::const_(Name::from_string("Float.val"), vec![]);
        Some(super::native_reducers::mk_wrapper_dec_is_false(
            &ty, &val_fn, args[0], args[1],
        ))
    }
}

/// Native reducer for `Float.decLt`. Float ordering is not backed by an
/// in-kernel order proof, so this *declines* (returns `None`) rather than
/// laundering a `Decidable sorryAx` witness — the kernel falls back to iota.
fn reduce_float_dec_lt(_args: &[&Expr]) -> Option<Expr> {
    None
}

/// Native reducer for `Float.decLe`. Declines for the same reason as
/// [`reduce_float_dec_lt`].
fn reduce_float_dec_le(_args: &[&Expr]) -> Option<Expr> {
    None
}

// === Float conversion ===

/// Native reducer for `Float.ofInt : Int -> Float`.
///
/// In Lean 4, `Int` is an inductive with two constructors:
/// - `Int.ofNat n` represents the non-negative integer n
/// - `Int.negSucc n` represents -(n+1)
///
/// We extract the signed value and convert to f64 bit pattern.
pub(crate) fn reduce_float_of_int(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    // Try to parse as Int constructor application
    let int_val = extract_int_val(args[0])?;
    Some(mk_float(f64_to_nat(int_val as f64)))
}

/// Extract a signed i64 value from an Int constructor application.
///
/// - `Int.ofNat n` -> n (non-negative)
/// - `Int.negSucc n` -> -(n+1) (negative)
/// - bare Nat literal -> n (treated as Int.ofNat n)
fn extract_int_val(e: &Expr) -> Option<i64> {
    static INT_OF_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.ofNat"));
    static INT_NEG_SUCC: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.negSucc"));

    match e.kind() {
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, levels) = f.kind() {
                if !levels.is_empty() {
                    return None;
                }
                if *name == *INT_OF_NAT {
                    let n = get_nat_val(arg)?;
                    return i64::try_from(n).ok();
                }
                if *name == *INT_NEG_SUCC {
                    let n = get_nat_val(arg)?;
                    let n_plus_1 = n.checked_add(1)?;
                    if n_plus_1 > i64::MIN.unsigned_abs() {
                        return None;
                    }
                    return Some((n_plus_1 as i64).wrapping_neg());
                }
            }
            None
        }
        // A bare Nat literal can appear if the kernel hasn't normalized;
        // treat it as Int.ofNat n.
        ExprKind::Lit(Literal::Nat(n)) => {
            let n = n.to_u64()?;
            i64::try_from(n).ok()
        }
        _ => None,
    }
}

/// Native reducer for `Float.ofNat : Nat -> Float`.
pub(crate) fn reduce_float_of_nat(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let n = get_nat_val(args[0])?;
    Some(mk_float(f64_to_nat(n as f64)))
}

/// Native reducer for `Float.ofScientific : Nat -> Bool -> Nat -> Float`.
pub(crate) fn reduce_float_of_scientific(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 3 {
        return None;
    }
    let mantissa = get_nat_val(args[0])?;
    let head = args[1].get_app_fn();
    let negate_exp = if let ExprKind::Const(name, _) = head.kind() {
        static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
        static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
        if *name == *BOOL_TRUE {
            true
        } else if *name == *BOOL_FALSE {
            false
        } else {
            return None;
        }
    } else {
        return None;
    };
    let exponent = get_nat_val(args[2])?;

    let m = mantissa as f64;
    let e = exponent as f64;
    let result = if negate_exp {
        m * 10.0_f64.powf(-e)
    } else {
        m * 10.0_f64.powf(e)
    };
    Some(mk_float(f64_to_nat(result)))
}

/// Native reducer for `Float.toString : Float -> String`.
pub(crate) fn reduce_float_to_string(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let f = nat_to_f64(get_nat_val(args[0])?);
    let s = if f.is_nan() {
        "NaN".to_string()
    } else if f.is_infinite() {
        if f > 0.0 {
            "inf".to_string()
        } else {
            "-inf".to_string()
        }
    } else if f == 0.0 && f.is_sign_negative() {
        "-0.000000".to_string()
    } else {
        format!("{:.6}", f)
    };
    Some(Expr::str_lit(&s))
}

/// Native reducer for `Float.toUInt8 : Float -> UInt8`.
pub(crate) fn reduce_float_to_uint8(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let f = nat_to_f64(get_nat_val(args[0])?);
    let n = if f.is_nan() || f < 0.0 {
        0u64
    } else if f > 255.0 {
        255
    } else {
        f as u64
    };
    Some(Expr::nat_lit(n))
}

/// Native reducer for `Float.toUInt16 : Float -> UInt16`.
pub(crate) fn reduce_float_to_uint16(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let f = nat_to_f64(get_nat_val(args[0])?);
    let n = if f.is_nan() || f < 0.0 {
        0u64
    } else if f > 65535.0 {
        65535
    } else {
        f as u64
    };
    Some(Expr::nat_lit(n))
}

/// Native reducer for `Float.toUInt32 : Float -> UInt32`.
pub(crate) fn reduce_float_to_uint32(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let f = nat_to_f64(get_nat_val(args[0])?);
    let max = u32::MAX as f64;
    let n = if f.is_nan() || f < 0.0 {
        0u64
    } else if f > max {
        u32::MAX as u64
    } else {
        f as u64
    };
    Some(Expr::nat_lit(n))
}

/// Native reducer for `Float.toUInt64 : Float -> UInt64`.
pub(crate) fn reduce_float_to_uint64(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let f = nat_to_f64(get_nat_val(args[0])?);
    let max = u64::MAX as f64;
    let n = if f.is_nan() || f < 0.0 {
        0u64
    } else if f > max {
        u64::MAX
    } else {
        f as u64
    };
    Some(Expr::nat_lit(n))
}

// === Float functions ===

pub(crate) fn reduce_float_sqrt(args: &[&Expr]) -> Option<Expr> {
    float_unary_op(args, f64::sqrt)
}

pub(crate) fn reduce_float_abs(args: &[&Expr]) -> Option<Expr> {
    float_unary_op(args, f64::abs)
}

pub(crate) fn reduce_float_ceil(args: &[&Expr]) -> Option<Expr> {
    float_unary_op(args, f64::ceil)
}

pub(crate) fn reduce_float_floor(args: &[&Expr]) -> Option<Expr> {
    float_unary_op(args, f64::floor)
}

pub(crate) fn reduce_float_round(args: &[&Expr]) -> Option<Expr> {
    float_unary_op(args, f64::round)
}

pub(crate) fn reduce_float_is_nan(args: &[&Expr]) -> Option<Expr> {
    float_unary_pred(args, f64::is_nan)
}

pub(crate) fn reduce_float_is_inf(args: &[&Expr]) -> Option<Expr> {
    float_unary_pred(args, f64::is_infinite)
}

pub(crate) fn reduce_float_is_finite(args: &[&Expr]) -> Option<Expr> {
    float_unary_pred(args, f64::is_finite)
}

/// Register all Float native reducers on the environment.
impl Environment {
    pub(crate) fn init_float_native_reducers(&mut self) {
        // Arithmetic
        self.register_native_reducer(names::FLOAT_ADD.clone(), reduce_float_add);
        self.register_native_reducer(names::FLOAT_SUB.clone(), reduce_float_sub);
        self.register_native_reducer(names::FLOAT_MUL.clone(), reduce_float_mul);
        self.register_native_reducer(names::FLOAT_DIV.clone(), reduce_float_div);
        self.register_native_reducer(names::FLOAT_NEG.clone(), reduce_float_neg);

        // Comparison
        self.register_native_reducer(names::FLOAT_BEQ.clone(), reduce_float_beq);
        self.register_native_reducer(names::FLOAT_BLT.clone(), reduce_float_blt);
        self.register_native_reducer(names::FLOAT_BLE.clone(), reduce_float_ble);
        self.register_native_reducer(names::FLOAT_DEC_EQ.clone(), reduce_float_dec_eq);
        self.register_native_reducer(names::FLOAT_DEC_LT.clone(), reduce_float_dec_lt);
        self.register_native_reducer(names::FLOAT_DEC_LE.clone(), reduce_float_dec_le);

        // Conversion
        self.register_native_reducer(names::FLOAT_OF_NAT.clone(), reduce_float_of_nat);
        self.register_native_reducer(names::FLOAT_OF_INT.clone(), reduce_float_of_int);
        self.register_native_reducer(
            names::FLOAT_OF_SCIENTIFIC.clone(),
            reduce_float_of_scientific,
        );
        self.register_native_reducer(names::FLOAT_TO_STRING.clone(), reduce_float_to_string);
        self.register_native_reducer(names::FLOAT_TO_UINT8.clone(), reduce_float_to_uint8);
        self.register_native_reducer(names::FLOAT_TO_UINT16.clone(), reduce_float_to_uint16);
        self.register_native_reducer(names::FLOAT_TO_UINT32.clone(), reduce_float_to_uint32);
        self.register_native_reducer(names::FLOAT_TO_UINT64.clone(), reduce_float_to_uint64);

        // Functions
        self.register_native_reducer(names::FLOAT_SQRT.clone(), reduce_float_sqrt);
        self.register_native_reducer(names::FLOAT_ABS.clone(), reduce_float_abs);
        self.register_native_reducer(names::FLOAT_CEIL.clone(), reduce_float_ceil);
        self.register_native_reducer(names::FLOAT_FLOOR.clone(), reduce_float_floor);
        self.register_native_reducer(names::FLOAT_ROUND.clone(), reduce_float_round);
        self.register_native_reducer(names::FLOAT_IS_NAN.clone(), reduce_float_is_nan);
        self.register_native_reducer(names::FLOAT_IS_INF.clone(), reduce_float_is_inf);
        self.register_native_reducer(names::FLOAT_IS_FINITE.clone(), reduce_float_is_finite);
    }
}
