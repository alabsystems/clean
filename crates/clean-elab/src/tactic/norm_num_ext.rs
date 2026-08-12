// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended numeric normalization beyond basic Nat/Int arithmetic.
//!
//! Handles rational normalization (`a / b`), power normalization (`a ^ n`),
//! modular arithmetic (`a % b`, `a / b` for Nat/Int), bitwise operations
//! (`land`, `lor`, `xor`, `shiftLeft`, `shiftRight`), comparison normalization,
//! compositional nested normalization, and a configurable extension-point
//! registry.
//!
//! Part of #3082 (Elaboration Parity).

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use crate::stack_safe;

use super::combinator::try_tactic_preserving_state;
use super::core::{Goal, ProofState, TacticError, TacticResult};
use super::equality::match_equality;
use super::nat_expr_eval::eval_nat_expr;
use super::norm_num::{eval_int_expr, try_eval_comparison};
use super::proof_term::{reduce_eq, rfl};
// Kernel-evaluating `decide` ladder, not the bare SMT bridge — see the note in
// `norm_num.rs`. No recursion: `eval_decide` calls the two
// `try_close_*_ground_comparison` helpers below, never `eval_norm_num_ext*`.
use super::decide::eval_decide as decide;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Controls which extension families are active and the maximum expression
/// depth for compositional normalization.
#[derive(Debug, Clone)]
pub(crate) struct NormNumExtConfig {
    pub(crate) max_depth: u32,
    pub(crate) enable_rational: bool,
    pub(crate) enable_power: bool,
    pub(crate) enable_modular: bool,
    pub(crate) enable_bitwise: bool,
    pub(crate) enable_comparison: bool,
}

impl Default for NormNumExtConfig {
    fn default() -> Self {
        Self {
            max_depth: 64,
            enable_rational: true,
            enable_power: true,
            enable_modular: true,
            enable_bitwise: true,
            enable_comparison: true,
        }
    }
}

// ---------------------------------------------------------------------------
// Extension registry
// ---------------------------------------------------------------------------

/// A custom norm_num extension: given an expression, optionally return its
/// evaluated result as an `i128` value. Extensions that do not apply return
/// `None`.
pub(crate) type NormNumExtension = fn(&Expr) -> Option<i128>;

// Registry of user-supplied extensions evaluated after the built-in families.
// Thread-local to avoid synchronization overhead.
std::thread_local! {
    static CUSTOM_EXTENSIONS: std::cell::RefCell<Vec<NormNumExtension>> =
        std::cell::RefCell::new(Vec::new());
}

/// Register a custom norm_num extension for the current thread.
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn register_norm_num_extension(ext: NormNumExtension) {
    CUSTOM_EXTENSIONS.with(|exts| exts.borrow_mut().push(ext));
}

/// Clear all registered extensions (useful in tests).
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn clear_norm_num_extensions() {
    CUSTOM_EXTENSIONS.with(|exts| exts.borrow_mut().clear());
}

/// Try all registered custom extensions.
fn try_custom_extensions(expr: &Expr) -> Option<i128> {
    CUSTOM_EXTENSIONS.with(|exts| {
        for ext in exts.borrow().iter() {
            if let Some(val) = ext(expr) {
                return Some(val);
            }
        }
        None
    })
}

// ---------------------------------------------------------------------------
// Extended evaluators
// ---------------------------------------------------------------------------

/// Evaluate an expression to `i128`, covering all built-in families plus
/// registered custom extensions.
///
/// Supports: Nat literals, Int literals (ofNat/negSucc), the four basic
/// arithmetic operations, `Int.subNatNat` (signed Nat difference), power,
/// modular arithmetic (mod, div), bitwise operations, the Int <-> Nat
/// conversions `Int.natAbs` / `Int.toNat`, and custom extensions.
///
/// Returns `None` for symbolic expressions or overflow.
pub(crate) fn eval_extended(expr: &Expr, config: &NormNumExtConfig, depth: u32) -> Option<i128> {
    if depth > config.max_depth {
        return None;
    }
    stack_safe(|| eval_extended_inner(expr, config, depth))
}

fn eval_extended_inner(expr: &Expr, config: &NormNumExtConfig, depth: u32) -> Option<i128> {
    // Nat literal
    if let ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) = expr.kind() {
        return n.to_u64().map(i128::from);
    }

    // Named constants (zero/one)
    if let ExprKind::Const(name, _) = expr.kind() {
        let s = name.to_string();
        if let v @ Some(_) = match s.as_str() {
            "Nat.zero" | "Int.zero" => Some(0),
            "Nat.one" | "Int.one" | "1" => Some(1),
            _ => None,
        } {
            return v;
        }
        // Fall through to the custom-extension registry so user-supplied
        // extensions can recognise arbitrary nullary constants (e.g. a
        // domain-specific `MyConst : Nat := 42`). Closed Gap 20 in
        // Wave 90 — the registry already existed; the dispatch path
        // simply returned `None` before consulting it.
        return try_custom_extensions(expr);
    }

    // Application forms
    if let ExprKind::App(_, _) = expr.kind() {
        let args = expr.get_app_args();
        let ExprKind::Const(op_name, _) = expr.get_app_fn().kind() else {
            return try_custom_extensions(expr);
        };
        let op = op_name.to_string();

        // Unary: succ, ofNat, negSucc, neg
        if let Some(val) = try_unary_ext(&op, &args, config, depth) {
            return Some(val);
        }

        // Binary (last two args are operands)
        if args.len() >= 2 {
            let l = eval_extended(args[args.len() - 2], config, depth + 1)?;
            let r = eval_extended(args[args.len() - 1], config, depth + 1)?;

            if let Some(val) = try_basic_binop(&op, l, r) {
                return Some(val);
            }
            if let Some(val) = try_int_sub_nat_nat(&op, l, r) {
                return Some(val);
            }
            if let Some(val) = try_gcd(&op, l, r) {
                return Some(val);
            }
            if config.enable_power {
                if let Some(val) = try_power(&op, l, r) {
                    return Some(val);
                }
            }
            if config.enable_modular {
                if let Some(val) = try_modular(&op, l, r) {
                    return Some(val);
                }
            }
            if config.enable_bitwise {
                if let Some(val) = try_bitwise(&op, l, r) {
                    return Some(val);
                }
            }
            if config.enable_rational {
                if let Some(val) = try_rational_div(&op, l, r) {
                    return Some(val);
                }
            }
        }

        return try_custom_extensions(expr);
    }

    try_custom_extensions(expr)
}

// ---------------------------------------------------------------------------
// Unary helpers
// ---------------------------------------------------------------------------

fn try_unary_ext(op: &str, args: &[&Expr], config: &NormNumExtConfig, depth: u32) -> Option<i128> {
    let arg = args.last()?;
    match op {
        "Int.ofNat" => {
            let v = eval_nat_expr(arg)?;
            Some(i128::from(v))
        }
        "Int.negSucc" => {
            let v = eval_nat_expr(arg)?;
            let pos = i128::from(v);
            pos.checked_add(1).and_then(|v| v.checked_neg())
        }
        "Int.neg" | "HNeg.hNeg" | "Neg.neg" => eval_extended(arg, config, depth + 1)?.checked_neg(),
        // Int.natAbs : Int -> Nat, the magnitude |v|. Matches Lean 4 core and
        // clean-kernel's native `reduce_int_nat_abs` (`a.unsigned_abs()`), so
        // the `rfl` close produced after this evaluation is kernel-checkable.
        "Int.natAbs" => eval_extended(arg, config, depth + 1)?.checked_abs(),
        // Int.toNat : Int -> Nat, clamping negatives to 0. Matches Lean 4 core
        // and clean-kernel's native `reduce_int_to_nat`, so the `rfl` close is
        // kernel-checkable.
        "Int.toNat" => Some(eval_extended(arg, config, depth + 1)?.max(0)),
        "Nat.succ" => {
            let v = eval_nat_expr(arg)?;
            let wide = i128::from(v);
            wide.checked_add(1)
        }
        "Nat.factorial" => try_factorial(arg),
        _ => None,
    }
}

/// Evaluate `Nat.factorial n` on a concrete Nat operand.
///
/// Lean 4 core defines `Nat.factorial 0 = 1` and
/// `Nat.factorial (n + 1) = (n + 1) * Nat.factorial n`, i.e. `n!`. The product
/// is built by iteration with `checked_mul`; on overflow (`> i128::MAX`, around
/// `34!`) the function returns `None` and the goal is left untouched — the same
/// decline-on-overflow contract the other extended helpers follow.
///
/// SOUNDNESS: clean-kernel has **no** native `Nat.factorial` reducer (unlike
/// `Nat.gcd` / `Nat.pow`), so this value can NOT, on its own, justify a literal
/// `rfl` close: the returned `i128` is only used to (a) decide whether an
/// equality goal's two sides agree (selecting `rfl` vs. an `ArithmeticFailed`
/// error) and (b) feed the comparison / `decide` gate. The proof itself is
/// always produced by `rfl` / `reduce_eq` / `decide`, which the kernel
/// re-checks: that close succeeds only when `Nat.factorial` is a recursor-based
/// `Declaration::Definition` in the environment that the kernel can unfold by
/// delta + iota to the literal result. When no such definition is present the
/// kernel close fails and `eval_norm_num_ext` returns `Err` — it never emits an
/// unsound or `sorryAx`-bearing proof.
fn try_factorial(arg: &Expr) -> Option<i128> {
    let n = eval_nat_expr(arg)?;
    let mut acc: i128 = 1;
    for k in 2..=n {
        acc = acc.checked_mul(i128::from(k))?;
    }
    Some(acc)
}

// ---------------------------------------------------------------------------
// Binary helpers
// ---------------------------------------------------------------------------

fn try_basic_binop(op: &str, l: i128, r: i128) -> Option<i128> {
    match op {
        "Nat.add" | "Int.add" | "HAdd.hAdd" | "Add.add" => l.checked_add(r),
        "Nat.mul" | "Int.mul" | "HMul.hMul" | "Mul.mul" => l.checked_mul(r),
        "Int.sub" | "HSub.hSub" | "Sub.sub" => l.checked_sub(r),
        // Nat subtraction is saturating
        "Nat.sub" => Some(if l >= r { l - r } else { 0 }),
        _ => None,
    }
}

fn try_power(op: &str, base: i128, exp: i128) -> Option<i128> {
    match op {
        "Nat.pow" | "HPow.hPow" | "Pow.pow" => {
            let e = u32::try_from(exp).ok()?;
            base.checked_pow(e)
        }
        _ => None,
    }
}

/// Evaluate `Int.subNatNat m n` on concrete Nat operands.
///
/// Lean 4 core defines `Int.subNatNat (m n : Nat) : Int` as the signed
/// difference `(m : Int) - (n : Int)`: it yields `Int.ofNat (m - n)` when
/// `m ≥ n` and `Int.negSucc (n - m - 1)` otherwise. As an `i128` magnitude
/// this is simply `m - n`. `Int.add` uses `subNatNat` for mixed-sign cases,
/// and Lean's `norm_num` closes goals such as `Int.subNatNat 5 2 = 3`.
///
/// SOUNDNESS: `Int.subNatNat` is a `Declaration::Definition` in clean-kernel's
/// prelude (`init_int_arith`, `data_types_arithmetic.rs`) built from
/// `Nat.rec` / `Int.rec`, so the kernel reduces `Int.subNatNat m n` to its
/// `Int.ofNat` / `Int.negSucc` normal form by delta + iota reduction with no
/// native shortcut and, crucially, **no `sorryAx`**. The `rfl` close produced
/// after this evaluation is therefore kernel-checkable and axiom-free. (The
/// definition must be present in the environment — `init_int_arith` or any
/// caller such as `init_int_ord_lemmas` provides it.)
fn try_int_sub_nat_nat(op: &str, l: i128, r: i128) -> Option<i128> {
    match op {
        "Int.subNatNat" => l.checked_sub(r),
        _ => None,
    }
}

/// Euclidean GCD on non-negative `i128` magnitudes.
fn gcd_i128(a: i128, b: i128) -> i128 {
    let mut a = a;
    let mut b = b;
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Evaluate `Nat.gcd` on concrete operands, matching Lean 4 semantics.
///
/// Lean 4 `Nat.gcd` is the Euclidean GCD with `Nat.gcd a 0 = a`,
/// `Nat.gcd 0 b = b`, and `Nat.gcd 0 0 = 0`.
///
/// SOUNDNESS: `Nat.gcd` is a native kernel reducer (see
/// `clean-kernel/src/tc/reduction/nat.rs`, `NAT_GCD`), so the `rfl` /
/// `decide` proof terms produced after this evaluation are kernel-checkable.
/// `Nat.lcm` is deliberately *not* handled here: the kernel has no native
/// `Nat.lcm` reducer, so a `rfl` close would fail type-checking. Adding it
/// would require a kernel change, which is out of scope.
fn try_gcd(op: &str, l: i128, r: i128) -> Option<i128> {
    match op {
        "Nat.gcd" => Some(gcd_i128(l, r)),
        _ => None,
    }
}

fn try_modular(op: &str, l: i128, r: i128) -> Option<i128> {
    if r == 0 {
        return match op {
            "Nat.mod" | "HMod.hMod" | "Mod.mod" => Some(l),
            "Nat.div" | "HDiv.hDiv" | "Div.div" => Some(0),
            "Int.mod" | "Int.emod" => Some(l),
            "Int.div" | "Int.ediv" => Some(0),
            _ => None,
        };
    }
    match op {
        "Nat.mod" | "HMod.hMod" | "Mod.mod" => {
            // Euclidean mod for non-negative operands
            Some(l.rem_euclid(r))
        }
        "Nat.div" | "HDiv.hDiv" | "Div.div" => {
            // Truncating division
            Some(l / r)
        }
        // T-division semantics (truncation toward zero); the remainder's
        // sign follows the dividend. Matches Lean 4 `Int.mod` / `Int.div`
        // and clean-kernel's native `reduce_int_mod` (checked_rem) /
        // `reduce_int_div` (checked_div). E.g. (-7) % 3 = -1, (-7) / 3 = -2.
        "Int.mod" => Some(l % r),
        "Int.div" => Some(l / r),
        // Euclidean semantics (remainder always non-negative); the quotient
        // rounds toward negative infinity for positive divisors. Matches
        // Lean 4 `Int.emod` / `Int.ediv`. E.g. (-7) emod 3 = 2,
        // (-7) ediv 3 = -3.
        "Int.emod" => Some(l.rem_euclid(r)),
        "Int.ediv" => Some(l.div_euclid(r)),
        _ => None,
    }
}

fn try_bitwise(op: &str, l: i128, r: i128) -> Option<i128> {
    // Bitwise ops only defined for non-negative values (Nat semantics).
    let lu = u64::try_from(l).ok()?;
    let ru = u64::try_from(r).ok()?;
    let result = match op {
        "Nat.land" | "HAnd.hAnd" | "AndOp.and" => lu & ru,
        "Nat.lor" | "HOr.hOr" | "OrOp.or" => lu | ru,
        "Nat.xor" | "HXor.hXor" | "Xor.xor" => lu ^ ru,
        "Nat.shiftLeft" | "HShiftLeft.hShiftLeft" | "ShiftLeft.shiftLeft" => {
            let shift = u32::try_from(ru).ok()?;
            lu.checked_shl(shift)?
        }
        "Nat.shiftRight" | "HShiftRight.hShiftRight" | "ShiftRight.shiftRight" => {
            let shift = u32::try_from(ru).ok()?;
            lu.checked_shr(shift)?
        }
        _ => return None,
    };
    Some(i128::from(result))
}

fn try_rational_div(op: &str, num: i128, den: i128) -> Option<i128> {
    // Rational division: only returns a value when the result is integral
    // (i.e. `den` divides `num` evenly).
    match op {
        "Rat.div" | "HDiv.hDiv" | "Div.div" => {
            if den == 0 {
                return Some(0); // Lean convention: a / 0 = 0
            }
            if num % den == 0 {
                Some(num / den)
            } else {
                None // non-integral result — cannot normalize to a single i128
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Extended comparison
// ---------------------------------------------------------------------------

/// Evaluate a comparison expression using the extended evaluator so that
/// compound expressions (powers, mod, bitwise, etc.) can be compared.
pub(crate) fn try_eval_ext_comparison(expr: &Expr, config: &NormNumExtConfig) -> Option<bool> {
    if !config.enable_comparison {
        return None;
    }

    // Delegate to the existing evaluator first (handles Nat/Int cases)
    if let Some(result) = try_eval_comparison(expr) {
        return Some(result);
    }

    // Try extended evaluation on the comparison operands
    let args = expr.get_app_args();
    if args.len() < 2 {
        return None;
    }
    let ExprKind::Const(op_name, _) = expr.get_app_fn().kind() else {
        return None;
    };
    let op = op_name.to_string();
    let l = eval_extended(args[args.len() - 2], config, 0)?;
    let r = eval_extended(args[args.len() - 1], config, 0)?;

    if op.contains("LT.lt") || op.contains("Nat.lt") || op.contains("Int.lt") {
        return Some(l < r);
    }
    if op.contains("LE.le") || op.contains("Nat.le") || op.contains("Int.le") {
        return Some(l <= r);
    }
    if op.contains("GT.gt") || op.contains("Int.gt") {
        return Some(l > r);
    }
    if op.contains("GE.ge") || op.contains("Int.ge") {
        return Some(l >= r);
    }
    None
}

// ---------------------------------------------------------------------------
// Extended proposition evaluator
// ---------------------------------------------------------------------------

fn try_eval_ext_prop(expr: &Expr, config: &NormNumExtConfig) -> bool {
    use clean_kernel::name::Name;

    if let ExprKind::Const(name, _) = expr.kind() {
        if name == &Name::from_string("True") {
            return true;
        }
    }

    if let Some(result) = try_eval_ext_comparison(expr, config) {
        return result;
    }

    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(expr) {
        if let (Some(l), Some(r)) = (
            eval_extended(&lhs, config, 0),
            eval_extended(&rhs, config, 0),
        ) {
            return l == r;
        }
    }

    false
}

// ---------------------------------------------------------------------------
// Ground Int comparison close (constructive `Int.NonNeg.mk` witness)
// ---------------------------------------------------------------------------

/// Classify a comparison goal head as a `<=` or `<` relation over `Int`.
///
/// Recognizes both the typeclass form (`@LE.le Int instLEInt a b`,
/// `@LT.lt Int instLTInt a b`) and the bare prelude form (`Int.le a b`,
/// `Int.lt a b`). `GE.ge` / `GT.gt` are intentionally NOT recognized: their
/// `Int` instances do not delta-reduce to `Int.le` / `Int.lt` in the kernel,
/// so a `Int.NonNeg.mk` witness would not type-check against the goal.
///
/// REQUIRES: `target` is a well-formed proposition.
/// ENSURES: `Some(true)` for a recognized strict (`<`) Int comparison,
///          `Some(false)` for a recognized non-strict (`<=`) Int comparison,
///          `None` otherwise.
fn int_comparison_is_strict(target: &Expr) -> Option<bool> {
    let ExprKind::Const(head, _) = target.get_app_fn().kind() else {
        return None;
    };
    let head = head.to_string();
    let args = target.get_app_args();

    // Typeclass form: @Rel.{u} Int inst a b — the type argument must be Int.
    if head == "LE.le" || head == "LT.lt" {
        if args.len() < 4 {
            return None;
        }
        if !matches!(args[0].kind(), ExprKind::Const(n, _) if n == &Name::from_string("Int")) {
            return None;
        }
        return Some(head == "LT.lt");
    }

    // Bare prelude form: Int.le a b / Int.lt a b.
    if head == "Int.le" || head == "Int.lt" {
        if args.len() < 2 {
            return None;
        }
        return Some(head == "Int.lt");
    }

    None
}

/// Build a constructive proof closing a TRUE ground `Int` `<=` / `<` goal.
///
/// `Int.le a b` is defined as `Int.NonNeg (Int.sub b a)` and `Int.lt a b` as
/// `Int.le (a + 1) b`. `Int.NonNeg` has the single constructor
/// `Int.NonNeg.mk : (n : Nat) -> Int.NonNeg (Int.ofNat n)`. For a true
/// comparison the difference `d` (`b - a` for `<=`, `b - a - 1` for `<`) is a
/// non-negative integer, so `@Int.NonNeg.mk d` proves
/// `Int.NonNeg (Int.ofNat d)`, which the kernel checks definitionally equal to
/// the goal by reducing `Int.sub` (native reducer) and unfolding `Int.le` /
/// `Int.lt`.
///
/// SOUNDNESS: the witness is `Int.NonNeg.mk`, an inductive constructor -- no
/// `sorryAx`, no decidability axiom (`instDecidableIntLe` / `instDecidableIntLt`
/// are non-computational axioms, which is why `decide` cannot close these
/// goals soundly). `close_goal` re-checks the term against the goal type.
///
/// REQUIRES: `goal.target` is a recognized ground `Int` `<=` / `<` comparison.
/// ENSURES: On `Some(())`, the goal has been closed with a kernel-checked
///          `Int.NonNeg.mk` proof term.
/// ENSURES: On `None`, the goal was not a ground Int comparison or evaluated
///          to false; the proof state is unchanged.
pub(crate) fn try_close_int_ground_comparison(state: &mut ProofState, goal: &Goal) -> Option<()> {
    let target = state.metas.instantiate(&goal.target);
    let strict = int_comparison_is_strict(&target)?;

    let args = target.get_app_args();
    let lhs = args[args.len() - 2];
    let rhs = args[args.len() - 1];

    let l = eval_int_expr(lhs)?;
    let r = eval_int_expr(rhs)?;

    // `a <= b` => diff = b - a; `a < b` => diff = b - a - 1. The comparison is
    // true exactly when diff >= 0.
    let diff = if strict {
        r.checked_sub(l)?.checked_sub(1)?
    } else {
        r.checked_sub(l)?
    };
    let diff = u64::try_from(diff).ok()?; // None => comparison is false

    // @Int.NonNeg.mk diff : Int.NonNeg (Int.ofNat diff)
    let witness = Expr::app(
        Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
        Expr::nat_lit(diff),
    );

    state.close_goal(goal, witness).ok()
}

// ---------------------------------------------------------------------------
// Ground Nat comparison close (constructive `Nat.le.step` chain witness)
// ---------------------------------------------------------------------------

/// A ground Nat order goal reduced to the canonical `Nat.le low high` shape.
///
/// Every Nat order relation reduces to `Nat.le`:
/// - `a <= b` → `Nat.le a b`            (`low = a`, `high = b`)
/// - `a <  b` → `Nat.le (a+1) b`        (`low = a+1`, `high = b`)
/// - `a >= b` → `Nat.le b a`            (`low = b`, `high = a`)
/// - `a >  b` → `Nat.le (b+1) a`        (`low = b+1`, `high = a`)
struct NatLeShape {
    low: u64,
    high: u64,
}

/// Classify a Nat order goal head and reduce it to a `Nat.le low high` shape.
///
/// Recognizes both the typeclass form (`@LE.le Nat instLENat a b`, and likewise
/// `LT.lt` / `GE.ge` / `GT.gt`) and the bare prelude form (`Nat.le a b`,
/// `Nat.lt a b`, `Nat.ge a b`, `Nat.gt a b`). The first explicit type argument
/// of the typeclass form must be `Nat`.
///
/// REQUIRES: `target` is a well-formed proposition.
/// ENSURES: `Some(shape)` for a recognized ground Nat order goal whose operands
///          both evaluate to concrete `Nat` values; `None` otherwise.
fn nat_comparison_shape(target: &Expr) -> Option<NatLeShape> {
    let ExprKind::Const(head, _) = target.get_app_fn().kind() else {
        return None;
    };
    let head = head.to_string();
    let args = target.get_app_args();

    // Determine the relation kind and whether the operands carry a leading
    // `Nat` type argument (typeclass form) that must be validated.
    //
    // `strict` selects `<` vs `<=`; `swap` selects the `>=` / `>` orientation
    // (which proves `Nat.le high low` instead of `Nat.le low high`).
    let (strict, swap) = match head.as_str() {
        "LE.le" | "Nat.le" => (false, false),
        "LT.lt" | "Nat.lt" => (true, false),
        "GE.ge" | "Nat.ge" => (false, true),
        "GT.gt" | "Nat.gt" => (true, true),
        _ => return None,
    };

    // Typeclass form carries the element type as the first explicit argument;
    // require it to be `Nat`. The bare `Nat.*` forms take only the two operands.
    let is_typeclass = matches!(head.as_str(), "LE.le" | "LT.lt" | "GE.ge" | "GT.gt");
    if is_typeclass {
        if args.len() < 4 {
            return None;
        }
        if !matches!(args[0].kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat")) {
            return None;
        }
    } else if args.len() < 2 {
        return None;
    }

    let lhs = eval_nat_expr(args[args.len() - 2])?;
    let rhs = eval_nat_expr(args[args.len() - 1])?;

    // Normalize to the operands of the underlying `Nat.le` after any `>=` / `>`
    // swap, then push the strict `<` into `low + 1`.
    let (mut low, high) = if swap { (rhs, lhs) } else { (lhs, rhs) };
    if strict {
        low = low.checked_add(1)?;
    }
    Some(NatLeShape { low, high })
}

/// Build a constructive `Nat.le low high` proof from inductive constructors.
///
/// `Nat.le` is the inductive with `Nat.le.refl : (n : Nat) -> Nat.le n n` and
/// `Nat.le.step : {n m : Nat} -> Nat.le n m -> Nat.le n (Nat.succ m)`. Starting
/// from `@Nat.le.refl low : Nat.le low low`, each `@Nat.le.step low m _`
/// advances the upper index by one `Nat.succ`, so `high - low` steps yield
/// `Nat.le low (Nat.succ^(high-low) low)`, which the kernel checks definitionally
/// equal to `Nat.le low high` (the native `Nat.succ` reducer collapses the
/// chain back to the `high` literal).
///
/// REQUIRES: `low <= high`.
pub(crate) fn build_nat_le_witness(low: u64, high: u64) -> Expr {
    // @Nat.le.refl low : Nat.le low low
    let mut proof = Expr::app(
        Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
        Expr::nat_lit(low),
    );
    // For m = low, low+1, ..., high-1: lift Nat.le low m to Nat.le low (succ m).
    let mut m = low;
    while m < high {
        proof = Expr::apps(
            Expr::const_(Name::from_string("Nat.le.step"), vec![]),
            [Expr::nat_lit(low), Expr::nat_lit(m), proof],
        );
        m += 1;
    }
    proof
}

/// Close a TRUE ground Nat `<=` / `<` / `>=` / `>` goal with a constructive
/// `Nat.le.refl` / `Nat.le.step` witness.
///
/// SOUNDNESS: the witness is built solely from the `Nat.le` inductive
/// constructors -- no `sorryAx`, and crucially no `Nat.decLe` / `Nat.decLt`
/// decidability reducer (the kernel's native `Nat.decLe` reducer emits
/// `Decidable.isTrue sorryAx`, so extracting a proof from it would smuggle in
/// `sorryAx`). `close_goal` re-checks the term against the goal type, where the
/// relation unfolds to the canonical `Nat.le` and the `Nat.succ` chain reduces
/// to the goal's literal upper bound.
///
/// REQUIRES: `goal.target` is a recognized ground Nat order comparison.
/// ENSURES: On `Some(())`, the goal has been closed with a kernel-checked
///          `Nat.le` witness.
/// ENSURES: On `None`, the goal was not a ground Nat comparison or evaluated to
///          false; the proof state is unchanged.
pub(crate) fn try_close_nat_ground_comparison(state: &mut ProofState, goal: &Goal) -> Option<()> {
    /// Cap on `Nat.le.step` chain length: each step is one term, so an
    /// unbounded gap (e.g. `0 <= 1_000_000`) would build a pathologically large
    /// proof term. Beyond this, decline and let `decide` handle it.
    const MAX_STEPS: u64 = 4096;

    let target = state.metas.instantiate(&goal.target);
    let shape = nat_comparison_shape(&target)?;

    // The comparison is true exactly when `low <= high`; otherwise reject so the
    // caller does not mis-close a false goal.
    if shape.low > shape.high {
        return None;
    }
    if shape.high - shape.low > MAX_STEPS {
        return None;
    }

    let witness = build_nat_le_witness(shape.low, shape.high);
    state.close_goal(goal, witness).ok()
}

// ---------------------------------------------------------------------------
// Tactic entry-point
// ---------------------------------------------------------------------------

/// Extended norm_num tactic.
///
/// Handles all operations supported by `eval_norm_num` plus rational division,
/// power, modular arithmetic, bitwise operations, and custom extensions.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the current goal is closed
/// ENSURES: On Err(ArithmeticFailed), evaluation determined the goal is false
/// ENSURES: Only closes goals where both sides reduce to the same value
pub fn eval_norm_num_ext(state: &mut ProofState) -> TacticResult {
    eval_norm_num_ext_with_config(state, &NormNumExtConfig::default())
}

/// Extended norm_num with explicit configuration.
pub(crate) fn eval_norm_num_ext_with_config(
    state: &mut ProofState,
    config: &NormNumExtConfig,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = &goal.target;

    // Try decidable proposition
    if try_eval_ext_prop(target, config) {
        if try_tactic_preserving_state(state, decide) {
            return Ok(());
        }
        if try_tactic_preserving_state(state, rfl) {
            return Ok(());
        }
    }

    // Equality: normalize both sides with extended evaluator
    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(target) {
        if let (Some(l), Some(r)) = (
            eval_extended(&lhs, config, 0),
            eval_extended(&rhs, config, 0),
        ) {
            if l == r {
                return rfl(state);
            }
            return Err(TacticError::ArithmeticFailed {
                tactic: "norm_num_ext".into(),
                reason: format!("extended: {l} != {r}"),
            });
        }

        // Fall back to Nat/Int-only evaluation
        if let (Some(l), Some(r)) = (eval_nat_expr(&lhs), eval_nat_expr(&rhs)) {
            if l == r {
                return rfl(state);
            }
            return Err(TacticError::ArithmeticFailed {
                tactic: "norm_num_ext".into(),
                reason: format!("Nat: {l} != {r}"),
            });
        }
        if let (Some(l), Some(r)) = (eval_int_expr(&lhs), eval_int_expr(&rhs)) {
            if l == r {
                return rfl(state);
            }
            return Err(TacticError::ArithmeticFailed {
                tactic: "norm_num_ext".into(),
                reason: format!("Int: {l} != {r}"),
            });
        }
    }

    // Comparison
    if let Some(result) = try_eval_ext_comparison(target, config) {
        if result {
            // Ground Int `<=` / `<` goals are closed with a constructive
            // `Int.NonNeg.mk` witness. `decide` cannot close these soundly
            // because `instDecidableIntLe` / `instDecidableIntLt` are
            // non-computational axioms, so the decidability reducer never
            // yields a real proof for Int.
            if try_close_int_ground_comparison(state, &goal).is_some() {
                return Ok(());
            }
            // Ground Nat `<=` / `<` / `>=` / `>` goals are closed with a
            // constructive `Nat.le.refl` / `Nat.le.step` chain. The kernel's
            // `Nat.decLe` / `Nat.decLt` reducers emit `Decidable.isTrue
            // sorryAx`, so the decidability path would smuggle in `sorryAx`;
            // the `>` / bare `Nat.gt` / bare `Nat.ge` shapes also never reached
            // a sound `decide` path at all.
            if try_close_nat_ground_comparison(state, &goal).is_some() {
                return Ok(());
            }
            return decide(state);
        }
        return Err(TacticError::ArithmeticFailed {
            tactic: "norm_num_ext".into(),
            reason: "comparison is false".into(),
        });
    }

    // Ground disequality `a ≠ b`: Lean's `norm_num` closes these. Route through
    // the kernel-checkable noConfusion disequality builder. Part of the
    // tactic-divergence parity work.
    if super::decide_eq::match_ne(target).is_some() {
        if super::decide_eq::try_close_ne_by_noconfusion(state).is_ok() {
            return Ok(());
        }
        return Err(TacticError::ArithmeticFailed {
            tactic: "norm_num_ext".into(),
            reason: "could not prove disequality".into(),
        });
    }

    // Fallback: reduce_eq
    reduce_eq(state).map_err(|_| TacticError::ArithmeticFailed {
        tactic: "norm_num_ext".into(),
        reason: "could not evaluate extended numeric goal".into(),
    })
}
