// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Char native reducers for the kernel type checker.
//!
//! O(1) computation for Char operations on literal values, avoiding
//! expensive expansion to constructor form. Part of #3134.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;
use std::sync::LazyLock;

/// Well-known names for Char native reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static CHAR_OF_NAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Char.ofNat"));
    pub(crate) static CHAR_TO_NAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Char.toNat"));
    pub(crate) static CHAR_VAL: LazyLock<Name> = LazyLock::new(|| Name::from_string("Char.val"));
    pub(crate) static CHAR_DEC_EQ: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Char.decEq"));
    pub(crate) static CHAR_DEC_LE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Char.decLe"));
    pub(crate) static CHAR_IS_ALPHA: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Char.isAlpha"));
    pub(crate) static CHAR_IS_DIGIT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Char.isDigit"));
    pub(crate) static CHAR_IS_WHITESPACE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Char.isWhitespace"));
    pub(crate) static CHAR_IS_LOWER: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Char.isLower"));
    pub(crate) static CHAR_IS_UPPER: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Char.isUpper"));
    pub(crate) static CHAR_TO_LOWER: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Char.toLower"));
    pub(crate) static CHAR_TO_UPPER: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Char.toUpper"));
}

/// Constructor names used in result building.
mod ctor_names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static CHAR_MK: LazyLock<Name> = LazyLock::new(|| Name::from_string("Char.mk"));
    pub(crate) static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
    pub(crate) static BOOL_FALSE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Bool.false"));
}

/// Extract a Nat value from an expression.
pub(crate) fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

/// Extract the code-point `Nat` carried by a `Char.mk` constructor application,
/// recognizing BOTH the pure-clean and the real-olean constructor shapes.
///
/// * pure-clean: `Char` has a 1-field constructor `Char.mk : Nat → Char`, so the
///   code point is the first argument as a bare `Nat` literal.
/// * real Lean 4 olean: `Char` has a 2-field constructor
///   `Char.mk (val : UInt32) (valid : …)`, and `val` is itself
///   `UInt32.ofBitVec (BitVec.ofFin ⟨n, _⟩)` (or other `BitVec.of*` shapes).
///   The code point is the `Nat` buried in that `BitVec.toNat`-equivalent chain.
///
/// Returns `None` when the first field is not yet reduced to a recognizable
/// literal form (the native reducer then declines and the kernel falls back to
/// δ/ι reduction, which is always sound).
pub(crate) fn char_code_point(e: &Expr) -> Option<u64> {
    let args = e.get_app_args();
    let head = e.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        if *name == *ctor_names::CHAR_MK {
            let field0 = args.first()?;
            // pure-clean: Char.mk <nat>
            if let Some(n) = get_nat_val(field0) {
                return Some(n);
            }
            // olean: Char.mk (UInt32.ofBitVec (BitVec.of* … <nat> …)) valid
            return uint32_field_code_point(field0);
        }
        // `Char.ofNat <natlit>` — the spelling `mk_char_expr` and Lean's own
        // `string_lit_to_constructor` emit, δ-unfolding to the genuine
        // constructor in both environments. Compute the code point Lean's
        // `Char.ofNat` yields WITHOUT forcing the δ-unfold: valid code points
        // pass through, INVALID ones map to 0 (`Char.ofNat n := if n.isValidChar
        // then ⟨n,…⟩ else ⟨0,…⟩`). Sound: this is exactly the value the genuine
        // `Char.ofNat` reduces to, so `Char.toNat`/`decEq`/`utf8Size`/… over a
        // `Char.ofNat` literal see the same code point Lean's kernel would.
        if *name == *names::CHAR_OF_NAT {
            let cp = get_nat_val(args.first()?)?;
            return Some(if is_valid_char(cp) { cp } else { 0 });
        }
    }
    // Bare Nat literal (legacy fast-path callers).
    get_nat_val(e)
}

/// `Nat.isValidChar` predicate: `n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)` —
/// the Unicode scalar-value range (excludes the surrogate block). Matches
/// Lean's `Nat.isValidChar`.
pub(crate) fn is_valid_char(n: u64) -> bool {
    n < 0xD800 || (0xDFFF < n && n < 0x0011_0000)
}

/// Extract a `Nat` code point from an olean `UInt32` value that wraps a
/// `BitVec 32` whose underlying `Nat` is a literal. Recognizes the genuine
/// olean constructor chain `UInt32.ofBitVec (BitVec.ofFin ⟨n, _⟩)` and the
/// `BitVec.ofNat`/`BitVec.ofNatLT` builder shapes. Sound: it only ever reads a
/// concrete `Nat` literal out of a genuine constructor application — exactly the
/// value Lean's own projection chain computes.
fn uint32_field_code_point(e: &Expr) -> Option<u64> {
    // Peel any number of single-field wrappers (UInt32.ofBitVec, BitVec.ofFin,
    // Fin.mk, …) looking for the first Nat literal among constructor arguments.
    // Each wrapper here is a genuine 1-relevant-field constructor whose payload
    // is the next layer; the terminal payload is the code-point Nat.
    let head = e.get_app_fn();
    let args = e.get_app_args();
    if let ExprKind::Const(name, _) = head.kind() {
        let s = name.to_string();
        match s.as_str() {
            // UInt32.ofBitVec b  ->  recurse into b (the BitVec)
            // BitVec.ofFin f     ->  recurse into f (the Fin)
            "UInt32.ofBitVec" | "BitVec.ofFin" => {
                return args.first().and_then(|a| uint32_field_code_point(a));
            }
            // Fin.mk val isLt: the code point is the first explicit Nat argument.
            "Fin.mk" => {
                return args.first().and_then(|a| get_nat_val(a));
            }
            // BitVec.ofNat w n  /  BitVec.ofNatLT {w} n h: the code point is at arg
            // index 1 (AFTER the width). `BitVec.ofNatLT {w} (i : Nat) (p)` carries
            // the width `w` as the first spine argument, so reading args.first()
            // would read the WIDTH, not the value. (Latent wrong-value bug — masked
            // in practice because the real-path width is `@OfNat.ofNat Nat w _`,
            // which the strict get_nat_val declines, falling back to sound δ; but a
            // bare-literal width would expose it. Fixed to match BitVec.ofNat.)
            "BitVec.ofNat" | "BitVec.ofNatLT" => {
                return args.get(1).and_then(|a| get_nat_val(a));
            }
            _ => {}
        }
    }
    // Direct Nat literal (e.g. already reduced).
    get_nat_val(e)
}

/// Extract a Char value, recognizing both pure-clean and olean Char shapes.
pub(crate) fn get_char_val(e: &Expr) -> Option<char> {
    char::from_u32(char_code_point(e)? as u32)
}

/// Build a Char expression from a Rust char value.
///
/// Emits **`Char.ofNat <code_point>`** — the spelling Lean's own kernel emits in
/// string-literal expansion (`string_lit_to_constructor`). `Char.ofNat`
/// δ-unfolds to the genuine constructor in BOTH environments Clean runs in:
/// the pure-clean 1-field `Char.mk <nat>` and the real-olean 2-field
/// `Char.mk (UInt32.ofBitVec (BitVec…)) valid`. Emitting the bare
/// `Char.mk <nat>` (P1-era) was ill-typed against the genuine 2-field ctor
/// (`UInt32` first field, not `Nat`), which broke every olean Char decl whose
/// reduction ran through this builder (`Char.toLower`/`toUpper._proof_*`, …).
/// The code points reaching here are always valid (produced by
/// `Char.toLower`/`toUpper`/`String.get`), so the `Char.ofNat` validity gate is
/// a no-op for them.
pub(crate) fn mk_char_expr(c: char) -> Expr {
    Expr::app(
        Expr::const_(names::CHAR_OF_NAT.clone(), vec![]),
        Expr::nat_lit(c as u64),
    )
}

/// Build a Bool expression.
pub(crate) fn mk_bool_expr(val: bool) -> Expr {
    if val {
        Expr::const_(ctor_names::BOOL_TRUE.clone(), vec![])
    } else {
        Expr::const_(ctor_names::BOOL_FALSE.clone(), vec![])
    }
}

// NOTE — `Char.ofNat` and `Char.val` have NO native reducer (deliberately
// removed; mirrors the `<Name>.ofNat` decline-precedent in
// `native_reducers_uint_conv.rs`).
//
// `Char.ofNat : Nat → Char` and `Char.val : Char → UInt32` are genuine
// definitions in BOTH environments clean runs in, but with DIFFERENT genuine
// constructors / field types:
//   * pure-clean: `Char.mk : Nat → Char` (1-field, Nat carrier), so `Char.ofNat`
//     aliases `Char.mk` and `Char.val` projects field 0 as a Nat.
//   * real Lean 4 olean: `Char.mk (val : UInt32) (valid : …)` (2-field), so
//     `Char.ofNat n` reduces to `Char.mk (UInt32.ofBitVec (BitVec.ofNatLT n h)) h`
//     and `Char.val : Char → UInt32` projects field 0 as a *UInt32*.
//
// A native reducer cannot see the environment (`fn(args) -> Option<Expr>`). The
// old `reduce_char_of_nat` fabricated a 1-arg `Char.mk <nat>` — fictional in the
// olean env (the real ctor is 2-field) — and the old `reduce_char_val` returned
// a BARE `Nat` where a `UInt32` is required. That wrong-typed result left the
// downstream `UInt32.toBitVec (…)` / `UInt32.toNat (…)` projection operand a
// non-constructor, so the projection stuck and `Nat.decLt`/`Nat.ble` never saw a
// literal operand — `decide (…)` never collapsed to `Bool.true`, breaking
// `Char.toLower._proof_1` / `Char.toUpper._proof_1`.
//
// SOUND FIX: decline both fast paths (neither is registered) and let ordinary
// δ-reduction unfold the *real* `Char.ofNat` / `Char.val` definitions. That
// yields the genuine constructor form for whichever environment is loaded; the
// `UInt32.toBitVec` / `UInt32.toNat` / `BitVec.toNat` projections then fire via
// the EXISTING generic proj-through-ctor path, reaching the real code-point
// `Nat`. The width is carried intrinsically by the real `BitVec.ofNatLT`/`ofFin`
// (no width-blind Nat fast path — preserves the #46 cross-width invariant).

/// Native reducer for `Char.toNat : Char → Nat`.
///
/// Extracts the code point from a Char value. Recognizes both the pure-clean
/// 1-field `Char.mk <nat>` and the olean 2-field
/// `Char.mk (UInt32.ofBitVec (BitVec…)) valid` constructor shapes via
/// [`get_char_val`]. Declines (falls back to δ/ι) when the field is not yet a
/// recognizable literal.
pub(crate) fn reduce_char_to_nat(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let c = get_char_val(args[0])?;
    Some(Expr::nat_lit(c as u64))
}

/// Native reducer for `Char.decEq : (a b : Char) → Decidable (a = b)`.
pub(crate) fn reduce_char_dec_eq(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_char_val(args[0])?;
    let b = get_char_val(args[1])?;
    static CHAR_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Char"));
    if a == b {
        Some(super::native_reducers::mk_dec_is_true(&CHAR_NAME, args[0]))
    } else {
        Some(super::native_reducers::mk_char_dec_is_false(
            args[0], args[1],
        ))
    }
}

/// Native reducer for `Char.decLe : (a b : Char) → Decidable (a ≤ b)`.
///
/// `Char` ordering (`a ≤ b` over the code-point `Nat`) is not backed by an
/// in-kernel order proof, so this reducer *declines* rather than emit a
/// `Decidable sorryAx` witness (the false branch) or a type-incorrect
/// `Decidable.isTrue (Eq.refl …)` for the `≤` proposition (the true branch).
/// Sound by omission; the kernel falls back to iota. (`Char.decEq` — genuine
/// equality — remains a real sorry-free disproof.)
pub(crate) fn reduce_char_dec_le(_args: &[&Expr]) -> Option<Expr> {
    None
}

/// Native reducer for `Char.isAlpha : Char → Bool`.
pub(crate) fn reduce_char_is_alpha(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let c = get_char_val(args[0])?;
    Some(mk_bool_expr(c.is_alphabetic()))
}

/// Native reducer for `Char.isDigit : Char → Bool`.
pub(crate) fn reduce_char_is_digit(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let c = get_char_val(args[0])?;
    // Lean 4: Char.isDigit checks '0'..'9' only (ASCII digit), not Unicode Nd.
    Some(mk_bool_expr(c.is_ascii_digit()))
}

/// Native reducer for `Char.isWhitespace : Char → Bool`.
pub(crate) fn reduce_char_is_whitespace(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let c = get_char_val(args[0])?;
    Some(mk_bool_expr(c.is_whitespace()))
}

/// Native reducer for `Char.isLower : Char → Bool`.
pub(crate) fn reduce_char_is_lower(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let c = get_char_val(args[0])?;
    Some(mk_bool_expr(c.is_lowercase()))
}

/// Native reducer for `Char.isUpper : Char → Bool`.
pub(crate) fn reduce_char_is_upper(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let c = get_char_val(args[0])?;
    Some(mk_bool_expr(c.is_uppercase()))
}

/// Native reducer for `Char.toLower : Char → Char`.
pub(crate) fn reduce_char_to_lower(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let c = get_char_val(args[0])?;
    // Lean 4 Char.toLower maps to a single char. For simplicity, use ASCII toLower.
    // Full Unicode lowercasing can produce multiple characters (which doesn't fit Char).
    let lower = if c.is_ascii() {
        c.to_ascii_lowercase()
    } else {
        c.to_lowercase().next().unwrap_or(c)
    };
    Some(mk_char_expr(lower))
}

/// Native reducer for `Char.toUpper : Char → Char`.
pub(crate) fn reduce_char_to_upper(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let c = get_char_val(args[0])?;
    let upper = if c.is_ascii() {
        c.to_ascii_uppercase()
    } else {
        c.to_uppercase().next().unwrap_or(c)
    };
    Some(mk_char_expr(upper))
}

/// Register all Char native reducers on the environment.
impl Environment {
    pub(crate) fn init_char_native_reducers(&mut self) {
        // NOTE: `Char.ofNat` (CHAR_OF_NAT) and `Char.val` (CHAR_VAL) are
        // intentionally NOT registered — see the comment block above. They
        // δ-unfold the real, env-correct definition (sound in both pure-clean and
        // olean envs); a hard-coded fictional/wrong-typed constructor result here
        // broke the Char→UInt32→BitVec→Nat projection chain.
        self.register_native_reducer(names::CHAR_TO_NAT.clone(), reduce_char_to_nat);
        self.register_native_reducer(names::CHAR_DEC_EQ.clone(), reduce_char_dec_eq);
        self.register_native_reducer(names::CHAR_DEC_LE.clone(), reduce_char_dec_le);
        self.register_native_reducer(names::CHAR_IS_ALPHA.clone(), reduce_char_is_alpha);
        self.register_native_reducer(names::CHAR_IS_DIGIT.clone(), reduce_char_is_digit);
        self.register_native_reducer(names::CHAR_IS_WHITESPACE.clone(), reduce_char_is_whitespace);
        self.register_native_reducer(names::CHAR_IS_LOWER.clone(), reduce_char_is_lower);
        self.register_native_reducer(names::CHAR_IS_UPPER.clone(), reduce_char_is_upper);
        self.register_native_reducer(names::CHAR_TO_LOWER.clone(), reduce_char_to_lower);
        self.register_native_reducer(names::CHAR_TO_UPPER.clone(), reduce_char_to_upper);
    }
}

#[cfg(test)]
#[path = "native_reducers_char_tests.rs"]
mod tests;
