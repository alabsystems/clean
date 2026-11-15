// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Char native reducers.

use super::*;
use crate::expr::{ExprKind, Literal};
use crate::name::Name;

// === Char.ofNat / Char.val: deliberately NO native reducer ===
//
// `Char.ofNat` and `Char.val` are intentionally NOT registered (see the comment
// block in `native_reducers_char.rs`): a hard-coded constructor result is
// fictional/wrong-typed in the real olean env (2-field `Char.mk`), which broke
// the Char→UInt32→BitVec→Nat projection chain. They δ-unfold the real, env-correct
// definitions instead. The registration test below asserts they are unregistered.

// === Char code-point extraction: olean 2-field Char.mk shape ===

/// The genuine kernel spine: `@BitVec.ofFin {w} (@Fin.mk {n} val isLt)`,
/// implicit arguments included (a kernel term carries every argument). With a
/// bare-literal width and bound, reading the spine's FIRST argument returned
/// the width (32) — or, one level down, the bound — instead of the value. The
/// fixture this test used to build omitted the implicits, which is exactly the
/// shape that hid the misread (fixed 2026-09-26, fold-authority audit).
fn olean_char(width: Expr, bound: Expr, value: u64) -> Expr {
    let fin = Expr::apps(
        Expr::const_(Name::from_string("Fin.mk"), vec![]),
        [
            bound,
            Expr::nat_lit(value),
            Expr::const_(Name::from_string("trivial"), vec![]),
        ],
    );
    let bv = Expr::apps(
        Expr::const_(Name::from_string("BitVec.ofFin"), vec![]),
        [width, fin],
    );
    let u32v = Expr::app(
        Expr::const_(Name::from_string("UInt32.ofBitVec"), vec![]),
        bv,
    );
    Expr::apps(
        Expr::const_(Name::from_string("Char.mk"), vec![]),
        [u32v, Expr::const_(Name::from_string("trivial"), vec![])],
    )
}

#[test]
fn test_char_code_point_ofin_reads_value_not_width_or_bound() {
    // Bare-literal width 32 and bound 2^32: the value is 90.
    let ch = olean_char(Expr::nat_lit(32), Expr::nat_lit(1 << 32), 90);
    assert_eq!(
        char_code_point(&ch),
        Some(90),
        "value, not width (32) or bound"
    );
    assert_eq!(get_char_val(&ch), Some('Z'));
}

#[test]
fn test_char_code_point_olean_two_field_shape() {
    // olean: Char.mk (UInt32.ofBitVec (@BitVec.ofFin w (@Fin.mk n <v> _))) valid
    // char_code_point must dig the literal <v> out of the genuine ctor chain.
    let n = Expr::nat_lit(90);
    let fin = Expr::apps(
        Expr::const_(Name::from_string("Fin.mk"), vec![]),
        [
            Expr::const_(Name::from_string("bound"), vec![]),
            n.clone(),
            Expr::const_(Name::from_string("trivial"), vec![]),
        ],
    );
    let bv = Expr::apps(
        Expr::const_(Name::from_string("BitVec.ofFin"), vec![]),
        [Expr::const_(Name::from_string("width"), vec![]), fin],
    );
    let u32v = Expr::app(
        Expr::const_(Name::from_string("UInt32.ofBitVec"), vec![]),
        bv,
    );
    let valid = Expr::const_(Name::from_string("trivial"), vec![]);
    let ch = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Char.mk"), vec![]), u32v),
        valid,
    );
    assert_eq!(char_code_point(&ch), Some(90));
    assert_eq!(get_char_val(&ch), Some('Z'));
}

#[test]
fn test_char_code_point_bitvec_ofnatlt_reads_value_not_width() {
    // Adversarial ratchet (#46): Char.mk (UInt32.ofBitVec (BitVec.ofNatLT <w> <v> _)) valid.
    // BitVec.ofNatLT {w} (i : Nat) (p) carries the WIDTH w as its first spine arg, so
    // char_code_point must read arg index 1 (the value v=90), NOT args.first() (the
    // width w=32). On the prior buggy code (args.first()) this returned Some(32).
    let width = Expr::nat_lit(32);
    let value = Expr::nat_lit(90);
    let bv = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("BitVec.ofNatLT"), vec![]),
                width,
            ),
            value,
        ),
        Expr::const_(Name::from_string("trivial"), vec![]),
    );
    let u32v = Expr::app(
        Expr::const_(Name::from_string("UInt32.ofBitVec"), vec![]),
        bv,
    );
    let ch = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Char.mk"), vec![]), u32v),
        Expr::const_(Name::from_string("trivial"), vec![]),
    );
    assert_eq!(
        char_code_point(&ch),
        Some(90),
        "must read the value (90), not the width (32)"
    );
}

#[test]
fn test_char_code_point_pure_clean_one_field_shape() {
    // pure-clean: Char.mk <nat>
    assert_eq!(char_code_point(&mk_char_expr('Z')), Some(90));
}

// === Char.toNat tests ===

#[test]
fn test_reduce_char_to_nat() {
    let c = mk_char_expr('A');
    let result = reduce_char_to_nat(&[&c]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(65));
    } else {
        panic!("Expected Nat literal 65");
    }
}

// === Char.decEq tests ===

#[test]
fn test_reduce_char_dec_eq_equal() {
    let a = mk_char_expr('x');
    let b = mk_char_expr('x');
    let result = reduce_char_dec_eq(&[&a, &b]);
    assert!(result.is_some());
}

#[test]
fn test_reduce_char_dec_eq_not_equal() {
    let a = mk_char_expr('x');
    let b = mk_char_expr('y');
    let result = reduce_char_dec_eq(&[&a, &b]);
    assert!(result.is_some());
}

// === Char.decLe tests ===

// `Char.decLe` (ordering) now *declines*: it is not backed by an in-kernel
// order proof, so it returns `None` instead of laundering a `Decidable sorryAx`
// witness (false branch) or a type-incorrect `isTrue (Eq.refl …)` for `≤` (true
// branch). Sound by omission. (`Char.decEq` — equality — stays a real disproof.)
#[test]
fn test_reduce_char_dec_le_declines() {
    for (x, y) in [('a', 'z'), ('m', 'm'), ('z', 'a')] {
        let a = mk_char_expr(x);
        let b = mk_char_expr(y);
        assert!(
            reduce_char_dec_le(&[&a, &b]).is_none(),
            "Char.decLe {x:?} {y:?} declines (unproven order)"
        );
    }
}

// === Char.isAlpha tests ===

#[test]
fn test_reduce_char_is_alpha_true() {
    let c = mk_char_expr('A');
    let result = reduce_char_is_alpha(&[&c]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.true"));
    } else {
        panic!("Expected Bool.true");
    }
}

#[test]
fn test_reduce_char_is_alpha_false() {
    let c = mk_char_expr('5');
    let result = reduce_char_is_alpha(&[&c]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.false"));
    } else {
        panic!("Expected Bool.false");
    }
}

// === Char.isDigit tests ===

#[test]
fn test_reduce_char_is_digit_true() {
    let c = mk_char_expr('7');
    let result = reduce_char_is_digit(&[&c]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.true"));
    } else {
        panic!("Expected Bool.true");
    }
}

#[test]
fn test_reduce_char_is_digit_false() {
    let c = mk_char_expr('x');
    let result = reduce_char_is_digit(&[&c]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.false"));
    } else {
        panic!("Expected Bool.false");
    }
}

// === Char.isWhitespace tests ===

#[test]
fn test_reduce_char_is_whitespace_true() {
    let c = mk_char_expr(' ');
    let result = reduce_char_is_whitespace(&[&c]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.true"));
    } else {
        panic!("Expected Bool.true");
    }
}

#[test]
fn test_reduce_char_is_whitespace_false() {
    let c = mk_char_expr('A');
    let result = reduce_char_is_whitespace(&[&c]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.false"));
    } else {
        panic!("Expected Bool.false");
    }
}

// === Char.isLower / Char.isUpper tests ===

#[test]
fn test_reduce_char_is_lower_true() {
    let c = mk_char_expr('a');
    let result = reduce_char_is_lower(&[&c]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.true"));
    } else {
        panic!("Expected Bool.true");
    }
}

#[test]
fn test_reduce_char_is_upper_true() {
    let c = mk_char_expr('A');
    let result = reduce_char_is_upper(&[&c]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.true"));
    } else {
        panic!("Expected Bool.true");
    }
}

// === Char.toLower / Char.toUpper tests ===

#[test]
fn test_reduce_char_to_lower() {
    let c = mk_char_expr('A');
    let result = reduce_char_to_lower(&[&c]);
    assert!(result.is_some());
    let result = result.unwrap();
    let args = result.get_app_args();
    let n = get_nat_val(args[0]).unwrap();
    assert_eq!(n, 97, "Expected 'a' (97)");
}

#[test]
fn test_reduce_char_to_upper() {
    let c = mk_char_expr('a');
    let result = reduce_char_to_upper(&[&c]);
    assert!(result.is_some());
    let result = result.unwrap();
    let args = result.get_app_args();
    let n = get_nat_val(args[0]).unwrap();
    assert_eq!(n, 65, "Expected 'A' (65)");
}

// === Registration test ===

#[test]
fn test_char_native_reducers_registered() {
    let mut env = Environment::new();
    env.init_char_native_reducers();

    // Char.ofNat / Char.val are intentionally NOT registered — they δ-unfold
    // the real env-correct definitions (a fictional/wrong-typed constructor
    // result broke the Char→UInt32→BitVec→Nat projection chain).
    assert!(
        env.get_native_reducer(&names::CHAR_OF_NAT).is_none(),
        "Char.ofNat must have NO native reducer (declines to δ)"
    );
    assert!(
        env.get_native_reducer(&names::CHAR_VAL).is_none(),
        "Char.val must have NO native reducer (declines to δ)"
    );
    assert!(env.get_native_reducer(&names::CHAR_TO_NAT).is_some());
    assert!(env.get_native_reducer(&names::CHAR_DEC_EQ).is_some());
    assert!(env.get_native_reducer(&names::CHAR_DEC_LE).is_some());
    assert!(env.get_native_reducer(&names::CHAR_IS_ALPHA).is_some());
    assert!(env.get_native_reducer(&names::CHAR_IS_DIGIT).is_some());
    assert!(env.get_native_reducer(&names::CHAR_IS_WHITESPACE).is_some());
    assert!(env.get_native_reducer(&names::CHAR_IS_LOWER).is_some());
    assert!(env.get_native_reducer(&names::CHAR_IS_UPPER).is_some());
    assert!(env.get_native_reducer(&names::CHAR_TO_LOWER).is_some());
    assert!(env.get_native_reducer(&names::CHAR_TO_UPPER).is_some());
}

#[test]
fn test_reduce_char_dec_eq_not_equal_is_sound() {
    use crate::env::Environment;
    use crate::tc::TypeChecker;
    fn mentions_sorry(e: &Expr) -> bool {
        match e.kind() {
            ExprKind::Const(n, _) => {
                let s = n.to_string();
                s == "sorryAx" || s == "sorry"
            }
            ExprKind::App(f, a) => mentions_sorry(f) || mentions_sorry(a),
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                mentions_sorry(t) || mentions_sorry(b)
            }
            ExprKind::Let(_, t, v, b, _) => {
                mentions_sorry(t) || mentions_sorry(v) || mentions_sorry(b)
            }
            _ => false,
        }
    }
    let a = mk_char_expr('x');
    let b = mk_char_expr('y');
    let term = reduce_char_dec_eq(&[&a, &b]).expect("reduces");
    assert!(
        !mentions_sorry(&term),
        "Char.decEq 'x' 'y' must be sorry-free: {term:?}"
    );
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&term)
        .expect("char decEq reducer output type-checks");
}

// === ASCII-only, like Lean ===

/// Lean v4.30.0-rc2 `src/Init/Data/Char/Basic.lean`, written out independently
/// of the reducers and WITHOUT any `char::is_*` helper, so a helper whose
/// notion of "ASCII whitespace" or "letter" differs from Lean's cannot make the
/// model and the reducer wrong together.
//
// `clippy::manual_is_ascii_check` wants `c.is_ascii_uppercase()` here. Taking
// that suggestion would defeat the paragraph above: the whole value of this
// module is that it does NOT route through a `char::is_*` helper, so a helper
// that disagrees with Lean cannot agree with the reducer and hide the
// disagreement. The manual range IS the independence.
#[allow(clippy::manual_is_ascii_check)]
mod lean_char_model {
    pub(super) fn is_whitespace(c: char) -> bool {
        c == ' ' || c == '\t' || c == '\r' || c == '\n'
    }
    pub(super) fn is_upper(c: char) -> bool {
        ('A'..='Z').contains(&c)
    }
    pub(super) fn is_lower(c: char) -> bool {
        ('a'..='z').contains(&c)
    }
    pub(super) fn is_alpha(c: char) -> bool {
        is_upper(c) || is_lower(c)
    }
    pub(super) fn to_lower(c: char) -> char {
        if is_upper(c) {
            char::from_u32(c as u32 + 32).expect("ASCII")
        } else {
            c
        }
    }
    pub(super) fn to_upper(c: char) -> char {
        if is_lower(c) {
            char::from_u32(c as u32 - 32).expect("ASCII")
        } else {
            c
        }
    }
}

/// The six classifier / case-map reducers agree with Lean on EVERY ASCII code
/// point and on the non-ASCII characters where a Unicode-aware answer differs.
/// Each near-miss below is what the previous (Rust-Unicode) reducers answered,
/// and each is FALSE in Lean 4.
#[test]
fn test_char_reducers_are_ascii_only_like_lean() {
    use lean_char_model as lean;
    let bool_of = |e: Option<Expr>| -> bool {
        let e = e.expect("reducer must fire on a Char literal");
        if e == mk_bool_expr(true) {
            true
        } else {
            assert_eq!(e, mk_bool_expr(false), "a Bool reducer must answer a Bool");
            false
        }
    };
    let char_of = |e: Option<Expr>| -> char {
        get_char_val(&e.expect("reducer must fire on a Char literal"))
            .expect("a Char reducer must answer a Char")
    };

    // U+00E9 é / U+00C9 É: a Unicode letter pair. U+00DF ß: uppercases to "SS".
    // U+0130 İ: lowercases to two code points. U+03A9 Ω / U+03C9 ω: Greek.
    // U+000B / U+000C: whitespace to Rust, not to Lean. U+00A0 / U+2003 /
    // U+3000: Unicode spaces. U+0661: a non-ASCII digit (control: `isDigit` was
    // already ASCII-only and must stay so).
    let non_ascii = [
        '\u{e9}',
        '\u{c9}',
        '\u{df}',
        '\u{130}',
        '\u{3a9}',
        '\u{3c9}',
        '\u{a0}',
        '\u{2003}',
        '\u{3000}',
        '\u{661}',
        '\u{10ffff}',
    ];
    for c in (0u8..=127).map(char::from).chain(non_ascii) {
        let e = mk_char_expr(c);
        let at = format!("U+{:04X}", c as u32);
        assert_eq!(
            bool_of(reduce_char_is_whitespace(&[&e])),
            lean::is_whitespace(c),
            "isWhitespace {at}"
        );
        assert_eq!(
            bool_of(reduce_char_is_upper(&[&e])),
            lean::is_upper(c),
            "isUpper {at}"
        );
        assert_eq!(
            bool_of(reduce_char_is_lower(&[&e])),
            lean::is_lower(c),
            "isLower {at}"
        );
        assert_eq!(
            bool_of(reduce_char_is_alpha(&[&e])),
            lean::is_alpha(c),
            "isAlpha {at}"
        );
        assert_eq!(
            char_of(reduce_char_to_lower(&[&e])),
            lean::to_lower(c),
            "toLower {at}"
        );
        assert_eq!(
            char_of(reduce_char_to_upper(&[&e])),
            lean::to_upper(c),
            "toUpper {at}"
        );
    }

    // The near-misses, spelled out so a regression names itself.
    let e_acute = mk_char_expr('\u{e9}');
    assert_eq!(char_of(reduce_char_to_upper(&[&e_acute])), '\u{e9}');
    assert_ne!(
        char_of(reduce_char_to_upper(&[&e_acute])),
        '\u{c9}',
        "'é'.toUpper = 'É' is FALSE in Lean"
    );
    assert!(
        !bool_of(reduce_char_is_alpha(&[&e_acute])),
        "'é'.isAlpha = true is FALSE in Lean"
    );
    assert!(
        !bool_of(reduce_char_is_lower(&[&e_acute])),
        "'é'.isLower = true is FALSE in Lean"
    );
    let form_feed = mk_char_expr('\u{c}');
    assert!(
        !bool_of(reduce_char_is_whitespace(&[&form_feed])),
        "U+000C is whitespace to Rust (even `is_ascii_whitespace`), not to Lean"
    );
    // Positive twins: the ASCII cases still work.
    assert_eq!(char_of(reduce_char_to_upper(&[&mk_char_expr('a')])), 'A');
    assert_eq!(char_of(reduce_char_to_upper(&[&mk_char_expr('z')])), 'Z');
    assert_eq!(char_of(reduce_char_to_lower(&[&mk_char_expr('Z')])), 'z');
    // The edges of the ranges: '`' (0x60) and '{' (0x7B) flank 'a'..'z'.
    assert_eq!(char_of(reduce_char_to_upper(&[&mk_char_expr('`')])), '`');
    assert_eq!(char_of(reduce_char_to_upper(&[&mk_char_expr('{')])), '{');
    assert_eq!(char_of(reduce_char_to_lower(&[&mk_char_expr('@')])), '@');
    assert_eq!(char_of(reduce_char_to_lower(&[&mk_char_expr('[')])), '[');
}
