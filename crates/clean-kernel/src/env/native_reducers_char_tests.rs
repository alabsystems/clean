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

#[test]
fn test_char_code_point_olean_two_field_shape() {
    // olean: Char.mk (UInt32.ofBitVec (BitVec.ofFin (Fin.mk <n> _))) valid
    // char_code_point must dig the literal <n> out of the genuine ctor chain.
    let n = Expr::nat_lit(90);
    let fin = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Fin.mk"), vec![]), n.clone()),
        Expr::const_(Name::from_string("trivial"), vec![]),
    );
    let bv = Expr::app(Expr::const_(Name::from_string("BitVec.ofFin"), vec![]), fin);
    let u32v = Expr::app(
        Expr::const_(Name::from_string("UInt32.ofBitVec"), vec![]),
        bv,
    );
    let valid = Expr::const_(Name::from_string("trivial"), vec![]);
    let ch = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Char.mk"), vec![]), u32v),
        valid,
    );
    assert_eq!(super::char_code_point(&ch), Some(90));
    assert_eq!(super::get_char_val(&ch), Some('Z'));
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
        super::char_code_point(&ch),
        Some(90),
        "must read the value (90), not the width (32)"
    );
}

#[test]
fn test_char_code_point_pure_clean_one_field_shape() {
    // pure-clean: Char.mk <nat>
    assert_eq!(super::char_code_point(&mk_char_expr('Z')), Some(90));
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
