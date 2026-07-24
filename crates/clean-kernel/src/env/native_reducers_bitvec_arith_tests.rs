// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the BitVec arithmetic / logic / shift / comparison native
//! reducers. Every expected value is `#eval`-verified against Lean v4.30.0-rc2
//! (toolchain `leanprover--lean4---v4.30.0-rc2`); a reducer that computes a
//! WRONG value would be a soundness bug (it would make the kernel accept a
//! false BitVec equation), so the boundary / wraparound / div-0 / over-width /
//! signed cases below are the guardrail.

use super::*;
use crate::expr::{ExprKind, Literal};
use crate::name::Name;

/// Binary op: build `[width, a, b]` (raw Nat literals — the documented payload
/// contract that `reduce_native` pre-WHNFs real operands into) and assert the
/// Nat-literal result.
fn nat_op_bin(reducer: fn(&[&Expr]) -> Option<Expr>, width: u64, a: u64, b: u64) -> u64 {
    let w = Expr::nat_lit(width);
    let av = Expr::nat_lit(a);
    let bv = Expr::nat_lit(b);
    let result = reducer(&[&w, &av, &bv]).expect("reducer should produce a result");
    match result.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64().expect("fits u64"),
        other => panic!("expected Nat literal, got {other:?}"),
    }
}

/// Unary op: build `[width, a]` and assert the Nat-literal result.
fn un(reducer: fn(&[&Expr]) -> Option<Expr>, width: u64, a: u64) -> u64 {
    let w = Expr::nat_lit(width);
    let av = Expr::nat_lit(a);
    let result = reducer(&[&w, &av]).expect("reducer should produce a result");
    match result.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64().expect("fits u64"),
        other => panic!("expected Nat literal, got {other:?}"),
    }
}

/// Comparison op: build `[width, a, b]` and assert the Bool constructor head.
fn bool_op(reducer: fn(&[&Expr]) -> Option<Expr>, width: u64, a: u64, b: u64) -> bool {
    let w = Expr::nat_lit(width);
    let av = Expr::nat_lit(a);
    let bv = Expr::nat_lit(b);
    let result = reducer(&[&w, &av, &bv]).expect("comparison reducer should produce a Bool");
    match result.get_app_fn().kind() {
        ExprKind::Const(name, _) if name.to_string() == "Bool.true" => true,
        ExprKind::Const(name, _) if name.to_string() == "Bool.false" => false,
        other => panic!("expected Bool constructor, got {other:?}"),
    }
}

// --- add / sub / mul / neg (wraparound) — #eval-verified ---

#[test]
fn test_bitvec_add_wraparound() {
    assert_eq!(nat_op_bin(reduce_bitvec_add, 8, 200, 100), 44); // (300)%256
    assert_eq!(nat_op_bin(reduce_bitvec_add, 8, 0, 0), 0);
    assert_eq!(nat_op_bin(reduce_bitvec_add, 32, 4294967295, 1), 0);
    assert_eq!(nat_op_bin(reduce_bitvec_add, 64, u64::MAX, 1), 0);
    assert_eq!(nat_op_bin(reduce_bitvec_add, 64, 5, 7), 12);
}

#[test]
fn test_bitvec_sub_wraparound() {
    assert_eq!(nat_op_bin(reduce_bitvec_sub, 8, 5, 10), 251);
    assert_eq!(nat_op_bin(reduce_bitvec_sub, 8, 0, 1), 255);
    assert_eq!(nat_op_bin(reduce_bitvec_sub, 8, 10, 5), 5);
    assert_eq!(nat_op_bin(reduce_bitvec_sub, 64, 0, 1), u64::MAX);
    assert_eq!(nat_op_bin(reduce_bitvec_sub, 32, 0, 1), 4294967295);
}

#[test]
fn test_bitvec_mul_wraparound() {
    assert_eq!(nat_op_bin(reduce_bitvec_mul, 8, 16, 16), 0); // 256%256
    assert_eq!(nat_op_bin(reduce_bitvec_mul, 8, 255, 255), 1); // 65025%256
    assert_eq!(nat_op_bin(reduce_bitvec_mul, 32, 65536, 65536), 0);
    assert_eq!(nat_op_bin(reduce_bitvec_mul, 64, u64::MAX, u64::MAX), 1);
}

#[test]
fn test_bitvec_neg() {
    assert_eq!(un(reduce_bitvec_neg, 8, 0), 0);
    assert_eq!(un(reduce_bitvec_neg, 8, 1), 255);
    assert_eq!(un(reduce_bitvec_neg, 8, 5), 251);
    assert_eq!(un(reduce_bitvec_neg, 8, 128), 128);
    assert_eq!(un(reduce_bitvec_neg, 64, 1), u64::MAX);
}

// --- and / or / xor / not — #eval-verified ---

#[test]
fn test_bitvec_bitwise() {
    assert_eq!(nat_op_bin(reduce_bitvec_and, 8, 0xF0, 0x0F), 0);
    assert_eq!(nat_op_bin(reduce_bitvec_or, 8, 0xF0, 0x0F), 255);
    assert_eq!(nat_op_bin(reduce_bitvec_xor, 8, 0xFF, 0x0F), 240);
    assert_eq!(un(reduce_bitvec_not, 8, 0x0F), 240);
    assert_eq!(un(reduce_bitvec_not, 8, 0), 255);
    assert_eq!(un(reduce_bitvec_not, 64, 0), u64::MAX);
    assert_eq!(un(reduce_bitvec_not, 32, 0), 4294967295);
    // not must stay within width (no stray high bits leaking through).
    assert_eq!(un(reduce_bitvec_not, 16, 0), 65535);
}

// --- shiftLeft / ushiftRight (RAW shift amount, over-width clears) ---

#[test]
fn test_bitvec_shift_left() {
    assert_eq!(nat_op_bin(reduce_bitvec_shift_left, 8, 1, 3), 8);
    assert_eq!(nat_op_bin(reduce_bitvec_shift_left, 8, 3, 7), 128); // (3<<7)%256
                                                                    // Over-width shifts are NOT taken mod-width at the BitVec layer: they clear.
    assert_eq!(nat_op_bin(reduce_bitvec_shift_left, 8, 1, 8), 0);
    assert_eq!(nat_op_bin(reduce_bitvec_shift_left, 8, 1, 254), 0);
    assert_eq!(nat_op_bin(reduce_bitvec_shift_left, 32, 1, 31), 2147483648);
    assert_eq!(nat_op_bin(reduce_bitvec_shift_left, 64, 1, 63), 1u64 << 63);
    assert_eq!(nat_op_bin(reduce_bitvec_shift_left, 64, 1, 64), 0);
    assert_eq!(nat_op_bin(reduce_bitvec_shift_left, 64, 1, 1_000_000), 0);
}

#[test]
fn test_bitvec_ushift_right() {
    assert_eq!(nat_op_bin(reduce_bitvec_ushift_right, 8, 255, 4), 15);
    assert_eq!(nat_op_bin(reduce_bitvec_ushift_right, 8, 255, 8), 0);
    assert_eq!(nat_op_bin(reduce_bitvec_ushift_right, 8, 255, 100), 0);
    assert_eq!(nat_op_bin(reduce_bitvec_ushift_right, 64, u64::MAX, 63), 1);
    assert_eq!(nat_op_bin(reduce_bitvec_ushift_right, 64, u64::MAX, 64), 0);
    assert_eq!(
        nat_op_bin(reduce_bitvec_ushift_right, 64, u64::MAX, 1_000_000),
        0
    );
}

// --- udiv / umod (division / mod by zero follow Lean) ---

#[test]
fn test_bitvec_udiv() {
    assert_eq!(nat_op_bin(reduce_bitvec_udiv, 8, 17, 5), 3);
    assert_eq!(nat_op_bin(reduce_bitvec_udiv, 8, 7, 0), 0); // x / 0 = 0
    assert_eq!(nat_op_bin(reduce_bitvec_udiv, 8, 0, 0), 0);
    assert_eq!(
        nat_op_bin(reduce_bitvec_udiv, 64, u64::MAX, 2),
        u64::MAX / 2
    );
}

#[test]
fn test_bitvec_umod() {
    assert_eq!(nat_op_bin(reduce_bitvec_umod, 8, 17, 5), 2);
    assert_eq!(nat_op_bin(reduce_bitvec_umod, 8, 7, 0), 7); // x % 0 = x
    assert_eq!(nat_op_bin(reduce_bitvec_umod, 8, 0, 0), 0);
    assert_eq!(
        nat_op_bin(reduce_bitvec_umod, 64, u64::MAX, 3),
        u64::MAX % 3
    );
}

// --- unsigned / signed comparisons — #eval-verified ---

#[test]
fn test_bitvec_unsigned_cmp() {
    assert!(bool_op(reduce_bitvec_ult, 8, 3, 5));
    assert!(!bool_op(reduce_bitvec_ult, 8, 5, 5));
    assert!(bool_op(reduce_bitvec_ule, 8, 5, 5));
    assert!(!bool_op(reduce_bitvec_ule, 8, 6, 5));
    // Unsigned: 255 > 0 (no sign interpretation).
    assert!(!bool_op(reduce_bitvec_ult, 8, 255, 0));
}

#[test]
fn test_bitvec_signed_cmp() {
    // Two's complement @8: 255 = -1, 128 = -128, 127 = 127.
    assert!(bool_op(reduce_bitvec_slt, 8, 255, 0)); // -1 < 0
    assert!(bool_op(reduce_bitvec_sle, 8, 128, 127)); // -128 <= 127
    assert!(!bool_op(reduce_bitvec_slt, 8, 127, 128)); // 127 < -128 is false
    assert!(!bool_op(reduce_bitvec_slt, 8, 0, 255)); // 0 < -1 is false
                                                     // @64: 2^63 = most negative, so it is < 0.
    assert!(bool_op(reduce_bitvec_slt, 64, 1u64 << 63, 0));
}

// --- operand peeling: ofNat / ofNatLT / ofFin(Fin.mk) forms ---

fn c(s: &str) -> Expr {
    Expr::const_(Name::from_string(s), vec![])
}

#[test]
fn test_bitvec_add_peels_of_nat_operands() {
    // BitVec.add 8 (BitVec.ofNat 8 200) (BitVec.ofNat 8 100) = 44.
    let w = Expr::nat_lit(8);
    let x = Expr::apps(c("BitVec.ofNat"), [Expr::nat_lit(8), Expr::nat_lit(200)]);
    let y = Expr::apps(c("BitVec.ofNat"), [Expr::nat_lit(8), Expr::nat_lit(100)]);
    let result = reduce_bitvec_add(&[&w, &x, &y]).expect("should peel ofNat operands");
    match result.kind() {
        ExprKind::Lit(Literal::Nat(n)) => assert_eq!(n.to_u64(), Some(44)),
        other => panic!("got {other:?}"),
    }
}

#[test]
fn test_bitvec_and_peels_of_nat_lt_operands() {
    // BitVec.and 8 (BitVec.ofNatLT 8 0xF0 _) (BitVec.ofNatLT 8 0x0F _) = 0.
    let w = Expr::nat_lit(8);
    let proof = c("proof");
    let x = Expr::apps(
        c("BitVec.ofNatLT"),
        [Expr::nat_lit(8), Expr::nat_lit(0xF0), proof.clone()],
    );
    let y = Expr::apps(
        c("BitVec.ofNatLT"),
        [Expr::nat_lit(8), Expr::nat_lit(0x0F), proof],
    );
    let result = reduce_bitvec_and(&[&w, &x, &y]).expect("should peel ofNatLT operands");
    match result.kind() {
        ExprKind::Lit(Literal::Nat(n)) => assert_eq!(n.to_u64(), Some(0)),
        other => panic!("got {other:?}"),
    }
}

#[test]
fn test_bitvec_or_peels_of_fin_operands() {
    // BitVec.or 8 (ofFin 8 (Fin.mk 256 0xF0 _)) (ofFin 8 (Fin.mk 256 0x0F _)) = 255.
    let w = Expr::nat_lit(8);
    let proof = c("proof");
    let fin_x = Expr::apps(
        c("Fin.mk"),
        [Expr::nat_lit(256), Expr::nat_lit(0xF0), proof.clone()],
    );
    let fin_y = Expr::apps(
        c("Fin.mk"),
        [Expr::nat_lit(256), Expr::nat_lit(0x0F), proof],
    );
    let x = Expr::apps(c("BitVec.ofFin"), [Expr::nat_lit(8), fin_x]);
    let y = Expr::apps(c("BitVec.ofFin"), [Expr::nat_lit(8), fin_y]);
    let result = reduce_bitvec_or(&[&w, &x, &y]).expect("should peel ofFin operands");
    match result.kind() {
        ExprKind::Lit(Literal::Nat(n)) => assert_eq!(n.to_u64(), Some(255)),
        other => panic!("got {other:?}"),
    }
}

// --- decline conditions (must fall back to δι, never compute wrongly) ---

#[test]
fn test_bitvec_declines_width_over_64() {
    // Width 65 cannot fit a u64 payload — decline.
    let w = Expr::nat_lit(65);
    let a = Expr::nat_lit(1);
    let b = Expr::nat_lit(2);
    assert!(reduce_bitvec_add(&[&w, &a, &b]).is_none());
    assert!(reduce_bitvec_ult(&[&w, &a, &b]).is_none());
}

#[test]
fn test_bitvec_declines_non_literal_operand() {
    let w = Expr::nat_lit(8);
    let var = Expr::bvar(0);
    let a = Expr::nat_lit(1);
    assert!(reduce_bitvec_add(&[&w, &var, &a]).is_none());
    assert!(reduce_bitvec_add(&[&w, &a, &var]).is_none());
    // Non-literal width also declines.
    assert!(reduce_bitvec_add(&[&var, &a, &a]).is_none());
}

#[test]
fn test_bitvec_declines_missing_args() {
    let w = Expr::nat_lit(8);
    let a = Expr::nat_lit(1);
    assert!(reduce_bitvec_add(&[&w, &a]).is_none()); // missing second operand
    assert!(reduce_bitvec_add(&[]).is_none());
    assert!(reduce_bitvec_not(&[&w]).is_none()); // missing operand
}

// --- width-0 BitVec (single element) ---

#[test]
fn test_bitvec_width_zero() {
    assert_eq!(nat_op_bin(reduce_bitvec_add, 0, 0, 0), 0);
    assert_eq!(un(reduce_bitvec_not, 0, 0), 0);
    assert_eq!(nat_op_bin(reduce_bitvec_shift_left, 0, 0, 5), 0);
    assert!(!bool_op(reduce_bitvec_ult, 0, 0, 0));
}
