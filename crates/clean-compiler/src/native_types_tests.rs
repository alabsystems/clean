// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for native type IR compilation.
//!
//! Part of #3084 - Native type compilation for UInt and Float.

use super::*;
use clean_kernel::expr::Expr;
use clean_kernel::Name;

// ---------------------------------------------------------------------------
// NativeType tests
// ---------------------------------------------------------------------------

#[test]
fn test_native_type_modulus_uint8() {
    assert_eq!(NativeType::UInt8.modulus(), Some(256));
}

#[test]
fn test_native_type_modulus_uint16() {
    assert_eq!(NativeType::UInt16.modulus(), Some(65536));
}

#[test]
fn test_native_type_modulus_uint32() {
    assert_eq!(NativeType::UInt32.modulus(), Some(1u64 << 32));
}

#[test]
fn test_native_type_modulus_uint64_is_none() {
    // UInt64 wraps via Rust wrapping ops, no explicit modulus
    assert_eq!(NativeType::UInt64.modulus(), None);
}

#[test]
fn test_native_type_modulus_float_is_none() {
    assert_eq!(NativeType::Float.modulus(), None);
}

#[test]
fn test_native_type_bit_width() {
    assert_eq!(NativeType::UInt8.bit_width(), Some(8));
    assert_eq!(NativeType::UInt16.bit_width(), Some(16));
    assert_eq!(NativeType::UInt32.bit_width(), Some(32));
    assert_eq!(NativeType::UInt64.bit_width(), Some(64));
    assert_eq!(NativeType::USize.bit_width(), Some(64));
    assert_eq!(NativeType::Float.bit_width(), Some(64));
    assert_eq!(NativeType::Bool.bit_width(), None);
}

// ---------------------------------------------------------------------------
// classify_native_op tests
// ---------------------------------------------------------------------------

#[test]
fn test_classify_uint32_add() {
    let name = Name::from_string("UInt32.add");
    let result = classify_native_op(&name);
    assert_eq!(result, Some((NativeType::UInt32, NativeOp::Add)));
}

#[test]
fn test_classify_uint64_mul() {
    let name = Name::from_string("UInt64.mul");
    let result = classify_native_op(&name);
    assert_eq!(result, Some((NativeType::UInt64, NativeOp::Mul)));
}

#[test]
fn test_classify_uint8_complement() {
    let name = Name::from_string("UInt8.complement");
    let result = classify_native_op(&name);
    assert_eq!(result, Some((NativeType::UInt8, NativeOp::Complement)));
}

#[test]
fn test_classify_usize_beq() {
    let name = Name::from_string("USize.beq");
    let result = classify_native_op(&name);
    assert_eq!(result, Some((NativeType::USize, NativeOp::Eq)));
}

#[test]
fn test_classify_float_add() {
    let name = Name::from_string("Float.add");
    let result = classify_native_op(&name);
    assert_eq!(result, Some((NativeType::Float, NativeOp::Add)));
}

#[test]
fn test_classify_unknown_name_returns_none() {
    let name = Name::from_string("Nat.add");
    assert_eq!(classify_native_op(&name), None);
}

#[test]
fn test_classify_unknown_suffix_returns_none() {
    let name = Name::from_string("UInt32.decEq");
    assert_eq!(classify_native_op(&name), None);
}

// ---------------------------------------------------------------------------
// compile_to_native tests
// ---------------------------------------------------------------------------

/// Helper: build `UInt32.add a b` as a kernel Expr.
fn mk_uint32_add(a: u64, b: u64) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("UInt32.add"), vec![]),
            Expr::nat_lit(a),
        ),
        Expr::nat_lit(b),
    )
}

#[test]
fn test_compile_nat_literal() {
    let expr = Expr::nat_lit(42);
    let native = compile_to_native(&expr);
    assert_eq!(native, Some(NativeExpr::Lit(NativeType::UInt64, 42)));
}

#[test]
fn test_compile_uint32_add() {
    let expr = mk_uint32_add(10, 20);
    let native = compile_to_native(&expr).expect("should compile UInt32.add");
    match native {
        NativeExpr::BinOp(NativeOp::Add, lhs, rhs) => {
            assert_eq!(*lhs, NativeExpr::Lit(NativeType::UInt64, 10));
            assert_eq!(*rhs, NativeExpr::Lit(NativeType::UInt64, 20));
        }
        other => panic!("expected BinOp(Add, ..), got {:?}", other),
    }
}

#[test]
fn test_compile_uint8_complement() {
    let expr = Expr::app(
        Expr::const_(Name::from_string("UInt8.complement"), vec![]),
        Expr::nat_lit(0xFF),
    );
    let native = compile_to_native(&expr).expect("should compile UInt8.complement");
    match native {
        NativeExpr::UnaryOp(NativeOp::Complement, operand) => {
            assert_eq!(*operand, NativeExpr::Lit(NativeType::UInt64, 0xFF));
        }
        other => panic!("expected UnaryOp(Complement, ..), got {:?}", other),
    }
}

#[test]
fn test_compile_uint64_sub() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("UInt64.sub"), vec![]),
            Expr::nat_lit(100),
        ),
        Expr::nat_lit(30),
    );
    let native = compile_to_native(&expr).expect("should compile UInt64.sub");
    assert!(matches!(native, NativeExpr::BinOp(NativeOp::Sub, _, _)));
}

#[test]
fn test_compile_usize_blt() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("USize.blt"), vec![]),
            Expr::nat_lit(5),
        ),
        Expr::nat_lit(10),
    );
    let native = compile_to_native(&expr).expect("should compile USize.blt");
    assert!(matches!(native, NativeExpr::BinOp(NativeOp::Lt, _, _)));
}

#[test]
fn test_compile_nested_ops() {
    // UInt32.add (UInt32.mul 2 3) 4
    let inner = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("UInt32.mul"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(3),
    );
    let outer = Expr::app(
        Expr::app(Expr::const_(Name::from_string("UInt32.add"), vec![]), inner),
        Expr::nat_lit(4),
    );
    let native = compile_to_native(&outer).expect("should compile nested ops");
    match native {
        NativeExpr::BinOp(NativeOp::Add, lhs, rhs) => {
            assert!(matches!(*lhs, NativeExpr::BinOp(NativeOp::Mul, _, _)));
            assert_eq!(*rhs, NativeExpr::Lit(NativeType::UInt64, 4));
        }
        other => panic!("expected BinOp(Add, ..), got {:?}", other),
    }
}

#[test]
fn test_compile_non_native_returns_none() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::nat_lit(1),
        ),
        Expr::nat_lit(2),
    );
    assert!(
        compile_to_native(&expr).is_none(),
        "Nat.add is not a native type op"
    );
}

#[test]
fn test_compile_lambda_head_returns_none() {
    let expr = Expr::app(
        Expr::lam(
            clean_kernel::expr::BinderInfo::Default,
            Expr::type_(),
            Expr::bvar(0),
        ),
        Expr::nat_lit(1),
    );
    assert!(
        compile_to_native(&expr).is_none(),
        "Lambda head should not compile to native"
    );
}

#[test]
fn test_compile_insufficient_args_returns_none() {
    // UInt32.add with only 1 argument
    let expr = Expr::app(
        Expr::const_(Name::from_string("UInt32.add"), vec![]),
        Expr::nat_lit(1),
    );
    assert!(
        compile_to_native(&expr).is_none(),
        "Binary op with 1 arg should return None"
    );
}

#[test]
fn test_compile_complement_no_args_returns_none() {
    let expr = Expr::const_(Name::from_string("UInt8.complement"), vec![]);
    assert!(
        compile_to_native(&expr).is_none(),
        "Unary op with 0 args should return None"
    );
}

#[test]
fn test_compile_float_div() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Float.div"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(3),
    );
    let native = compile_to_native(&expr).expect("should compile Float.div");
    assert!(matches!(native, NativeExpr::BinOp(NativeOp::Div, _, _)));
}

#[test]
fn test_compile_uint16_shift_left() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("UInt16.shiftLeft"), vec![]),
            Expr::nat_lit(1),
        ),
        Expr::nat_lit(4),
    );
    let native = compile_to_native(&expr).expect("should compile UInt16.shiftLeft");
    assert!(matches!(
        native,
        NativeExpr::BinOp(NativeOp::ShiftLeft, _, _)
    ));
}

#[test]
fn test_compile_uint32_xor() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("UInt32.xor"), vec![]),
            Expr::nat_lit(0xAA),
        ),
        Expr::nat_lit(0x55),
    );
    let native = compile_to_native(&expr).expect("should compile UInt32.xor");
    assert!(matches!(native, NativeExpr::BinOp(NativeOp::Xor, _, _)));
}

#[test]
fn test_compile_uint64_to_nat() {
    let expr = Expr::app(
        Expr::const_(Name::from_string("UInt64.toNat"), vec![]),
        Expr::nat_lit(42),
    );
    let native = compile_to_native(&expr).expect("should compile UInt64.toNat");
    assert!(matches!(native, NativeExpr::UnaryOp(NativeOp::ToNat, _)));
}
