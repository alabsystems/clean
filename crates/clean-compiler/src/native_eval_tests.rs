// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// 3.14 here is an arbitrary test value, not an approximation of PI.
#![allow(clippy::approx_constant)]

//! Tests for native expression evaluator.
//!
//! Part of #3084 - Native type compilation for UInt and Float.

use super::*;
use crate::native_types::{NativeExpr, NativeOp, NativeType};

// ---------------------------------------------------------------------------
// Literal evaluation
// ---------------------------------------------------------------------------

#[test]
fn test_eval_uint8_literal() {
    let expr = NativeExpr::Lit(NativeType::UInt8, 42);
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt8(42));
}

#[test]
fn test_eval_uint16_literal() {
    let expr = NativeExpr::Lit(NativeType::UInt16, 1000);
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt16(1000));
}

#[test]
fn test_eval_uint32_literal() {
    let expr = NativeExpr::Lit(NativeType::UInt32, 0xDEAD_BEEF);
    assert_eq!(
        eval_native(&expr).unwrap(),
        NativeValue::UInt32(0xDEAD_BEEF)
    );
}

#[test]
fn test_eval_uint64_literal() {
    let expr = NativeExpr::Lit(NativeType::UInt64, u64::MAX);
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt64(u64::MAX));
}

#[test]
fn test_eval_float_literal() {
    let bits = 3.14f64.to_bits();
    let expr = NativeExpr::Lit(NativeType::Float, bits);
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Float(3.14));
}

#[test]
fn test_eval_bool_literal_true() {
    let expr = NativeExpr::Lit(NativeType::Bool, 1);
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Bool(true));
}

#[test]
fn test_eval_bool_literal_false() {
    let expr = NativeExpr::Lit(NativeType::Bool, 0);
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Bool(false));
}

// ---------------------------------------------------------------------------
// Arithmetic: basic operations
// ---------------------------------------------------------------------------

fn uint32(val: u64) -> NativeExpr {
    NativeExpr::Lit(NativeType::UInt32, val)
}

fn uint64(val: u64) -> NativeExpr {
    NativeExpr::Lit(NativeType::UInt64, val)
}

fn uint8(val: u64) -> NativeExpr {
    NativeExpr::Lit(NativeType::UInt8, val)
}

fn uint16(val: u64) -> NativeExpr {
    NativeExpr::Lit(NativeType::UInt16, val)
}

fn float_expr(val: f64) -> NativeExpr {
    NativeExpr::Lit(NativeType::Float, val.to_bits())
}

#[test]
fn test_eval_uint32_add() {
    let expr = NativeExpr::BinOp(NativeOp::Add, Box::new(uint32(10)), Box::new(uint32(20)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(30));
}

#[test]
fn test_eval_uint32_sub() {
    let expr = NativeExpr::BinOp(NativeOp::Sub, Box::new(uint32(50)), Box::new(uint32(30)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(20));
}

#[test]
fn test_eval_uint32_mul() {
    let expr = NativeExpr::BinOp(NativeOp::Mul, Box::new(uint32(7)), Box::new(uint32(6)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(42));
}

#[test]
fn test_eval_uint32_div() {
    let expr = NativeExpr::BinOp(NativeOp::Div, Box::new(uint32(100)), Box::new(uint32(7)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(14));
}

#[test]
fn test_eval_uint32_mod() {
    let expr = NativeExpr::BinOp(NativeOp::Mod, Box::new(uint32(100)), Box::new(uint32(7)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(2));
}

// ---------------------------------------------------------------------------
// Overflow wrapping per UInt size
// ---------------------------------------------------------------------------

#[test]
fn test_eval_uint8_overflow_wrapping_add() {
    // 200 + 100 = 300, wraps to 300 % 256 = 44
    let expr = NativeExpr::BinOp(NativeOp::Add, Box::new(uint8(200)), Box::new(uint8(100)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt8(44));
}

#[test]
fn test_eval_uint8_overflow_wrapping_mul() {
    // 20 * 20 = 400, wraps to 400 % 256 = 144
    let expr = NativeExpr::BinOp(NativeOp::Mul, Box::new(uint8(20)), Box::new(uint8(20)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt8(144));
}

#[test]
fn test_eval_uint8_underflow_wrapping_sub() {
    // 0 - 1 wraps: u64 wrapping_sub gives u64::MAX, % 256 = 255
    let expr = NativeExpr::BinOp(NativeOp::Sub, Box::new(uint8(0)), Box::new(uint8(1)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt8(255));
}

#[test]
fn test_eval_uint16_overflow_wrapping() {
    // 60000 + 10000 = 70000, wraps to 70000 % 65536 = 4464
    let expr = NativeExpr::BinOp(
        NativeOp::Add,
        Box::new(uint16(60000)),
        Box::new(uint16(10000)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt16(4464));
}

#[test]
fn test_eval_uint32_overflow_wrapping() {
    // (2^32 - 1) + 1 wraps to 0 (mod 2^32)
    let expr = NativeExpr::BinOp(
        NativeOp::Add,
        Box::new(uint32(0xFFFF_FFFF)),
        Box::new(uint32(1)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(0));
}

#[test]
fn test_eval_uint64_overflow_wrapping() {
    // u64::MAX + 1 wraps to 0
    let expr = NativeExpr::BinOp(
        NativeOp::Add,
        Box::new(uint64(u64::MAX)),
        Box::new(uint64(1)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt64(0));
}

// ---------------------------------------------------------------------------
// Division by zero
// ---------------------------------------------------------------------------

#[test]
fn test_eval_uint_div_by_zero_returns_zero() {
    let expr = NativeExpr::BinOp(NativeOp::Div, Box::new(uint32(42)), Box::new(uint32(0)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(0));
}

#[test]
fn test_eval_uint_mod_by_zero_returns_dividend() {
    // Lean 4: n % 0 = n
    let expr = NativeExpr::BinOp(NativeOp::Mod, Box::new(uint32(42)), Box::new(uint32(0)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(42));
}

#[test]
fn test_eval_float_div_by_zero_returns_inf() {
    let expr = NativeExpr::BinOp(
        NativeOp::Div,
        Box::new(float_expr(1.0)),
        Box::new(float_expr(0.0)),
    );
    match eval_native(&expr).unwrap() {
        NativeValue::Float(v) => assert!(v.is_infinite(), "1.0/0.0 should be Inf"),
        other => panic!("expected Float, got {:?}", other),
    }
}

#[test]
fn test_eval_float_zero_div_zero_returns_nan() {
    let expr = NativeExpr::BinOp(
        NativeOp::Div,
        Box::new(float_expr(0.0)),
        Box::new(float_expr(0.0)),
    );
    match eval_native(&expr).unwrap() {
        NativeValue::Float(v) => assert!(v.is_nan(), "0.0/0.0 should be NaN"),
        other => panic!("expected Float, got {:?}", other),
    }
}

// ---------------------------------------------------------------------------
// Float arithmetic
// ---------------------------------------------------------------------------

#[test]
fn test_eval_float_add() {
    let expr = NativeExpr::BinOp(
        NativeOp::Add,
        Box::new(float_expr(1.5)),
        Box::new(float_expr(2.5)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Float(4.0));
}

#[test]
fn test_eval_float_sub() {
    let expr = NativeExpr::BinOp(
        NativeOp::Sub,
        Box::new(float_expr(10.0)),
        Box::new(float_expr(3.5)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Float(6.5));
}

#[test]
fn test_eval_float_mul() {
    let expr = NativeExpr::BinOp(
        NativeOp::Mul,
        Box::new(float_expr(3.0)),
        Box::new(float_expr(4.0)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Float(12.0));
}

#[test]
fn test_eval_float_div() {
    let expr = NativeExpr::BinOp(
        NativeOp::Div,
        Box::new(float_expr(10.0)),
        Box::new(float_expr(4.0)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Float(2.5));
}

// ---------------------------------------------------------------------------
// Comparison operations
// ---------------------------------------------------------------------------

#[test]
fn test_eval_uint32_eq_true() {
    let expr = NativeExpr::BinOp(NativeOp::Eq, Box::new(uint32(42)), Box::new(uint32(42)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Bool(true));
}

#[test]
fn test_eval_uint32_eq_false() {
    let expr = NativeExpr::BinOp(NativeOp::Eq, Box::new(uint32(42)), Box::new(uint32(43)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Bool(false));
}

#[test]
fn test_eval_uint32_lt() {
    let expr = NativeExpr::BinOp(NativeOp::Lt, Box::new(uint32(5)), Box::new(uint32(10)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Bool(true));
}

#[test]
fn test_eval_uint32_le_equal() {
    let expr = NativeExpr::BinOp(NativeOp::Le, Box::new(uint32(10)), Box::new(uint32(10)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Bool(true));
}

#[test]
fn test_eval_uint32_gt() {
    let expr = NativeExpr::BinOp(NativeOp::Gt, Box::new(uint32(10)), Box::new(uint32(5)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Bool(true));
}

#[test]
fn test_eval_uint32_ge() {
    let expr = NativeExpr::BinOp(NativeOp::Ge, Box::new(uint32(10)), Box::new(uint32(10)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Bool(true));
}

#[test]
fn test_eval_uint32_ne() {
    let expr = NativeExpr::BinOp(NativeOp::Ne, Box::new(uint32(1)), Box::new(uint32(2)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Bool(true));
}

#[test]
fn test_eval_float_lt() {
    let expr = NativeExpr::BinOp(
        NativeOp::Lt,
        Box::new(float_expr(1.0)),
        Box::new(float_expr(2.0)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Bool(true));
}

#[test]
fn test_eval_float_eq() {
    let expr = NativeExpr::BinOp(
        NativeOp::Eq,
        Box::new(float_expr(3.14)),
        Box::new(float_expr(3.14)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Bool(true));
}

// ---------------------------------------------------------------------------
// Bitwise operations
// ---------------------------------------------------------------------------

#[test]
fn test_eval_uint32_and() {
    let expr = NativeExpr::BinOp(
        NativeOp::And,
        Box::new(uint32(0xFF00)),
        Box::new(uint32(0x0F0F)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(0x0F00));
}

#[test]
fn test_eval_uint32_or() {
    let expr = NativeExpr::BinOp(
        NativeOp::Or,
        Box::new(uint32(0xFF00)),
        Box::new(uint32(0x00FF)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(0xFFFF));
}

#[test]
fn test_eval_uint32_xor() {
    let expr = NativeExpr::BinOp(
        NativeOp::Xor,
        Box::new(uint32(0xFF)),
        Box::new(uint32(0x0F)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(0xF0));
}

#[test]
fn test_eval_uint32_shift_left() {
    let expr = NativeExpr::BinOp(
        NativeOp::ShiftLeft,
        Box::new(uint32(1)),
        Box::new(uint32(8)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(256));
}

#[test]
fn test_eval_uint32_shift_right() {
    let expr = NativeExpr::BinOp(
        NativeOp::ShiftRight,
        Box::new(uint32(256)),
        Box::new(uint32(4)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(16));
}

#[test]
fn test_eval_uint32_shift_left_overflow() {
    // Shift by >= bit_width yields 0
    let expr = NativeExpr::BinOp(
        NativeOp::ShiftLeft,
        Box::new(uint32(1)),
        Box::new(uint32(32)),
    );
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt32(0));
}

#[test]
fn test_eval_uint8_complement() {
    let expr = NativeExpr::UnaryOp(NativeOp::Complement, Box::new(uint8(0)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt8(255));
}

#[test]
fn test_eval_uint8_complement_ff() {
    let expr = NativeExpr::UnaryOp(NativeOp::Complement, Box::new(uint8(0xFF)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt8(0));
}

#[test]
fn test_eval_uint32_complement() {
    let expr = NativeExpr::UnaryOp(NativeOp::Complement, Box::new(uint32(0)));
    assert_eq!(
        eval_native(&expr).unwrap(),
        NativeValue::UInt32(0xFFFF_FFFF)
    );
}

// ---------------------------------------------------------------------------
// Conversion operations
// ---------------------------------------------------------------------------

#[test]
fn test_eval_to_nat() {
    let expr = NativeExpr::UnaryOp(NativeOp::ToNat, Box::new(uint32(42)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt64(42));
}

#[test]
fn test_eval_to_float() {
    let expr = NativeExpr::UnaryOp(NativeOp::ToFloat, Box::new(uint64(100)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::Float(100.0));
}

#[test]
fn test_eval_from_float() {
    let expr = NativeExpr::UnaryOp(NativeOp::FromFloat, Box::new(float_expr(42.7)));
    assert_eq!(eval_native(&expr).unwrap(), NativeValue::UInt64(42));
}

// ---------------------------------------------------------------------------
// Error cases
// ---------------------------------------------------------------------------

#[test]
fn test_eval_unresolved_variable() {
    let expr = NativeExpr::Var("x".to_string());
    let err = eval_native(&expr).unwrap_err();
    assert!(
        matches!(err, NativeEvalError::UnresolvedVariable(ref name) if name == "x"),
        "expected UnresolvedVariable, got {:?}",
        err,
    );
}

#[test]
fn test_eval_unresolved_call() {
    let expr = NativeExpr::Call("foo".to_string(), vec![uint32(1)]);
    let err = eval_native(&expr).unwrap_err();
    assert!(
        matches!(err, NativeEvalError::UnresolvedCall(ref name) if name == "foo"),
        "expected UnresolvedCall, got {:?}",
        err,
    );
}

// ---------------------------------------------------------------------------
// Nested expression evaluation
// ---------------------------------------------------------------------------

#[test]
fn test_eval_nested_arithmetic() {
    // (10 + 20) * 3 = 90
    let add = NativeExpr::BinOp(NativeOp::Add, Box::new(uint32(10)), Box::new(uint32(20)));
    let mul = NativeExpr::BinOp(NativeOp::Mul, Box::new(add), Box::new(uint32(3)));
    assert_eq!(eval_native(&mul).unwrap(), NativeValue::UInt32(90));
}

#[test]
fn test_eval_deeply_nested() {
    // ((1 + 2) + 3) + 4 = 10
    let a = NativeExpr::BinOp(NativeOp::Add, Box::new(uint32(1)), Box::new(uint32(2)));
    let b = NativeExpr::BinOp(NativeOp::Add, Box::new(a), Box::new(uint32(3)));
    let c = NativeExpr::BinOp(NativeOp::Add, Box::new(b), Box::new(uint32(4)));
    assert_eq!(eval_native(&c).unwrap(), NativeValue::UInt32(10));
}
