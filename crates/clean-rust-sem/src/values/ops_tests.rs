// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_binop_add() {
    let left = Value::u32(10);
    let right = Value::u32(20);

    let result = eval_binop(BinOp::Add, &left, &right);
    assert_eq!(result, Some(Value::u32(30)));
}

#[test]
fn test_binop_compare() {
    let left = Value::i32(5);
    let right = Value::i32(10);

    assert_eq!(
        eval_binop(BinOp::Lt, &left, &right),
        Some(Value::Bool(true))
    );
    assert_eq!(
        eval_binop(BinOp::Gt, &left, &right),
        Some(Value::Bool(false))
    );
    assert_eq!(
        eval_binop(BinOp::Eq, &left, &right),
        Some(Value::Bool(false))
    );
}

#[test]
fn test_unop_neg() {
    let val = Value::i32(42);
    let result = eval_unop(UnOp::Neg, &val);
    assert_eq!(result, Some(Value::i32(-42)));
}

#[test]
fn test_unop_not() {
    let val = Value::Bool(true);
    let result = eval_unop(UnOp::Not, &val);
    assert_eq!(result, Some(Value::Bool(false)));
}

#[test]
fn test_cast_int_to_int() {
    let val = Value::u32(256);
    let result = cast_value(&val, &RustType::Uint(UintType::U8));
    assert_eq!(result, Some(Value::u8(0)));
}

#[test]
fn test_cast_bool_to_int() {
    let val = Value::Bool(true);
    let result = cast_value(&val, &RustType::Uint(UintType::U32));
    assert_eq!(result, Some(Value::u32(1)));
}

#[test]
fn test_overflow_wrapping() {
    let left = Value::u8(255);
    let right = Value::u8(1);

    let result = eval_binop(BinOp::Add, &left, &right);
    assert_eq!(result, Some(Value::u8(0)));
}

#[test]
fn test_division_by_zero() {
    let left = Value::u32(10);
    let right = Value::u32(0);

    let result = eval_binop(BinOp::Div, &left, &right);
    assert_eq!(result, None);
}

#[test]
fn test_float_operations() {
    let left = Value::f64(3.0);
    let right = Value::f64(2.0);

    let result =
        eval_binop(BinOp::Add, &left, &right).expect("f64 addition should produce a result");

    let result_f64 = result.as_f64().expect("float result should convert");
    assert!((result_f64 - 5.0).abs() < f64::EPSILON);
}

#[test]
fn test_signed_overflow_wrapping_i8() {
    let left = Value::Int {
        value: 127,
        ty: IntType::I8,
    };
    let right = Value::Int {
        value: 1,
        ty: IntType::I8,
    };
    let result = eval_binop(BinOp::Add, &left, &right);
    assert_eq!(
        result,
        Some(Value::Int {
            value: -128,
            ty: IntType::I8,
        })
    );
}

#[test]
fn test_signed_sub_wrapping_i8() {
    let left = Value::Int {
        value: -128,
        ty: IntType::I8,
    };
    let right = Value::Int {
        value: 1,
        ty: IntType::I8,
    };
    let result = eval_binop(BinOp::Sub, &left, &right);
    assert_eq!(
        result,
        Some(Value::Int {
            value: 127,
            ty: IntType::I8,
        })
    );
}

#[test]
fn test_bitwise_not_u8() {
    let val = Value::u8(0);
    let result = eval_unop(UnOp::Not, &val);
    assert_eq!(result, Some(Value::u8(255)));
}

#[test]
fn test_bitwise_not_u16() {
    let val = Value::Uint {
        value: 0,
        ty: UintType::U16,
    };
    let result = eval_unop(UnOp::Not, &val);
    assert_eq!(
        result,
        Some(Value::Uint {
            value: 0xFFFF,
            ty: UintType::U16,
        })
    );
}

#[test]
fn test_neg_wrapping_i8() {
    let val = Value::Int {
        value: -128,
        ty: IntType::I8,
    };
    let result = eval_unop(UnOp::Neg, &val);
    assert_eq!(
        result,
        Some(Value::Int {
            value: -128,
            ty: IntType::I8,
        })
    );
}

#[test]
fn test_cast_int_to_uint_truncates() {
    let val = Value::Int {
        value: -1,
        ty: IntType::I8,
    };
    let result = cast_value(&val, &RustType::Uint(UintType::U32));
    assert_eq!(
        result,
        Some(Value::Uint {
            value: 0xFFFF_FFFF,
            ty: UintType::U32,
        })
    );
}

#[test]
fn test_cast_int_to_uint_small() {
    let val = Value::Int {
        value: -1,
        ty: IntType::I32,
    };
    let result = cast_value(&val, &RustType::Uint(UintType::U8));
    assert_eq!(result, Some(Value::u8(255)));
}

#[test]
fn test_cast_uint_to_int_truncates() {
    let val = Value::u32(256);
    let result = cast_value(&val, &RustType::Int(IntType::I8));
    assert_eq!(
        result,
        Some(Value::Int {
            value: 0,
            ty: IntType::I8,
        })
    );
}

#[test]
fn test_cast_uint_to_int_sign_extends() {
    let val = Value::u32(255);
    let result = cast_value(&val, &RustType::Int(IntType::I8));
    assert_eq!(
        result,
        Some(Value::Int {
            value: -1,
            ty: IntType::I8,
        })
    );
}

#[test]
fn test_cast_int_to_int_truncates() {
    let val = Value::i32(256);
    let result = cast_value(&val, &RustType::Int(IntType::I8));
    assert_eq!(
        result,
        Some(Value::Int {
            value: 0,
            ty: IntType::I8,
        })
    );
}

#[test]
fn test_cast_int_to_int_sign_extends() {
    let val = Value::i32(128);
    let result = cast_value(&val, &RustType::Int(IntType::I8));
    assert_eq!(
        result,
        Some(Value::Int {
            value: -128,
            ty: IntType::I8,
        })
    );
}

#[test]
fn test_shl_u8_wraps_shift_amount() {
    let result = eval_binop(BinOp::Shl, &Value::u8(1), &Value::u8(8));
    assert_eq!(result, Some(Value::u8(1)));
}

#[test]
fn test_shr_u8_wraps_shift_amount() {
    let result = eval_binop(BinOp::Shr, &Value::u8(255), &Value::u8(8));
    assert_eq!(result, Some(Value::u8(255)));
}

#[test]
fn test_shl_u16_wraps_shift_amount() {
    let left = Value::Uint {
        value: 1,
        ty: UintType::U16,
    };
    let right = Value::Uint {
        value: 16,
        ty: UintType::U16,
    };
    let result = eval_binop(BinOp::Shl, &left, &right);
    assert_eq!(
        result,
        Some(Value::Uint {
            value: 1,
            ty: UintType::U16
        })
    );
}

#[test]
fn test_shl_u32_wraps_shift_amount() {
    let result = eval_binop(BinOp::Shl, &Value::u32(1), &Value::u32(32));
    assert_eq!(result, Some(Value::u32(1)));
}

#[test]
fn test_shl_u64_wraps_shift_amount() {
    let result = eval_binop(BinOp::Shl, &Value::u64(1), &Value::u64(64));
    assert_eq!(result, Some(Value::u64(1)));
}

#[test]
fn test_shl_i8_wraps_shift_amount() {
    let left = Value::Int {
        value: 1,
        ty: IntType::I8,
    };
    let right = Value::Int {
        value: 8,
        ty: IntType::I8,
    };
    let result = eval_binop(BinOp::Shl, &left, &right);
    assert_eq!(
        result,
        Some(Value::Int {
            value: 1,
            ty: IntType::I8
        })
    );
}

#[test]
fn test_shr_i8_wraps_shift_amount() {
    let left = Value::Int {
        value: -1,
        ty: IntType::I8,
    };
    let right = Value::Int {
        value: 8,
        ty: IntType::I8,
    };
    let result = eval_binop(BinOp::Shr, &left, &right);
    assert_eq!(
        result,
        Some(Value::Int {
            value: -1,
            ty: IntType::I8
        })
    );
}

#[test]
fn test_shr_i64_wraps_shift_amount() {
    let result = eval_binop(BinOp::Shr, &Value::i64(-1), &Value::i64(64));
    assert_eq!(result, Some(Value::i64(-1)));
}

#[test]
fn test_shl_u8_partial_wrap() {
    let result = eval_binop(BinOp::Shl, &Value::u8(1), &Value::u8(9));
    assert_eq!(result, Some(Value::u8(2)));
}
