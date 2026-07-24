// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::{eval_binop, BinOp, IntType, Value};

#[test]
fn test_shl_usize_wraps_shift_amount() {
    let result = eval_binop(BinOp::Shl, &Value::usize(1), &Value::usize(64));
    assert_eq!(result, Some(Value::usize(1)));
}

#[test]
fn test_shr_isize_wraps_shift_amount() {
    let left = Value::Int {
        value: -1,
        ty: IntType::Isize,
    };
    let right = Value::Int {
        value: 64,
        ty: IntType::Isize,
    };

    let result = eval_binop(BinOp::Shr, &left, &right);
    assert_eq!(
        result,
        Some(Value::Int {
            value: -1,
            ty: IntType::Isize
        })
    );
}
