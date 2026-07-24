// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::runtime::eval_atomic_op;
use super::{validate_compare_exchange_failure_ordering, validate_ordering};
use super::{AtomicOp, MemoryOrdering};
use crate::error::RustSemError;
use crate::eval::Interpreter;
use crate::expr::EvalResult;
use crate::values::{EnumPayload, Ordering, Value};

fn atomic(value: Value) -> Value {
    Value::Atomic {
        inner: Box::new(value),
    }
}

fn ok(value: Value) -> Value {
    Value::Enum {
        name: "Result".to_string(),
        variant: "Ok".to_string(),
        payload: Box::new(EnumPayload::Tuple(vec![value])),
    }
}

fn err(value: Value) -> Value {
    Value::Enum {
        name: "Result".to_string(),
        variant: "Err".to_string(),
        payload: Box::new(EnumPayload::Tuple(vec![value])),
    }
}

fn assert_atomic_value(result: EvalResult, expected: Value) {
    assert_eq!(result.value(), Some(expected));
}

#[test]
fn eval_load_returns_current_value() {
    let mut value = atomic(Value::i32(7));
    assert_atomic_value(
        eval_atomic_op(AtomicOp::Load, &mut value, None, MemoryOrdering::SeqCst),
        Value::i32(7),
    );
}

#[test]
fn eval_store_updates_value() {
    let mut value = atomic(Value::i32(1));
    assert_atomic_value(
        eval_atomic_op(
            AtomicOp::Store,
            &mut value,
            Some(Value::i32(9)),
            MemoryOrdering::SeqCst,
        ),
        Value::Unit,
    );
    assert_eq!(value, atomic(Value::i32(9)));
}

#[test]
fn eval_swap_returns_previous_value() {
    let mut value = atomic(Value::i32(1));
    assert_atomic_value(
        eval_atomic_op(
            AtomicOp::Swap,
            &mut value,
            Some(Value::i32(4)),
            MemoryOrdering::SeqCst,
        ),
        Value::i32(1),
    );
    assert_eq!(value, atomic(Value::i32(4)));
}

#[test]
fn eval_compare_exchange_success_updates_value() {
    let mut value = atomic(Value::i32(3));
    assert_atomic_value(
        eval_atomic_op(
            AtomicOp::CompareExchange,
            &mut value,
            Some(Value::Tuple(vec![Value::i32(3), Value::i32(8)])),
            MemoryOrdering::SeqCst,
        ),
        ok(Value::i32(3)),
    );
    assert_eq!(value, atomic(Value::i32(8)));
}

#[test]
fn eval_compare_exchange_failure_preserves_value() {
    let mut value = atomic(Value::i32(3));
    assert_atomic_value(
        eval_atomic_op(
            AtomicOp::CompareExchange,
            &mut value,
            Some(Value::Tuple(vec![Value::i32(2), Value::i32(8)])),
            MemoryOrdering::SeqCst,
        ),
        err(Value::i32(3)),
    );
    assert_eq!(value, atomic(Value::i32(3)));
}

#[test]
fn eval_fetch_add_returns_previous_value() {
    let mut value = atomic(Value::i32(3));
    assert_atomic_value(
        eval_atomic_op(
            AtomicOp::FetchAdd,
            &mut value,
            Some(Value::i32(5)),
            MemoryOrdering::SeqCst,
        ),
        Value::i32(3),
    );
    assert_eq!(value, atomic(Value::i32(8)));
}

#[test]
fn eval_fetch_sub_returns_previous_value() {
    let mut value = atomic(Value::i32(9));
    assert_atomic_value(
        eval_atomic_op(
            AtomicOp::FetchSub,
            &mut value,
            Some(Value::i32(4)),
            MemoryOrdering::SeqCst,
        ),
        Value::i32(9),
    );
    assert_eq!(value, atomic(Value::i32(5)));
}

#[test]
fn eval_fetch_and_returns_previous_value() {
    let mut value = atomic(Value::u32(0b1100));
    assert_atomic_value(
        eval_atomic_op(
            AtomicOp::FetchAnd,
            &mut value,
            Some(Value::u32(0b1010)),
            MemoryOrdering::SeqCst,
        ),
        Value::u32(0b1100),
    );
    assert_eq!(value, atomic(Value::u32(0b1000)));
}

#[test]
fn eval_fetch_or_returns_previous_value() {
    let mut value = atomic(Value::u32(0b0100));
    assert_atomic_value(
        eval_atomic_op(
            AtomicOp::FetchOr,
            &mut value,
            Some(Value::u32(0b0011)),
            MemoryOrdering::SeqCst,
        ),
        Value::u32(0b0100),
    );
    assert_eq!(value, atomic(Value::u32(0b0111)));
}

#[test]
fn eval_fetch_xor_returns_previous_value() {
    let mut value = atomic(Value::u32(0b1111));
    assert_atomic_value(
        eval_atomic_op(
            AtomicOp::FetchXor,
            &mut value,
            Some(Value::u32(0b0101)),
            MemoryOrdering::SeqCst,
        ),
        Value::u32(0b1111),
    );
    assert_eq!(value, atomic(Value::u32(0b1010)));
}

#[test]
fn validate_ordering_rejects_release_load() {
    assert_eq!(
        validate_ordering(AtomicOp::Load, MemoryOrdering::Release),
        Err("atomic load does not permit `Release` ordering".to_string())
    );
}

#[test]
fn compare_exchange_failure_must_not_be_stronger_than_success() {
    assert_eq!(
        validate_compare_exchange_failure_ordering(
            MemoryOrdering::Relaxed,
            MemoryOrdering::Acquire
        ),
        Err(
            "atomic compare_exchange failure ordering `Acquire` cannot be stronger than success ordering `Relaxed`"
                .to_string()
        )
    );
}

#[test]
fn fence_intrinsic_returns_unit() {
    let interp = Interpreter::new();
    let result = interp.try_atomic_intrinsic(
        "std::sync::atomic::fence",
        &[Value::Ordering(Ordering::AcqRel)],
    );
    assert!(matches!(result, Some(Ok(Value::Unit))));
}

#[test]
fn fence_intrinsic_rejects_relaxed_ordering() {
    let interp = Interpreter::new();
    let result = interp.try_atomic_intrinsic(
        "std::sync::atomic::compiler_fence",
        &[Value::Ordering(Ordering::Relaxed)],
    );
    assert!(matches!(
        result,
        Some(Err(RustSemError::Eval(ref msg)))
            if msg == "atomic compiler_fence does not permit `Relaxed` ordering"
    ));
}
