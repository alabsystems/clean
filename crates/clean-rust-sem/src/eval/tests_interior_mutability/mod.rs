// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::tests_support::make_let;
use super::*;
use crate::stmt::FunctionDef;
use crate::values::{EnumPayload, RefCellBorrowState};

mod cells;
mod sync;

pub(super) fn var(name: &str) -> Expr {
    Expr::Var {
        name: name.to_string(),
        local_idx: 0,
    }
}

pub(super) fn call(name: &str, args: Vec<Expr>) -> Expr {
    Expr::Call {
        func: Box::new(var(name)),
        args,
        type_args: vec![],
    }
}

pub(super) fn method(receiver: Expr, name: &str, args: Vec<Expr>) -> Expr {
    Expr::MethodCall {
        receiver: Box::new(receiver),
        method: name.to_string(),
        args,
        type_args: vec![],
    }
}

pub(super) fn unwrap(expr: Expr) -> Expr {
    method(expr, "unwrap", vec![])
}

pub(super) fn deref(expr: Expr) -> Expr {
    Expr::Deref(Box::new(expr))
}

pub(super) fn assert_refcell_state(value: &Value, inner: Value, borrow: RefCellBorrowState) {
    match value {
        Value::RefCell {
            value: actual_inner,
            borrow: actual_borrow,
            ..
        } => {
            assert_eq!(actual_inner.as_ref(), &inner);
            assert_eq!(actual_borrow, &borrow);
        }
        other => panic!("expected RefCell value, got {other:?}"),
    }
}

pub(super) fn assert_once_cell_state(value: &Value, inner: Option<Value>) {
    match value {
        Value::OnceCell { value: actual, .. } | Value::OnceLock { value: actual, .. } => {
            assert_eq!(actual.as_deref().cloned(), inner);
        }
        other => panic!("expected once-cell value, got {other:?}"),
    }
}

pub(super) fn assert_mutex_state(value: &Value, inner: Value, locked: bool, poisoned: bool) {
    match value {
        Value::Mutex {
            value: actual,
            locked: actual_locked,
            poisoned: actual_poisoned,
            ..
        } => {
            assert_eq!(actual.as_ref(), &inner);
            assert_eq!(*actual_locked, locked);
            assert_eq!(*actual_poisoned, poisoned);
        }
        other => panic!("expected Mutex value, got {other:?}"),
    }
}

pub(super) fn assert_rwlock_state(
    value: &Value,
    inner: Value,
    reader_count: usize,
    writer_locked: bool,
    poisoned: bool,
) {
    match value {
        Value::RwLock {
            value: actual,
            reader_count: actual_readers,
            writer_locked: actual_writer,
            poisoned: actual_poisoned,
            ..
        } => {
            assert_eq!(actual.as_ref(), &inner);
            assert_eq!(*actual_readers, reader_count);
            assert_eq!(*actual_writer, writer_locked);
            assert_eq!(*actual_poisoned, poisoned);
        }
        other => panic!("expected RwLock value, got {other:?}"),
    }
}

pub(super) fn assert_result_ok_unit(value: &Value) {
    match value {
        Value::Enum {
            name,
            variant,
            payload,
        } => {
            assert_eq!(name, "Result");
            assert_eq!(variant, "Ok");
            assert_eq!(payload.as_ref(), &EnumPayload::Tuple(vec![Value::Unit]));
        }
        other => panic!("expected Result::Ok(()), got {other:?}"),
    }
}

pub(super) fn assert_result_err_value(value: &Value, expected: Value) {
    match value {
        Value::Enum {
            name,
            variant,
            payload,
        } => {
            assert_eq!(name, "Result");
            assert_eq!(variant, "Err");
            assert_eq!(payload.as_ref(), &EnumPayload::Tuple(vec![expected]));
        }
        other => panic!("expected Result::Err, got {other:?}"),
    }
}

pub(super) fn assert_try_lock_would_block(value: &Value) {
    match value {
        Value::Enum {
            name,
            variant,
            payload,
        } => {
            assert_eq!(name, "Result");
            assert_eq!(variant, "Err");
            match payload.as_ref() {
                EnumPayload::Tuple(values) => match values.as_slice() {
                    [Value::Enum {
                        name,
                        variant,
                        payload,
                    }] => {
                        assert_eq!(name, "TryLockError");
                        assert_eq!(variant, "WouldBlock");
                        assert!(matches!(payload.as_ref(), EnumPayload::Unit));
                    }
                    other => panic!("expected TryLockError payload, got {other:?}"),
                },
                other => panic!("expected tuple payload, got {other:?}"),
            }
        }
        other => panic!("expected Result::Err(TryLockError::WouldBlock), got {other:?}"),
    }
}

pub(super) fn assert_poison_error_result(value: &Value, guard_assert: impl FnOnce(&Value)) {
    match value {
        Value::Enum {
            name,
            variant,
            payload,
        } => {
            assert_eq!(name, "Result");
            assert_eq!(variant, "Err");
            match payload.as_ref() {
                EnumPayload::Tuple(values) => match values.as_slice() {
                    [Value::Struct { name, fields }] => {
                        assert_eq!(name, "PoisonError");
                        let guard = fields
                            .get("guard")
                            .unwrap_or_else(|| panic!("missing poison guard in {fields:?}"));
                        guard_assert(guard);
                    }
                    other => panic!("expected PoisonError payload, got {other:?}"),
                },
                other => panic!("expected tuple payload, got {other:?}"),
            }
        }
        other => panic!("expected Result::Err(PoisonError<_>), got {other:?}"),
    }
}

pub(super) fn register_nullary_function(interp: &mut Interpreter, name: &str, value: Value) {
    interp.ctx.register_function(FunctionDef {
        name: name.to_string(),
        params: vec![],
        ret_ty: value.get_type(),
        body: Expr::Literal(value),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
}
