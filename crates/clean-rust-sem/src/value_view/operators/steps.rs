// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-[`ViewOp`] step implementations.
//!
//! One function per view step (project / deref / index / unwrap) plus the
//! shared `ViewOpError` constructors and the `value_kind` label table that
//! every error carries. The chain type, the error enum and the dispatcher
//! live in the parent `operators` module; this file is the step bodies it
//! dispatches to.

use super::*;

fn missing_field(field: &str, value_kind: &'static str) -> ViewOpError {
    ViewOpError::MissingField {
        field: field.to_string(),
        value_kind,
    }
}

fn unsupported(op: ViewOp, value_kind: &'static str) -> ViewOpError {
    ViewOpError::Unsupported { op, value_kind }
}

pub(super) fn project_field(value: &Value, field: &str) -> Result<Value, ViewOpError> {
    let kind = value_kind(value);
    match value {
        Value::Struct { fields, .. } => clone_named_field(fields, field, kind),
        Value::Enum { payload, .. } => match payload.as_ref() {
            EnumPayload::Struct(fields) => clone_named_field(fields, field, kind),
            _ => Err(unsupported(ViewOp::Project(field.to_string()), kind)),
        },
        Value::Union {
            active_field,
            value,
            ..
        } if active_field == field => Ok((**value).clone()),
        Value::Cell { value, .. }
        | Value::UnsafeCell { value, .. }
        | Value::MutexGuard { value, .. }
        | Value::RwLockReadGuard { value, .. }
        | Value::RwLockWriteGuard { value, .. }
        | Value::RefCellRef { value, .. }
        | Value::RefCellRefMut { value, .. }
            if field == "value" =>
        {
            Ok((**value).clone())
        }
        Value::OnceCell { value, .. } | Value::OnceLock { value, .. } if field == "value" => value
            .as_deref()
            .cloned()
            .ok_or_else(|| missing_field(field, kind)),
        Value::RefCell { value, .. } if field == "value" => Ok((**value).clone()),
        Value::Mutex {
            value,
            locked,
            poisoned,
            ..
        } => match field {
            "value" => Ok((**value).clone()),
            "locked" => Ok(Value::Bool(*locked)),
            "poisoned" => Ok(Value::Bool(*poisoned)),
            _ => Err(missing_field(field, "mutex")),
        },
        Value::RwLock {
            value,
            reader_count,
            writer_locked,
            poisoned,
            ..
        } => match field {
            "value" => Ok((**value).clone()),
            "reader_count" => Ok(Value::usize(*reader_count)),
            "writer_locked" => Ok(Value::Bool(*writer_locked)),
            "poisoned" => Ok(Value::Bool(*poisoned)),
            _ => Err(missing_field(field, "rwlock")),
        },
        Value::Atomic { inner } if field == "inner" => Ok((**inner).clone()),
        Value::Reference { referent, .. } if field == "referent" => referent
            .as_deref()
            .cloned()
            .ok_or(ViewOpError::MissingReferent {
                value_kind: value_kind(value),
            }),
        Value::FatPtr(FatPointer { data_pointer, .. }) if field == "data_pointer" => {
            Ok((**data_pointer).clone())
        }
        Value::TraitObject { data, .. } if field == "data" => Ok((**data).clone()),
        Value::Range {
            start,
            end,
            inclusive,
        } => match field {
            "start" => start
                .as_deref()
                .cloned()
                .ok_or_else(|| missing_field(field, kind)),
            "end" => end
                .as_deref()
                .cloned()
                .ok_or_else(|| missing_field(field, kind)),
            "inclusive" => Ok(Value::Bool(*inclusive)),
            _ => Err(missing_field(field, kind)),
        },
        _ => Err(unsupported(ViewOp::Project(field.to_string()), kind)),
    }
}

fn clone_named_field(
    fields: &BTreeMap<String, Value>,
    field: &str,
    value_kind: &'static str,
) -> Result<Value, ViewOpError> {
    fields
        .get(field)
        .cloned()
        .ok_or_else(|| missing_field(field, value_kind))
}

pub(super) fn deref_once(value: &Value) -> Result<Value, ViewOpError> {
    let kind = value_kind(value);
    match value {
        Value::Reference {
            referent: Some(referent),
            ..
        }
        | Value::MutexGuard {
            value: referent, ..
        }
        | Value::RwLockReadGuard {
            value: referent, ..
        }
        | Value::RwLockWriteGuard {
            value: referent, ..
        }
        | Value::RefCellRef {
            value: referent, ..
        }
        | Value::RefCellRefMut {
            value: referent, ..
        }
        | Value::FatPtr(FatPointer {
            data_pointer: referent,
            ..
        })
        | Value::TraitObject { data: referent, .. } => Ok((**referent).clone()),
        Value::Reference { referent: None, .. } => {
            Err(ViewOpError::MissingReferent { value_kind: kind })
        }
        _ => Err(unsupported(ViewOp::Deref, kind)),
    }
}

pub(super) fn index_value(value: &Value, index: usize) -> Result<Value, ViewOpError> {
    let kind = value_kind(value);
    match value {
        Value::Tuple(values) | Value::Array(values) => clone_indexed_value(values, index, value),
        Value::Enum { payload, .. } => match payload.as_ref() {
            EnumPayload::Tuple(values) => clone_indexed_value(values, index, value),
            _ => Err(unsupported(ViewOp::Index(index), kind)),
        },
        Value::Closure { captures, .. } => captures
            .get(index)
            .map(|(_, inner, _)| inner.clone())
            .ok_or(ViewOpError::IndexOutOfBounds {
                index,
                len: captures.len(),
                value_kind: kind,
            }),
        _ => Err(unsupported(ViewOp::Index(index), kind)),
    }
}

fn clone_indexed_value(
    values: &[Value],
    index: usize,
    value: &Value,
) -> Result<Value, ViewOpError> {
    values
        .get(index)
        .cloned()
        .ok_or(ViewOpError::IndexOutOfBounds {
            index,
            len: values.len(),
            value_kind: value_kind(value),
        })
}

pub(super) fn unwrap_value(value: &Value) -> Result<Value, ViewOpError> {
    match value {
        Value::Enum { payload, .. } => unwrap_payload(payload.as_ref(), value_kind(value)),
        Value::Tuple(values) if values.len() == 1 => Ok(values[0].clone()),
        Value::Struct { fields, .. } if fields.len() == 1 => {
            Ok(fields.values().next().expect("single field").clone())
        }
        Value::Cell { value, .. }
        | Value::RefCell { value, .. }
        | Value::UnsafeCell { value, .. }
        | Value::Mutex { value, .. }
        | Value::RwLock { value, .. }
        | Value::Atomic { inner: value } => Ok((**value).clone()),
        _ => Err(ViewOpError::InvalidUnwrap {
            value_kind: value_kind(value),
        }),
    }
}

fn unwrap_payload(payload: &EnumPayload, value_kind: &'static str) -> Result<Value, ViewOpError> {
    match payload {
        EnumPayload::Tuple(values) if values.len() == 1 => Ok(values[0].clone()),
        EnumPayload::Struct(fields) if fields.len() == 1 => {
            Ok(fields.values().next().expect("single field").clone())
        }
        _ => Err(ViewOpError::InvalidUnwrap { value_kind }),
    }
}

pub(super) fn value_kind(value: &Value) -> &'static str {
    match value {
        Value::Unit => "unit",
        Value::Bool(_) => "bool",
        Value::Char(_) => "char",
        Value::Str(_) => "str",
        Value::Uint { .. } => "uint",
        Value::Int { .. } => "int",
        Value::Float { .. } => "float",
        Value::Reference { .. } => "reference",
        Value::RawPtr { .. } => "raw pointer",
        Value::Cell { .. } => "cell",
        Value::RefCell { .. } => "refcell",
        Value::UnsafeCell { .. } => "unsafe cell",
        Value::OnceCell { .. } => "once cell",
        Value::OnceLock { .. } => "once lock",
        Value::Mutex { .. } => "mutex",
        Value::MutexGuard { .. } => "mutex guard",
        Value::RwLock { .. } => "rwlock",
        Value::RwLockReadGuard { .. } => "rwlock read guard",
        Value::RwLockWriteGuard { .. } => "rwlock write guard",
        Value::RefCellRef { .. } => "refcell ref",
        Value::RefCellRefMut { .. } => "refcell ref mut",
        Value::FatPtr(_) => "fat pointer",
        Value::Ordering(_) => "ordering",
        Value::Atomic { .. } => "atomic",
        Value::Tuple(_) => "tuple",
        Value::Range { .. } => "range",
        Value::Array(_) => "array",
        Value::Struct { .. } => "struct",
        Value::Enum { .. } => "enum",
        Value::Union { .. } => "union",
        Value::FnPtr { .. } => "fn ptr",
        Value::Closure { .. } => "closure",
        Value::Never => "never",
        Value::Uninit => "uninit",
        Value::TraitObject { .. } => "trait object",
        Value::Future { .. } => "future",
    }
}
