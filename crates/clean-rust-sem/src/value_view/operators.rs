// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::values::cast_value;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ViewOp {
    Project(String),
    Deref,
    Index(usize),
    Cast(RustType),
    Unwrap,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ViewOpChain {
    ops: Vec<ViewOp>,
}

impl ViewOpChain {
    #[must_use]
    pub fn new(ops: Vec<ViewOp>) -> Self {
        Self { ops }
    }

    #[must_use]
    pub fn ops(&self) -> &[ViewOp] {
        &self.ops
    }

    pub fn apply(&self, value: &Value) -> Result<Value, ViewOpError> {
        self.ops
            .iter()
            .try_fold(value.clone(), |current, op| apply_view_op(&current, op))
    }
}

impl From<Vec<ViewOp>> for ViewOpChain {
    fn from(ops: Vec<ViewOp>) -> Self {
        Self::new(ops)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ViewOpError {
    #[error("field `{field}` not found on {value_kind}")]
    MissingField {
        field: String,
        value_kind: &'static str,
    },
    #[error("{value_kind} has no preserved referent")]
    MissingReferent { value_kind: &'static str },
    #[error("index {index} out of bounds for {value_kind} of length {len}")]
    IndexOutOfBounds {
        index: usize,
        len: usize,
        value_kind: &'static str,
    },
    #[error("cannot cast {value_kind} to {target:?}")]
    CastFailed {
        value_kind: &'static str,
        target: RustType,
    },
    #[error("cannot unwrap {value_kind}")]
    InvalidUnwrap { value_kind: &'static str },
    #[error("{op:?} is not supported on {value_kind}")]
    Unsupported {
        op: ViewOp,
        value_kind: &'static str,
    },
}

pub fn apply_view_op(value: &Value, op: &ViewOp) -> Result<Value, ViewOpError> {
    match op {
        ViewOp::Project(field) => project_field(value, field),
        ViewOp::Deref => deref_once(value),
        ViewOp::Index(index) => index_value(value, *index),
        ViewOp::Cast(target) => cast_value(value, target).ok_or_else(|| ViewOpError::CastFailed {
            value_kind: value_kind(value),
            target: target.clone(),
        }),
        ViewOp::Unwrap => unwrap_value(value),
    }
}

#[must_use]
pub fn optimize_chain(chain: &ViewOpChain) -> ViewOpChain {
    let mut optimized = Vec::with_capacity(chain.ops.len());
    for op in chain.ops() {
        if let (Some(ViewOp::Cast(previous)), ViewOp::Cast(current)) = (optimized.last(), op) {
            if previous == current {
                continue;
            }
        }
        optimized.push(op.clone());
    }
    ViewOpChain::new(optimized)
}

fn missing_field(field: &str, value_kind: &'static str) -> ViewOpError {
    ViewOpError::MissingField {
        field: field.to_string(),
        value_kind,
    }
}

fn unsupported(op: ViewOp, value_kind: &'static str) -> ViewOpError {
    ViewOpError::Unsupported { op, value_kind }
}

fn project_field(value: &Value, field: &str) -> Result<Value, ViewOpError> {
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

fn deref_once(value: &Value) -> Result<Value, ViewOpError> {
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

fn index_value(value: &Value, index: usize) -> Result<Value, ViewOpError> {
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

fn unwrap_value(value: &Value) -> Result<Value, ViewOpError> {
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

fn value_kind(value: &Value) -> &'static str {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memory::{Address, AllocId};
    use crate::types::{IntType, Lifetime, Mutability, UintType};

    fn shared_ref(referent: Option<Value>) -> Value {
        Value::Reference {
            addr: Address::new(AllocId(3), 0),
            mutability: Mutability::Shared,
            lifetime: Lifetime::Static,
            referent: referent.map(Box::new),
        }
    }

    #[test]
    fn apply_view_op_supports_core_operators() {
        let pair = Value::Struct {
            name: "Pair".to_string(),
            fields: BTreeMap::from([("right".to_string(), Value::Bool(true))]),
        };
        let tuple = Value::Tuple(vec![Value::Bool(false), Value::i64(-7)]);
        let option = Value::Enum {
            name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Box::new(EnumPayload::Tuple(vec![Value::u32(11)])),
        };
        assert_eq!(
            apply_view_op(&pair, &ViewOp::Project("right".to_string())),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            apply_view_op(&shared_ref(Some(Value::u32(9))), &ViewOp::Deref),
            Ok(Value::u32(9))
        );
        assert_eq!(apply_view_op(&tuple, &ViewOp::Index(1)), Ok(Value::i64(-7)));
        assert_eq!(
            apply_view_op(&Value::i32(-1), &ViewOp::Cast(RustType::Uint(UintType::U8))),
            Ok(Value::u8(u8::MAX))
        );
        assert_eq!(apply_view_op(&option, &ViewOp::Unwrap), Ok(Value::u32(11)));
    }

    #[test]
    fn chain_composes_multiple_operators() {
        let value = Value::Struct {
            name: "Wrapper".to_string(),
            fields: BTreeMap::from([(
                "slot".to_string(),
                Value::Reference {
                    addr: Address::new(AllocId(5), 8),
                    mutability: Mutability::Shared,
                    lifetime: Lifetime::Static,
                    referent: Some(Box::new(Value::Enum {
                        name: "Option".to_string(),
                        variant: "Some".to_string(),
                        payload: Box::new(EnumPayload::Tuple(vec![Value::i32(-4)])),
                    })),
                },
            )]),
        };
        let chain = ViewOpChain::from(vec![
            ViewOp::Project("slot".to_string()),
            ViewOp::Deref,
            ViewOp::Unwrap,
            ViewOp::Cast(RustType::Int(IntType::I64)),
        ]);

        assert_eq!(chain.apply(&value), Ok(Value::i64(-4)));
    }

    #[test]
    fn apply_view_op_reports_edge_case_errors() {
        let empty_lock = Value::OnceLock { id: 1, value: None };
        let missing_range_start = Value::Range {
            start: None,
            end: Some(Box::new(Value::u32(4))),
            inclusive: false,
        };
        let struct_value = Value::Struct {
            name: "OnlyLeft".to_string(),
            fields: BTreeMap::from([("left".to_string(), Value::u32(1))]),
        };
        let none_value = Value::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            payload: Box::new(EnumPayload::Unit),
        };
        assert_eq!(
            apply_view_op(&shared_ref(None), &ViewOp::Deref),
            Err(ViewOpError::MissingReferent {
                value_kind: "reference"
            })
        );
        assert_eq!(
            apply_view_op(&empty_lock, &ViewOp::Project("value".to_string())),
            Err(ViewOpError::MissingField {
                field: "value".to_string(),
                value_kind: "once lock"
            })
        );
        assert_eq!(
            apply_view_op(&missing_range_start, &ViewOp::Project("start".to_string())),
            Err(ViewOpError::MissingField {
                field: "start".to_string(),
                value_kind: "range"
            })
        );
        assert_eq!(
            apply_view_op(&struct_value, &ViewOp::Project("right".to_string())),
            Err(ViewOpError::MissingField {
                field: "right".to_string(),
                value_kind: "struct"
            })
        );
        assert_eq!(
            apply_view_op(&none_value, &ViewOp::Unwrap),
            Err(ViewOpError::InvalidUnwrap { value_kind: "enum" })
        );
    }

    #[test]
    fn apply_view_op_handles_closure_index_and_single_field_unwrap() {
        let closure = Value::Closure {
            fn_id: "f".to_string(),
            captures: vec![("flag".to_string(), Value::Bool(true), Mutability::Shared)],
            param_types: vec![],
            ret_type: RustType::Unit,
            kind: ClosureKind::Fn,
        };
        let wrapper = Value::Struct {
            name: "Wrapper".to_string(),
            fields: BTreeMap::from([("only".to_string(), Value::u8(2))]),
        };
        assert_eq!(
            apply_view_op(&closure, &ViewOp::Index(0)),
            Ok(Value::Bool(true))
        );
        assert_eq!(
            apply_view_op(&closure, &ViewOp::Index(1)),
            Err(ViewOpError::IndexOutOfBounds {
                index: 1,
                len: 1,
                value_kind: "closure"
            })
        );
        assert_eq!(apply_view_op(&wrapper, &ViewOp::Unwrap), Ok(Value::u8(2)));
    }

    #[test]
    fn optimize_chain_removes_only_adjacent_duplicate_casts() {
        let chain = ViewOpChain::from(vec![
            ViewOp::Cast(RustType::Uint(UintType::U8)),
            ViewOp::Cast(RustType::Uint(UintType::U8)),
            ViewOp::Project("value".to_string()),
            ViewOp::Cast(RustType::Int(IntType::I64)),
            ViewOp::Cast(RustType::Uint(UintType::U8)),
            ViewOp::Cast(RustType::Uint(UintType::U8)),
        ]);
        let optimized = ViewOpChain::from(vec![
            ViewOp::Cast(RustType::Uint(UintType::U8)),
            ViewOp::Project("value".to_string()),
            ViewOp::Cast(RustType::Int(IntType::I64)),
            ViewOp::Cast(RustType::Uint(UintType::U8)),
        ]);
        assert_eq!(optimize_chain(&chain), optimized);
        assert_eq!(optimize_chain(&optimized), optimized);
    }
}
