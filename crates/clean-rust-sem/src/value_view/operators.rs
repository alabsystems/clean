// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::values::cast_value;

mod steps;

use steps::{deref_once, index_value, project_field, unwrap_value, value_kind};

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
