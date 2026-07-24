// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust Value Representation
//!
//! This module defines how Rust values are represented in the semantic model.
//! Values are the runtime representations of data.

mod methods;
mod ops;
mod view_methods;
pub use ops::{cast_value, eval_binop, eval_unop, BinOp, UnOp};
#[cfg(test)]
mod ops_tests;
#[cfg(test)]
mod view_tests;

use crate::memory::Address;
use crate::stacked_borrows::BorrowTag;
use crate::types::{
    ClosureKind, FloatType, IntType, Lifetime, Mutability, RustType, UintType, VTable,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Opaque expression wrapper for `Value` variants where structural equality
/// is not meaningful (e.g., futures). Two futures are never equal.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OpaqueExpr(pub Box<crate::expr::Expr>);

impl PartialEq for OpaqueExpr {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

/// Runtime borrow state for `RefCell<T>`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RefCellBorrowState {
    /// No active borrows.
    Unborrowed,
    /// One or more active shared borrows.
    Shared { count: usize },
    /// An active mutable borrow.
    Mutable,
}

/// Symbolic vtable pointer metadata for a trait-object fat pointer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VtablePtr {
    pub trait_name: String,
}

impl VtablePtr {
    #[must_use]
    pub fn new(trait_name: impl Into<String>) -> Self {
        Self {
            trait_name: trait_name.into(),
        }
    }
}

/// Metadata stored alongside a dynamically sized pointer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FatPtrMetadata {
    /// Trait-object dispatch metadata.
    VtablePtr(VtablePtr),
    /// Slice length metadata.
    SliceLen(usize),
}

/// A wide pointer to a dynamically sized value.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FatPointer {
    pub data_pointer: Box<Value>,
    pub metadata: FatPtrMetadata,
}

impl FatPointer {
    #[must_use]
    pub fn new(data_pointer: Value, metadata: FatPtrMetadata) -> Self {
        Self {
            data_pointer: Box::new(data_pointer),
            metadata,
        }
    }

    #[must_use]
    pub fn slice(data_pointer: Value, len: usize) -> Self {
        Self::new(data_pointer, FatPtrMetadata::SliceLen(len))
    }

    #[must_use]
    pub fn vtable(data_pointer: Value, trait_name: impl Into<String>) -> Self {
        Self::new(
            data_pointer,
            FatPtrMetadata::VtablePtr(VtablePtr::new(trait_name)),
        )
    }
}

/// Memory ordering for atomic operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Ordering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
}

impl Ordering {
    /// Recover an ordering from a literal value.
    pub fn from_value(value: &Value) -> Option<Self> {
        match value {
            Value::Ordering(ordering) => Some(*ordering),
            Value::Enum {
                name,
                variant,
                payload,
            } if (name == "Ordering" || name.ends_with("::Ordering"))
                && matches!(payload.as_ref(), EnumPayload::Unit) =>
            {
                match variant.as_str() {
                    "Relaxed" => Some(Self::Relaxed),
                    "Acquire" => Some(Self::Acquire),
                    "Release" => Some(Self::Release),
                    "AcqRel" => Some(Self::AcqRel),
                    "SeqCst" => Some(Self::SeqCst),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

/// A Rust value.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Value {
    /// Unit value ().
    Unit,
    /// Boolean.
    Bool(bool),
    /// Character (Unicode scalar value).
    Char(char),
    /// String value.
    Str(String),
    /// Unsigned integer with size.
    Uint { value: u128, ty: UintType },
    /// Signed integer with size.
    Int { value: i128, ty: IntType },
    /// Floating point.
    Float {
        /// Stored as bits to preserve NaN payloads.
        bits: u64,
        ty: FloatType,
    },
    /// Reference (pointer with provenance).
    Reference {
        addr: Address,
        mutability: Mutability,
        lifetime: Lifetime,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        referent: Option<Box<Value>>,
    },
    /// Raw pointer (no provenance tracking).
    RawPtr {
        addr: Address,
        mutability: Mutability,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        tag: Option<BorrowTag>,
    },
    /// `Cell<T>`.
    Cell { id: u64, value: Box<Value> },
    /// `RefCell<T>`.
    RefCell {
        id: u64,
        value: Box<Value>,
        borrow: RefCellBorrowState,
    },
    /// `UnsafeCell<T>`.
    UnsafeCell { id: u64, value: Box<Value> },
    /// `OnceCell<T>`.
    OnceCell { id: u64, value: Option<Box<Value>> },
    /// `OnceLock<T>`.
    OnceLock { id: u64, value: Option<Box<Value>> },
    /// `Mutex<T>`.
    Mutex {
        id: u64,
        value: Box<Value>,
        locked: bool,
        poisoned: bool,
    },
    /// `MutexGuard<'_, T>`.
    MutexGuard { lock_id: u64, value: Box<Value> },
    /// `RwLock<T>`.
    RwLock {
        id: u64,
        value: Box<Value>,
        reader_count: usize,
        writer_locked: bool,
        poisoned: bool,
    },
    /// `RwLockReadGuard<'_, T>`.
    RwLockReadGuard { lock_id: u64, value: Box<Value> },
    /// `RwLockWriteGuard<'_, T>`.
    RwLockWriteGuard { lock_id: u64, value: Box<Value> },
    /// Shared borrow guard produced by `RefCell::borrow`.
    RefCellRef { cell_id: u64, value: Box<Value> },
    /// Mutable borrow guard produced by `RefCell::borrow_mut`.
    RefCellRefMut { cell_id: u64, value: Box<Value> },
    /// Fat pointer for DST references and owning pointers.
    FatPtr(FatPointer),
    /// Atomic memory ordering literal.
    Ordering(Ordering),
    /// Atomic scalar or pointer value.
    Atomic { inner: Box<Value> },
    /// Tuple of values.
    Tuple(Vec<Value>),
    /// Range value.
    Range {
        start: Option<Box<Value>>,
        end: Option<Box<Value>>,
        inclusive: bool,
    },
    /// Array of values (fixed size).
    Array(Vec<Value>),
    /// Struct value.
    Struct {
        name: String,
        fields: BTreeMap<String, Value>,
    },
    /// Enum variant.
    Enum {
        name: String,
        variant: String,
        payload: Box<EnumPayload>,
    },
    /// Union value.
    Union {
        name: String,
        active_field: String,
        value: Box<Value>,
    },
    /// Function pointer.
    FnPtr { name: String },
    /// Closure (captured environment with type information).
    Closure {
        fn_id: String,
        captures: Vec<(String, Value, Mutability)>,
        param_types: Vec<RustType>,
        ret_type: RustType,
        kind: ClosureKind,
    },
    /// The "never" value (unreachable).
    Never,
    /// Uninitialized memory (poison).
    Uninit,
    /// Trait object (dyn Trait).
    TraitObject {
        data: Box<Value>,
        vtable: VTable,
        lifetime: Lifetime,
    },
    /// Future value (unevaluated async computation).
    Future { body: OpaqueExpr },
}

/// Enum variant payload.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum EnumPayload {
    /// Unit variant: Foo.
    Unit,
    /// Tuple variant: Foo(x, y).
    Tuple(Vec<Value>),
    /// Struct variant: Foo { a, b }.
    Struct(BTreeMap<String, Value>),
}

/// Verification-facing structural view of a Rust value.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ValueView {
    /// Primitive scalar leaf.
    Scalar(Value),
    /// Named fields of a struct-like or tuple-like value.
    Aggregate(Vec<(String, ValueView)>),
    /// Enum-like variant plus its payload.
    Variant(String, Box<ValueView>),
    /// Reference to an inner view.
    Reference(Box<ValueView>),
    /// Collection of element views.
    Collection(Vec<ValueView>),
    /// Value that cannot be structurally decomposed.
    Opaque(String),
}
