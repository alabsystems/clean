// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Borrowed inspection operators for runtime values.
//!
//! This module provides a non-owning `ValueView` over runtime `Value`s plus
//! a structural pattern language and deep-access helpers for verification code
//! that needs to inspect values without cloning them.

mod matchers;
mod operators;
pub use matchers::{extract, matches};
pub use operators::{apply_view_op, optimize_chain, ViewOp, ViewOpChain, ViewOpError};
#[cfg(test)]
mod tests;

use crate::memory::Address;
use crate::stacked_borrows::BorrowTag;
use crate::types::{
    ClosureKind, FloatType, IntType, Lifetime, Mutability, RustType, UintType, VTable,
};
use crate::values::{
    EnumPayload, FatPointer, FatPtrMetadata, OpaqueExpr, Ordering, RefCellBorrowState, Value,
};
use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EnumPayloadView<'a> {
    Unit,
    Tuple(&'a [Value]),
    Struct(&'a BTreeMap<String, Value>),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ValueView<'a> {
    Unit,
    Bool(bool),
    Char(char),
    Str(&'a str),
    Uint {
        value: u128,
        ty: UintType,
    },
    Int {
        value: i128,
        ty: IntType,
    },
    Float {
        bits: u64,
        ty: FloatType,
    },
    Reference {
        addr: Address,
        mutability: Mutability,
        lifetime: &'a Lifetime,
        referent: Option<&'a Value>,
    },
    RawPtr {
        addr: Address,
        mutability: Mutability,
        tag: Option<BorrowTag>,
    },
    Cell {
        id: u64,
        value: &'a Value,
    },
    RefCell {
        id: u64,
        value: &'a Value,
        borrow: &'a RefCellBorrowState,
    },
    UnsafeCell {
        id: u64,
        value: &'a Value,
    },
    OnceCell {
        id: u64,
        value: Option<&'a Value>,
    },
    OnceLock {
        id: u64,
        value: Option<&'a Value>,
    },
    Mutex {
        id: u64,
        value: &'a Value,
        locked: bool,
        poisoned: bool,
    },
    MutexGuard {
        lock_id: u64,
        value: &'a Value,
    },
    RwLock {
        id: u64,
        value: &'a Value,
        reader_count: usize,
        writer_locked: bool,
        poisoned: bool,
    },
    RwLockReadGuard {
        lock_id: u64,
        value: &'a Value,
    },
    RwLockWriteGuard {
        lock_id: u64,
        value: &'a Value,
    },
    RefCellRef {
        cell_id: u64,
        value: &'a Value,
    },
    RefCellRefMut {
        cell_id: u64,
        value: &'a Value,
    },
    FatPtr {
        data: &'a Value,
        metadata: &'a FatPtrMetadata,
    },
    Ordering(Ordering),
    Atomic {
        inner: &'a Value,
    },
    Tuple(&'a [Value]),
    Range {
        start: Option<&'a Value>,
        end: Option<&'a Value>,
        inclusive: bool,
    },
    Array(&'a [Value]),
    Struct {
        name: &'a str,
        fields: &'a BTreeMap<String, Value>,
    },
    Enum {
        name: &'a str,
        variant: &'a str,
        payload: EnumPayloadView<'a>,
    },
    Union {
        name: &'a str,
        active_field: &'a str,
        value: &'a Value,
    },
    FnPtr {
        name: &'a str,
    },
    Closure {
        fn_id: &'a str,
        captures: &'a [(String, Value, Mutability)],
        param_types: &'a [RustType],
        ret_type: &'a RustType,
        kind: ClosureKind,
    },
    Never,
    Uninit,
    TraitObject {
        data: &'a Value,
        vtable: &'a VTable,
        lifetime: &'a Lifetime,
    },
    Future {
        body: &'a OpaqueExpr,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValuePattern {
    Any,
    IsUnit,
    IsBool(bool),
    IsChar(char),
    IsStr(String),
    IsUint(u128),
    IsUintOfType {
        value: u128,
        ty: UintType,
    },
    IsInt(i64),
    IsIntOfType {
        value: i128,
        ty: IntType,
    },
    IsFloatBits {
        bits: u64,
        ty: FloatType,
    },
    IsRef {
        mutability: Option<Mutability>,
        inner: Option<Box<ValuePattern>>,
    },
    IsRawPtr {
        mutability: Option<Mutability>,
    },
    IsCell {
        inner: Box<ValuePattern>,
    },
    IsRefCell {
        inner: Box<ValuePattern>,
        borrow: Option<RefCellBorrowPattern>,
    },
    IsUnsafeCell {
        inner: Box<ValuePattern>,
    },
    IsRefCellRef {
        inner: Box<ValuePattern>,
    },
    IsRefCellRefMut {
        inner: Box<ValuePattern>,
    },
    IsFatPtr {
        data: Box<ValuePattern>,
        metadata: Option<FatPtrMetadataPattern>,
    },
    IsOrdering(Ordering),
    IsAtomic {
        inner: Box<ValuePattern>,
    },
    IsTuple(Vec<ValuePattern>),
    IsRange {
        start: ValueSlotPattern,
        end: ValueSlotPattern,
        inclusive: Option<bool>,
    },
    IsArray(Vec<ValuePattern>),
    IsStruct {
        name: String,
        fields: Vec<(String, ValuePattern)>,
    },
    IsEnum {
        name: String,
        variant: String,
        payload: Option<EnumPayloadPattern>,
    },
    IsUnion {
        name: String,
        active_field: String,
        value: Option<Box<ValuePattern>>,
    },
    IsFnPtr {
        name: String,
    },
    IsClosure {
        fn_id: Option<String>,
        captures: Vec<(String, ValuePattern)>,
    },
    IsNever,
    IsUninit,
    IsTraitObject {
        trait_name: Option<String>,
        data: Option<Box<ValuePattern>>,
    },
    IsFuture,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueSlotPattern {
    Any,
    None,
    Some(Box<ValuePattern>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnumPayloadPattern {
    Any,
    Unit,
    Tuple(Vec<ValuePattern>),
    Struct(Vec<(String, ValuePattern)>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefCellBorrowPattern {
    Unborrowed,
    Shared { count: Option<usize> },
    Mutable,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FatPtrMetadataPattern {
    Any,
    VTable { trait_name: Option<String> },
    Length(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueAccessor {
    Deref,
    Inner,
    Field(String),
    Index(usize),
    Start,
    End,
}

#[must_use]
pub fn view(value: &Value) -> ValueView<'_> {
    match value {
        Value::Unit => ValueView::Unit,
        Value::Bool(value) => ValueView::Bool(*value),
        Value::Char(value) => ValueView::Char(*value),
        Value::Str(value) => ValueView::Str(value),
        Value::Uint { value, ty } => ValueView::Uint {
            value: *value,
            ty: *ty,
        },
        Value::Int { value, ty } => ValueView::Int {
            value: *value,
            ty: *ty,
        },
        Value::Float { bits, ty } => ValueView::Float {
            bits: *bits,
            ty: *ty,
        },
        Value::Reference {
            addr,
            mutability,
            lifetime,
            referent,
        } => ValueView::Reference {
            addr: *addr,
            mutability: *mutability,
            lifetime,
            referent: referent.as_deref(),
        },
        Value::RawPtr {
            addr,
            mutability,
            tag,
        } => ValueView::RawPtr {
            addr: *addr,
            mutability: *mutability,
            tag: *tag,
        },
        Value::Cell { id, value } => ValueView::Cell {
            id: *id,
            value: value.as_ref(),
        },
        Value::RefCell { id, value, borrow } => ValueView::RefCell {
            id: *id,
            value: value.as_ref(),
            borrow,
        },
        Value::UnsafeCell { id, value } => ValueView::UnsafeCell {
            id: *id,
            value: value.as_ref(),
        },
        Value::OnceCell { id, value } => ValueView::OnceCell {
            id: *id,
            value: value.as_deref(),
        },
        Value::OnceLock { id, value } => ValueView::OnceLock {
            id: *id,
            value: value.as_deref(),
        },
        Value::Mutex {
            id,
            value,
            locked,
            poisoned,
        } => ValueView::Mutex {
            id: *id,
            value: value.as_ref(),
            locked: *locked,
            poisoned: *poisoned,
        },
        Value::MutexGuard { lock_id, value } => ValueView::MutexGuard {
            lock_id: *lock_id,
            value: value.as_ref(),
        },
        Value::RwLock {
            id,
            value,
            reader_count,
            writer_locked,
            poisoned,
        } => ValueView::RwLock {
            id: *id,
            value: value.as_ref(),
            reader_count: *reader_count,
            writer_locked: *writer_locked,
            poisoned: *poisoned,
        },
        Value::RwLockReadGuard { lock_id, value } => ValueView::RwLockReadGuard {
            lock_id: *lock_id,
            value: value.as_ref(),
        },
        Value::RwLockWriteGuard { lock_id, value } => ValueView::RwLockWriteGuard {
            lock_id: *lock_id,
            value: value.as_ref(),
        },
        Value::RefCellRef { cell_id, value } => ValueView::RefCellRef {
            cell_id: *cell_id,
            value: value.as_ref(),
        },
        Value::RefCellRefMut { cell_id, value } => ValueView::RefCellRefMut {
            cell_id: *cell_id,
            value: value.as_ref(),
        },
        Value::FatPtr(FatPointer {
            data_pointer,
            metadata,
        }) => ValueView::FatPtr {
            data: data_pointer.as_ref(),
            metadata,
        },
        Value::Ordering(ordering) => ValueView::Ordering(*ordering),
        Value::Atomic { inner } => ValueView::Atomic {
            inner: inner.as_ref(),
        },
        Value::Tuple(values) => ValueView::Tuple(values),
        Value::Range {
            start,
            end,
            inclusive,
        } => ValueView::Range {
            start: start.as_deref(),
            end: end.as_deref(),
            inclusive: *inclusive,
        },
        Value::Array(values) => ValueView::Array(values),
        Value::Struct { name, fields } => ValueView::Struct { name, fields },
        Value::Enum {
            name,
            variant,
            payload,
        } => ValueView::Enum {
            name,
            variant,
            payload: payload_view(payload.as_ref()),
        },
        Value::Union {
            name,
            active_field,
            value,
        } => ValueView::Union {
            name,
            active_field,
            value: value.as_ref(),
        },
        Value::FnPtr { name } => ValueView::FnPtr { name },
        Value::Closure {
            fn_id,
            captures,
            param_types,
            ret_type,
            kind,
        } => ValueView::Closure {
            fn_id,
            captures,
            param_types,
            ret_type,
            kind: *kind,
        },
        Value::Never => ValueView::Never,
        Value::Uninit => ValueView::Uninit,
        Value::TraitObject {
            data,
            vtable,
            lifetime,
        } => ValueView::TraitObject {
            data: data.as_ref(),
            vtable,
            lifetime,
        },
        Value::Future { body } => ValueView::Future { body },
    }
}

fn payload_view(payload: &EnumPayload) -> EnumPayloadView<'_> {
    match payload {
        EnumPayload::Unit => EnumPayloadView::Unit,
        EnumPayload::Tuple(values) => EnumPayloadView::Tuple(values),
        EnumPayload::Struct(fields) => EnumPayloadView::Struct(fields),
    }
}
