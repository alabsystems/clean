// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl ValueView {
    /// Collect all scalar leaves reachable from this view.
    pub fn flatten(&self) -> Vec<Value> {
        match self {
            Self::Scalar(value) => vec![value.clone()],
            Self::Aggregate(fields) => fields.iter().flat_map(|(_, view)| view.flatten()).collect(),
            Self::Variant(_, payload) | Self::Reference(payload) => payload.flatten(),
            Self::Collection(values) => values.iter().flat_map(ValueView::flatten).collect(),
            Self::Opaque(_) => Vec::new(),
        }
    }
}

impl Value {
    /// Create a u8 value.
    pub fn u8(v: u8) -> Self {
        Value::Uint {
            value: v as u128,
            ty: UintType::U8,
        }
    }

    /// Create a u16 value.
    pub fn u16(v: u16) -> Self {
        Value::Uint {
            value: v as u128,
            ty: UintType::U16,
        }
    }

    /// Create a u32 value.
    pub fn u32(v: u32) -> Self {
        Value::Uint {
            value: v as u128,
            ty: UintType::U32,
        }
    }

    /// Create a u64 value.
    pub fn u64(v: u64) -> Self {
        Value::Uint {
            value: v as u128,
            ty: UintType::U64,
        }
    }

    /// Create a usize value.
    pub fn usize(v: usize) -> Self {
        Value::Uint {
            value: v as u128,
            ty: UintType::Usize,
        }
    }

    /// Create an i32 value.
    pub fn i32(v: i32) -> Self {
        Value::Int {
            value: v as i128,
            ty: IntType::I32,
        }
    }

    /// Create an i64 value.
    pub fn i64(v: i64) -> Self {
        Value::Int {
            value: v as i128,
            ty: IntType::I64,
        }
    }

    /// Create an f64 value.
    pub fn f64(v: f64) -> Self {
        Value::Float {
            bits: v.to_bits(),
            ty: FloatType::F64,
        }
    }

    /// Create an f32 value.
    pub fn f32(v: f32) -> Self {
        Value::Float {
            bits: u64::from(v.to_bits()),
            ty: FloatType::F32,
        }
    }

    fn aggregate_fields<I>(fields: I) -> ValueView
    where
        I: IntoIterator<Item = (String, ValueView)>,
    {
        ValueView::Aggregate(fields.into_iter().collect())
    }

    fn tuple_view_fields(values: &[Value]) -> ValueView {
        Self::aggregate_fields(
            values
                .iter()
                .enumerate()
                .map(|(idx, value)| (idx.to_string(), value.view())),
        )
    }

    fn named_view_fields(fields: &BTreeMap<String, Value>) -> ValueView {
        Self::aggregate_fields(
            fields
                .iter()
                .map(|(name, value)| (name.clone(), value.view())),
        )
    }

    fn option_view(value: Option<&Value>) -> ValueView {
        match value {
            Some(value) => ValueView::Variant("Some".to_string(), Box::new(value.view())),
            None => ValueView::Variant(
                "None".to_string(),
                Box::new(ValueView::Aggregate(Vec::new())),
            ),
        }
    }

    fn enum_payload_view(payload: &EnumPayload) -> ValueView {
        match payload {
            EnumPayload::Unit => ValueView::Aggregate(Vec::new()),
            EnumPayload::Tuple(values) => Self::tuple_view_fields(values),
            EnumPayload::Struct(fields) => Self::named_view_fields(fields),
        }
    }

    fn borrow_state_view(borrow: &RefCellBorrowState) -> ValueView {
        match borrow {
            RefCellBorrowState::Unborrowed => ValueView::Variant(
                "Unborrowed".to_string(),
                Box::new(ValueView::Aggregate(Vec::new())),
            ),
            RefCellBorrowState::Shared { count } => ValueView::Variant(
                "Shared".to_string(),
                Box::new(ValueView::Scalar(Value::usize(*count))),
            ),
            RefCellBorrowState::Mutable => ValueView::Variant(
                "Mutable".to_string(),
                Box::new(ValueView::Aggregate(Vec::new())),
            ),
        }
    }

    fn fat_ptr_metadata_view(metadata: &FatPtrMetadata) -> ValueView {
        match metadata {
            FatPtrMetadata::VtablePtr(vtable_ptr) => ValueView::Variant(
                "VtablePtr".to_string(),
                Box::new(ValueView::Opaque(vtable_ptr.trait_name.clone())),
            ),
            FatPtrMetadata::SliceLen(len) => ValueView::Variant(
                "SliceLen".to_string(),
                Box::new(ValueView::Scalar(Value::usize(*len))),
            ),
        }
    }

    fn reference_opaque_label(kind: &str, addr: &Address) -> String {
        format!("{kind}@{:?}", addr)
    }

    /// Convert this runtime value into a verification-facing structural view.
    pub fn view(&self) -> ValueView {
        match self {
            Value::Unit => ValueView::Aggregate(Vec::new()),
            Value::Bool(_)
            | Value::Char(_)
            | Value::Uint { .. }
            | Value::Int { .. }
            | Value::Float { .. } => ValueView::Scalar(self.clone()),
            Value::Str(value) => ValueView::Collection(
                value
                    .chars()
                    .map(|ch| ValueView::Scalar(Value::Char(ch)))
                    .collect(),
            ),
            Value::Reference { addr, referent, .. } => referent.as_deref().map_or_else(
                || ValueView::Opaque(Self::reference_opaque_label("ref", addr)),
                |referent| ValueView::Reference(Box::new(referent.view())),
            ),
            Value::RawPtr { addr, .. } => {
                ValueView::Opaque(Self::reference_opaque_label("raw_ptr", addr))
            }
            Value::Cell { value, .. } => {
                Self::aggregate_fields([("value".to_string(), value.view())])
            }
            Value::RefCell { value, borrow, .. } => Self::aggregate_fields([
                ("value".to_string(), value.view()),
                ("borrow".to_string(), Self::borrow_state_view(borrow)),
            ]),
            Value::UnsafeCell { value, .. } => {
                Self::aggregate_fields([("value".to_string(), value.view())])
            }
            Value::OnceCell { value, .. } | Value::OnceLock { value, .. } => {
                Self::aggregate_fields([("value".to_string(), Self::option_view(value.as_deref()))])
            }
            Value::Mutex {
                value,
                locked,
                poisoned,
                ..
            } => Self::aggregate_fields([
                ("value".to_string(), value.view()),
                (
                    "locked".to_string(),
                    ValueView::Scalar(Value::Bool(*locked)),
                ),
                (
                    "poisoned".to_string(),
                    ValueView::Scalar(Value::Bool(*poisoned)),
                ),
            ]),
            Value::RwLock {
                value,
                reader_count,
                writer_locked,
                poisoned,
                ..
            } => Self::aggregate_fields([
                ("value".to_string(), value.view()),
                (
                    "reader_count".to_string(),
                    ValueView::Scalar(Value::usize(*reader_count)),
                ),
                (
                    "writer_locked".to_string(),
                    ValueView::Scalar(Value::Bool(*writer_locked)),
                ),
                (
                    "poisoned".to_string(),
                    ValueView::Scalar(Value::Bool(*poisoned)),
                ),
            ]),
            Value::RefCellRef { value, .. }
            | Value::RefCellRefMut { value, .. }
            | Value::MutexGuard { value, .. }
            | Value::RwLockReadGuard { value, .. }
            | Value::RwLockWriteGuard { value, .. } => ValueView::Reference(Box::new(value.view())),
            Value::FatPtr(FatPointer {
                data_pointer,
                metadata,
            }) => Self::aggregate_fields([
                ("data_pointer".to_string(), data_pointer.view()),
                (
                    "metadata".to_string(),
                    Self::fat_ptr_metadata_view(metadata),
                ),
            ]),
            Value::Ordering(ordering) => ValueView::Variant(
                format!("{ordering:?}"),
                Box::new(ValueView::Aggregate(Vec::new())),
            ),
            Value::Atomic { inner } => {
                Self::aggregate_fields([("inner".to_string(), inner.view())])
            }
            Value::Tuple(values) => Self::tuple_view_fields(values),
            Value::Range {
                start,
                end,
                inclusive,
            } => Self::aggregate_fields([
                ("start".to_string(), Self::option_view(start.as_deref())),
                ("end".to_string(), Self::option_view(end.as_deref())),
                (
                    "inclusive".to_string(),
                    ValueView::Scalar(Value::Bool(*inclusive)),
                ),
            ]),
            Value::Array(values) => ValueView::Collection(values.iter().map(Value::view).collect()),
            Value::Struct { fields, .. } => Self::named_view_fields(fields),
            Value::Enum {
                variant, payload, ..
            } => ValueView::Variant(
                variant.clone(),
                Box::new(Self::enum_payload_view(payload.as_ref())),
            ),
            Value::Union {
                active_field,
                value,
                ..
            } => ValueView::Variant(active_field.clone(), Box::new(value.view())),
            Value::FnPtr { name } => ValueView::Opaque(format!("fn_ptr:{name}")),
            Value::Closure {
                fn_id, captures, ..
            } => {
                if captures.is_empty() {
                    ValueView::Opaque(format!("closure:{fn_id}"))
                } else {
                    Self::aggregate_fields(captures.iter().enumerate().map(
                        |(idx, (name, value, _))| {
                            let field_name = if name.is_empty() {
                                idx.to_string()
                            } else {
                                name.clone()
                            };
                            (field_name, value.view())
                        },
                    ))
                }
            }
            Value::Never => ValueView::Opaque("never".to_string()),
            Value::Uninit => ValueView::Opaque("uninit".to_string()),
            Value::TraitObject { data, vtable, .. } => Self::aggregate_fields([
                ("data".to_string(), data.view()),
                (
                    "trait".to_string(),
                    ValueView::Opaque(vtable.trait_name.clone()),
                ),
                (
                    "concrete_type".to_string(),
                    ValueView::Opaque(vtable.concrete_type.clone()),
                ),
            ]),
            Value::Future { .. } => ValueView::Opaque("future".to_string()),
        }
    }

    /// Check if value is uninitialized.
    pub fn is_uninit(&self) -> bool {
        matches!(self, Value::Uninit)
    }

    /// Check if value is zero/default.
    pub fn is_zero(&self) -> bool {
        match self {
            Value::Atomic { inner } => inner.is_zero(),
            Value::Bool(false)
            | Value::Uint { value: 0, .. }
            | Value::Int { value: 0, .. }
            | Value::Float { bits: 0, .. } => true,
            _ => false,
        }
    }
}
