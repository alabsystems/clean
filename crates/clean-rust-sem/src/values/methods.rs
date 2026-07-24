// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Value {
    /// Recover the runtime slice length when available.
    pub fn slice_len(&self) -> Option<usize> {
        match self {
            Value::Str(text) => Some(text.len()),
            Value::Array(values) => Some(values.len()),
            Value::FatPtr(FatPointer {
                metadata: FatPtrMetadata::SliceLen(len),
                ..
            }) => Some(*len),
            _ => None,
        }
    }

    fn range_rust_type(start: Option<&Value>, end: Option<&Value>, inclusive: bool) -> RustType {
        let element_ty = start.or(end).map_or(RustType::Unit, Value::get_type);
        RustType::Named {
            name: if inclusive {
                "std::ops::RangeInclusive".to_string()
            } else {
                "std::ops::Range".to_string()
            },
            type_args: vec![element_ty],
            lifetime_args: vec![],
            const_args: vec![],
        }
    }

    fn fat_ptr_type(fat_ptr: &FatPointer) -> RustType {
        match (&fat_ptr.metadata, fat_ptr.data_pointer.get_type()) {
            (
                FatPtrMetadata::VtablePtr(vtable_ptr),
                RustType::Reference {
                    lifetime,
                    mutability,
                    ..
                },
            ) => RustType::Reference {
                lifetime,
                mutability,
                inner: Box::new(Self::dyn_trait_type(vtable_ptr.trait_name.clone())),
            },
            (FatPtrMetadata::VtablePtr(vtable_ptr), RustType::RawPtr { mutability, .. }) => {
                RustType::RawPtr {
                    mutability,
                    inner: Box::new(Self::dyn_trait_type(vtable_ptr.trait_name.clone())),
                }
            }
            (FatPtrMetadata::VtablePtr(vtable_ptr), _) => RustType::Box {
                inner: Box::new(Self::dyn_trait_type(vtable_ptr.trait_name.clone())),
            },
            (
                FatPtrMetadata::SliceLen(_),
                RustType::Reference {
                    lifetime,
                    mutability,
                    inner,
                },
            ) => RustType::Reference {
                lifetime,
                mutability,
                inner: Box::new(Self::slice_type_from_inner(*inner)),
            },
            (FatPtrMetadata::SliceLen(_), RustType::RawPtr { mutability, inner }) => {
                RustType::RawPtr {
                    mutability,
                    inner: Box::new(Self::slice_type_from_inner(*inner)),
                }
            }
            (FatPtrMetadata::SliceLen(_), inner) => RustType::Box {
                inner: Box::new(Self::slice_type_from_inner(inner)),
            },
        }
    }

    /// Get the type of this value.
    pub fn get_type(&self) -> RustType {
        match self {
            Value::Bool(_) => RustType::Bool,
            Value::Char(_) => RustType::Char,
            Value::Str(_) => RustType::Str,
            Value::Uint { ty, .. } => RustType::Uint(*ty),
            Value::Int { ty, .. } => RustType::Int(*ty),
            Value::Float { ty, .. } => RustType::Float(*ty),
            Value::Reference {
                mutability,
                lifetime,
                referent,
                ..
            } => RustType::Reference {
                lifetime: lifetime.clone(),
                mutability: *mutability,
                inner: Box::new(referent.as_deref().map_or(RustType::Unit, Value::get_type)),
            },
            Value::RawPtr { mutability, .. } => RustType::RawPtr {
                mutability: *mutability,
                inner: Box::new(RustType::Unit),
            },
            Value::Cell { value, .. } => RustType::Cell {
                inner: Box::new(value.get_type()),
            },
            Value::RefCell { value, .. } => RustType::RefCell {
                inner: Box::new(value.get_type()),
            },
            Value::UnsafeCell { value, .. } => RustType::UnsafeCell {
                inner: Box::new(value.get_type()),
            },
            Value::OnceCell { value, .. } => RustType::Named {
                name: "OnceCell".to_string(),
                type_args: vec![value.as_deref().map_or(RustType::Unit, Value::get_type)],
                lifetime_args: vec![],
                const_args: vec![],
            },
            Value::OnceLock { value, .. } => RustType::Named {
                name: "OnceLock".to_string(),
                type_args: vec![value.as_deref().map_or(RustType::Unit, Value::get_type)],
                lifetime_args: vec![],
                const_args: vec![],
            },
            Value::Mutex { value, .. } => RustType::Named {
                name: "Mutex".to_string(),
                type_args: vec![value.get_type()],
                lifetime_args: vec![],
                const_args: vec![],
            },
            Value::MutexGuard { value, .. } => RustType::Named {
                name: "MutexGuard".to_string(),
                type_args: vec![value.get_type()],
                lifetime_args: vec![],
                const_args: vec![],
            },
            Value::RwLock { value, .. } => RustType::Named {
                name: "RwLock".to_string(),
                type_args: vec![value.get_type()],
                lifetime_args: vec![],
                const_args: vec![],
            },
            Value::RwLockReadGuard { value, .. } => RustType::Named {
                name: "RwLockReadGuard".to_string(),
                type_args: vec![value.get_type()],
                lifetime_args: vec![],
                const_args: vec![],
            },
            Value::RwLockWriteGuard { value, .. } => RustType::Named {
                name: "RwLockWriteGuard".to_string(),
                type_args: vec![value.get_type()],
                lifetime_args: vec![],
                const_args: vec![],
            },
            Value::RefCellRef { value, .. } => RustType::Named {
                name: "Ref".to_string(),
                type_args: vec![value.get_type()],
                lifetime_args: vec![],
                const_args: vec![],
            },
            Value::RefCellRefMut { value, .. } => RustType::Named {
                name: "RefMut".to_string(),
                type_args: vec![value.get_type()],
                lifetime_args: vec![],
                const_args: vec![],
            },
            Value::FatPtr(fat_ptr) => Self::fat_ptr_type(fat_ptr),
            Value::Ordering(_) => RustType::Named {
                name: "Ordering".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
            Value::Atomic { inner } => RustType::Atomic {
                inner: Box::new(inner.get_type()),
            },
            Value::Tuple(elems) => RustType::Tuple(elems.iter().map(Value::get_type).collect()),
            Value::Range {
                start,
                end,
                inclusive,
            } => Self::range_rust_type(start.as_deref(), end.as_deref(), *inclusive),
            Value::Array(elems) => {
                let elem_ty = elems.first().map_or(RustType::Unit, Value::get_type);
                RustType::Array {
                    element: Box::new(elem_ty),
                    len: crate::types::ConstGenericArg::usize(elems.len()),
                }
            }
            Value::Struct { name, .. } | Value::Enum { name, .. } | Value::Union { name, .. } => {
                RustType::Named {
                    name: name.clone(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                }
            }
            Value::FnPtr { .. } => RustType::Function {
                params: vec![],
                ret: Box::new(RustType::Unit),
            },
            Value::Closure {
                param_types,
                ret_type,
                captures,
                kind,
                ..
            } => RustType::Closure {
                params: param_types.clone(),
                ret: Box::new(ret_type.clone()),
                captures: captures
                    .iter()
                    .map(|(name, val, mutability)| (name.clone(), val.get_type(), *mutability))
                    .collect(),
                kind: *kind,
            },
            Value::Never => RustType::Never,
            Value::Unit | Value::Uninit => RustType::Unit,
            Value::TraitObject { vtable, .. } => RustType::DynTrait {
                trait_name: vtable.trait_name.clone(),
                auto_traits: vec![],
            },
            Value::Future { .. } => RustType::ImplTrait {
                traits: vec!["Future".to_string()],
            },
        }
    }

    /// Get the concrete type name for named values (structs/enums).
    pub fn concrete_type_name(&self) -> Option<&str> {
        match self.deref_view() {
            Value::Struct { name, .. } | Value::Enum { name, .. } => Some(name.as_str()),
            _ => None,
        }
    }

    /// Follow preserved reference payloads until reaching the concrete referent.
    pub fn deref_view(&self) -> &Value {
        let mut current = self;
        loop {
            match current {
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
                | Value::TraitObject { data: referent, .. } => {
                    current = referent.as_ref();
                }
                Value::FatPtr(FatPointer { data_pointer, .. }) => {
                    current = data_pointer.as_ref();
                }
                _ => return current,
            }
        }
    }

    fn dyn_trait_type(trait_name: String) -> RustType {
        RustType::DynTrait {
            trait_name,
            auto_traits: vec![],
        }
    }

    fn slice_type_from_inner(inner: RustType) -> RustType {
        match inner {
            RustType::Array { element, .. } => RustType::Slice { elem: element },
            RustType::Slice { elem } => RustType::Slice { elem },
            other => RustType::Slice {
                elem: Box::new(other),
            },
        }
    }

    /// Try to convert to bool.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            Value::Atomic { inner } => inner.as_bool(),
            _ => None,
        }
    }

    /// Try to convert to u64, returning None if the value doesn't fit.
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Value::Uint { value, .. } => u64::try_from(*value).ok(),
            Value::Atomic { inner } => inner.as_u64(),
            _ => None,
        }
    }

    /// Try to convert to i64, returning None if the value doesn't fit.
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Value::Int { value, .. } => i64::try_from(*value).ok(),
            Value::Atomic { inner } => inner.as_i64(),
            _ => None,
        }
    }

    /// Try to convert to f64.
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Value::Float { bits, ty } => match ty {
                FloatType::F64 => Some(f64::from_bits(*bits)),
                #[allow(clippy::cast_possible_truncation)]
                FloatType::F32 => Some(f32::from_bits(*bits as u32) as f64),
            },
            Value::Atomic { inner } => inner.as_f64(),
            _ => None,
        }
    }
}
