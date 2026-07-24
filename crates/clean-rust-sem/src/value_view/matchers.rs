// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::values::VtablePtr;

#[must_use]
pub fn matches(value: &Value, pattern: &ValuePattern) -> bool {
    match pattern {
        ValuePattern::Any => true,
        ValuePattern::IsUnit => matches!(value, Value::Unit),
        ValuePattern::IsBool(expected) => {
            matches!(value, Value::Bool(actual) if actual == expected)
        }
        ValuePattern::IsChar(expected) => {
            matches!(value, Value::Char(actual) if actual == expected)
        }
        ValuePattern::IsStr(expected) => matches!(value, Value::Str(actual) if actual == expected),
        ValuePattern::IsUint(expected) => {
            matches!(value, Value::Uint { value: actual, .. } if actual == expected)
        }
        ValuePattern::IsUintOfType {
            value: expected,
            ty,
        } => {
            matches!(value, Value::Uint { value: actual, ty: actual_ty } if actual == expected && actual_ty == ty)
        }
        ValuePattern::IsInt(expected) => match value {
            Value::Int { value: actual, .. } => i64::try_from(*actual).ok() == Some(*expected),
            _ => false,
        },
        ValuePattern::IsIntOfType {
            value: expected,
            ty,
        } => {
            matches!(value, Value::Int { value: actual, ty: actual_ty } if actual == expected && actual_ty == ty)
        }
        ValuePattern::IsFloatBits { bits, ty } => {
            matches!(value, Value::Float { bits: actual_bits, ty: actual_ty } if actual_bits == bits && actual_ty == ty)
        }
        ValuePattern::IsRef { mutability, inner } => match value {
            Value::Reference {
                mutability: actual_mutability,
                referent,
                ..
            } => {
                mutability.is_none_or(|expected| expected == *actual_mutability)
                    && match inner {
                        None => true,
                        Some(pattern) => referent
                            .as_deref()
                            .is_some_and(|referent| matches(referent, pattern)),
                    }
            }
            _ => false,
        },
        ValuePattern::IsRawPtr { mutability } => match value {
            Value::RawPtr {
                mutability: actual_mutability,
                ..
            } => mutability.is_none_or(|expected| expected == *actual_mutability),
            _ => false,
        },
        ValuePattern::IsCell { inner } => match value {
            Value::Cell { value, .. } => matches(value.as_ref(), inner),
            _ => false,
        },
        ValuePattern::IsRefCell { inner, borrow } => match value {
            Value::RefCell {
                value: inner_value,
                borrow: actual_borrow,
                ..
            } => {
                matches(inner_value.as_ref(), inner)
                    && borrow
                        .as_ref()
                        .is_none_or(|pattern| matches_ref_cell_borrow(actual_borrow, pattern))
            }
            _ => false,
        },
        ValuePattern::IsUnsafeCell { inner } => match value {
            Value::UnsafeCell { value, .. } => matches(value.as_ref(), inner),
            _ => false,
        },
        ValuePattern::IsRefCellRef { inner } => match value {
            Value::RefCellRef { value, .. } => matches(value.as_ref(), inner),
            _ => false,
        },
        ValuePattern::IsRefCellRefMut { inner } => match value {
            Value::RefCellRefMut { value, .. } => matches(value.as_ref(), inner),
            _ => false,
        },
        ValuePattern::IsFatPtr { data, metadata } => match value {
            Value::FatPtr(FatPointer {
                data_pointer: inner,
                metadata: actual_metadata,
            }) => {
                matches(inner.as_ref(), data)
                    && metadata
                        .as_ref()
                        .is_none_or(|pattern| matches_fat_ptr_metadata(actual_metadata, pattern))
            }
            _ => false,
        },
        ValuePattern::IsOrdering(expected) => {
            matches!(value, Value::Ordering(actual) if actual == expected)
        }
        ValuePattern::IsAtomic { inner } => match value {
            Value::Atomic { inner: actual } => matches(actual.as_ref(), inner),
            _ => false,
        },
        ValuePattern::IsTuple(patterns) => match value {
            Value::Tuple(values) => match_sequence(values, patterns),
            _ => false,
        },
        ValuePattern::IsRange {
            start,
            end,
            inclusive,
        } => match value {
            Value::Range {
                start: actual_start,
                end: actual_end,
                inclusive: actual_inclusive,
            } => {
                inclusive.is_none_or(|expected| expected == *actual_inclusive)
                    && matches_value_slot(actual_start.as_deref(), start)
                    && matches_value_slot(actual_end.as_deref(), end)
            }
            _ => false,
        },
        ValuePattern::IsArray(patterns) => match value {
            Value::Array(values) => match_sequence(values, patterns),
            _ => false,
        },
        ValuePattern::IsStruct { name, fields } => match value {
            Value::Struct {
                name: actual_name,
                fields: actual_fields,
            } => actual_name == name && match_named_fields(actual_fields, fields),
            _ => false,
        },
        ValuePattern::IsEnum {
            name,
            variant,
            payload,
        } => match value {
            Value::Enum {
                name: actual_name,
                variant: actual_variant,
                payload: actual_payload,
            } => {
                actual_name == name
                    && actual_variant == variant
                    && payload.as_ref().is_none_or(|pattern| {
                        matches_enum_payload(actual_payload.as_ref(), pattern)
                    })
            }
            _ => false,
        },
        ValuePattern::IsUnion {
            name,
            active_field,
            value: pattern_value,
        } => match value {
            Value::Union {
                name: actual_name,
                active_field: actual_field,
                value: actual_value,
            } => {
                actual_name == name
                    && actual_field == active_field
                    && pattern_value
                        .as_ref()
                        .is_none_or(|pattern| matches(actual_value.as_ref(), pattern))
            }
            _ => false,
        },
        ValuePattern::IsFnPtr { name } => {
            matches!(value, Value::FnPtr { name: actual } if actual == name)
        }
        ValuePattern::IsClosure { fn_id, captures } => match value {
            Value::Closure {
                fn_id: actual_fn_id,
                captures: actual_captures,
                ..
            } => {
                fn_id
                    .as_ref()
                    .is_none_or(|expected| expected == actual_fn_id)
                    && captures.iter().all(|(capture_name, pattern)| {
                        actual_captures
                            .iter()
                            .enumerate()
                            .find(|(index, (actual_name, _, _))| {
                                capture_name_matches(*index, actual_name, capture_name)
                            })
                            .is_some_and(|(_, (_, value, _))| matches(value, pattern))
                    })
            }
            _ => false,
        },
        ValuePattern::IsNever => matches!(value, Value::Never),
        ValuePattern::IsUninit => matches!(value, Value::Uninit),
        ValuePattern::IsTraitObject { trait_name, data } => match value {
            Value::TraitObject {
                data: actual_data,
                vtable,
                ..
            } => {
                trait_name
                    .as_ref()
                    .is_none_or(|expected| expected == &vtable.trait_name)
                    && data
                        .as_ref()
                        .is_none_or(|pattern| matches(actual_data.as_ref(), pattern))
            }
            _ => false,
        },
        ValuePattern::IsFuture => matches!(value, Value::Future { .. }),
    }
}

#[must_use]
pub fn extract<'a>(value: &'a Value, path: &[ValueAccessor]) -> Option<&'a Value> {
    let mut current = value;

    for accessor in path {
        current = match accessor {
            ValueAccessor::Deref => match current {
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
                | Value::TraitObject { data: referent, .. } => referent.as_ref(),
                _ => return None,
            },
            ValueAccessor::Inner => match current {
                Value::Cell { value, .. }
                | Value::RefCell { value, .. }
                | Value::UnsafeCell { value, .. }
                | Value::Mutex { value, .. }
                | Value::RwLock { value, .. }
                | Value::Atomic { inner: value }
                | Value::Union { value, .. } => value.as_ref(),
                Value::OnceCell { value, .. } | Value::OnceLock { value, .. } => {
                    value.as_deref()?
                }
                _ => return None,
            },
            ValueAccessor::Field(name) => match current {
                Value::Struct { fields, .. } => fields.get(name)?,
                Value::Enum { payload, .. } => match payload.as_ref() {
                    EnumPayload::Struct(fields) => fields.get(name)?,
                    _ => return None,
                },
                Value::Union {
                    active_field,
                    value,
                    ..
                } if active_field == name => value.as_ref(),
                Value::Closure { captures, .. } => captures
                    .iter()
                    .enumerate()
                    .find(|(index, (capture_name, _, _))| {
                        capture_name_matches(*index, capture_name, name)
                    })
                    .map(|(_, (_, value, _))| value)?,
                _ => return None,
            },
            ValueAccessor::Index(index) => match current {
                Value::Tuple(values) | Value::Array(values) => values.get(*index)?,
                Value::Enum { payload, .. } => match payload.as_ref() {
                    EnumPayload::Tuple(values) => values.get(*index)?,
                    _ => return None,
                },
                Value::Closure { captures, .. } => {
                    captures.get(*index).map(|(_, value, _)| value)?
                }
                _ => return None,
            },
            ValueAccessor::Start => match current {
                Value::Range { start, .. } => start.as_deref()?,
                _ => return None,
            },
            ValueAccessor::End => match current {
                Value::Range { end, .. } => end.as_deref()?,
                _ => return None,
            },
        };
    }

    Some(current)
}

fn match_sequence(values: &[Value], patterns: &[ValuePattern]) -> bool {
    values.len() == patterns.len()
        && values
            .iter()
            .zip(patterns)
            .all(|(value, pattern)| matches(value, pattern))
}

fn match_named_fields(
    fields: &BTreeMap<String, Value>,
    patterns: &[(String, ValuePattern)],
) -> bool {
    patterns.iter().all(|(name, pattern)| {
        fields
            .get(name)
            .is_some_and(|value| matches(value, pattern))
    })
}

fn matches_value_slot(value: Option<&Value>, pattern: &ValueSlotPattern) -> bool {
    match pattern {
        ValueSlotPattern::Any => true,
        ValueSlotPattern::None => value.is_none(),
        ValueSlotPattern::Some(pattern) => value.is_some_and(|value| matches(value, pattern)),
    }
}

fn matches_enum_payload(payload: &EnumPayload, pattern: &EnumPayloadPattern) -> bool {
    match pattern {
        EnumPayloadPattern::Any => true,
        EnumPayloadPattern::Unit => matches!(payload, EnumPayload::Unit),
        EnumPayloadPattern::Tuple(patterns) => match payload {
            EnumPayload::Tuple(values) => match_sequence(values, patterns),
            _ => false,
        },
        EnumPayloadPattern::Struct(patterns) => match payload {
            EnumPayload::Struct(fields) => match_named_fields(fields, patterns),
            _ => false,
        },
    }
}

fn matches_ref_cell_borrow(borrow: &RefCellBorrowState, pattern: &RefCellBorrowPattern) -> bool {
    match (borrow, pattern) {
        (RefCellBorrowState::Unborrowed, RefCellBorrowPattern::Unborrowed) => true,
        (
            RefCellBorrowState::Shared {
                count: actual_count,
            },
            RefCellBorrowPattern::Shared { count },
        ) => count.is_none_or(|expected| expected == *actual_count),
        (RefCellBorrowState::Mutable, RefCellBorrowPattern::Mutable) => true,
        _ => false,
    }
}

fn matches_fat_ptr_metadata(metadata: &FatPtrMetadata, pattern: &FatPtrMetadataPattern) -> bool {
    match (metadata, pattern) {
        (_, FatPtrMetadataPattern::Any) => true,
        (
            FatPtrMetadata::VtablePtr(VtablePtr {
                trait_name: actual_name,
            }),
            FatPtrMetadataPattern::VTable { trait_name },
        ) => trait_name
            .as_ref()
            .is_none_or(|expected| expected == actual_name),
        (FatPtrMetadata::SliceLen(actual_len), FatPtrMetadataPattern::Length(expected_len)) => {
            actual_len == expected_len
        }
        _ => false,
    }
}

fn capture_name_matches(index: usize, actual_name: &str, expected_name: &str) -> bool {
    if actual_name.is_empty() {
        expected_name == index.to_string()
    } else {
        actual_name == expected_name
    }
}
