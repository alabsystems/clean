// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C Type System Formalization
//!
//! This module defines the C type system following the C11 standard.
//! Types are fundamental for memory layout, alignment, and value representation.
//!
//! ## Type Categories
//!
//! 1. **Integer Types**: char, short, int, long, long long (signed/unsigned)
//! 2. **Floating Types**: float, double, long double
//! 3. **Pointer Types**: T* for any complete type T
//! 4. **Array Types**: `T[N]` for fixed-size arrays
//! 5. **Struct Types**: struct { ... }
//! 6. **Union Types**: union { ... }
//! 7. **Enum Types**: enum { ... }
//! 8. **Function Types**: T(T1, T2, ...) -> T
//! 9. **Void**: void (incomplete type)
//!
//! ## Data Model
//!
//! We use the LP64 data model (common on 64-bit Unix):
//! - char: 1 byte
//! - short: 2 bytes
//! - int: 4 bytes
//! - long: 8 bytes
//! - long long: 8 bytes
//! - pointer: 8 bytes
//!
//! ## Alignment
//!
//! Alignment follows C11 rules:
//! - Natural alignment for primitives
//! - Struct alignment is max of member alignments
//! - Arrays have element alignment

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Constraint violations on a struct's flexible array member (C99 6.7.2.1p18).
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum FlexibleArrayError {
    /// A flexible array member (`T[]`) appeared somewhere other than as the
    /// final member of the struct.
    #[error("flexible array member '{name}' must be the last member of the struct")]
    NotLast {
        /// Name of the offending flexible array member.
        name: String,
    },

    /// A struct's only member is a flexible array member. A struct with a
    /// flexible array member must have at least one other named member.
    #[error("a struct with a flexible array member must have at least one other member")]
    SoleMember,

    /// A flexible array member appeared outside of a struct (e.g. in a union
    /// or as a non-final aggregate member). Only structs may contain one.
    #[error("flexible array member '{name}' is only permitted as the last member of a struct")]
    NotInStruct {
        /// Name of the offending flexible array member.
        name: String,
    },
}

/// Integer kinds in C
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum IntKind {
    /// char (1 byte)
    Char,
    /// short (2 bytes)
    Short,
    /// int (4 bytes)
    Int,
    /// long (8 bytes on LP64)
    Long,
    /// long long (8 bytes)
    LongLong,
    /// _Bool / bool (1 byte, C99+)
    Bool,
}

impl IntKind {
    /// Size in bytes (LP64 model)
    pub fn size(&self) -> usize {
        match self {
            IntKind::Bool | IntKind::Char => 1,
            IntKind::Short => 2,
            IntKind::Int => 4,
            IntKind::Long | IntKind::LongLong => 8,
        }
    }

    /// Alignment in bytes
    pub fn align(&self) -> usize {
        self.size()
    }

    /// Minimum value for signed variant
    pub fn signed_min(&self) -> i128 {
        match self {
            IntKind::Bool => 0,
            IntKind::Char => i8::MIN as i128,
            IntKind::Short => i16::MIN as i128,
            IntKind::Int => i32::MIN as i128,
            IntKind::Long | IntKind::LongLong => i64::MIN as i128,
        }
    }

    /// Maximum value for signed variant
    pub fn signed_max(&self) -> i128 {
        match self {
            IntKind::Bool => 1,
            IntKind::Char => i8::MAX as i128,
            IntKind::Short => i16::MAX as i128,
            IntKind::Int => i32::MAX as i128,
            IntKind::Long | IntKind::LongLong => i64::MAX as i128,
        }
    }

    /// Maximum value for unsigned variant
    pub fn unsigned_max(&self) -> u128 {
        match self {
            IntKind::Bool => 1,
            IntKind::Char => u8::MAX as u128,
            IntKind::Short => u16::MAX as u128,
            IntKind::Int => u32::MAX as u128,
            IntKind::Long | IntKind::LongLong => u64::MAX as u128,
        }
    }
}

/// Floating-point kinds in C
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum FloatKind {
    /// float (4 bytes)
    Float,
    /// double (8 bytes)
    Double,
    /// long double (16 bytes on most platforms)
    LongDouble,
}

impl FloatKind {
    /// Size in bytes
    pub fn size(&self) -> usize {
        match self {
            FloatKind::Float => 4,
            FloatKind::Double => 8,
            FloatKind::LongDouble => 16,
        }
    }

    /// Alignment in bytes
    pub fn align(&self) -> usize {
        self.size().min(16) // Max alignment is typically 16
    }
}

/// Signedness of integer types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Signedness {
    Signed,
    Unsigned,
}

/// A field in a struct or union
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct StructField {
    pub name: String,
    pub ty: CType,
    /// Bit-field width in bits, if this member is a bit-field
    /// (`unsigned a : 3;`). `None` for ordinary members. A width of `Some(0)`
    /// denotes an unnamed zero-width bit-field, which forces alignment of the
    /// next bit-field to the next storage unit (C11 6.7.2.1p12).
    pub bit_width: Option<usize>,
}

impl StructField {
    /// Construct an ordinary (non bit-field) struct/union member.
    pub fn new(name: impl Into<String>, ty: CType) -> Self {
        Self {
            name: name.into(),
            ty,
            bit_width: None,
        }
    }

    /// Construct a bit-field member with the given declared width in bits.
    pub fn bitfield(name: impl Into<String>, ty: CType, bit_width: usize) -> Self {
        Self {
            name: name.into(),
            ty,
            bit_width: Some(bit_width),
        }
    }

    /// Is this member a bit-field (including a zero-width separator)?
    pub fn is_bitfield(&self) -> bool {
        self.bit_width.is_some()
    }
}

/// Placement of a single bit-field within its storage unit.
///
/// Bit offsets are counted from the least-significant bit of the storage unit
/// (the GCC layout on little-endian targets), so a field at `bit_offset = 0`
/// with `bit_width = 3` occupies bits 0..3 of the unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BitFieldPlacement {
    /// Byte offset of the storage unit holding this bit-field.
    pub byte_offset: usize,
    /// Size in bytes of the storage unit (the declared type's size).
    pub unit_bytes: usize,
    /// Offset (in bits) of the field within its storage unit.
    pub bit_offset: usize,
    /// Width of the field in bits.
    pub bit_width: usize,
}

/// Resolved layout of one struct/union member.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FieldLayout {
    /// Byte offset of the member (storage unit for bit-fields).
    pub byte_offset: usize,
    /// Bit-field placement, if this member is a (named) bit-field.
    pub bitfield: Option<BitFieldPlacement>,
}

/// Round `offset` up to the next multiple of `align` (a power of two ≥ 1).
fn align_up(offset: usize, align: usize) -> usize {
    if align <= 1 {
        return offset;
    }
    offset.div_ceil(align) * align
}

/// Compute the byte offset / bit-field placement of every member of a struct,
/// together with the total size (before trailing padding) reached after the
/// last member.
///
/// Bit-field packing follows the standard GCC-like model for the LP64 ABI
/// (C11 6.7.2.1, implementation-defined but conventional):
///
/// * Consecutive bit-fields of the same declared type pack into one storage
///   unit (of that type) until the next field would not fit, at which point a
///   new, suitably aligned unit begins.
/// * An unnamed zero-width bit-field (`unsigned : 0;`) flushes the current
///   unit so that the following bit-field starts a fresh, aligned unit.
/// * An ordinary (non bit-field) member flushes any in-progress bit-field unit
///   and is then laid out at its natural alignment.
///
/// The returned `Vec` is parallel to `fields`; entries for zero-width
/// separators carry `bitfield: None` (they occupy no addressable storage and
/// are unnamed, so they are never looked up by name).
fn struct_layout(fields: &[StructField]) -> (Vec<FieldLayout>, usize) {
    let mut layouts = Vec::with_capacity(fields.len());
    // `cursor` is the next free byte after all storage allocated so far.
    let mut cursor = 0usize;
    // Active bit-field storage unit, if any: (unit byte offset, unit bytes,
    // bits already consumed within the unit).
    let mut active_unit: Option<(usize, usize, usize)> = None;

    for field in fields {
        match field.bit_width {
            Some(width) => {
                let unit_bytes = field.ty.size().max(1);
                let unit_bits = unit_bytes * 8;

                if width == 0 {
                    // Zero-width: force the next bit-field to a new unit. No
                    // storage is allocated for the separator itself, but the
                    // cursor is aligned to the declared type so the next unit
                    // begins on that boundary.
                    cursor = align_up(cursor, field.ty.align().max(1));
                    active_unit = None;
                    layouts.push(FieldLayout {
                        byte_offset: cursor,
                        bitfield: None,
                    });
                    continue;
                }

                // Decide whether the field fits in the active unit. It does
                // only when the active unit has the same width and there is
                // room left.
                let placement = match active_unit {
                    Some((off, ubytes, used))
                        if ubytes == unit_bytes && used + width <= unit_bits =>
                    {
                        active_unit = Some((off, ubytes, used + width));
                        BitFieldPlacement {
                            byte_offset: off,
                            unit_bytes,
                            bit_offset: used,
                            bit_width: width,
                        }
                    }
                    _ => {
                        // Start a fresh storage unit aligned to the declared
                        // type.
                        let off = align_up(cursor, field.ty.align().max(1));
                        cursor = off + unit_bytes;
                        active_unit = Some((off, unit_bytes, width));
                        BitFieldPlacement {
                            byte_offset: off,
                            unit_bytes,
                            bit_offset: 0,
                            bit_width: width,
                        }
                    }
                };
                layouts.push(FieldLayout {
                    byte_offset: placement.byte_offset,
                    bitfield: Some(placement),
                });
            }
            None => {
                // Ordinary member: flush any in-progress bit-field unit.
                active_unit = None;
                let off = align_up(cursor, field.ty.align().max(1));
                cursor = off + field.ty.size();
                layouts.push(FieldLayout {
                    byte_offset: off,
                    bitfield: None,
                });
            }
        }
    }

    (layouts, cursor)
}

/// Validate the flexible-array-member constraints of a struct's field list
/// (C99 6.7.2.1p18): a flexible array member must be the last member, and the
/// struct must contain at least one other (non-flexible) member.
///
/// Returns `Ok(())` when the field list contains no flexible array member, or
/// exactly one that is the final member of a struct with another member.
fn validate_struct_flexible_array(fields: &[StructField]) -> Result<(), FlexibleArrayError> {
    let last_index = fields.len().checked_sub(1);
    for (i, field) in fields.iter().enumerate() {
        if !field.ty.is_flexible_array() {
            continue;
        }
        // A flexible array member must be the final member.
        if Some(i) != last_index {
            return Err(FlexibleArrayError::NotLast {
                name: field.name.clone(),
            });
        }
        // It cannot be the sole member: the struct needs at least one other
        // member to give the flexible array something to follow.
        if fields.len() < 2 {
            return Err(FlexibleArrayError::SoleMember);
        }
    }
    Ok(())
}

/// A function parameter
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FuncParam {
    pub name: Option<String>,
    pub ty: CType,
}

/// C Type representation
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CType {
    /// void (incomplete type)
    Void,

    /// Integer types: char, short, int, long, long long, _Bool
    Int(IntKind, Signedness),

    /// Floating-point types: float, double, long double
    Float(FloatKind),

    /// Pointer to another type: T*
    Pointer(Box<CType>),

    /// Fixed-size array: `T[N]`
    Array(Box<CType>, usize),

    /// Flexible array member / incomplete array: `T[]` (C99 6.7.2.1p18).
    ///
    /// This is an *incomplete* type: it has no known size of its own, so
    /// [`CType::is_complete`] returns `false` and `sizeof` on it is an error.
    /// As the last member of a struct it contributes 0 to the struct's size
    /// while its element alignment still participates in the struct alignment.
    IncompleteArray(Box<CType>),

    /// Struct type: struct { ... }
    Struct {
        name: Option<String>,
        fields: Vec<StructField>,
    },

    /// Union type: union { ... }
    Union {
        name: Option<String>,
        fields: Vec<StructField>,
    },

    /// Enum type: enum { ... }
    Enum {
        name: Option<String>,
        /// (name, value)
        variants: Vec<(String, i64)>,
    },

    /// Function type: T(T1, T2, ...) -> RetT
    Function {
        return_type: Box<CType>,
        params: Vec<FuncParam>,
        variadic: bool,
    },

    /// typedef reference (resolved during type checking)
    TypeDef(String),

    /// Qualified type (const, volatile, restrict)
    Qualified {
        ty: Box<CType>,
        is_const: bool,
        is_volatile: bool,
        is_restrict: bool,
    },
}

impl CType {
    /// Create a void type
    pub fn void() -> Self {
        CType::Void
    }

    /// Create a signed int type
    pub fn int() -> Self {
        CType::Int(IntKind::Int, Signedness::Signed)
    }

    /// Create an unsigned int type
    pub fn uint() -> Self {
        CType::Int(IntKind::Int, Signedness::Unsigned)
    }

    /// Create a signed char type
    pub fn char() -> Self {
        CType::Int(IntKind::Char, Signedness::Signed)
    }

    /// Create an unsigned char type
    pub fn unsigned_char() -> Self {
        CType::Int(IntKind::Char, Signedness::Unsigned)
    }

    /// Create a size_t type (unsigned long on LP64)
    pub fn size_t() -> Self {
        CType::Int(IntKind::Long, Signedness::Unsigned)
    }

    /// Create a pointer type
    pub fn ptr(inner: CType) -> Self {
        CType::Pointer(Box::new(inner))
    }

    /// Create an array type
    pub fn array(elem: CType, size: usize) -> Self {
        CType::Array(Box::new(elem), size)
    }

    /// Create a flexible array member / incomplete array type (`T[]`).
    pub fn incomplete_array(elem: CType) -> Self {
        CType::IncompleteArray(Box::new(elem))
    }

    /// Create a const-qualified type
    pub fn const_ty(ty: CType) -> Self {
        CType::Qualified {
            ty: Box::new(ty),
            is_const: true,
            is_volatile: false,
            is_restrict: false,
        }
    }

    /// Wrap `ty` in a `Qualified` node carrying the given qualifiers.
    ///
    /// If none of the qualifiers are set, `ty` is returned unchanged so that
    /// unqualified types are never wrapped in a redundant `Qualified` layer.
    /// When `ty` is already a `Qualified` type, the new qualifiers are merged
    /// (OR-ed) into the existing flags rather than nested.
    pub fn with_qualifiers(
        ty: CType,
        is_const: bool,
        is_volatile: bool,
        is_restrict: bool,
    ) -> Self {
        if !is_const && !is_volatile && !is_restrict {
            return ty;
        }
        match ty {
            CType::Qualified {
                ty,
                is_const: c,
                is_volatile: v,
                is_restrict: r,
            } => CType::Qualified {
                ty,
                is_const: is_const || c,
                is_volatile: is_volatile || v,
                is_restrict: is_restrict || r,
            },
            other => CType::Qualified {
                ty: Box::new(other),
                is_const,
                is_volatile,
                is_restrict,
            },
        }
    }

    /// Size in bytes
    ///
    /// Returns None for incomplete types (void, unsized arrays, forward decls)
    pub fn size(&self) -> usize {
        match self {
            // Incomplete types and function types have no size
            CType::Void | CType::Function { .. } => 0,

            CType::Int(kind, _) => kind.size(),

            CType::Float(kind) => kind.size(),

            CType::Pointer(_) => 8, // LP64: all pointers are 8 bytes

            CType::Array(elem, count) => elem.size() * count,

            // An incomplete array (flexible array member) has no size of its
            // own; it is an incomplete type. As a struct member it contributes
            // 0 to the enclosing struct's size (C99 6.7.2.1p18). Callers that
            // need to reject `sizeof` of an incomplete type check
            // [`CType::is_complete`] first.
            CType::IncompleteArray(_) => 0,

            CType::Struct { fields, .. } => {
                // Calculate size with padding for alignment, accounting for
                // bit-field packing.
                let (_, used) = struct_layout(fields);
                // Add trailing padding to align to struct's overall alignment.
                align_up(used, self.align())
            }

            CType::Union { fields, .. } => {
                // Union size is max of all field sizes
                fields.iter().map(|f| f.ty.size()).max().unwrap_or(0)
            }

            CType::Enum { .. } => 4, // Enums are int-sized by default

            CType::TypeDef(_) => panic!("typedef should be resolved before size calculation"),

            CType::Qualified { ty, .. } => ty.size(),
        }
    }

    /// Alignment in bytes
    pub fn align(&self) -> usize {
        match self {
            CType::Void | CType::Function { .. } => 1,

            CType::Int(kind, _) => kind.align(),

            CType::Float(kind) => kind.align(),

            CType::Pointer(_) => 8,

            CType::Array(elem, _) => elem.align(),

            // A flexible array member still imposes its element's alignment on
            // the enclosing struct (C99 6.7.2.1p18), even though it has size 0.
            CType::IncompleteArray(elem) => elem.align(),

            CType::Struct { fields, .. } => {
                // Struct alignment is max of all field alignments
                fields.iter().map(|f| f.ty.align()).max().unwrap_or(1)
            }

            CType::Union { fields, .. } => {
                // Union alignment is max of all field alignments
                fields.iter().map(|f| f.ty.align()).max().unwrap_or(1)
            }

            CType::Enum { .. } => 4,

            CType::TypeDef(_) => panic!("typedef should be resolved before alignment calculation"),

            CType::Qualified { ty, .. } => ty.align(),
        }
    }

    /// Check if type is complete (has known size)
    pub fn is_complete(&self) -> bool {
        match self {
            // A flexible array member (`T[]`) is an incomplete type: its size
            // is not known (C99 6.7.2.1p18, 6.2.5p22).
            CType::Void
            | CType::Function { .. }
            | CType::TypeDef(_)
            | CType::IncompleteArray(_) => false,
            CType::Qualified { ty, .. } => ty.is_complete(),
            CType::Array(elem, _) => elem.is_complete(),
            // A struct/union with no fields is a forward declaration
            // (`struct S;`), i.e. an incomplete type whose size is not yet
            // known (C11 6.7.2.3, 6.2.5p22). It only becomes complete once a
            // definition with members is seen.
            CType::Struct { fields, .. } | CType::Union { fields, .. } => !fields.is_empty(),
            _ => true,
        }
    }

    /// Check if type is an integer type
    pub fn is_integer(&self) -> bool {
        match self {
            CType::Int(_, _) | CType::Enum { .. } => true,
            CType::Qualified { ty, .. } => ty.is_integer(),
            _ => false,
        }
    }

    /// Check if type is a floating-point type
    pub fn is_float(&self) -> bool {
        match self {
            CType::Float(_) => true,
            CType::Qualified { ty, .. } => ty.is_float(),
            _ => false,
        }
    }

    /// Check if type is an arithmetic type (integer or float)
    pub fn is_arithmetic(&self) -> bool {
        self.is_integer() || self.is_float()
    }

    /// Check if type is a scalar type (arithmetic or pointer)
    pub fn is_scalar(&self) -> bool {
        self.is_arithmetic() || self.is_pointer()
    }

    /// Check if type is a pointer type
    pub fn is_pointer(&self) -> bool {
        match self {
            CType::Pointer(_) => true,
            CType::Qualified { ty, .. } => ty.is_pointer(),
            _ => false,
        }
    }

    /// Check if type is an array type (fixed-size or a flexible array member).
    pub fn is_array(&self) -> bool {
        match self {
            CType::Array(_, _) | CType::IncompleteArray(_) => true,
            CType::Qualified { ty, .. } => ty.is_array(),
            _ => false,
        }
    }

    /// Check if type is a flexible array member / incomplete array (`T[]`).
    pub fn is_flexible_array(&self) -> bool {
        match self {
            CType::IncompleteArray(_) => true,
            CType::Qualified { ty, .. } => ty.is_flexible_array(),
            _ => false,
        }
    }

    /// Check if type is a struct type
    pub fn is_struct(&self) -> bool {
        matches!(self, CType::Struct { .. })
    }

    /// Check if type is a union type
    pub fn is_union(&self) -> bool {
        matches!(self, CType::Union { .. })
    }

    /// Check if type is a function type
    pub fn is_function(&self) -> bool {
        matches!(self, CType::Function { .. })
    }

    /// Get the pointee type if this is a pointer
    pub fn pointee(&self) -> Option<&CType> {
        match self {
            CType::Pointer(inner) => Some(inner),
            CType::Qualified { ty, .. } => ty.pointee(),
            _ => None,
        }
    }

    /// Get the element type if this is an array (fixed-size or flexible).
    pub fn element(&self) -> Option<&CType> {
        match self {
            CType::Array(elem, _) | CType::IncompleteArray(elem) => Some(elem),
            CType::Qualified { ty, .. } => ty.element(),
            _ => None,
        }
    }

    /// Get struct field by name
    pub fn get_field(&self, name: &str) -> Option<(usize, &StructField)> {
        match self {
            CType::Struct { fields, .. } | CType::Union { fields, .. } => {
                fields.iter().enumerate().find(|(_, f)| f.name == name)
            }
            CType::Qualified { ty, .. } => ty.get_field(name),
            _ => None,
        }
    }

    /// Get field offset (in bytes) in a struct or union.
    ///
    /// For a bit-field member, this is the byte offset of its storage unit.
    /// Use [`CType::field_layout`] to recover the bit position within the unit.
    pub fn field_offset(&self, name: &str) -> Option<usize> {
        self.field_layout(name).map(|l| l.byte_offset)
    }

    /// Compute the layout of every member of a struct, parallel to its field
    /// list (including unnamed zero-width bit-field separators). Returns `None`
    /// for non-struct types.
    pub fn struct_field_layouts(&self) -> Option<Vec<FieldLayout>> {
        match self {
            CType::Struct { fields, .. } => Some(struct_layout(fields).0),
            CType::Qualified { ty, .. } => ty.struct_field_layouts(),
            _ => None,
        }
    }

    /// Resolve the full layout (byte offset plus any bit-field placement) of a
    /// named member of a struct or union.
    pub fn field_layout(&self, name: &str) -> Option<FieldLayout> {
        match self {
            CType::Struct { fields, .. } => {
                let (layouts, _) = struct_layout(fields);
                fields
                    .iter()
                    .zip(layouts)
                    .find(|(f, _)| f.name == name)
                    .map(|(_, layout)| layout)
            }
            CType::Union { fields, .. } => {
                // All union members live at offset 0. A bit-field union member
                // still starts at bit 0 of a storage unit at offset 0.
                fields.iter().find(|f| f.name == name).map(|f| {
                    let bitfield = f.bit_width.and_then(|width| {
                        (width > 0).then(|| {
                            let unit_bytes = f.ty.size().max(1);
                            BitFieldPlacement {
                                byte_offset: 0,
                                unit_bytes,
                                bit_offset: 0,
                                bit_width: width,
                            }
                        })
                    });
                    FieldLayout {
                        byte_offset: 0,
                        bitfield,
                    }
                })
            }
            CType::Qualified { ty, .. } => ty.field_layout(name),
            _ => None,
        }
    }

    /// Validate the flexible-array-member constraints of a struct or union
    /// type (C99 6.7.2.1p18).
    ///
    /// * In a struct, a flexible array member (`T[]`) must be the last member,
    ///   and the struct must have at least one other member.
    /// * A union may not contain a flexible array member.
    ///
    /// Non-aggregate types and aggregates without a flexible array member
    /// validate trivially.
    pub fn validate_flexible_array_member(&self) -> Result<(), FlexibleArrayError> {
        match self {
            CType::Struct { fields, .. } => validate_struct_flexible_array(fields),
            CType::Union { fields, .. } => {
                // A union member cannot be a flexible array (it would have no
                // following member to extend over).
                if let Some(field) = fields.iter().find(|f| f.ty.is_flexible_array()) {
                    return Err(FlexibleArrayError::NotInStruct {
                        name: field.name.clone(),
                    });
                }
                Ok(())
            }
            CType::Qualified { ty, .. } => ty.validate_flexible_array_member(),
            _ => Ok(()),
        }
    }

    /// Remove qualifiers from type
    pub fn unqualified(&self) -> &CType {
        match self {
            CType::Qualified { ty, .. } => ty.unqualified(),
            _ => self,
        }
    }

    /// Check if types are compatible (C11 6.2.7)
    pub fn is_compatible(&self, other: &CType) -> bool {
        match (self.unqualified(), other.unqualified()) {
            (CType::Void, CType::Void) => true,

            (CType::Int(k1, s1), CType::Int(k2, s2)) => k1 == k2 && s1 == s2,

            (CType::Float(k1), CType::Float(k2)) => k1 == k2,

            (CType::Pointer(p1), CType::Pointer(p2)) => p1.is_compatible(p2),

            (CType::Array(e1, n1), CType::Array(e2, n2)) => n1 == n2 && e1.is_compatible(e2),

            (CType::IncompleteArray(e1), CType::IncompleteArray(e2)) => e1.is_compatible(e2),

            (
                CType::Struct {
                    name: n1,
                    fields: f1,
                },
                CType::Struct {
                    name: n2,
                    fields: f2,
                },
            ) => {
                if n1 != n2 {
                    return false;
                }
                if f1.len() != f2.len() {
                    return false;
                }
                f1.iter()
                    .zip(f2.iter())
                    .all(|(a, b)| a.name == b.name && a.ty.is_compatible(&b.ty))
            }

            (
                CType::Union {
                    name: n1,
                    fields: f1,
                },
                CType::Union {
                    name: n2,
                    fields: f2,
                },
            ) => {
                if n1 != n2 {
                    return false;
                }
                if f1.len() != f2.len() {
                    return false;
                }
                f1.iter()
                    .zip(f2.iter())
                    .all(|(a, b)| a.name == b.name && a.ty.is_compatible(&b.ty))
            }

            (
                CType::Enum {
                    name: n1,
                    variants: v1,
                },
                CType::Enum {
                    name: n2,
                    variants: v2,
                },
            ) => n1 == n2 && v1 == v2,

            (
                CType::Function {
                    return_type: r1,
                    params: p1,
                    variadic: v1,
                },
                CType::Function {
                    return_type: r2,
                    params: p2,
                    variadic: v2,
                },
            ) => {
                if v1 != v2 {
                    return false;
                }
                if !r1.is_compatible(r2) {
                    return false;
                }
                if p1.len() != p2.len() {
                    return false;
                }
                p1.iter()
                    .zip(p2.iter())
                    .all(|(a, b)| a.ty.is_compatible(&b.ty))
            }

            _ => false,
        }
    }

    /// Integer promotion (C11 6.3.1.1)
    ///
    /// Small integer types are promoted to int or unsigned int
    #[must_use]
    pub fn integer_promotion(&self) -> CType {
        match self {
            CType::Int(IntKind::Bool | IntKind::Char | IntKind::Short, _) => {
                CType::Int(IntKind::Int, Signedness::Signed)
            }

            CType::Int(IntKind::Int, Signedness::Unsigned) => {
                CType::Int(IntKind::Int, Signedness::Unsigned)
            }

            // C11 6.3.1.1p2: an object of enumeration type is converted to its
            // promoted underlying integer type when used in an expression. The
            // underlying type is chosen to represent all enumerators (CompCert /
            // GCC / Clang use a 4-byte type by default); it is then promoted.
            CType::Enum { .. } => self.enum_underlying_type().integer_promotion(),

            // Qualifiers are dropped under the integer promotions (the result of
            // promotion is always an unqualified rvalue type).
            CType::Qualified { ty, .. } => ty.integer_promotion(),

            ty => ty.clone(),
        }
    }

    /// Underlying integer type of an enumeration (C11 6.7.2.2p4).
    ///
    /// The implementation must choose an integer type capable of representing
    /// all enumerator values. Matching CompCert / GCC / Clang defaults, this
    /// model keeps enumerations 4-byte sized, so the underlying type is `int`
    /// when every enumerator fits in the signed `int` range, and
    /// `unsigned int` when an enumerator exceeds `INT_MAX` but still fits in a
    /// non-negative 4-byte value. Non-enumeration types return themselves.
    #[must_use]
    pub fn enum_underlying_type(&self) -> CType {
        match self {
            CType::Enum { variants, .. } => {
                let needs_unsigned = variants
                    .iter()
                    .any(|(_, value)| *value > i64::from(i32::MAX));
                let has_negative = variants.iter().any(|(_, value)| *value < 0);
                if needs_unsigned && !has_negative {
                    CType::Int(IntKind::Int, Signedness::Unsigned)
                } else {
                    CType::Int(IntKind::Int, Signedness::Signed)
                }
            }
            CType::Qualified { ty, .. } => ty.enum_underlying_type(),
            ty => ty.clone(),
        }
    }

    /// Usual arithmetic conversions (C11 6.3.1.8)
    ///
    /// Returns the common type for arithmetic operations
    #[must_use]
    pub fn usual_arithmetic_conversion(&self, other: &CType) -> CType {
        let a = self.integer_promotion();
        let b = other.integer_promotion();

        // If either is long double
        if matches!(a, CType::Float(FloatKind::LongDouble))
            || matches!(b, CType::Float(FloatKind::LongDouble))
        {
            return CType::Float(FloatKind::LongDouble);
        }

        // If either is double
        if matches!(a, CType::Float(FloatKind::Double))
            || matches!(b, CType::Float(FloatKind::Double))
        {
            return CType::Float(FloatKind::Double);
        }

        // If either is float
        if matches!(a, CType::Float(FloatKind::Float))
            || matches!(b, CType::Float(FloatKind::Float))
        {
            return CType::Float(FloatKind::Float);
        }

        // Both are integers after promotion
        match (&a, &b) {
            (CType::Int(k1, s1), CType::Int(k2, s2)) => {
                // If same signedness, use larger rank
                if s1 == s2 {
                    if k1.size() >= k2.size() {
                        return a;
                    }
                    return b;
                }

                // Different signedness: complex rules
                let (unsigned, signed, unsigned_kind, signed_kind) = if *s1 == Signedness::Unsigned
                {
                    (&a, &b, k1, k2)
                } else {
                    (&b, &a, k2, k1)
                };

                // If unsigned has rank >= signed, use unsigned
                if unsigned_kind.size() >= signed_kind.size() {
                    return unsigned.clone();
                }

                // If signed can represent all unsigned values
                if signed_kind.size() > unsigned_kind.size() {
                    return signed.clone();
                }

                // Otherwise, use unsigned version of signed type
                CType::Int(*signed_kind, Signedness::Unsigned)
            }

            _ => a, // Shouldn't happen after promotion
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_kind_sizes() {
        assert_eq!(IntKind::Char.size(), 1);
        assert_eq!(IntKind::Short.size(), 2);
        assert_eq!(IntKind::Int.size(), 4);
        assert_eq!(IntKind::Long.size(), 8);
        assert_eq!(IntKind::LongLong.size(), 8);
        assert_eq!(IntKind::Bool.size(), 1);
    }

    #[test]
    fn test_int_kind_ranges() {
        assert_eq!(IntKind::Char.signed_min(), -128);
        assert_eq!(IntKind::Char.signed_max(), 127);
        assert_eq!(IntKind::Char.unsigned_max(), 255);

        assert_eq!(IntKind::Int.signed_min(), -2_147_483_648);
        assert_eq!(IntKind::Int.signed_max(), 2_147_483_647);
        assert_eq!(IntKind::Int.unsigned_max(), 4_294_967_295);
    }

    #[test]
    fn test_struct_layout() {
        // struct { char a; int b; char c; }
        let fields = vec![
            StructField::new("a", CType::Int(IntKind::Char, Signedness::Signed)),
            StructField::new("b", CType::Int(IntKind::Int, Signedness::Signed)),
            StructField::new("c", CType::Int(IntKind::Char, Signedness::Signed)),
        ];
        let struct_ty = CType::Struct { name: None, fields };

        // Layout: a(1) + pad(3) + b(4) + c(1) + pad(3) = 12
        assert_eq!(struct_ty.size(), 12);
        assert_eq!(struct_ty.align(), 4);

        // Field offsets
        assert_eq!(struct_ty.field_offset("a"), Some(0));
        assert_eq!(struct_ty.field_offset("b"), Some(4));
        assert_eq!(struct_ty.field_offset("c"), Some(8));
    }

    #[test]
    fn test_struct_bitfield_layout_packs_and_separates() {
        let uchar = || CType::Int(IntKind::Char, Signedness::Unsigned);
        // struct { unsigned char a:3; unsigned char b:5; unsigned char :0;
        //          unsigned char c:2; int d; }
        let ty = CType::Struct {
            name: None,
            fields: vec![
                StructField::bitfield("a", uchar(), 3),
                StructField::bitfield("b", uchar(), 5),
                StructField::bitfield("", uchar(), 0),
                StructField::bitfield("c", uchar(), 2),
                StructField::new("d", CType::Int(IntKind::Int, Signedness::Signed)),
            ],
        };
        // a,b share byte 0; zero-width forces c into byte 1; d aligns to 4.
        let la = ty.field_layout("a").expect("a").bitfield.expect("a bf");
        let lb = ty.field_layout("b").expect("b").bitfield.expect("b bf");
        let lc = ty.field_layout("c").expect("c").bitfield.expect("c bf");
        assert_eq!((la.byte_offset, la.bit_offset, la.bit_width), (0, 0, 3));
        assert_eq!((lb.byte_offset, lb.bit_offset, lb.bit_width), (0, 3, 5));
        assert_eq!((lc.byte_offset, lc.bit_offset, lc.bit_width), (1, 0, 2));
        assert_eq!(ty.field_offset("d"), Some(4));
        // d (offset 4..8) plus struct alignment 4 → size 8.
        assert_eq!(ty.size(), 8);
        assert_eq!(ty.align(), 4);
    }

    #[test]
    fn test_struct_bitfield_overflow_starts_new_unit() {
        let uchar = || CType::Int(IntKind::Char, Signedness::Unsigned);
        // a:6 then b:4 cannot share one byte → size 2.
        let ty = CType::Struct {
            name: None,
            fields: vec![
                StructField::bitfield("a", uchar(), 6),
                StructField::bitfield("b", uchar(), 4),
            ],
        };
        assert_eq!(ty.field_offset("a"), Some(0));
        assert_eq!(ty.field_offset("b"), Some(1));
        assert_eq!(ty.size(), 2);
    }

    #[test]
    fn test_union_layout() {
        // union { int i; double d; char c; }
        let fields = vec![
            StructField::new("i", CType::Int(IntKind::Int, Signedness::Signed)),
            StructField::new("d", CType::Float(FloatKind::Double)),
            StructField::new("c", CType::Int(IntKind::Char, Signedness::Signed)),
        ];
        let union_ty = CType::Union { name: None, fields };

        // Size is max(4, 8, 1) = 8
        assert_eq!(union_ty.size(), 8);
        // Align is max(4, 8, 1) = 8
        assert_eq!(union_ty.align(), 8);

        // All fields at offset 0
        assert_eq!(union_ty.field_offset("i"), Some(0));
        assert_eq!(union_ty.field_offset("d"), Some(0));
        assert_eq!(union_ty.field_offset("c"), Some(0));
    }

    #[test]
    fn test_integer_promotion() {
        let char_ty = CType::Int(IntKind::Char, Signedness::Signed);
        let short_ty = CType::Int(IntKind::Short, Signedness::Unsigned);
        let int_ty = CType::Int(IntKind::Int, Signedness::Signed);
        let long_ty = CType::Int(IntKind::Long, Signedness::Signed);

        // char -> int
        assert_eq!(
            char_ty.integer_promotion(),
            CType::Int(IntKind::Int, Signedness::Signed)
        );

        // unsigned short -> int (fits)
        assert_eq!(
            short_ty.integer_promotion(),
            CType::Int(IntKind::Int, Signedness::Signed)
        );

        // int stays int
        assert_eq!(int_ty.integer_promotion(), int_ty);

        // long stays long
        assert_eq!(long_ty.integer_promotion(), long_ty);
    }

    #[test]
    fn test_usual_arithmetic_conversions() {
        let int_ty = CType::Int(IntKind::Int, Signedness::Signed);
        let uint_ty = CType::Int(IntKind::Int, Signedness::Unsigned);
        let long_ty = CType::Int(IntKind::Long, Signedness::Signed);
        let double_ty = CType::Float(FloatKind::Double);

        // int + unsigned int -> unsigned int
        assert_eq!(
            int_ty.usual_arithmetic_conversion(&uint_ty),
            CType::Int(IntKind::Int, Signedness::Unsigned)
        );

        // int + long -> long
        assert_eq!(int_ty.usual_arithmetic_conversion(&long_ty), long_ty);

        // int + double -> double
        assert_eq!(int_ty.usual_arithmetic_conversion(&double_ty), double_ty);
    }

    fn enum_ty(variants: &[(&str, i64)]) -> CType {
        CType::Enum {
            name: None,
            variants: variants
                .iter()
                .map(|(n, v)| ((*n).to_string(), *v))
                .collect(),
        }
    }

    #[test]
    fn test_integer_promotion_enum_small_values_promotes_to_int() {
        // C11 6.3.1.1p2: an enum with values fitting in `int` promotes to `int`.
        let color = enum_ty(&[("RED", 0), ("GREEN", 1), ("BLUE", 2)]);
        assert_eq!(
            color.integer_promotion(),
            CType::Int(IntKind::Int, Signedness::Signed)
        );
    }

    #[test]
    fn test_integer_promotion_enum_negative_value_promotes_to_int() {
        // Negative enumerators force a signed underlying type.
        let signed = enum_ty(&[("LO", -1), ("HI", 1)]);
        assert_eq!(
            signed.integer_promotion(),
            CType::Int(IntKind::Int, Signedness::Signed)
        );
    }

    #[test]
    fn test_integer_promotion_enum_above_int_max_promotes_to_uint() {
        // A non-negative enumerator above INT_MAX needs `unsigned int`.
        let big = enum_ty(&[("LOW", 0), ("HIGH", i64::from(i32::MAX) + 1)]);
        assert_eq!(
            big.integer_promotion(),
            CType::Int(IntKind::Int, Signedness::Unsigned)
        );
    }

    #[test]
    fn test_usual_arithmetic_conversion_enum_and_int_is_int() {
        // enum + int -> int (both promote to int).
        let color = enum_ty(&[("A", 0), ("B", 1)]);
        let int_ty = CType::Int(IntKind::Int, Signedness::Signed);
        assert_eq!(color.usual_arithmetic_conversion(&int_ty), int_ty);
    }

    #[test]
    fn test_usual_arithmetic_conversion_enum_and_uint_is_uint() {
        // enum + unsigned int -> unsigned int (after both promote to int).
        let color = enum_ty(&[("A", 0), ("B", 1)]);
        let uint_ty = CType::Int(IntKind::Int, Signedness::Unsigned);
        assert_eq!(color.usual_arithmetic_conversion(&uint_ty), uint_ty);
    }

    #[test]
    fn test_usual_arithmetic_conversion_two_enums_is_int() {
        // enum - enum -> int (e.g. computing the distance between enumerators).
        let a = enum_ty(&[("A", 0), ("B", 1)]);
        let b = enum_ty(&[("C", 5), ("D", 6)]);
        assert_eq!(
            a.usual_arithmetic_conversion(&b),
            CType::Int(IntKind::Int, Signedness::Signed)
        );
    }

    #[test]
    fn test_usual_arithmetic_conversion_enum_and_long_is_long() {
        // enum + long -> long: after the enum promotes to int, long has higher rank.
        let color = enum_ty(&[("A", 0), ("B", 1)]);
        let long_ty = CType::Int(IntKind::Long, Signedness::Signed);
        assert_eq!(color.usual_arithmetic_conversion(&long_ty), long_ty);
    }

    #[test]
    fn test_integer_promotion_qualified_char_drops_qualifier_and_promotes() {
        // `const char` promotes to (unqualified) int.
        let cqual = CType::const_ty(CType::Int(IntKind::Char, Signedness::Signed));
        assert_eq!(
            cqual.integer_promotion(),
            CType::Int(IntKind::Int, Signedness::Signed)
        );
    }

    #[test]
    fn test_enum_underlying_type_non_enum_returns_self() {
        let int_ty = CType::Int(IntKind::Int, Signedness::Signed);
        assert_eq!(int_ty.enum_underlying_type(), int_ty);
    }

    #[test]
    fn test_type_predicates() {
        let int_ty = CType::int();
        let ptr_ty = CType::ptr(CType::int());
        let arr_ty = CType::array(CType::int(), 10);
        let void_ty = CType::void();

        assert!(int_ty.is_integer());
        assert!(int_ty.is_arithmetic());
        assert!(int_ty.is_scalar());
        assert!(int_ty.is_complete());

        assert!(ptr_ty.is_pointer());
        assert!(ptr_ty.is_scalar());
        assert!(!ptr_ty.is_arithmetic());

        assert!(arr_ty.is_array());
        assert!(!arr_ty.is_scalar());

        assert!(!void_ty.is_complete());
    }

    #[test]
    fn test_pointer_pointee() {
        let int_ty = CType::int();
        let ptr_ty = CType::ptr(int_ty.clone());
        let ptr_ptr_ty = CType::ptr(ptr_ty.clone());

        assert_eq!(ptr_ty.pointee(), Some(&int_ty));
        assert_eq!(ptr_ptr_ty.pointee(), Some(&ptr_ty));
        assert_eq!(int_ty.pointee(), None);
    }

    #[test]
    fn test_qualified_types() {
        let int_ty = CType::int();
        let const_int = CType::const_ty(int_ty.clone());

        assert_eq!(const_int.size(), 4);
        assert_eq!(const_int.unqualified(), &int_ty);
        assert!(const_int.is_integer());
    }

    fn fam_struct(fields: Vec<StructField>) -> CType {
        CType::Struct {
            name: Some("S".to_string()),
            fields,
        }
    }

    #[test]
    fn test_incomplete_array_is_incomplete_array_typed() {
        // A flexible array member type `int[]` is an incomplete array type.
        let fam = CType::incomplete_array(CType::int());
        assert!(fam.is_flexible_array());
        assert!(fam.is_array());
        assert!(!fam.is_complete(), "T[] is an incomplete type");
        assert_eq!(fam.element(), Some(&CType::int()));
        // It contributes 0 size of its own, but keeps the element alignment.
        assert_eq!(fam.size(), 0);
        assert_eq!(fam.align(), 4);
    }

    #[test]
    fn test_fieldless_struct_is_incomplete() {
        // A forward-declared struct (`struct S;`) is modeled as a fieldless
        // struct and is an incomplete type (C11 6.7.2.3, 6.2.5p22).
        let fwd = CType::Struct {
            name: Some("S".to_string()),
            fields: Vec::new(),
        };
        assert!(!fwd.is_complete(), "a fieldless struct is incomplete");
    }

    #[test]
    fn test_fieldless_union_is_incomplete() {
        // A forward-declared union (`union U;`) is likewise incomplete.
        let fwd = CType::Union {
            name: Some("U".to_string()),
            fields: Vec::new(),
        };
        assert!(!fwd.is_complete(), "a fieldless union is incomplete");
    }

    #[test]
    fn test_struct_with_members_is_complete() {
        // Once a struct has at least one member it is a complete type with a
        // known size, even when the trailing member is a flexible array.
        let defined = fam_struct(vec![StructField::new("x", CType::int())]);
        assert!(defined.is_complete(), "a defined struct is complete");
        let with_fam = fam_struct(vec![
            StructField::new("x", CType::int()),
            StructField::new("arr", CType::incomplete_array(CType::int())),
        ]);
        assert!(
            with_fam.is_complete(),
            "a struct with members (incl. a FAM) is complete"
        );
    }

    #[test]
    fn test_struct_with_fam_omits_fam_from_size() {
        // struct S { int x; int arr[]; } — sizeof is just the int x (the
        // flexible array member contributes 0), C99 6.7.2.1p18.
        let ty = fam_struct(vec![
            StructField::new("x", CType::int()),
            StructField::new("arr", CType::incomplete_array(CType::int())),
        ]);
        assert_eq!(ty.size(), 4, "FAM omitted from struct size");
        assert_eq!(ty.align(), 4);
        // The fixed member is laid out normally; the FAM lives just past it.
        assert_eq!(ty.field_offset("x"), Some(0));
        assert_eq!(ty.field_offset("arr"), Some(4));
        ty.validate_flexible_array_member()
            .expect("FAM as last member of a multi-member struct is valid");
    }

    #[test]
    fn test_struct_with_fam_alignment_accounts_for_element_type() {
        // struct S { char c; double d[]; } — the FAM's double element forces
        // 8-byte struct alignment even though it contributes 0 to the size,
        // so the struct rounds up to 8.
        let ty = fam_struct(vec![
            StructField::new("c", CType::char()),
            StructField::new(
                "d",
                CType::incomplete_array(CType::Float(FloatKind::Double)),
            ),
        ]);
        assert_eq!(ty.align(), 8, "FAM element alignment participates");
        assert_eq!(ty.size(), 8, "char + trailing pad to 8-byte alignment");
        assert_eq!(ty.field_offset("d"), Some(8));
    }

    #[test]
    fn test_struct_fam_not_last_is_rejected() {
        // struct S { int arr[]; int y; } — a FAM that is not the last member.
        let ty = fam_struct(vec![
            StructField::new("arr", CType::incomplete_array(CType::int())),
            StructField::new("y", CType::int()),
        ]);
        assert_eq!(
            ty.validate_flexible_array_member(),
            Err(FlexibleArrayError::NotLast {
                name: "arr".to_string()
            })
        );
    }

    #[test]
    fn test_struct_fam_sole_member_is_rejected() {
        // struct S { int arr[]; } — a FAM cannot be the only member.
        let ty = fam_struct(vec![StructField::new(
            "arr",
            CType::incomplete_array(CType::int()),
        )]);
        assert_eq!(
            ty.validate_flexible_array_member(),
            Err(FlexibleArrayError::SoleMember)
        );
    }

    #[test]
    fn test_union_with_fam_is_rejected() {
        // A union may not contain a flexible array member.
        let ty = CType::Union {
            name: Some("U".to_string()),
            fields: vec![
                StructField::new("x", CType::int()),
                StructField::new("arr", CType::incomplete_array(CType::int())),
            ],
        };
        assert_eq!(
            ty.validate_flexible_array_member(),
            Err(FlexibleArrayError::NotInStruct {
                name: "arr".to_string()
            })
        );
    }

    #[test]
    fn test_struct_without_fam_validates_trivially() {
        // An ordinary struct (no FAM) passes validation, and a trailing
        // zero-length fixed array `int[0]` is NOT a flexible array member.
        let ty = fam_struct(vec![
            StructField::new("x", CType::int()),
            StructField::new("arr", CType::array(CType::int(), 0)),
        ]);
        assert!(!ty.get_field("arr").unwrap().1.ty.is_flexible_array());
        ty.validate_flexible_array_member()
            .expect("a zero-length fixed array is not a FAM");
    }
}
