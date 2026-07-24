// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended native type analysis: layout computation, compatibility checking,
//! type classification, statistics, ABI analysis, pretty printing, and
//! endianness handling for `NativeType`.
//!
//! Complements `native_types` (core type definitions, compile_to_native).
//! Part of #3084 - Native type compilation for UInt and Float.

use crate::ir::IRType;
use crate::native_types::NativeType;
use std::fmt;
use thiserror::Error;

// ── Error ──────────────────────────────────────────────────────────────────

/// Errors from native type layout and compatibility operations.
#[derive(Debug, Clone, Error)]
pub(crate) enum NativeTypeError {
    #[error("type {0:?} has no defined layout (e.g. Bool has no fixed byte size)")]
    NoLayout(NativeType),

    #[error("types {0:?} and {1:?} are not layout-compatible")]
    IncompatibleLayout(NativeType, NativeType),

    #[error("unsupported target pointer width: {0}")]
    UnsupportedPointerWidth(u32),
}

// ── Target configuration ──────────────────────────────────────────────────

/// Target platform configuration for layout computation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TargetConfig {
    /// Pointer width in bits (32 or 64).
    pub(crate) pointer_width: u32,
    /// Whether the target is big-endian.
    pub(crate) big_endian: bool,
}

impl TargetConfig {
    /// Standard 64-bit little-endian target (x86-64, aarch64).
    #[must_use]
    pub(crate) fn lp64_le() -> Self {
        Self {
            pointer_width: 64,
            big_endian: false,
        }
    }

    /// Standard 32-bit little-endian target.
    #[must_use]
    pub(crate) fn ilp32_le() -> Self {
        Self {
            pointer_width: 32,
            big_endian: false,
        }
    }

    /// Standard 64-bit big-endian target (s390x).
    #[must_use]
    pub(crate) fn lp64_be() -> Self {
        Self {
            pointer_width: 64,
            big_endian: true,
        }
    }
}

impl Default for TargetConfig {
    fn default() -> Self {
        Self::lp64_le()
    }
}

// ── Type layout ───────────────────────────────────────────────────────────

/// Computed layout for a native type on a specific target.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TypeLayout {
    /// Size in bytes.
    pub(crate) size: u32,
    /// Alignment in bytes (always a power of two).
    pub(crate) alignment: u32,
}

/// Compute the layout (size, alignment) of a `NativeType` on a given target.
///
/// Returns an error for `Bool` since it has no fixed numeric byte size
/// in this representation (it is a 1-bit logical type, not a stored scalar).
pub(crate) fn compute_layout(
    ty: NativeType,
    target: &TargetConfig,
) -> Result<TypeLayout, NativeTypeError> {
    match ty {
        NativeType::UInt8 => Ok(TypeLayout {
            size: 1,
            alignment: 1,
        }),
        NativeType::UInt16 => Ok(TypeLayout {
            size: 2,
            alignment: 2,
        }),
        NativeType::UInt32 => Ok(TypeLayout {
            size: 4,
            alignment: 4,
        }),
        NativeType::UInt64 => Ok(TypeLayout {
            size: 8,
            alignment: 8,
        }),
        NativeType::USize => {
            let bytes = target.pointer_width / 8;
            Ok(TypeLayout {
                size: bytes,
                alignment: bytes,
            })
        }
        NativeType::Float => Ok(TypeLayout {
            size: 8,
            alignment: 8,
        }),
        NativeType::Bool => Err(NativeTypeError::NoLayout(ty)),
    }
}

/// Compute padding needed between two consecutive fields.
///
/// Returns the number of padding bytes to insert after a field ending at
/// `offset` so that the next field starts at a correctly aligned address.
#[must_use]
pub(crate) fn compute_padding(offset: u32, next_alignment: u32) -> u32 {
    debug_assert!(next_alignment > 0 && next_alignment.is_power_of_two());
    let misalignment = offset % next_alignment;
    if misalignment == 0 {
        0
    } else {
        next_alignment - misalignment
    }
}

/// Compute the total size of a struct containing the given native types,
/// including inter-field padding and trailing padding.
pub(crate) fn compute_struct_layout(
    fields: &[NativeType],
    target: &TargetConfig,
) -> Result<TypeLayout, NativeTypeError> {
    if fields.is_empty() {
        return Ok(TypeLayout {
            size: 0,
            alignment: 1,
        });
    }

    let mut offset: u32 = 0;
    let mut max_align: u32 = 1;

    for &field_ty in fields {
        let field_layout = compute_layout(field_ty, target)?;
        let padding = compute_padding(offset, field_layout.alignment);
        offset += padding + field_layout.size;
        max_align = max_align.max(field_layout.alignment);
    }

    // Trailing padding to align struct size to its own alignment.
    let trailing = compute_padding(offset, max_align);
    offset += trailing;

    Ok(TypeLayout {
        size: offset,
        alignment: max_align,
    })
}

// ── Type compatibility ────────────────────────────────────────────────────

/// Check if two native types are layout-compatible on the given target.
///
/// Layout-compatible means both types have the same size and alignment,
/// so a reinterpret cast between them preserves memory layout.
pub(crate) fn is_layout_compatible(
    a: NativeType,
    b: NativeType,
    target: &TargetConfig,
) -> Result<bool, NativeTypeError> {
    let la = compute_layout(a, target)?;
    let lb = compute_layout(b, target)?;
    Ok(la == lb)
}

/// Check if a value of type `from` can be safely widened to type `to`.
///
/// Safe widening preserves value (e.g. UInt8 -> UInt16, UInt16 -> UInt32).
/// Does not consider narrowing or float conversions safe.
#[must_use]
pub(crate) fn is_safe_widening(from: NativeType, to: NativeType) -> bool {
    use NativeType::*;
    matches!(
        (from, to),
        (UInt8, UInt16)
            | (UInt8, UInt32)
            | (UInt8, UInt64)
            | (UInt8, USize)
            | (UInt16, UInt32)
            | (UInt16, UInt64)
            | (UInt16, USize)
            | (UInt32, UInt64)
            | (UInt32, USize)
    )
}

// ── Type classification ───────────────────────────────────────────────────

/// High-level classification of a native type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum TypeCategory {
    /// Integer types (UInt8..UInt64, USize).
    Integer,
    /// Floating-point types (Float).
    FloatingPoint,
    /// Boolean type.
    Boolean,
}

/// Classify a `NativeType` into a high-level category.
#[must_use]
pub(crate) fn classify_type(ty: NativeType) -> TypeCategory {
    match ty {
        NativeType::UInt8
        | NativeType::UInt16
        | NativeType::UInt32
        | NativeType::UInt64
        | NativeType::USize => TypeCategory::Integer,
        NativeType::Float => TypeCategory::FloatingPoint,
        NativeType::Bool => TypeCategory::Boolean,
    }
}

/// Classify an `IRType` into a high-level native category, if applicable.
///
/// Returns `None` for composite/reference/special IR types that do not map
/// to a single native scalar.
#[must_use]
pub(crate) fn classify_ir_type(ty: &IRType) -> Option<TypeCategory> {
    match ty {
        IRType::UInt8 | IRType::UInt16 | IRType::UInt32 | IRType::UInt64 | IRType::USize => {
            Some(TypeCategory::Integer)
        }
        IRType::Float32 | IRType::Float64 => Some(TypeCategory::FloatingPoint),
        IRType::Bool => Some(TypeCategory::Boolean),
        _ => None,
    }
}

// ── Type statistics ───────────────────────────────────────────────────────

/// Statistics about a collection of native types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeStats {
    pub(crate) integer_count: usize,
    pub(crate) float_count: usize,
    pub(crate) bool_count: usize,
    pub(crate) total: usize,
}

/// Compute statistics over a slice of native types.
#[must_use]
pub(crate) fn compute_type_stats(types: &[NativeType]) -> TypeStats {
    let mut stats = TypeStats {
        integer_count: 0,
        float_count: 0,
        bool_count: 0,
        total: types.len(),
    };
    for &ty in types {
        match classify_type(ty) {
            TypeCategory::Integer => stats.integer_count += 1,
            TypeCategory::FloatingPoint => stats.float_count += 1,
            TypeCategory::Boolean => stats.bool_count += 1,
        }
    }
    stats
}

/// Compute the average field size in bytes for a slice of native types,
/// skipping types without a defined layout (Bool).
///
/// Returns `None` if no types have a valid layout.
#[must_use]
pub(crate) fn average_field_size(types: &[NativeType], target: &TargetConfig) -> Option<f64> {
    let mut sum: u64 = 0;
    let mut count: u64 = 0;
    for &ty in types {
        if let Ok(layout) = compute_layout(ty, target) {
            sum += u64::from(layout.size);
            count += 1;
        }
    }
    if count == 0 {
        None
    } else {
        Some(sum as f64 / count as f64)
    }
}

// ── ABI analysis ──────────────────────────────────────────────────────────

/// ABI passing convention for a native type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum PassingConvention {
    /// Passed in a general-purpose integer register.
    IntegerRegister,
    /// Passed in a floating-point / SIMD register.
    FloatRegister,
    /// Passed on the stack (e.g. Bool or unsupported).
    Stack,
}

/// Determine the ABI passing convention for a native type.
///
/// On System V AMD64 ABI:
/// - Integer scalars up to 64 bits go in GPRs (rdi, rsi, rdx, rcx, r8, r9).
/// - Floating-point values go in SSE registers (xmm0..xmm7).
/// - Bool has no fixed numeric width and uses the stack convention.
#[must_use]
pub(crate) fn passing_convention(ty: NativeType) -> PassingConvention {
    match classify_type(ty) {
        TypeCategory::Integer => PassingConvention::IntegerRegister,
        TypeCategory::FloatingPoint => PassingConvention::FloatRegister,
        TypeCategory::Boolean => PassingConvention::Stack,
    }
}

/// Count how many integer and float registers a parameter list would consume
/// on the System V AMD64 ABI. Stack-passed parameters are counted separately.
#[must_use]
pub(crate) fn count_register_usage(params: &[NativeType]) -> RegisterUsage {
    let mut usage = RegisterUsage {
        integer_regs: 0,
        float_regs: 0,
        stack_params: 0,
    };
    for &ty in params {
        match passing_convention(ty) {
            PassingConvention::IntegerRegister => {
                if usage.integer_regs < MAX_INTEGER_REGS {
                    usage.integer_regs += 1;
                } else {
                    usage.stack_params += 1;
                }
            }
            PassingConvention::FloatRegister => {
                if usage.float_regs < MAX_FLOAT_REGS {
                    usage.float_regs += 1;
                } else {
                    usage.stack_params += 1;
                }
            }
            PassingConvention::Stack => {
                usage.stack_params += 1;
            }
        }
    }
    usage
}

/// Maximum integer registers available for parameter passing (System V AMD64).
const MAX_INTEGER_REGS: u32 = 6;
/// Maximum float registers available for parameter passing (System V AMD64).
const MAX_FLOAT_REGS: u32 = 8;

/// Register usage summary for a parameter list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RegisterUsage {
    pub(crate) integer_regs: u32,
    pub(crate) float_regs: u32,
    pub(crate) stack_params: u32,
}

impl RegisterUsage {
    /// Whether all parameters fit in registers (no stack spills).
    #[must_use]
    pub(crate) fn all_in_registers(&self) -> bool {
        self.stack_params == 0
    }
}

// ── Pretty printing ───────────────────────────────────────────────────────

/// Format a `NativeType` as a C-like type name for debug output.
#[must_use]
pub(crate) fn native_type_to_c_name(ty: NativeType) -> &'static str {
    match ty {
        NativeType::UInt8 => "uint8_t",
        NativeType::UInt16 => "uint16_t",
        NativeType::UInt32 => "uint32_t",
        NativeType::UInt64 => "uint64_t",
        NativeType::USize => "size_t",
        NativeType::Float => "double",
        NativeType::Bool => "_Bool",
    }
}

/// Format a struct layout as a C-like struct declaration.
pub(crate) fn format_struct_c(
    name: &str,
    fields: &[(String, NativeType)],
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    writeln!(f, "struct {} {{", name)?;
    for (field_name, ty) in fields {
        writeln!(f, "    {} {};", native_type_to_c_name(*ty), field_name)?;
    }
    write!(f, "}}")
}

/// A helper struct for Display-based struct formatting.
pub(crate) struct CStructDisplay<'a> {
    pub(crate) name: &'a str,
    pub(crate) fields: &'a [(String, NativeType)],
}

impl fmt::Display for CStructDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        format_struct_c(self.name, self.fields, f)
    }
}

// ── Endianness handling ───────────────────────────────────────────────────

/// Check if a native type is endianness-sensitive.
///
/// Single-byte types and Bool are endianness-agnostic. Multi-byte types
/// are sensitive to byte order.
#[must_use]
pub(crate) fn is_endian_sensitive(ty: NativeType) -> bool {
    match ty {
        NativeType::UInt8 | NativeType::Bool => false,
        NativeType::UInt16
        | NativeType::UInt32
        | NativeType::UInt64
        | NativeType::USize
        | NativeType::Float => true,
    }
}

/// Byte-swap a `u64` value for a given `NativeType` width.
///
/// Only swaps the meaningful bytes for the type width. For example,
/// `byte_swap(NativeType::UInt16, 0x0102)` returns `0x0201`.
///
/// Returns an error for Bool (no numeric width).
pub(crate) fn byte_swap(ty: NativeType, value: u64) -> Result<u64, NativeTypeError> {
    match ty {
        NativeType::UInt8 => Ok(value & 0xFF),
        NativeType::UInt16 => Ok(u64::from((value as u16).swap_bytes())),
        NativeType::UInt32 => Ok(u64::from((value as u32).swap_bytes())),
        NativeType::UInt64 | NativeType::USize => Ok(value.swap_bytes()),
        NativeType::Float => Ok(value.swap_bytes()),
        NativeType::Bool => Err(NativeTypeError::NoLayout(ty)),
    }
}

/// Convert a `NativeType` to the corresponding `IRType`.
#[must_use]
pub(crate) fn native_to_ir_type(ty: NativeType) -> IRType {
    match ty {
        NativeType::UInt8 => IRType::UInt8,
        NativeType::UInt16 => IRType::UInt16,
        NativeType::UInt32 => IRType::UInt32,
        NativeType::UInt64 => IRType::UInt64,
        NativeType::USize => IRType::USize,
        NativeType::Float => IRType::Float64,
        NativeType::Bool => IRType::Bool,
    }
}

/// Try to convert an `IRType` to a `NativeType`.
///
/// Returns `None` for IR types without a native equivalent (Object, Struct, etc.).
#[must_use]
pub(crate) fn ir_to_native_type(ty: &IRType) -> Option<NativeType> {
    match ty {
        IRType::UInt8 => Some(NativeType::UInt8),
        IRType::UInt16 => Some(NativeType::UInt16),
        IRType::UInt32 => Some(NativeType::UInt32),
        IRType::UInt64 => Some(NativeType::UInt64),
        IRType::USize => Some(NativeType::USize),
        IRType::Float64 => Some(NativeType::Float),
        IRType::Bool => Some(NativeType::Bool),
        _ => None,
    }
}

#[cfg(test)]
#[path = "native_types_ext_tests.rs"]
mod tests;
