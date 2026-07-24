// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type-mapping and literal emission helpers for the C backend.
//!
//! Pure functions that map IR types to C runtime API names and format
//! literal values as valid C source text. Separated from the main
//! emitter to keep file sizes under the 500-line project guideline.

use crate::ir::IRType;
use crate::ir_checker::IRError;

/// Map scalar IRType to the C `clean_ctor_get_*` getter function name.
///
/// Only valid for SProj scalar types. Returns an error on invalid types.
pub(crate) fn c_scalar_getter_name(ty: &IRType) -> Result<&'static str, IRError> {
    match ty {
        IRType::Bool | IRType::UInt8 => Ok("clean_ctor_get_uint8"),
        IRType::UInt16 => Ok("clean_ctor_get_uint16"),
        IRType::UInt32 => Ok("clean_ctor_get_uint32"),
        IRType::UInt64 => Ok("clean_ctor_get_uint64"),
        IRType::Float32 => Ok("clean_ctor_get_float32"),
        IRType::Float64 => Ok("clean_ctor_get_float"),
        _ => Err(IRError::InvalidScalarType {
            ty: ty.clone(),
            op: "SProj",
        }),
    }
}

/// Map scalar IRType to the C `clean_ctor_set_*` setter function name.
///
/// Only valid for SSet scalar types. Returns an error on invalid types.
pub(crate) fn c_scalar_setter_name(ty: &IRType) -> Result<&'static str, IRError> {
    match ty {
        IRType::Bool | IRType::UInt8 => Ok("clean_ctor_set_uint8"),
        IRType::UInt16 => Ok("clean_ctor_set_uint16"),
        IRType::UInt32 => Ok("clean_ctor_set_uint32"),
        IRType::UInt64 => Ok("clean_ctor_set_uint64"),
        IRType::Float32 => Ok("clean_ctor_set_float32"),
        IRType::Float64 => Ok("clean_ctor_set_float"),
        _ => Err(IRError::InvalidScalarType {
            ty: ty.clone(),
            op: "SSet",
        }),
    }
}

/// Format a C byte offset expression for scalar field access.
pub(crate) fn c_byte_offset(n: u32, offset: u32) -> String {
    format!("sizeof(void*)*{} + {}", n, offset)
}

/// Emit a C float32 literal, handling NaN, Infinity, and -Infinity.
///
/// Standard C has no literal syntax for these values. Uses `NAN` and
/// `INFINITY` macros from `<math.h>` (C99), cast to `float`.
pub(super) fn emit_c_float32(f: f32) -> String {
    if f.is_nan() {
        "((float)NAN)".to_string()
    } else if f.is_infinite() {
        if f.is_sign_positive() {
            "((float)INFINITY)".to_string()
        } else {
            "(-(float)INFINITY)".to_string()
        }
    } else {
        format!("{}f", f)
    }
}

/// Emit a C float64 literal, handling NaN, Infinity, and -Infinity.
pub(super) fn emit_c_float64(f: f64) -> String {
    if f.is_nan() {
        "NAN".to_string()
    } else if f.is_infinite() {
        if f.is_sign_positive() {
            "INFINITY".to_string()
        } else {
            "(-INFINITY)".to_string()
        }
    } else {
        format!("{}", f)
    }
}

/// Emit a C string literal that preserves the input's UTF-8 bytes.
///
/// The C runtime takes `const char*` and copies bytes with `strlen`/`memcpy`,
/// so non-ASCII characters must be emitted as byte escapes rather than Rust's
/// `\u{...}` debug syntax.
pub(super) fn emit_c_string_literal(s: &str) -> String {
    let mut result = String::from("\"");
    for &byte in s.as_bytes() {
        match byte {
            b'"' => result.push_str("\\\""),
            b'\\' => result.push_str("\\\\"),
            b'\n' => result.push_str("\\n"),
            b'\r' => result.push_str("\\r"),
            b'\t' => result.push_str("\\t"),
            0x20..=0x21 | 0x23..=0x5B | 0x5D..=0x7E => result.push(byte as char),
            _ => {
                result.push('\\');
                result.push(char::from(b'0' + ((byte >> 6) & 0b111)));
                result.push(char::from(b'0' + ((byte >> 3) & 0b111)));
                result.push(char::from(b'0' + (byte & 0b111)));
            }
        }
    }
    result.push('"');
    result
}
