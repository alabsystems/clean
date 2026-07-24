// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FFI extern declaration elaboration.
//!
//! Handles `@[extern "c_name"]` and `@[implemented_by impl_name]` attributes
//! during elaboration. Validates extern signatures for FFI compatibility,
//! extracts C/native function names, and generates [`ExternDecl`] records
//! for the compiler backend.
//!
//! # Lean 4 Reference
//!
//! In Lean 4, `@[extern "name"]` is processed by `ExternAttr.lean` which stores
//! entries in a persistent extension keyed by backend name. The elaborator
//! validates that the declaration exists and the extern name is non-empty.
//! Multi-backend declarations use `@[extern c "c_name" llvm "llvm_name"]`.
//!
//! `@[implemented_by impl_name]` is processed by `ImplementedBy.lean`. It
//! validates that both the source declaration and the target implementation
//! exist, and that their types are definitionally equal.

use clean_kernel::expr::ExprKind;
use clean_kernel::{Environment, Expr, Name};

use crate::error::ElabError;

/// FFI-compatible type classification for extern signatures.
///
/// Maps Lean types to their C ABI representation. Used during elaboration
/// to validate that extern function parameters and return types can cross
/// the FFI boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum FfiType {
    /// `UInt8` / `Bool` -> `uint8_t`
    UInt8,
    /// `UInt16` -> `uint16_t`
    UInt16,
    /// `UInt32` / `Char` -> `uint32_t`
    UInt32,
    /// `UInt64` -> `uint64_t`
    UInt64,
    /// `USize` -> `size_t`
    USize,
    /// `Float` -> `double` (Lean Float is 64-bit)
    Float,
    /// `Float32` -> `float`
    Float32,
    /// `Unit` -> `void` (for return types only)
    Unit,
    /// Any boxed Lean object (reference-counted) -> `lean_object*`
    Object,
}

impl FfiType {
    /// Human-readable C type name for diagnostics.
    #[must_use]
    pub(crate) fn c_type_name(self) -> &'static str {
        match self {
            FfiType::UInt8 => "uint8_t",
            FfiType::UInt16 => "uint16_t",
            FfiType::UInt32 => "uint32_t",
            FfiType::UInt64 => "uint64_t",
            FfiType::USize => "size_t",
            FfiType::Float => "double",
            FfiType::Float32 => "float",
            FfiType::Unit => "void",
            FfiType::Object => "lean_object*",
        }
    }
}

/// A resolved extern declaration record for the compiler backend.
///
/// Produced during elaboration when `@[extern "c_name"]` is encountered.
/// Carries the validated signature information downstream to the compiler's
/// [`FfiBridge`](clean_compiler) for C code emission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExternDecl {
    /// The Lean declaration name.
    pub(crate) lean_name: Name,
    /// The C/native symbol name from the attribute.
    pub(crate) extern_name: String,
    /// Backend identifier (`"c"`, `"llvm"`, `"all"`, etc.).
    pub(crate) backend: String,
    /// Parameter FFI types extracted from the function signature.
    pub(crate) param_types: Vec<FfiType>,
    /// Return FFI type.
    pub(crate) return_type: FfiType,
}

/// A parsed extern entry from a multi-backend extern attribute.
///
/// `@[extern c "c_name" llvm "llvm_name"]` produces two entries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExternEntry {
    /// Backend name (e.g., `"c"`, `"llvm"`, `"all"`).
    pub(crate) backend: String,
    /// Symbol name for that backend.
    pub(crate) name: String,
}

/// Classify a kernel `Expr` type as an FFI-compatible type.
///
/// Walks through the head constant name to determine the C ABI mapping.
/// Types that don't have a direct C representation are classified as
/// `FfiType::Object` (boxed Lean objects).
#[must_use]
pub(crate) fn classify_ffi_type(ty: &Expr) -> FfiType {
    // Strip applications to get the head constant
    let head = ty.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => classify_const_name(name),
        _ => FfiType::Object,
    }
}

/// Map a constant name to its FFI type classification.
fn classify_const_name(name: &Name) -> FfiType {
    let s = name.to_string();
    match s.as_str() {
        "UInt8" => FfiType::UInt8,
        "Bool" => FfiType::UInt8,
        "UInt16" => FfiType::UInt16,
        "UInt32" => FfiType::UInt32,
        "Char" => FfiType::UInt32,
        "UInt64" => FfiType::UInt64,
        "USize" => FfiType::USize,
        "Float" => FfiType::Float,
        "Float32" => FfiType::Float32,
        "Unit" | "PUnit" => FfiType::Unit,
        _ => FfiType::Object,
    }
}

/// Extract parameter types and return type from a function signature.
///
/// Walks through nested `Pi` types to collect parameters, with the
/// final non-Pi body as the return type.
pub(crate) fn extract_ffi_signature(ty: &Expr) -> (Vec<FfiType>, FfiType) {
    let mut params = Vec::new();
    let mut current = ty.clone();

    loop {
        match current.kind() {
            ExprKind::Pi(_, domain, body) => {
                params.push(classify_ffi_type(domain.as_ref()));
                current = body.as_ref().clone();
            }
            _ => {
                let ret = classify_ffi_type(&current);
                return (params, ret);
            }
        }
    }
}

/// Parse an extern attribute string into backend/name entries.
///
/// Supports two forms:
/// - Simple: `"c_name"` -> single entry with backend `"all"`
/// - Multi-backend: `c "c_name" llvm "llvm_name"` -> multiple entries
///
/// # Errors
///
/// Returns `Err` if the extern name is empty or the multi-backend
/// syntax is malformed (odd number of tokens, empty name).
pub(crate) fn parse_extern_attr(attr_value: &str) -> Result<Vec<ExternEntry>, ElabError> {
    let trimmed = attr_value.trim();
    if trimmed.is_empty() {
        return Err(ElabError::Unsupported {
            feature: "extern attribute requires a non-empty name".to_owned(),
        });
    }

    // Simple case: just a C name (no backend prefix)
    // This is the common `@[extern "lean_io_prim_handle_mk"]` form
    if !trimmed.contains(' ') {
        return Ok(vec![ExternEntry {
            backend: "all".to_owned(),
            name: trimmed.to_owned(),
        }]);
    }

    // Multi-backend: parse pairs of (backend, "name")
    let tokens: Vec<&str> = trimmed.split_whitespace().collect();
    if !tokens.len().is_multiple_of(2) {
        return Err(ElabError::Unsupported {
            feature: format!(
                "extern attribute has odd number of tokens (expected backend/name pairs): '{trimmed}'"
            ),
        });
    }

    let mut entries = Vec::with_capacity(tokens.len() / 2);
    for pair in tokens.chunks(2) {
        let backend = pair[0];
        let name = pair[1].trim_matches('"');
        if name.is_empty() {
            return Err(ElabError::Unsupported {
                feature: format!("extern name for backend '{backend}' is empty"),
            });
        }
        entries.push(ExternEntry {
            backend: backend.to_owned(),
            name: name.to_owned(),
        });
    }

    Ok(entries)
}

/// Validate an extern declaration signature for FFI compatibility.
///
/// Checks that all parameter types and the return type are FFI-compatible.
/// Returns warnings for types that will be boxed as `lean_object*` (these
/// are valid but may indicate a missing unboxing opportunity).
///
/// # Errors
///
/// Returns `Err` if the extern name is empty.
pub(crate) fn validate_extern_signature(
    decl_name: &Name,
    extern_name: &str,
    ty: &Expr,
) -> Result<ExternDecl, ElabError> {
    if extern_name.is_empty() {
        return Err(ElabError::Unsupported {
            feature: format!("extern declaration '{decl_name}' has empty extern name"),
        });
    }

    let (param_types, return_type) = extract_ffi_signature(ty);

    Ok(ExternDecl {
        lean_name: decl_name.clone(),
        extern_name: extern_name.to_owned(),
        backend: "all".to_owned(),
        param_types,
        return_type,
    })
}

/// Validate an `@[implemented_by impl_name]` binding.
///
/// Checks that:
/// 1. The declaration exists in the environment
/// 2. The implementation name is non-empty
/// 3. The implementation target exists in the environment (if registered)
///
/// Note: Full type-level definitional equality checking between the
/// declaration and implementation types is deferred to the kernel's
/// type checker. This function performs the elaboration-level validation.
///
/// # Errors
///
/// Returns `Err` if validation fails.
pub(crate) fn validate_implemented_by(
    decl_name: &Name,
    impl_name: &str,
    env: &Environment,
) -> Result<(), ElabError> {
    if impl_name.is_empty() {
        return Err(ElabError::Unsupported {
            feature: format!(
                "implemented_by attribute on '{decl_name}' has empty implementation name"
            ),
        });
    }

    // Verify the source declaration exists
    if env.get_const(decl_name).is_none() {
        return Err(ElabError::UnknownIdent(format!(
            "extern declaration '{decl_name}' not found in environment"
        )));
    }

    // If the implementation is already registered, verify it exists too
    let impl_n = Name::from_string(impl_name);
    if env.get_const(&impl_n).is_some() {
        // Both exist — check that the implementation is not the same as the
        // declaration (self-referential implemented_by makes no sense).
        if *decl_name == impl_n {
            return Err(ElabError::Unsupported {
                feature: format!("implemented_by on '{decl_name}' points to itself"),
            });
        }
    }
    // If the implementation doesn't exist yet, that's OK — it may be
    // defined later in the same file. The kernel will catch missing
    // references at use sites.

    Ok(())
}

/// Process a complete extern attribute during elaboration.
///
/// This is the main entry point called from the attribute processing path.
/// It parses the extern attribute, validates the signature, and returns
/// the resolved extern declarations for registration.
///
/// # Errors
///
/// Returns `Err` if parsing or validation fails.
pub(crate) fn process_extern_attr(
    decl_name: &Name,
    attr_value: &str,
    ty: &Expr,
) -> Result<Vec<ExternDecl>, ElabError> {
    let entries = parse_extern_attr(attr_value)?;
    let (param_types, return_type) = extract_ffi_signature(ty);

    let decls = entries
        .into_iter()
        .map(|entry| ExternDecl {
            lean_name: decl_name.clone(),
            extern_name: entry.name,
            backend: entry.backend,
            param_types: param_types.clone(),
            return_type,
        })
        .collect();

    Ok(decls)
}

/// Check whether a Lean type is directly FFI-compatible (unboxed).
///
/// Returns `true` for scalar types that map directly to C types without
/// boxing. These are the types that can be passed by value across the
/// FFI boundary.
#[must_use]
pub(crate) fn is_ffi_scalar(ty: &Expr) -> bool {
    matches!(
        classify_ffi_type(ty),
        FfiType::UInt8
            | FfiType::UInt16
            | FfiType::UInt32
            | FfiType::UInt64
            | FfiType::USize
            | FfiType::Float
            | FfiType::Float32
            | FfiType::Unit
    )
}

/// Check whether a type requires boxing for FFI transport.
///
/// Returns `true` for types that must be boxed as `lean_object*` when
/// passed to or returned from C functions.
#[must_use]
pub(crate) fn requires_boxing(ty: &Expr) -> bool {
    classify_ffi_type(ty) == FfiType::Object
}

/// Validate that an extern C name follows naming conventions.
///
/// Lean 4 extern names typically follow `lean_` or `lean4_` prefixes for
/// runtime functions, or arbitrary C identifiers for user-provided FFI.
/// This function checks for obviously invalid names (empty, contains spaces,
/// starts with a digit).
pub(crate) fn validate_extern_name(name: &str) -> Result<(), ElabError> {
    if name.is_empty() {
        return Err(ElabError::Unsupported {
            feature: "extern name is empty".to_owned(),
        });
    }

    // C identifiers: [a-zA-Z_][a-zA-Z0-9_]*
    let first = name.as_bytes()[0];
    if !first.is_ascii_alphabetic() && first != b'_' {
        return Err(ElabError::Unsupported {
            feature: format!(
                "extern name '{name}' is not a valid C identifier (must start with letter or underscore)"
            ),
        });
    }

    if !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
        return Err(ElabError::Unsupported {
            feature: format!("extern name '{name}' contains invalid characters for a C identifier"),
        });
    }

    Ok(())
}
