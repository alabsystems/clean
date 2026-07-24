// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended FFI extern elaboration: `@[export]`, `@[implementedBy]` validation,
//! FFI safety checking, foreign type registration, ABI validation, extended
//! type mapping (Int8/16/32/64, ByteArray, FloatArray), extern constants,
//! and diagnostic error reporting.

use clean_kernel::expr::ExprKind;
use clean_kernel::{Expr, Name};

use crate::error::ElabError;
use crate::ffi_extern::{classify_ffi_type, extract_ffi_signature, FfiType};

/// Extended FFI type classification covering signed integers and pointer types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum ExtFfiType {
    /// Base FFI type (delegates to `FfiType` classification).
    Base(FfiType),
    /// `Int8` -> `int8_t`
    Int8,
    /// `Int16` -> `int16_t`
    Int16,
    /// `Int32` -> `int32_t`
    Int32,
    /// `Int64` -> `int64_t`
    Int64,
    /// `ByteArray` -> `uint8_t*` (pointer to byte buffer)
    ByteArray,
    /// `FloatArray` -> `double*` (pointer to float buffer)
    FloatArray,
}

impl ExtFfiType {
    /// Human-readable C type name for diagnostics.
    #[must_use]
    pub(crate) fn c_type_name(self) -> &'static str {
        match self {
            ExtFfiType::Base(base) => base.c_type_name(),
            ExtFfiType::Int8 => "int8_t",
            ExtFfiType::Int16 => "int16_t",
            ExtFfiType::Int32 => "int32_t",
            ExtFfiType::Int64 => "int64_t",
            ExtFfiType::ByteArray => "uint8_t*",
            ExtFfiType::FloatArray => "double*",
        }
    }

    /// Whether this type requires special ownership handling at the FFI boundary.
    #[must_use]
    pub(crate) fn requires_ownership_transfer(self) -> bool {
        matches!(
            self,
            ExtFfiType::ByteArray | ExtFfiType::FloatArray | ExtFfiType::Base(FfiType::Object)
        )
    }

    /// Whether this is a pointer type that needs lifetime management.
    #[must_use]
    pub(crate) fn is_pointer_type(self) -> bool {
        matches!(self, ExtFfiType::ByteArray | ExtFfiType::FloatArray)
    }
}

/// Classify a kernel `Expr` type using extended FFI type mapping.
#[must_use]
pub(crate) fn classify_ext_ffi_type(ty: &Expr) -> ExtFfiType {
    let head = ty.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => classify_ext_const_name(name),
        _ => ExtFfiType::Base(FfiType::Object),
    }
}

/// Map a constant name to its extended FFI type. Extended types are matched
/// first; unmatched names fall through to the base `classify_ffi_type`.
fn classify_ext_const_name(name: &Name) -> ExtFfiType {
    let s = name.to_string();
    match s.as_str() {
        "Int8" => ExtFfiType::Int8,
        "Int16" => ExtFfiType::Int16,
        "Int32" => ExtFfiType::Int32,
        "Int64" => ExtFfiType::Int64,
        "ByteArray" => ExtFfiType::ByteArray,
        "FloatArray" => ExtFfiType::FloatArray,
        _ => {
            let expr = Expr::const_str(&s);
            ExtFfiType::Base(classify_ffi_type(&expr))
        }
    }
}

/// A resolved `@[export]` declaration for C-callable wrapper generation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExportDecl {
    pub(crate) lean_name: Name,
    pub(crate) export_name: String,
    pub(crate) param_types: Vec<FfiType>,
    pub(crate) return_type: FfiType,
}

/// Process an `@[export]` attribute. Validates the export name as a C
/// identifier and extracts the FFI signature from the declaration type.
pub(crate) fn process_export_attr(
    decl_name: &Name,
    export_name: &str,
    ty: &Expr,
) -> Result<ExportDecl, ElabError> {
    validate_c_identifier(export_name)?;
    let (param_types, return_type) = extract_ffi_signature(ty);
    Ok(ExportDecl {
        lean_name: decl_name.clone(),
        export_name: export_name.to_owned(),
        param_types,
        return_type,
    })
}

/// A registered foreign (opaque) type. Always boxed as `lean_object*`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ForeignTypeDecl {
    pub(crate) lean_name: Name,
    pub(crate) c_type_name: String,
    pub(crate) has_finalizer: bool,
    pub(crate) has_foreach: bool,
}

/// Configuration for foreign type registration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ForeignTypeConfig {
    pub(crate) finalizer: bool,
    pub(crate) foreach: bool,
}

impl Default for ForeignTypeConfig {
    fn default() -> Self {
        Self {
            finalizer: true,
            foreach: false,
        }
    }
}

/// Register a foreign opaque type for FFI use.
pub(crate) fn register_foreign_type(
    lean_name: &Name,
    c_type_name: &str,
    config: &ForeignTypeConfig,
) -> Result<ForeignTypeDecl, ElabError> {
    validate_c_identifier(c_type_name)?;
    Ok(ForeignTypeDecl {
        lean_name: lean_name.clone(),
        c_type_name: c_type_name.to_owned(),
        has_finalizer: config.finalizer,
        has_foreach: config.foreach,
    })
}

/// ABI mismatch diagnostic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AbiMismatch {
    pub(crate) message: String,
}

/// Validate that two FFI signatures are ABI-compatible.
/// Returns a list of mismatches (empty = compatible).
#[must_use]
pub(crate) fn validate_abi_compatibility(
    expected_params: &[FfiType],
    expected_ret: FfiType,
    actual_params: &[FfiType],
    actual_ret: FfiType,
) -> Vec<AbiMismatch> {
    let mut mismatches = Vec::new();
    if expected_params.len() != actual_params.len() {
        mismatches.push(AbiMismatch {
            message: format!(
                "parameter count mismatch: expected {}, got {}",
                expected_params.len(),
                actual_params.len()
            ),
        });
        return mismatches;
    }
    for (i, (exp, act)) in expected_params.iter().zip(actual_params.iter()).enumerate() {
        if exp != act {
            mismatches.push(AbiMismatch {
                message: format!(
                    "parameter {} type mismatch: expected {}, got {}",
                    i,
                    exp.c_type_name(),
                    act.c_type_name()
                ),
            });
        }
    }
    if expected_ret != actual_ret {
        mismatches.push(AbiMismatch {
            message: format!(
                "return type mismatch: expected {}, got {}",
                expected_ret.c_type_name(),
                actual_ret.c_type_name()
            ),
        });
    }
    mismatches
}

/// FFI safety warning levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum FfiSafetyLevel {
    /// Fully safe: all scalar types, no ownership concerns.
    Safe,
    /// Requires care: boxed objects need refcount management.
    RequiresRefcounting,
    /// Potentially unsafe: pointer types with ownership transfer.
    OwnershipTransfer,
}

/// Check the FFI safety level of a function signature.
#[must_use]
pub(crate) fn check_ffi_safety(params: &[FfiType], ret: FfiType) -> FfiSafetyLevel {
    if params.contains(&FfiType::Object) || ret == FfiType::Object {
        return FfiSafetyLevel::RequiresRefcounting;
    }
    FfiSafetyLevel::Safe
}

/// Check the extended FFI safety level including pointer types.
#[must_use]
pub(crate) fn check_ext_ffi_safety(params: &[ExtFfiType], ret: ExtFfiType) -> FfiSafetyLevel {
    if params.iter().any(|p| p.is_pointer_type()) || ret.is_pointer_type() {
        return FfiSafetyLevel::OwnershipTransfer;
    }
    if params.iter().any(|p| p.requires_ownership_transfer()) || ret.requires_ownership_transfer() {
        return FfiSafetyLevel::RequiresRefcounting;
    }
    FfiSafetyLevel::Safe
}

/// An extern-defined constant (not a function). Produced when `@[extern]`
/// is applied to a non-function declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExternConst {
    pub(crate) lean_name: Name,
    pub(crate) extern_name: String,
    pub(crate) ffi_type: FfiType,
}

/// Elaborate an extern constant (non-function) declaration.
pub(crate) fn elaborate_extern_const(
    decl_name: &Name,
    extern_name: &str,
    ty: &Expr,
) -> Result<ExternConst, ElabError> {
    validate_c_identifier(extern_name)?;
    if matches!(ty.kind(), ExprKind::Pi(..)) {
        return Err(ElabError::Unsupported {
            feature: format!(
                "extern constant '{decl_name}' has function type; use @[extern] on a function instead"
            ),
        });
    }
    let ffi_type = classify_ffi_type(ty);
    Ok(ExternConst {
        lean_name: decl_name.clone(),
        extern_name: extern_name.to_owned(),
        ffi_type,
    })
}

/// Validate `@[implementedBy]` with FFI signature compatibility checking.
pub(crate) fn validate_implemented_by_ext(
    decl_name: &Name,
    impl_name: &str,
    decl_ty: &Expr,
    impl_ty: &Expr,
) -> Result<Vec<AbiMismatch>, ElabError> {
    if impl_name.is_empty() {
        return Err(ElabError::Unsupported {
            feature: format!(
                "implemented_by attribute on '{decl_name}' has empty implementation name"
            ),
        });
    }
    let (decl_params, decl_ret) = extract_ffi_signature(decl_ty);
    let (impl_params, impl_ret) = extract_ffi_signature(impl_ty);
    Ok(validate_abi_compatibility(
        &decl_params,
        decl_ret,
        &impl_params,
        impl_ret,
    ))
}

/// Format an FFI type mismatch error with diagnostic context.
#[must_use]
pub(crate) fn format_ffi_type_mismatch(
    decl_name: &Name,
    param_index: usize,
    expected: FfiType,
    actual: FfiType,
) -> String {
    format!(
        "FFI type mismatch in '{}' parameter {}: expected {} (C: {}), got {} (C: {})",
        decl_name,
        param_index,
        ffi_lean_name(expected),
        expected.c_type_name(),
        ffi_lean_name(actual),
        actual.c_type_name(),
    )
}

/// Format an FFI return type mismatch error.
#[must_use]
pub(crate) fn format_ffi_return_mismatch(
    decl_name: &Name,
    expected: FfiType,
    actual: FfiType,
) -> String {
    format!(
        "FFI return type mismatch in '{}': expected {} (C: {}), got {} (C: {})",
        decl_name,
        ffi_lean_name(expected),
        expected.c_type_name(),
        ffi_lean_name(actual),
        actual.c_type_name(),
    )
}

/// Get the Lean type name for an FFI type (for diagnostics).
fn ffi_lean_name(ty: FfiType) -> &'static str {
    match ty {
        FfiType::UInt8 => "UInt8",
        FfiType::UInt16 => "UInt16",
        FfiType::UInt32 => "UInt32",
        FfiType::UInt64 => "UInt64",
        FfiType::USize => "USize",
        FfiType::Float => "Float",
        FfiType::Float32 => "Float32",
        FfiType::Unit => "Unit",
        FfiType::Object => "Object",
    }
}

/// Validate that a string is a valid C identifier.
fn validate_c_identifier(name: &str) -> Result<(), ElabError> {
    if name.is_empty() {
        return Err(ElabError::Unsupported {
            feature: "C identifier is empty".to_owned(),
        });
    }
    let first = name.as_bytes()[0];
    if !first.is_ascii_alphabetic() && first != b'_' {
        return Err(ElabError::Unsupported {
            feature: format!(
                "'{name}' is not a valid C identifier (must start with letter or underscore)"
            ),
        });
    }
    if !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
        return Err(ElabError::Unsupported {
            feature: format!("'{name}' contains invalid characters for a C identifier"),
        });
    }
    Ok(())
}

/// Extract the extended FFI signature from a function type.
pub(crate) fn extract_ext_ffi_signature(ty: &Expr) -> (Vec<ExtFfiType>, ExtFfiType) {
    let mut params = Vec::new();
    let mut current = ty.clone();
    loop {
        match current.kind() {
            ExprKind::Pi(_, domain, body) => {
                params.push(classify_ext_ffi_type(domain.as_ref()));
                current = body.as_ref().clone();
            }
            _ => {
                let ret = classify_ext_ffi_type(&current);
                return (params, ret);
            }
        }
    }
}
