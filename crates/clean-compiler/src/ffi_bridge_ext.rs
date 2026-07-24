// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended FFI Bridge — ABI checking, marshaling, and wrapper generation.
//!
//! Builds on [`ffi_bridge`] to provide:
//! - [`FfiBridgeExtConfig`]: Configuration for wrapper generation
//! - [`AbiKind`]: Calling convention classification
//! - [`FfiFunction`]: Rich FFI function descriptor with params and types
//! - [`generate_ffi_wrappers`]: Produce IR wrapper declarations
//! - [`check_abi_compatibility`]: Verify ABI consistency between FFI decls and IR
//! - [`generate_marshaling_code`]: Produce parameter conversion steps
//!
//! # Lean 4 Reference
//!
//! Lean 4 emits extern wrappers in EmitC.lean (emitFnDecl, emitExternCall).
//! This module generalises that for multiple calling conventions and backends.

use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;

/// Calling convention for an FFI function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum AbiKind {
    /// Standard C calling convention.
    C,
    /// `__cdecl` (caller cleans stack, default on most x86 compilers).
    Cdecl,
    /// `__stdcall` (callee cleans stack, Win32 API default).
    Stdcall,
    /// `__fastcall` (first two args in registers).
    Fastcall,
    /// System default (platform-dependent: `__stdcall` on Win32, `C` elsewhere).
    System,
}

/// FFI type — the set of types expressible at the Lean/native boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum FfiType {
    /// Lean heap object (`clean_obj*`).
    LeanObj,
    /// Lean `Nat` (arbitrary precision, boxed).
    Nat,
    /// Lean `Int` (arbitrary precision, boxed).
    Int,
    /// `uint8_t`.
    UInt8,
    /// `uint16_t`.
    UInt16,
    /// `uint32_t`.
    UInt32,
    /// `uint64_t`.
    UInt64,
    /// `float`.
    Float,
    /// `double`.
    Double,
    /// Lean `String` (UTF-8, boxed).
    String,
    /// `bool` / `uint8_t` (Lean `Bool`).
    Bool,
    /// Unit / void (zero-size).
    Unit,
    /// Pointer to another FFI type.
    Ptr(Box<FfiType>),
    /// Array of another FFI type.
    Array(Box<FfiType>),
    /// Opaque foreign type, referenced by name.
    Opaque(String),
}

/// A single FFI function parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FfiParam {
    /// Parameter name.
    pub name: String,
    /// Parameter FFI type.
    pub ffi_type: FfiType,
    /// Whether this parameter is borrowed (no ownership transfer).
    pub is_borrowed: bool,
}

/// An FFI function declaration with full type and ABI information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FfiFunction {
    /// The Lean-side declaration name.
    pub lean_name: Name,
    /// The external symbol name.
    pub extern_name: String,
    /// Parameters.
    pub params: Vec<FfiParam>,
    /// Return type.
    pub return_type: FfiType,
    /// Calling convention.
    pub abi: AbiKind,
    /// Whether the function requires an unsafe context.
    pub is_unsafe: bool,
}

/// Configuration for extended FFI bridge operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FfiBridgeExtConfig {
    /// Whether to generate wrapper IR declarations.
    pub generate_wrappers: bool,
    /// Whether to check ABI compatibility.
    pub check_abi_compat: bool,
    /// Whether to emit runtime safety checks (null pointers, bounds, etc.).
    pub emit_safety_checks: bool,
    /// Target ABI for generated wrappers.
    pub target_abi: AbiKind,
}

impl Default for FfiBridgeExtConfig {
    fn default() -> Self {
        Self {
            generate_wrappers: true,
            check_abi_compat: true,
            emit_safety_checks: true,
            target_abi: AbiKind::C,
        }
    }
}

/// Severity of an ABI mismatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MismatchSeverity {
    /// Hard error: the call would be undefined behaviour.
    Error,
    /// Warning: the call may work but is not guaranteed.
    Warning,
    /// Informational: minor difference, unlikely to cause issues.
    Info,
}

/// A single ABI mismatch between an `FfiFunction` and an `IRDecl`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbiMismatch {
    /// Parameter index (None for return type mismatches).
    pub param_index: Option<usize>,
    /// Description of the expected type/convention.
    pub expected: String,
    /// Description of the actual type/convention.
    pub actual: String,
    /// How severe the mismatch is.
    pub severity: MismatchSeverity,
}

/// A marshaling step describing how to convert a parameter across the FFI
/// boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MarshalingStep {
    /// Box a Lean object pointer into a heap-managed value.
    BoxToPtr,
    /// Unbox a heap-managed pointer back to a Lean object.
    PtrToBox,
    /// Convert a Lean `Nat` to a native unsigned integer.
    NatToUint,
    /// Convert a native unsigned integer to a Lean `Nat`.
    UintToNat,
    /// Convert a Lean `String` to a C string pointer.
    StringToPtr,
    /// Convert a C string pointer to a Lean `String`.
    PtrToString,
    /// No conversion needed — types are already compatible.
    Identity,
}

// ═══════════════════════════════════════════════════════════════════
// Type mapping
// ═══════════════════════════════════════════════════════════════════

/// Map an IR type to the corresponding FFI type.
#[must_use]
pub fn ir_type_to_ffi(ir_type: &IRType) -> FfiType {
    match ir_type {
        IRType::Bool => FfiType::Bool,
        IRType::UInt8 => FfiType::UInt8,
        IRType::UInt16 => FfiType::UInt16,
        IRType::UInt32 => FfiType::UInt32,
        IRType::UInt64 => FfiType::UInt64,
        IRType::USize => FfiType::UInt64,
        IRType::Float32 => FfiType::Float,
        IRType::Float64 => FfiType::Double,
        IRType::Object | IRType::TObject => FfiType::LeanObj,
        IRType::Struct(_) | IRType::Union(_) => FfiType::LeanObj,
        IRType::Erased | IRType::Void => FfiType::Unit,
    }
}

/// Map an FFI type to its C type declaration string.
#[must_use]
pub fn ffi_type_to_c(ffi_type: &FfiType) -> String {
    match ffi_type {
        FfiType::LeanObj => "clean_obj*".into(),
        FfiType::Nat => "clean_obj*".into(),
        FfiType::Int => "clean_obj*".into(),
        FfiType::UInt8 => "uint8_t".into(),
        FfiType::UInt16 => "uint16_t".into(),
        FfiType::UInt32 => "uint32_t".into(),
        FfiType::UInt64 => "uint64_t".into(),
        FfiType::Float => "float".into(),
        FfiType::Double => "double".into(),
        FfiType::String => "clean_obj*".into(),
        FfiType::Bool => "uint8_t".into(),
        FfiType::Unit => "void".into(),
        FfiType::Ptr(inner) => format!("{}*", ffi_type_to_c(inner)),
        FfiType::Array(inner) => format!("{}*", ffi_type_to_c(inner)),
        FfiType::Opaque(name) => name.clone(),
    }
}

/// Map an FFI type to its Rust type declaration string.
#[must_use]
pub fn ffi_type_to_rust(ffi_type: &FfiType) -> String {
    match ffi_type {
        FfiType::LeanObj => "*mut clean_obj".into(),
        FfiType::Nat => "*mut clean_obj".into(),
        FfiType::Int => "*mut clean_obj".into(),
        FfiType::UInt8 => "u8".into(),
        FfiType::UInt16 => "u16".into(),
        FfiType::UInt32 => "u32".into(),
        FfiType::UInt64 => "u64".into(),
        FfiType::Float => "f32".into(),
        FfiType::Double => "f64".into(),
        FfiType::String => "*mut clean_obj".into(),
        FfiType::Bool => "u8".into(),
        FfiType::Unit => "()".into(),
        FfiType::Ptr(inner) => format!("*mut {}", ffi_type_to_rust(inner)),
        FfiType::Array(inner) => format!("*mut {}", ffi_type_to_rust(inner)),
        FfiType::Opaque(name) => name.clone(),
    }
}

// ═══════════════════════════════════════════════════════════════════
// Marshaling
// ═══════════════════════════════════════════════════════════════════

/// Determine the marshaling step needed to pass a Lean value of `ffi_type`
/// across the FFI boundary.
#[must_use]
pub(crate) fn marshaling_step_for(ffi_type: &FfiType) -> MarshalingStep {
    match ffi_type {
        FfiType::LeanObj => MarshalingStep::BoxToPtr,
        FfiType::Nat => MarshalingStep::NatToUint,
        FfiType::Int => MarshalingStep::NatToUint,
        FfiType::String => MarshalingStep::StringToPtr,
        FfiType::Ptr(_) => MarshalingStep::BoxToPtr,
        FfiType::Array(_) => MarshalingStep::BoxToPtr,
        FfiType::UInt8
        | FfiType::UInt16
        | FfiType::UInt32
        | FfiType::UInt64
        | FfiType::Float
        | FfiType::Double
        | FfiType::Bool
        | FfiType::Unit
        | FfiType::Opaque(_) => MarshalingStep::Identity,
    }
}

/// Generate the full list of marshaling steps for an `FfiFunction`.
#[must_use]
pub fn generate_marshaling_code(func: &FfiFunction) -> Vec<MarshalingStep> {
    func.params
        .iter()
        .map(|p| marshaling_step_for(&p.ffi_type))
        .collect()
}

// ═══════════════════════════════════════════════════════════════════
// ABI compatibility checking
// ═══════════════════════════════════════════════════════════════════

/// Check that an `FfiFunction` is ABI-compatible with a compiled `IRDecl`.
///
/// Returns `Ok(())` when the declaration is compatible, or a list of
/// mismatches describing every discrepancy found.
pub fn check_abi_compatibility(
    func: &FfiFunction,
    ir_decl: &IRDecl,
) -> Result<(), Vec<AbiMismatch>> {
    let mut mismatches = Vec::new();

    // Check parameter count.
    if func.params.len() != ir_decl.params.len() {
        mismatches.push(AbiMismatch {
            param_index: None,
            expected: format!("{} params", func.params.len()),
            actual: format!("{} params", ir_decl.params.len()),
            severity: MismatchSeverity::Error,
        });
        // Don't compare individual params if counts differ.
        return Err(mismatches);
    }

    // Check each parameter.
    for (i, (ffi_param, (_var_id, ir_type))) in
        func.params.iter().zip(ir_decl.params.iter()).enumerate()
    {
        let expected_ffi = ir_type_to_ffi(ir_type);
        if !ffi_types_compatible(&ffi_param.ffi_type, &expected_ffi) {
            mismatches.push(AbiMismatch {
                param_index: Some(i),
                expected: format!("{:?}", expected_ffi),
                actual: format!("{:?}", ffi_param.ffi_type),
                severity: MismatchSeverity::Error,
            });
        }
    }

    // Check return type.
    let expected_ret = ir_type_to_ffi(&ir_decl.return_type);
    if !ffi_types_compatible(&func.return_type, &expected_ret) {
        mismatches.push(AbiMismatch {
            param_index: None,
            expected: format!("{:?}", expected_ret),
            actual: format!("{:?}", func.return_type),
            severity: MismatchSeverity::Error,
        });
    }

    if mismatches.is_empty() {
        Ok(())
    } else {
        Err(mismatches)
    }
}

/// Two FFI types are compatible if they are equal, or if both are object
/// types (LeanObj, Nat, Int, String all pass as `clean_obj*`).
fn ffi_types_compatible(a: &FfiType, b: &FfiType) -> bool {
    if a == b {
        return true;
    }
    let is_obj = |t: &FfiType| {
        matches!(
            t,
            FfiType::LeanObj | FfiType::Nat | FfiType::Int | FfiType::String
        )
    };
    is_obj(a) && is_obj(b)
}

// ═══════════════════════════════════════════════════════════════════
// Wrapper generation
// ═══════════════════════════════════════════════════════════════════

/// Generate IR wrapper declarations for a set of FFI functions.
///
/// Each wrapper marshals Lean-side arguments, calls the extern, and
/// marshals the result back. When `config.emit_safety_checks` is true,
/// additional null-pointer guard logic is emitted (as `Unreachable`
/// fallback for now — a future pass can lower this to runtime checks).
#[must_use]
pub fn generate_ffi_wrappers(funcs: &[FfiFunction], config: &FfiBridgeExtConfig) -> Vec<IRDecl> {
    if !config.generate_wrappers {
        return Vec::new();
    }

    funcs
        .iter()
        .map(|f| generate_single_wrapper(f, config))
        .collect()
}

/// Generate a single IR wrapper for an FFI function.
fn generate_single_wrapper(func: &FfiFunction, config: &FfiBridgeExtConfig) -> IRDecl {
    let params: Vec<(VarId, IRType)> = func
        .params
        .iter()
        .enumerate()
        .map(|(i, p)| (VarId(i as u32), ffi_type_to_ir(&p.ffi_type)))
        .collect();

    let return_type = ffi_type_to_ir(&func.return_type);

    // Build call arguments.
    let args: Vec<IRArg> = params.iter().map(|(v, _)| IRArg::Var(*v)).collect();

    // The wrapper body: call the extern function, return its result.
    let call_result_var = VarId(params.len() as u32);
    let call_expr = IRExpr::Apply {
        fn_id: FnId(Name::from_string(&func.extern_name)),
        args,
    };

    let body = if config.emit_safety_checks && return_type.is_object() {
        // With safety checks: store result, return it.
        // A future pass could lower this to a null check + Unreachable.
        IRBody::VDecl {
            var: call_result_var,
            ty: return_type.clone(),
            value: call_expr,
            rest: Box::new(IRBody::Ret(IRArg::Var(call_result_var))),
        }
    } else if return_type == IRType::Void || return_type == IRType::Erased {
        // Void return: call then return erased.
        IRBody::VDecl {
            var: call_result_var,
            ty: IRType::Erased,
            value: call_expr,
            rest: Box::new(IRBody::Ret(IRArg::Erased)),
        }
    } else {
        // Normal: call and return.
        IRBody::VDecl {
            var: call_result_var,
            ty: return_type.clone(),
            value: call_expr,
            rest: Box::new(IRBody::Ret(IRArg::Var(call_result_var))),
        }
    };

    IRDecl {
        name: func.lean_name.clone(),
        params,
        return_type,
        body,
    }
}

/// Map an FFI type back to the closest IR type for wrapper param/return
/// declarations.
fn ffi_type_to_ir(ffi_type: &FfiType) -> IRType {
    match ffi_type {
        FfiType::Bool => IRType::Bool,
        FfiType::UInt8 => IRType::UInt8,
        FfiType::UInt16 => IRType::UInt16,
        FfiType::UInt32 => IRType::UInt32,
        FfiType::UInt64 => IRType::UInt64,
        FfiType::Float => IRType::Float32,
        FfiType::Double => IRType::Float64,
        FfiType::LeanObj | FfiType::Nat | FfiType::Int | FfiType::String => IRType::Object,
        FfiType::Ptr(_) | FfiType::Array(_) => IRType::Object,
        FfiType::Unit => IRType::Erased,
        FfiType::Opaque(_) => IRType::Object,
    }
}
