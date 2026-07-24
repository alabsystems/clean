// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended FFI verification for calling conventions, marshaling, type safety,
//! dependency tracking, ABI drift detection, and diagnostics.
//!
//! The structure follows Lean 4 `src/Lean/Compiler/IR/EmitC.lean`: first check
//! whether an extern call shape is legal on the target platform, then check
//! whether Lean IR types can safely cross the native boundary.

use std::collections::HashMap;

use crate::ffi_bridge_ext::{
    ir_type_to_ffi, AbiKind, AbiMismatch, FfiFunction, FfiParam, FfiType, MarshalingStep,
    MismatchSeverity,
};
use crate::ffi_verify::{ExternBindingData, ExternBindingEntry, FfiMismatch};
use crate::ir::IRType;
use clean_kernel::Name;
use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum TargetPlatform {
    LinuxX86_64,
    MacOsArm64,
    WindowsX86_64,
    Generic,
}

#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum FfiVerifyExtError {
    #[error(transparent)]
    BaseMismatch(#[from] FfiMismatch),
    #[error("unsupported calling convention {abi:?} on {platform}")]
    UnsupportedCallingConvention { abi: AbiKind, platform: String },
    #[error("no native mapping for {ffi_type:?} parameter {param_name} on backend {backend}")]
    UnmappableType {
        ffi_type: FfiType,
        param_name: String,
        backend: String,
    },
    #[error("invalid marshaling for parameter {param_name}: {reason}")]
    InvalidMarshaling { param_name: String, reason: String },
    #[error("ABI break for {symbol}: {description}")]
    AbiBreak { symbol: String, description: String },
    #[error("missing native extern binding for {decl:?}: {extern_name}")]
    MissingBinding { decl: Name, extern_name: String },
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct FfiSignatureVerification {
    pub(crate) marshaling_steps: Vec<MarshalingStep>,
    pub(crate) errors: Vec<FfiVerifyExtError>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeSafetyMismatch {
    pub(crate) param_name: String,
    pub(crate) expected: String,
    pub(crate) actual: String,
    pub(crate) severity: MismatchSeverity,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct TypeSafetyReport {
    pub(crate) param_mismatches: Vec<TypeSafetyMismatch>,
    pub(crate) return_mismatch: Option<AbiMismatch>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct FfiDependencyIndex {
    decl_to_symbols: HashMap<Name, Vec<String>>,
    symbol_to_decls: HashMap<String, Vec<Name>>,
}

impl FfiDependencyIndex {
    #[must_use]
    pub(crate) fn build(funcs: &[FfiFunction]) -> Self {
        let mut index = Self::default();
        for func in funcs {
            index.record_function(func);
        }
        index
    }

    pub(crate) fn record_function(&mut self, func: &FfiFunction) {
        self.record_symbol(&func.lean_name, &func.extern_name);
    }

    pub(crate) fn record_binding(&mut self, decl_name: &Name, extern_data: &ExternBindingData) {
        for entry in &extern_data.entries {
            self.record_entry(decl_name, entry);
        }
    }

    #[must_use]
    pub(crate) fn symbol_count(&self) -> usize {
        self.symbol_to_decls.len()
    }

    #[must_use]
    pub(crate) fn decl_count(&self) -> usize {
        self.decl_to_symbols.len()
    }

    #[must_use]
    pub(crate) fn symbols_for_decl(&self, name: &Name) -> &[String] {
        self.decl_to_symbols.get(name).map_or(&[], Vec::as_slice)
    }

    #[must_use]
    pub(crate) fn decls_for_symbol(&self, symbol: &str) -> &[Name] {
        self.symbol_to_decls.get(symbol).map_or(&[], Vec::as_slice)
    }

    fn record_entry(&mut self, decl_name: &Name, entry: &ExternBindingEntry) {
        self.record_symbol(decl_name, &entry.name);
    }

    fn record_symbol(&mut self, decl_name: &Name, symbol: &str) {
        let symbols = self.decl_to_symbols.entry(decl_name.clone()).or_default();
        if !symbols.iter().any(|existing| existing == symbol) {
            symbols.push(symbol.to_owned());
        }
        let decls = self.symbol_to_decls.entry(symbol.to_owned()).or_default();
        if !decls.iter().any(|existing| existing == decl_name) {
            decls.push(decl_name.clone());
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum AbiChangeKind {
    Added,
    Removed,
    ArityChanged,
    ParamTypeChanged,
    ReturnTypeChanged,
    CallingConventionChanged,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AbiChange {
    pub(crate) kind: AbiChangeKind,
    pub(crate) symbol: String,
    pub(crate) description: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub(crate) enum DiagnosticLevel {
    Note,
    Warning,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FfiDiagnostic {
    pub(crate) level: DiagnosticLevel,
    pub(crate) function_name: String,
    pub(crate) message: String,
}

#[must_use]
pub(crate) fn is_calling_convention_valid(abi: AbiKind, platform: TargetPlatform) -> bool {
    match abi {
        AbiKind::C | AbiKind::Cdecl | AbiKind::System => true,
        AbiKind::Stdcall | AbiKind::Fastcall => matches!(platform, TargetPlatform::WindowsX86_64),
    }
}

#[must_use]
pub(crate) fn verify_ffi_signature(
    func: &FfiFunction,
    platform: TargetPlatform,
    backend: &str,
) -> FfiSignatureVerification {
    let mut verification = FfiSignatureVerification {
        marshaling_steps: func
            .params
            .iter()
            .map(|param| marshaling_step_for(&param.ffi_type))
            .collect(),
        errors: Vec::new(),
    };
    if !is_calling_convention_valid(func.abi, platform) {
        verification
            .errors
            .push(FfiVerifyExtError::UnsupportedCallingConvention {
                abi: func.abi,
                platform: format!("{platform:?}"),
            });
    }
    for param in &func.params {
        validate_backend_type(
            &mut verification.errors,
            &param.ffi_type,
            &param.name,
            backend,
        );
        validate_marshaling(&mut verification.errors, param);
    }
    validate_backend_type(
        &mut verification.errors,
        &func.return_type,
        "<return>",
        backend,
    );
    verification
}

pub(crate) fn verify_ffi_binding_signature(
    decl_name: &Name,
    extern_data: &ExternBindingData,
    func: &FfiFunction,
    platform: TargetPlatform,
    backend: &str,
) -> FfiSignatureVerification {
    let mut verification = verify_ffi_signature(func, platform, backend);
    if !extern_data
        .entries
        .iter()
        .any(|entry| is_native_backend(&entry.backend) && entry.name == func.extern_name)
    {
        verification.errors.push(FfiVerifyExtError::MissingBinding {
            decl: decl_name.clone(),
            extern_name: func.extern_name.clone(),
        });
    }
    verification
}

#[must_use]
pub(crate) fn check_type_safety(
    func: &FfiFunction,
    param_types: &[IRType],
    return_type: &IRType,
) -> TypeSafetyReport {
    let mut report = TypeSafetyReport::default();
    if func.params.len() != param_types.len() {
        report.param_mismatches.push(TypeSafetyMismatch {
            param_name: "<arity>".to_owned(),
            expected: func.params.len().to_string(),
            actual: param_types.len().to_string(),
            severity: MismatchSeverity::Error,
        });
    }
    for (param, ir_type) in func.params.iter().zip(param_types.iter()) {
        if !ffi_type_safe_for_ir(&param.ffi_type, ir_type) {
            report.param_mismatches.push(TypeSafetyMismatch {
                param_name: param.name.clone(),
                expected: format!("{:?}", param.ffi_type),
                actual: format!("{:?}", ir_type_to_ffi(ir_type)),
                severity: MismatchSeverity::Error,
            });
        }
    }
    if !ffi_type_safe_for_ir(&func.return_type, return_type) {
        report.return_mismatch = Some(AbiMismatch {
            param_index: None,
            expected: format!("{:?}", func.return_type),
            actual: format!("{:?}", ir_type_to_ffi(return_type)),
            severity: MismatchSeverity::Error,
        });
    }
    report
}

#[must_use]
pub(crate) fn diff_abi_versions(old: &[FfiFunction], new: &[FfiFunction]) -> Vec<AbiChange> {
    let old_map: HashMap<&str, &FfiFunction> = old
        .iter()
        .map(|func| (func.extern_name.as_str(), func))
        .collect();
    let new_map: HashMap<&str, &FfiFunction> = new
        .iter()
        .map(|func| (func.extern_name.as_str(), func))
        .collect();
    let mut changes = Vec::new();

    for (symbol, old_func) in &old_map {
        let Some(new_func) = new_map.get(symbol) else {
            changes.push(AbiChange {
                kind: AbiChangeKind::Removed,
                symbol: (*symbol).to_owned(),
                description: format!("removed declaration {:?}", old_func.lean_name),
            });
            continue;
        };
        if old_func.abi != new_func.abi {
            changes.push(AbiChange {
                kind: AbiChangeKind::CallingConventionChanged,
                symbol: (*symbol).to_owned(),
                description: format!("{:?} -> {:?}", old_func.abi, new_func.abi),
            });
        }
        if old_func.params.len() != new_func.params.len() {
            changes.push(AbiChange {
                kind: AbiChangeKind::ArityChanged,
                symbol: (*symbol).to_owned(),
                description: format!("{} -> {}", old_func.params.len(), new_func.params.len()),
            });
        } else if old_func.params.iter().zip(new_func.params.iter()).any(
            |(old_param, new_param)| {
                old_param.ffi_type != new_param.ffi_type
                    || old_param.is_borrowed != new_param.is_borrowed
            },
        ) {
            changes.push(AbiChange {
                kind: AbiChangeKind::ParamTypeChanged,
                symbol: (*symbol).to_owned(),
                description: "parameter signature changed".to_owned(),
            });
        }
        if old_func.return_type != new_func.return_type {
            changes.push(AbiChange {
                kind: AbiChangeKind::ReturnTypeChanged,
                symbol: (*symbol).to_owned(),
                description: format!("{:?} -> {:?}", old_func.return_type, new_func.return_type),
            });
        }
    }

    for (symbol, new_func) in &new_map {
        if !old_map.contains_key(symbol) {
            changes.push(AbiChange {
                kind: AbiChangeKind::Added,
                symbol: (*symbol).to_owned(),
                description: format!("added declaration {:?}", new_func.lean_name),
            });
        }
    }
    changes
}

pub(crate) fn verify_abi_compatibility(
    old: &[FfiFunction],
    new: &[FfiFunction],
) -> Result<(), FfiVerifyExtError> {
    let Some(change) = diff_abi_versions(old, new).into_iter().find(|change| {
        matches!(
            change.kind,
            AbiChangeKind::Removed
                | AbiChangeKind::ArityChanged
                | AbiChangeKind::ParamTypeChanged
                | AbiChangeKind::ReturnTypeChanged
                | AbiChangeKind::CallingConventionChanged
        )
    }) else {
        return Ok(());
    };
    Err(FfiVerifyExtError::AbiBreak {
        symbol: change.symbol,
        description: change.description,
    })
}

#[must_use]
pub(crate) fn collect_diagnostics(verification: &FfiSignatureVerification) -> Vec<FfiDiagnostic> {
    let mut diagnostics = Vec::new();
    for error in &verification.errors {
        diagnostics.extend(diagnostics_for_error(error));
    }
    diagnostics
}

#[must_use]
pub(crate) fn collect_type_safety_diagnostics(report: &TypeSafetyReport) -> Vec<FfiDiagnostic> {
    let mut diagnostics = report
        .param_mismatches
        .iter()
        .map(|mismatch| FfiDiagnostic {
            level: diagnostic_level(mismatch.severity),
            function_name: mismatch.param_name.clone(),
            message: format!(
                "param {} expected {}, found {}",
                mismatch.param_name, mismatch.expected, mismatch.actual
            ),
        })
        .collect::<Vec<_>>();
    if let Some(return_mismatch) = &report.return_mismatch {
        diagnostics.push(FfiDiagnostic {
            level: diagnostic_level(return_mismatch.severity),
            function_name: "<return>".to_owned(),
            message: format!(
                "return expected {}, found {}",
                return_mismatch.expected, return_mismatch.actual
            ),
        });
    }
    diagnostics
}

#[must_use]
pub(crate) fn format_diagnostics(diagnostics: &[FfiDiagnostic]) -> String {
    diagnostics
        .iter()
        .map(|diag| {
            format!(
                "[{}] {}: {}",
                diagnostic_level_name(diag.level),
                diag.function_name,
                diag.message
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

#[must_use]
pub(crate) fn collect_mismatch_diagnostics(mismatch: &FfiMismatch) -> Vec<FfiDiagnostic> {
    match mismatch {
        FfiMismatch::UnknownExtern {
            decl, extern_name, ..
        } => vec![FfiDiagnostic {
            level: DiagnosticLevel::Error,
            function_name: name_to_string(decl),
            message: format!("unknown extern symbol {extern_name}"),
        }],
        FfiMismatch::ArityMismatch {
            decl,
            extern_name,
            expected,
            found,
            ..
        } => vec![FfiDiagnostic {
            level: DiagnosticLevel::Error,
            function_name: name_to_string(decl),
            message: format!("extern {extern_name} expected arity {expected}, found {found}"),
        }],
        FfiMismatch::TypeMismatch {
            decl,
            extern_name,
            expected,
            found,
            ..
        } => vec![FfiDiagnostic {
            level: DiagnosticLevel::Error,
            function_name: name_to_string(decl),
            message: format!("extern {extern_name} expected return {expected}, found {found}"),
        }],
    }
}

fn is_native_backend(backend: &str) -> bool {
    backend.eq_ignore_ascii_case("c") || backend.eq_ignore_ascii_case("all")
}

fn diagnostics_for_error(error: &FfiVerifyExtError) -> Vec<FfiDiagnostic> {
    match error {
        FfiVerifyExtError::BaseMismatch(mismatch) => collect_mismatch_diagnostics(mismatch),
        FfiVerifyExtError::UnsupportedCallingConvention { platform, .. } => vec![FfiDiagnostic {
            level: DiagnosticLevel::Error,
            function_name: platform.clone(),
            message: error.to_string(),
        }],
        FfiVerifyExtError::UnmappableType { param_name, .. }
        | FfiVerifyExtError::InvalidMarshaling { param_name, .. } => {
            vec![FfiDiagnostic {
                level: DiagnosticLevel::Error,
                function_name: param_name.clone(),
                message: error.to_string(),
            }]
        }
        FfiVerifyExtError::AbiBreak { symbol, .. } => vec![FfiDiagnostic {
            level: DiagnosticLevel::Error,
            function_name: symbol.clone(),
            message: error.to_string(),
        }],
        FfiVerifyExtError::MissingBinding { decl, extern_name } => vec![FfiDiagnostic {
            level: DiagnosticLevel::Error,
            function_name: name_to_string(decl),
            message: format!("missing native binding for {extern_name}"),
        }],
    }
}

fn validate_backend_type(
    errors: &mut Vec<FfiVerifyExtError>,
    ffi_type: &FfiType,
    param_name: &str,
    backend: &str,
) {
    if backend.eq_ignore_ascii_case("rust") && matches!(ffi_type, FfiType::Opaque(_)) {
        errors.push(FfiVerifyExtError::UnmappableType {
            ffi_type: ffi_type.clone(),
            param_name: param_name.to_owned(),
            backend: backend.to_owned(),
        });
    }
}

fn validate_marshaling(errors: &mut Vec<FfiVerifyExtError>, param: &FfiParam) {
    if param.is_borrowed
        && !matches!(
            marshaling_step_for(&param.ffi_type),
            MarshalingStep::BoxToPtr | MarshalingStep::Identity
        )
    {
        errors.push(FfiVerifyExtError::InvalidMarshaling {
            param_name: param.name.clone(),
            reason: format!(
                "borrowed {:?} requires ownership-sensitive conversion",
                param.ffi_type
            ),
        });
    }
}

fn ffi_type_safe_for_ir(ffi_type: &FfiType, ir_type: &IRType) -> bool {
    let lowered = ir_type_to_ffi(ir_type);
    ffi_types_compatible_ext(ffi_type, &lowered)
        || matches!(
            ffi_type,
            FfiType::Ptr(_) | FfiType::Array(_) | FfiType::Opaque(_)
        ) && ir_type.is_object()
}

fn ffi_types_compatible_ext(expected: &FfiType, actual: &FfiType) -> bool {
    if expected == actual {
        return true;
    }
    match (expected, actual) {
        (FfiType::Bool, FfiType::UInt8) | (FfiType::UInt8, FfiType::Bool) => true,
        (FfiType::Ptr(lhs), FfiType::Ptr(rhs))
        | (FfiType::Array(lhs), FfiType::Array(rhs))
        | (FfiType::Ptr(lhs), FfiType::Array(rhs))
        | (FfiType::Array(lhs), FfiType::Ptr(rhs)) => ffi_types_compatible_ext(lhs, rhs),
        _ => ffi_type_is_object(expected) && ffi_type_is_object(actual),
    }
}

fn ffi_type_is_object(ffi_type: &FfiType) -> bool {
    matches!(
        ffi_type,
        FfiType::LeanObj | FfiType::Nat | FfiType::Int | FfiType::String
    )
}

fn marshaling_step_for(ffi_type: &FfiType) -> MarshalingStep {
    match ffi_type {
        FfiType::LeanObj => MarshalingStep::BoxToPtr,
        FfiType::Nat | FfiType::Int => MarshalingStep::NatToUint,
        FfiType::String => MarshalingStep::StringToPtr,
        FfiType::Ptr(_) | FfiType::Array(_) => MarshalingStep::BoxToPtr,
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

fn diagnostic_level(severity: MismatchSeverity) -> DiagnosticLevel {
    match severity {
        MismatchSeverity::Info => DiagnosticLevel::Note,
        MismatchSeverity::Warning => DiagnosticLevel::Warning,
        MismatchSeverity::Error => DiagnosticLevel::Error,
    }
}

fn diagnostic_level_name(level: DiagnosticLevel) -> &'static str {
    match level {
        DiagnosticLevel::Note => "note",
        DiagnosticLevel::Warning => "warning",
        DiagnosticLevel::Error => "error",
    }
}

fn name_to_string(name: &Name) -> String {
    format!("{name}")
}
