// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended FFI verification module.

use super::ffi_verify_ext::*;
use crate::ffi_bridge_ext::{
    AbiKind, AbiMismatch, FfiFunction, FfiParam, FfiType, MismatchSeverity,
};
use crate::ffi_verify::{ExternBindingData, FfiMismatch};
use crate::ir::IRType;
use crate::lcnf::{ExternAttr, ExternEntry};
use clean_kernel::Name;

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn make_func(lean: &str, ext: &str, params: Vec<FfiParam>, ret: FfiType) -> FfiFunction {
    FfiFunction {
        lean_name: name(lean),
        extern_name: ext.to_owned(),
        params,
        return_type: ret,
        abi: AbiKind::C,
        is_unsafe: false,
    }
}

fn make_func_abi(
    lean: &str,
    ext: &str,
    params: Vec<FfiParam>,
    ret: FfiType,
    abi: AbiKind,
) -> FfiFunction {
    FfiFunction {
        lean_name: name(lean),
        extern_name: ext.to_owned(),
        params,
        return_type: ret,
        abi,
        is_unsafe: false,
    }
}

fn param(n: &str, ty: FfiType) -> FfiParam {
    FfiParam {
        name: n.to_owned(),
        ffi_type: ty,
        is_borrowed: false,
    }
}

fn borrowed_param(n: &str, ty: FfiType) -> FfiParam {
    FfiParam {
        name: n.to_owned(),
        ffi_type: ty,
        is_borrowed: true,
    }
}

fn extern_data(backend: &str, extern_name: &str) -> ExternBindingData {
    ExternAttr {
        entries: vec![ExternEntry {
            backend: backend.to_owned(),
            name: extern_name.to_owned(),
        }],
    }
}

// ════════════════════════════════════════════════════════════════════
// is_calling_convention_valid
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_calling_conv_c_valid_everywhere() {
    assert!(is_calling_convention_valid(
        AbiKind::C,
        TargetPlatform::LinuxX86_64
    ));
    assert!(is_calling_convention_valid(
        AbiKind::C,
        TargetPlatform::MacOsArm64
    ));
    assert!(is_calling_convention_valid(
        AbiKind::C,
        TargetPlatform::WindowsX86_64
    ));
    assert!(is_calling_convention_valid(
        AbiKind::C,
        TargetPlatform::Generic
    ));
}

#[test]
fn test_calling_conv_cdecl_valid_everywhere() {
    assert!(is_calling_convention_valid(
        AbiKind::Cdecl,
        TargetPlatform::LinuxX86_64
    ));
    assert!(is_calling_convention_valid(
        AbiKind::Cdecl,
        TargetPlatform::WindowsX86_64
    ));
}

#[test]
fn test_calling_conv_system_valid_everywhere() {
    assert!(is_calling_convention_valid(
        AbiKind::System,
        TargetPlatform::LinuxX86_64
    ));
    assert!(is_calling_convention_valid(
        AbiKind::System,
        TargetPlatform::MacOsArm64
    ));
}

#[test]
fn test_calling_conv_stdcall_windows_only() {
    assert!(is_calling_convention_valid(
        AbiKind::Stdcall,
        TargetPlatform::WindowsX86_64
    ));
    assert!(!is_calling_convention_valid(
        AbiKind::Stdcall,
        TargetPlatform::LinuxX86_64
    ));
    assert!(!is_calling_convention_valid(
        AbiKind::Stdcall,
        TargetPlatform::MacOsArm64
    ));
}

#[test]
fn test_calling_conv_fastcall_windows_only() {
    assert!(is_calling_convention_valid(
        AbiKind::Fastcall,
        TargetPlatform::WindowsX86_64
    ));
    assert!(!is_calling_convention_valid(
        AbiKind::Fastcall,
        TargetPlatform::LinuxX86_64
    ));
    assert!(!is_calling_convention_valid(
        AbiKind::Fastcall,
        TargetPlatform::Generic
    ));
}

// ════════════════════════════════════════════════════════════════════
// verify_ffi_signature
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_verify_signature_valid_c_abi() {
    let func = make_func(
        "inc",
        "clean_inc",
        vec![param("x", FfiType::LeanObj)],
        FfiType::Unit,
    );
    let result = verify_ffi_signature(&func, TargetPlatform::LinuxX86_64, "c");
    assert!(
        result.errors.is_empty(),
        "valid C ABI should have no errors: {:?}",
        result.errors
    );
    assert_eq!(result.marshaling_steps.len(), 1);
}

#[test]
fn test_verify_signature_stdcall_on_linux_fails() {
    let func = make_func_abi(
        "win_fn",
        "win_fn",
        vec![param("x", FfiType::UInt32)],
        FfiType::UInt32,
        AbiKind::Stdcall,
    );
    let result = verify_ffi_signature(&func, TargetPlatform::LinuxX86_64, "c");
    assert!(
        !result.errors.is_empty(),
        "Stdcall on Linux should be an error"
    );
    assert!(result
        .errors
        .iter()
        .any(|e| matches!(e, FfiVerifyExtError::UnsupportedCallingConvention { .. })));
}

#[test]
fn test_verify_signature_stdcall_on_windows_ok() {
    let func = make_func_abi(
        "win_fn",
        "win_fn",
        vec![param("x", FfiType::UInt32)],
        FfiType::UInt32,
        AbiKind::Stdcall,
    );
    let result = verify_ffi_signature(&func, TargetPlatform::WindowsX86_64, "c");
    assert!(
        result.errors.is_empty(),
        "Stdcall on Windows should work: {:?}",
        result.errors
    );
}

#[test]
fn test_verify_signature_opaque_on_rust_backend_fails() {
    let func = make_func(
        "f",
        "ext_f",
        vec![param("x", FfiType::Opaque("MyType".to_owned()))],
        FfiType::Unit,
    );
    let result = verify_ffi_signature(&func, TargetPlatform::LinuxX86_64, "rust");
    assert!(result
        .errors
        .iter()
        .any(|e| matches!(e, FfiVerifyExtError::UnmappableType { .. })));
}

#[test]
fn test_verify_signature_borrowed_non_identity_marshaling() {
    let func = make_func(
        "f",
        "ext_f",
        vec![borrowed_param("x", FfiType::Nat)],
        FfiType::Unit,
    );
    let result = verify_ffi_signature(&func, TargetPlatform::LinuxX86_64, "c");
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, FfiVerifyExtError::InvalidMarshaling { .. })),
        "borrowed Nat needs ownership-sensitive conversion: {:?}",
        result.errors
    );
}

#[test]
fn test_verify_signature_empty_params() {
    let func = make_func("init", "clean_init", vec![], FfiType::Unit);
    let result = verify_ffi_signature(&func, TargetPlatform::LinuxX86_64, "c");
    assert!(result.errors.is_empty());
    assert!(result.marshaling_steps.is_empty());
}

// ════════════════════════════════════════════════════════════════════
// verify_ffi_binding_signature
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_binding_signature_valid() {
    let data = extern_data("c", "clean_inc");
    let func = make_func(
        "inc",
        "clean_inc",
        vec![param("x", FfiType::LeanObj)],
        FfiType::Unit,
    );
    let result =
        verify_ffi_binding_signature(&name("inc"), &data, &func, TargetPlatform::LinuxX86_64, "c");
    assert!(
        result.errors.is_empty(),
        "valid binding should pass: {:?}",
        result.errors
    );
}

#[test]
fn test_binding_signature_missing_native() {
    let data = ExternAttr {
        entries: vec![ExternEntry {
            backend: "llvm".to_owned(),
            name: "llvm_inc".to_owned(),
        }],
    };
    let func = make_func(
        "inc",
        "clean_inc",
        vec![param("x", FfiType::LeanObj)],
        FfiType::Unit,
    );
    let result =
        verify_ffi_binding_signature(&name("inc"), &data, &func, TargetPlatform::LinuxX86_64, "c");
    assert!(result
        .errors
        .iter()
        .any(|e| matches!(e, FfiVerifyExtError::MissingBinding { .. })));
}

#[test]
fn test_binding_signature_all_backend_matches() {
    let data = extern_data("all", "clean_inc");
    let func = make_func(
        "inc",
        "clean_inc",
        vec![param("x", FfiType::LeanObj)],
        FfiType::Unit,
    );
    let result =
        verify_ffi_binding_signature(&name("inc"), &data, &func, TargetPlatform::LinuxX86_64, "c");
    assert!(
        result.errors.is_empty(),
        "'all' backend should match: {:?}",
        result.errors
    );
}

// ════════════════════════════════════════════════════════════════════
// check_type_safety
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_type_safety_matching_scalars() {
    let func = make_func(
        "add",
        "ext_add",
        vec![param("x", FfiType::UInt32), param("y", FfiType::UInt32)],
        FfiType::UInt32,
    );
    let report = check_type_safety(&func, &[IRType::UInt32, IRType::UInt32], &IRType::UInt32);
    assert!(
        report.param_mismatches.is_empty(),
        "matching scalars should pass: {:?}",
        report.param_mismatches
    );
    assert!(report.return_mismatch.is_none());
}

#[test]
fn test_type_safety_object_variants_compatible() {
    let func = make_func(
        "f",
        "ext_f",
        vec![param("x", FfiType::Nat)],
        FfiType::String,
    );
    let report = check_type_safety(&func, &[IRType::Object], &IRType::Object);
    assert!(
        report.param_mismatches.is_empty(),
        "Nat/String/Object should be compatible: {:?}",
        report.param_mismatches
    );
    assert!(report.return_mismatch.is_none());
}

#[test]
fn test_type_safety_param_type_mismatch() {
    let func = make_func(
        "f",
        "ext_f",
        vec![param("x", FfiType::Double)],
        FfiType::Unit,
    );
    let report = check_type_safety(&func, &[IRType::UInt32], &IRType::Erased);
    assert!(
        !report.param_mismatches.is_empty(),
        "Double vs UInt32 should mismatch"
    );
    assert!(report
        .param_mismatches
        .iter()
        .any(|m| m.severity == MismatchSeverity::Error));
}

#[test]
fn test_type_safety_return_mismatch() {
    let func = make_func(
        "f",
        "ext_f",
        vec![param("x", FfiType::UInt32)],
        FfiType::Double,
    );
    let report = check_type_safety(&func, &[IRType::UInt32], &IRType::Bool);
    assert!(
        report.return_mismatch.is_some(),
        "Double return vs Bool IR should mismatch"
    );
}

#[test]
fn test_type_safety_arity_mismatch() {
    let func = make_func(
        "f",
        "ext_f",
        vec![param("x", FfiType::UInt32), param("y", FfiType::UInt32)],
        FfiType::Unit,
    );
    let report = check_type_safety(&func, &[IRType::UInt32], &IRType::Erased);
    assert!(
        report
            .param_mismatches
            .iter()
            .any(|m| m.param_name == "<arity>"),
        "arity mismatch should be reported"
    );
}

// ════════════════════════════════════════════════════════════════════
// FfiDependencyIndex
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_dependency_index_empty() {
    let index = FfiDependencyIndex::build(&[]);
    assert_eq!(index.symbol_count(), 0);
    assert_eq!(index.decl_count(), 0);
}

#[test]
fn test_dependency_index_single_function() {
    let func = make_func(
        "inc",
        "clean_inc",
        vec![param("x", FfiType::LeanObj)],
        FfiType::Unit,
    );
    let index = FfiDependencyIndex::build(&[func]);
    assert_eq!(index.symbol_count(), 1);
    assert_eq!(index.decl_count(), 1);
    assert_eq!(index.symbols_for_decl(&name("inc")), &["clean_inc"]);
    assert_eq!(index.decls_for_symbol("clean_inc"), &[name("inc")]);
}

#[test]
fn test_dependency_index_multiple_functions() {
    let func1 = make_func(
        "inc",
        "clean_inc",
        vec![param("x", FfiType::LeanObj)],
        FfiType::Unit,
    );
    let func2 = make_func(
        "dec",
        "clean_dec",
        vec![param("x", FfiType::LeanObj)],
        FfiType::Unit,
    );
    let index = FfiDependencyIndex::build(&[func1, func2]);
    assert_eq!(index.symbol_count(), 2);
    assert_eq!(index.decl_count(), 2);
}

#[test]
fn test_dependency_index_dedup() {
    let func = make_func(
        "inc",
        "clean_inc",
        vec![param("x", FfiType::LeanObj)],
        FfiType::Unit,
    );
    let index = FfiDependencyIndex::build(&[func.clone(), func]);
    assert_eq!(
        index.symbols_for_decl(&name("inc")).len(),
        1,
        "duplicate should not be added"
    );
}

#[test]
fn test_dependency_index_record_binding() {
    let mut index = FfiDependencyIndex::default();
    let data = extern_data("c", "clean_inc");
    index.record_binding(&name("inc"), &data);
    assert_eq!(index.symbols_for_decl(&name("inc")), &["clean_inc"]);
    assert_eq!(index.decls_for_symbol("clean_inc"), &[name("inc")]);
}

#[test]
fn test_dependency_index_unknown_decl() {
    let index = FfiDependencyIndex::default();
    assert!(index.symbols_for_decl(&name("nonexistent")).is_empty());
    assert!(index.decls_for_symbol("nonexistent").is_empty());
}

// ════════════════════════════════════════════════════════════════════
// diff_abi_versions
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_diff_identical() {
    let func = make_func(
        "inc",
        "clean_inc",
        vec![param("x", FfiType::LeanObj)],
        FfiType::Unit,
    );
    // `&[func.clone()]` and `&[func]` are both needed: the borrow check
    // would fail if we used `from_ref(&func)` on the first and moved `func`
    // on the second. The explicit clone is intentional.
    #[allow(clippy::cloned_ref_to_slice_refs)]
    let changes = diff_abi_versions(&[func.clone()], &[func]);
    assert!(
        changes.is_empty(),
        "identical functions should have no changes"
    );
}

#[test]
fn test_diff_removed() {
    let func = make_func(
        "inc",
        "clean_inc",
        vec![param("x", FfiType::LeanObj)],
        FfiType::Unit,
    );
    let changes = diff_abi_versions(&[func], &[]);
    assert!(changes.iter().any(|c| c.kind == AbiChangeKind::Removed));
}

#[test]
fn test_diff_added() {
    let func = make_func(
        "inc",
        "clean_inc",
        vec![param("x", FfiType::LeanObj)],
        FfiType::Unit,
    );
    let changes = diff_abi_versions(&[], &[func]);
    assert!(changes.iter().any(|c| c.kind == AbiChangeKind::Added));
}

#[test]
fn test_diff_arity_changed() {
    let old = make_func(
        "f",
        "ext_f",
        vec![param("x", FfiType::UInt32)],
        FfiType::Unit,
    );
    let new = make_func(
        "f",
        "ext_f",
        vec![param("x", FfiType::UInt32), param("y", FfiType::UInt32)],
        FfiType::Unit,
    );
    let changes = diff_abi_versions(&[old], &[new]);
    assert!(changes
        .iter()
        .any(|c| c.kind == AbiChangeKind::ArityChanged));
}

#[test]
fn test_diff_param_type_changed() {
    let old = make_func(
        "f",
        "ext_f",
        vec![param("x", FfiType::UInt32)],
        FfiType::Unit,
    );
    let new = make_func(
        "f",
        "ext_f",
        vec![param("x", FfiType::UInt64)],
        FfiType::Unit,
    );
    let changes = diff_abi_versions(&[old], &[new]);
    assert!(changes
        .iter()
        .any(|c| c.kind == AbiChangeKind::ParamTypeChanged));
}

#[test]
fn test_diff_return_type_changed() {
    let old = make_func("f", "ext_f", vec![], FfiType::UInt32);
    let new = make_func("f", "ext_f", vec![], FfiType::UInt64);
    let changes = diff_abi_versions(&[old], &[new]);
    assert!(changes
        .iter()
        .any(|c| c.kind == AbiChangeKind::ReturnTypeChanged));
}

#[test]
fn test_diff_calling_convention_changed() {
    let old = make_func_abi("f", "ext_f", vec![], FfiType::Unit, AbiKind::C);
    let new = make_func_abi("f", "ext_f", vec![], FfiType::Unit, AbiKind::Stdcall);
    let changes = diff_abi_versions(&[old], &[new]);
    assert!(changes
        .iter()
        .any(|c| c.kind == AbiChangeKind::CallingConventionChanged));
}

// ════════════════════════════════════════════════════════════════════
// verify_abi_compatibility
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_abi_compat_identical_ok() {
    let func = make_func(
        "inc",
        "clean_inc",
        vec![param("x", FfiType::LeanObj)],
        FfiType::Unit,
    );
    // See above: the explicit clone keeps both arguments separate slices.
    #[allow(clippy::cloned_ref_to_slice_refs)]
    let result = verify_abi_compatibility(&[func.clone()], &[func]);
    assert!(result.is_ok());
}

#[test]
fn test_abi_compat_breaking_change_err() {
    let old = make_func(
        "f",
        "ext_f",
        vec![param("x", FfiType::UInt32)],
        FfiType::Unit,
    );
    let new = make_func(
        "f",
        "ext_f",
        vec![param("x", FfiType::UInt32), param("y", FfiType::UInt32)],
        FfiType::Unit,
    );
    let result = verify_abi_compatibility(&[old], &[new]);
    assert!(result.is_err());
    match result {
        Err(FfiVerifyExtError::AbiBreak { .. }) => {}
        other => panic!("expected AbiBreak, got: {:?}", other),
    }
}

#[test]
fn test_abi_compat_addition_is_ok() {
    let old_func = make_func("f", "ext_f", vec![], FfiType::Unit);
    let new_func = make_func("g", "ext_g", vec![], FfiType::Unit);
    // See above: explicit clone separates the borrow from the move.
    #[allow(clippy::cloned_ref_to_slice_refs)]
    let result = verify_abi_compatibility(&[old_func.clone()], &[old_func, new_func]);
    assert!(result.is_ok(), "adding a new function should not break ABI");
}

// ════════════════════════════════════════════════════════════════════
// collect_diagnostics
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_collect_diagnostics_empty() {
    let verification = FfiSignatureVerification::default();
    let diags = collect_diagnostics(&verification);
    assert!(diags.is_empty());
}

#[test]
fn test_collect_diagnostics_from_errors() {
    let verification = FfiSignatureVerification {
        marshaling_steps: vec![],
        errors: vec![FfiVerifyExtError::MissingBinding {
            decl: name("f"),
            extern_name: "ext_f".to_owned(),
        }],
    };
    let diags = collect_diagnostics(&verification);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].level, DiagnosticLevel::Error);
}

// ════════════════════════════════════════════════════════════════════
// collect_type_safety_diagnostics
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_type_safety_diagnostics_empty() {
    let report = TypeSafetyReport::default();
    let diags = collect_type_safety_diagnostics(&report);
    assert!(diags.is_empty());
}

#[test]
fn test_type_safety_diagnostics_param_mismatch() {
    let report = TypeSafetyReport {
        param_mismatches: vec![TypeSafetyMismatch {
            param_name: "x".to_owned(),
            expected: "UInt32".to_owned(),
            actual: "Double".to_owned(),
            severity: MismatchSeverity::Error,
        }],
        return_mismatch: None,
    };
    let diags = collect_type_safety_diagnostics(&report);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].level, DiagnosticLevel::Error);
    assert!(diags[0].message.contains("x"));
}

#[test]
fn test_type_safety_diagnostics_return_mismatch() {
    let report = TypeSafetyReport {
        param_mismatches: vec![],
        return_mismatch: Some(AbiMismatch {
            param_index: None,
            expected: "void".to_owned(),
            actual: "UInt32".to_owned(),
            severity: MismatchSeverity::Error,
        }),
    };
    let diags = collect_type_safety_diagnostics(&report);
    assert_eq!(diags.len(), 1);
    assert!(diags[0].message.contains("return"));
}

// ════════════════════════════════════════════════════════════════════
// format_diagnostics
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_format_diagnostics_empty() {
    let output = format_diagnostics(&[]);
    assert!(output.is_empty());
}

#[test]
fn test_format_diagnostics_single() {
    let diags = vec![FfiDiagnostic {
        level: DiagnosticLevel::Error,
        function_name: "ext_f".to_owned(),
        message: "type mismatch".to_owned(),
    }];
    let output = format_diagnostics(&diags);
    assert!(output.contains("[error]"));
    assert!(output.contains("ext_f"));
    assert!(output.contains("type mismatch"));
}

#[test]
fn test_format_diagnostics_multiple() {
    let diags = vec![
        FfiDiagnostic {
            level: DiagnosticLevel::Error,
            function_name: "ext_f".to_owned(),
            message: "problem 1".to_owned(),
        },
        FfiDiagnostic {
            level: DiagnosticLevel::Warning,
            function_name: "ext_g".to_owned(),
            message: "problem 2".to_owned(),
        },
    ];
    let output = format_diagnostics(&diags);
    assert!(output.contains("[error]"));
    assert!(output.contains("[warning]"));
    assert!(output.lines().count() == 2);
}

// ════════════════════════════════════════════════════════════════════
// collect_mismatch_diagnostics
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_mismatch_diagnostics_unknown_extern() {
    let mismatch = FfiMismatch::UnknownExtern {
        decl: name("mystery"),
        backend: "c".to_owned(),
        extern_name: "clean_missing".to_owned(),
    };
    let diags = collect_mismatch_diagnostics(&mismatch);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].level, DiagnosticLevel::Error);
    assert!(diags[0].message.contains("unknown extern"));
}

#[test]
fn test_mismatch_diagnostics_arity() {
    let mismatch = FfiMismatch::ArityMismatch {
        decl: name("f"),
        backend: "c".to_owned(),
        extern_name: "clean_f".to_owned(),
        expected: "2".to_owned(),
        found: 1,
    };
    let diags = collect_mismatch_diagnostics(&mismatch);
    assert_eq!(diags.len(), 1);
    assert!(diags[0].message.contains("arity"));
}

#[test]
fn test_mismatch_diagnostics_type() {
    let mismatch = FfiMismatch::TypeMismatch {
        decl: name("f"),
        backend: "c".to_owned(),
        extern_name: "clean_f".to_owned(),
        expected: "void".to_owned(),
        found: "USize".to_owned(),
    };
    let diags = collect_mismatch_diagnostics(&mismatch);
    assert_eq!(diags.len(), 1);
    assert!(diags[0].message.contains("return"));
}

// ════════════════════════════════════════════════════════════════════
// Error Display
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_error_missing_binding_display() {
    let err = FfiVerifyExtError::MissingBinding {
        decl: name("inc"),
        extern_name: "clean_inc".to_owned(),
    };
    let msg = err.to_string();
    assert!(msg.contains("native extern binding"));
}

#[test]
fn test_error_unsupported_calling_conv_display() {
    let err = FfiVerifyExtError::UnsupportedCallingConvention {
        abi: AbiKind::Stdcall,
        platform: "LinuxX86_64".to_owned(),
    };
    let msg = err.to_string();
    assert!(msg.contains("unsupported calling convention"));
    assert!(msg.contains("Stdcall"));
}

#[test]
fn test_error_unmappable_type_display() {
    let err = FfiVerifyExtError::UnmappableType {
        ffi_type: FfiType::Opaque("MyType".to_owned()),
        param_name: "x".to_owned(),
        backend: "rust".to_owned(),
    };
    let msg = err.to_string();
    assert!(msg.contains("no native mapping"));
}

#[test]
fn test_error_invalid_marshaling_display() {
    let err = FfiVerifyExtError::InvalidMarshaling {
        param_name: "x".to_owned(),
        reason: "borrowed Nat requires ownership-sensitive conversion".to_owned(),
    };
    let msg = err.to_string();
    assert!(msg.contains("invalid marshaling"));
}

#[test]
fn test_error_abi_break_display() {
    let err = FfiVerifyExtError::AbiBreak {
        symbol: "ext_f".to_owned(),
        description: "arity changed".to_owned(),
    };
    let msg = err.to_string();
    assert!(msg.contains("ABI break"));
}

#[test]
fn test_error_from_base_mismatch() {
    let base = FfiMismatch::UnknownExtern {
        decl: name("f"),
        backend: "c".to_owned(),
        extern_name: "unknown".to_owned(),
    };
    let err: FfiVerifyExtError = base.into();
    let msg = err.to_string();
    assert!(msg.contains("unknown"));
}
