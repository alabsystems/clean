// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended FFI extern elaboration.

use clean_kernel::{Expr, Name};

use crate::ffi_extern::FfiType;
use crate::ffi_extern_ext::{
    check_ext_ffi_safety, check_ffi_safety, classify_ext_ffi_type, elaborate_extern_const,
    extract_ext_ffi_signature, format_ffi_return_mismatch, format_ffi_type_mismatch,
    process_export_attr, register_foreign_type, validate_abi_compatibility,
    validate_implemented_by_ext, ExtFfiType, FfiSafetyLevel, ForeignTypeConfig,
};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

// ============================================================================
// ExtFfiType classification tests
// ============================================================================

#[test]
fn test_classify_ext_ffi_type_int8() {
    let ty = Expr::const_str("Int8");
    assert_eq!(classify_ext_ffi_type(&ty), ExtFfiType::Int8);
}

#[test]
fn test_classify_ext_ffi_type_int16() {
    let ty = Expr::const_str("Int16");
    assert_eq!(classify_ext_ffi_type(&ty), ExtFfiType::Int16);
}

#[test]
fn test_classify_ext_ffi_type_int32() {
    let ty = Expr::const_str("Int32");
    assert_eq!(classify_ext_ffi_type(&ty), ExtFfiType::Int32);
}

#[test]
fn test_classify_ext_ffi_type_int64() {
    let ty = Expr::const_str("Int64");
    assert_eq!(classify_ext_ffi_type(&ty), ExtFfiType::Int64);
}

#[test]
fn test_classify_ext_ffi_type_byte_array() {
    let ty = Expr::const_str("ByteArray");
    assert_eq!(classify_ext_ffi_type(&ty), ExtFfiType::ByteArray);
}

#[test]
fn test_classify_ext_ffi_type_float_array() {
    let ty = Expr::const_str("FloatArray");
    assert_eq!(classify_ext_ffi_type(&ty), ExtFfiType::FloatArray);
}

#[test]
fn test_classify_ext_ffi_type_base_uint32() {
    let ty = Expr::const_str("UInt32");
    assert_eq!(
        classify_ext_ffi_type(&ty),
        ExtFfiType::Base(FfiType::UInt32)
    );
}

#[test]
fn test_classify_ext_ffi_type_base_object() {
    let ty = Expr::const_str("Nat");
    assert_eq!(
        classify_ext_ffi_type(&ty),
        ExtFfiType::Base(FfiType::Object)
    );
}

#[test]
fn test_classify_ext_ffi_type_bvar_is_object() {
    let ty = Expr::bvar(0);
    assert_eq!(
        classify_ext_ffi_type(&ty),
        ExtFfiType::Base(FfiType::Object)
    );
}

// ============================================================================
// ExtFfiType method tests
// ============================================================================

#[test]
fn test_ext_ffi_type_c_type_names() {
    assert_eq!(ExtFfiType::Int8.c_type_name(), "int8_t");
    assert_eq!(ExtFfiType::Int16.c_type_name(), "int16_t");
    assert_eq!(ExtFfiType::Int32.c_type_name(), "int32_t");
    assert_eq!(ExtFfiType::Int64.c_type_name(), "int64_t");
    assert_eq!(ExtFfiType::ByteArray.c_type_name(), "uint8_t*");
    assert_eq!(ExtFfiType::FloatArray.c_type_name(), "double*");
    assert_eq!(ExtFfiType::Base(FfiType::UInt64).c_type_name(), "uint64_t");
}

#[test]
fn test_ext_ffi_type_ownership_transfer() {
    assert!(ExtFfiType::ByteArray.requires_ownership_transfer());
    assert!(ExtFfiType::FloatArray.requires_ownership_transfer());
    assert!(ExtFfiType::Base(FfiType::Object).requires_ownership_transfer());
    assert!(!ExtFfiType::Int32.requires_ownership_transfer());
    assert!(!ExtFfiType::Base(FfiType::UInt64).requires_ownership_transfer());
}

#[test]
fn test_ext_ffi_type_is_pointer_type() {
    assert!(ExtFfiType::ByteArray.is_pointer_type());
    assert!(ExtFfiType::FloatArray.is_pointer_type());
    assert!(!ExtFfiType::Int32.is_pointer_type());
    assert!(!ExtFfiType::Base(FfiType::Object).is_pointer_type());
}

// ============================================================================
// @[export] attribute processing tests
// ============================================================================

#[test]
fn test_process_export_attr_simple() {
    let ty = Expr::arrow(Expr::const_str("UInt32"), Expr::const_str("UInt64"));
    let decl =
        process_export_attr(&name("MyMod.myFunc"), "lean_my_func", &ty).expect("should succeed");
    assert_eq!(decl.lean_name, name("MyMod.myFunc"));
    assert_eq!(decl.export_name, "lean_my_func");
    assert_eq!(decl.param_types, vec![FfiType::UInt32]);
    assert_eq!(decl.return_type, FfiType::UInt64);
}

#[test]
fn test_process_export_attr_no_params() {
    let ty = Expr::const_str("Unit");
    let decl = process_export_attr(&name("init"), "lean_init", &ty).expect("should succeed");
    assert!(decl.param_types.is_empty());
    assert_eq!(decl.return_type, FfiType::Unit);
}

#[test]
fn test_process_export_attr_empty_name_fails() {
    let ty = Expr::const_str("Unit");
    let result = process_export_attr(&name("init"), "", &ty);
    assert!(result.is_err());
}

#[test]
fn test_process_export_attr_invalid_name_fails() {
    let ty = Expr::const_str("Unit");
    let result = process_export_attr(&name("init"), "3bad", &ty);
    assert!(result.is_err());
}

#[test]
fn test_process_export_attr_dash_in_name_fails() {
    let ty = Expr::const_str("Unit");
    let result = process_export_attr(&name("init"), "my-export", &ty);
    assert!(result.is_err());
}

// ============================================================================
// Foreign type registration tests
// ============================================================================

#[test]
fn test_register_foreign_type_default_config() {
    let config = ForeignTypeConfig::default();
    let decl = register_foreign_type(&name("IO.FS.Handle"), "lean_io_handle", &config)
        .expect("should succeed");
    assert_eq!(decl.lean_name, name("IO.FS.Handle"));
    assert_eq!(decl.c_type_name, "lean_io_handle");
    assert!(decl.has_finalizer);
    assert!(!decl.has_foreach);
}

#[test]
fn test_register_foreign_type_custom_config() {
    let config = ForeignTypeConfig {
        finalizer: false,
        foreach: true,
    };
    let decl = register_foreign_type(&name("Task"), "lean_task", &config).expect("should succeed");
    assert!(!decl.has_finalizer);
    assert!(decl.has_foreach);
}

#[test]
fn test_register_foreign_type_empty_name_fails() {
    let config = ForeignTypeConfig::default();
    let result = register_foreign_type(&name("Bad"), "", &config);
    assert!(result.is_err());
}

#[test]
fn test_register_foreign_type_invalid_name_fails() {
    let config = ForeignTypeConfig::default();
    let result = register_foreign_type(&name("Bad"), "1invalid", &config);
    assert!(result.is_err());
}

// ============================================================================
// ABI validation tests
// ============================================================================

#[test]
fn test_validate_abi_compatibility_matching() {
    let params = vec![FfiType::UInt32, FfiType::UInt64];
    let mismatches = validate_abi_compatibility(&params, FfiType::UInt8, &params, FfiType::UInt8);
    assert!(mismatches.is_empty());
}

#[test]
fn test_validate_abi_compatibility_param_count_mismatch() {
    let expected = vec![FfiType::UInt32, FfiType::UInt64];
    let actual = vec![FfiType::UInt32];
    let mismatches = validate_abi_compatibility(&expected, FfiType::Unit, &actual, FfiType::Unit);
    assert_eq!(mismatches.len(), 1);
    assert!(mismatches[0].message.contains("parameter count"));
}

#[test]
fn test_validate_abi_compatibility_param_type_mismatch() {
    let expected = vec![FfiType::UInt32];
    let actual = vec![FfiType::UInt64];
    let mismatches = validate_abi_compatibility(&expected, FfiType::Unit, &actual, FfiType::Unit);
    assert_eq!(mismatches.len(), 1);
    assert!(mismatches[0].message.contains("parameter 0"));
}

#[test]
fn test_validate_abi_compatibility_return_type_mismatch() {
    let params = vec![FfiType::UInt32];
    let mismatches = validate_abi_compatibility(&params, FfiType::UInt32, &params, FfiType::UInt64);
    assert_eq!(mismatches.len(), 1);
    assert!(mismatches[0].message.contains("return type"));
}

#[test]
fn test_validate_abi_compatibility_multiple_mismatches() {
    let expected = vec![FfiType::UInt32, FfiType::USize];
    let actual = vec![FfiType::UInt64, FfiType::Float];
    let mismatches =
        validate_abi_compatibility(&expected, FfiType::UInt8, &actual, FfiType::Object);
    // 2 param mismatches + 1 return mismatch
    assert_eq!(mismatches.len(), 3);
}

#[test]
fn test_validate_abi_compatibility_empty_params() {
    let mismatches = validate_abi_compatibility(&[], FfiType::Unit, &[], FfiType::Unit);
    assert!(mismatches.is_empty());
}

// ============================================================================
// FFI safety checking tests
// ============================================================================

#[test]
fn test_check_ffi_safety_all_scalar() {
    let params = vec![FfiType::UInt32, FfiType::UInt64, FfiType::Float];
    assert_eq!(
        check_ffi_safety(&params, FfiType::UInt8),
        FfiSafetyLevel::Safe
    );
}

#[test]
fn test_check_ffi_safety_object_param() {
    let params = vec![FfiType::Object];
    assert_eq!(
        check_ffi_safety(&params, FfiType::Unit),
        FfiSafetyLevel::RequiresRefcounting
    );
}

#[test]
fn test_check_ffi_safety_object_return() {
    assert_eq!(
        check_ffi_safety(&[], FfiType::Object),
        FfiSafetyLevel::RequiresRefcounting
    );
}

#[test]
fn test_check_ffi_safety_void_return() {
    assert_eq!(
        check_ffi_safety(&[FfiType::UInt32], FfiType::Unit),
        FfiSafetyLevel::Safe
    );
}

#[test]
fn test_check_ext_ffi_safety_pointer_type() {
    let params = vec![ExtFfiType::ByteArray];
    assert_eq!(
        check_ext_ffi_safety(&params, ExtFfiType::Base(FfiType::Unit)),
        FfiSafetyLevel::OwnershipTransfer
    );
}

#[test]
fn test_check_ext_ffi_safety_object_type() {
    let params = vec![ExtFfiType::Base(FfiType::Object)];
    assert_eq!(
        check_ext_ffi_safety(&params, ExtFfiType::Base(FfiType::Unit)),
        FfiSafetyLevel::RequiresRefcounting
    );
}

#[test]
fn test_check_ext_ffi_safety_all_scalars() {
    let params = vec![ExtFfiType::Int32, ExtFfiType::Base(FfiType::UInt64)];
    assert_eq!(
        check_ext_ffi_safety(&params, ExtFfiType::Base(FfiType::UInt8)),
        FfiSafetyLevel::Safe
    );
}

// ============================================================================
// Extern constant elaboration tests
// ============================================================================

#[test]
fn test_elaborate_extern_const_scalar() {
    let ty = Expr::const_str("UInt64");
    let ec =
        elaborate_extern_const(&name("pageSize"), "lean_page_size", &ty).expect("should succeed");
    assert_eq!(ec.lean_name, name("pageSize"));
    assert_eq!(ec.extern_name, "lean_page_size");
    assert_eq!(ec.ffi_type, FfiType::UInt64);
}

#[test]
fn test_elaborate_extern_const_object() {
    let ty = Expr::const_str("String");
    let ec = elaborate_extern_const(&name("version"), "lean_version_string", &ty)
        .expect("should succeed");
    assert_eq!(ec.ffi_type, FfiType::Object);
}

#[test]
fn test_elaborate_extern_const_function_type_fails() {
    let ty = Expr::arrow(Expr::const_str("UInt32"), Expr::const_str("UInt64"));
    let result = elaborate_extern_const(&name("bad"), "bad_func", &ty);
    assert!(result.is_err());
}

#[test]
fn test_elaborate_extern_const_empty_name_fails() {
    let ty = Expr::const_str("UInt32");
    let result = elaborate_extern_const(&name("x"), "", &ty);
    assert!(result.is_err());
}

// ============================================================================
// @[implementedBy] extended validation tests
// ============================================================================

#[test]
fn test_validate_implemented_by_ext_matching() {
    let ty = Expr::arrow(Expr::const_str("UInt32"), Expr::const_str("UInt64"));
    let mismatches =
        validate_implemented_by_ext(&name("foo"), "foo_impl", &ty, &ty).expect("should succeed");
    assert!(mismatches.is_empty());
}

#[test]
fn test_validate_implemented_by_ext_mismatch() {
    let decl_ty = Expr::arrow(Expr::const_str("UInt32"), Expr::const_str("UInt64"));
    let impl_ty = Expr::arrow(Expr::const_str("UInt32"), Expr::const_str("UInt32"));
    let mismatches = validate_implemented_by_ext(&name("foo"), "foo_impl", &decl_ty, &impl_ty)
        .expect("should succeed");
    assert_eq!(mismatches.len(), 1);
    assert!(mismatches[0].message.contains("return type"));
}

#[test]
fn test_validate_implemented_by_ext_empty_impl_fails() {
    let ty = Expr::const_str("Unit");
    let result = validate_implemented_by_ext(&name("foo"), "", &ty, &ty);
    assert!(result.is_err());
}

// ============================================================================
// FFI error reporting tests
// ============================================================================

#[test]
fn test_format_ffi_type_mismatch_message() {
    let msg = format_ffi_type_mismatch(&name("my_func"), 0, FfiType::UInt32, FfiType::UInt64);
    assert!(msg.contains("my_func"));
    assert!(msg.contains("parameter 0"));
    assert!(msg.contains("uint32_t"));
    assert!(msg.contains("uint64_t"));
}

#[test]
fn test_format_ffi_return_mismatch_message() {
    let msg = format_ffi_return_mismatch(&name("my_func"), FfiType::Unit, FfiType::Object);
    assert!(msg.contains("my_func"));
    assert!(msg.contains("return type"));
    assert!(msg.contains("void"));
    assert!(msg.contains("lean_object*"));
}

// ============================================================================
// Extended signature extraction tests
// ============================================================================

#[test]
fn test_extract_ext_ffi_signature_mixed() {
    // Int32 -> ByteArray -> UInt64
    let inner = Expr::arrow(Expr::const_str("ByteArray"), Expr::const_str("UInt64"));
    let ty = Expr::arrow(Expr::const_str("Int32"), inner);
    let (params, ret) = extract_ext_ffi_signature(&ty);
    assert_eq!(params, vec![ExtFfiType::Int32, ExtFfiType::ByteArray]);
    assert_eq!(ret, ExtFfiType::Base(FfiType::UInt64));
}

#[test]
fn test_extract_ext_ffi_signature_no_params() {
    let ty = Expr::const_str("FloatArray");
    let (params, ret) = extract_ext_ffi_signature(&ty);
    assert!(params.is_empty());
    assert_eq!(ret, ExtFfiType::FloatArray);
}
