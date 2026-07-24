// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for FFI extern declaration elaboration.

use clean_kernel::{Environment, Expr, Name};

use crate::ffi_extern::{
    classify_ffi_type, extract_ffi_signature, is_ffi_scalar, parse_extern_attr,
    process_extern_attr, requires_boxing, validate_extern_name, validate_extern_signature,
    validate_implemented_by, FfiType,
};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

// ============================================================================
// classify_ffi_type tests
// ============================================================================

#[test]
fn test_classify_ffi_type_uint8() {
    let ty = Expr::const_str("UInt8");
    assert_eq!(classify_ffi_type(&ty), FfiType::UInt8);
}

#[test]
fn test_classify_ffi_type_bool_maps_to_uint8() {
    let ty = Expr::const_str("Bool");
    assert_eq!(classify_ffi_type(&ty), FfiType::UInt8);
}

#[test]
fn test_classify_ffi_type_uint16() {
    let ty = Expr::const_str("UInt16");
    assert_eq!(classify_ffi_type(&ty), FfiType::UInt16);
}

#[test]
fn test_classify_ffi_type_uint32() {
    let ty = Expr::const_str("UInt32");
    assert_eq!(classify_ffi_type(&ty), FfiType::UInt32);
}

#[test]
fn test_classify_ffi_type_char_maps_to_uint32() {
    let ty = Expr::const_str("Char");
    assert_eq!(classify_ffi_type(&ty), FfiType::UInt32);
}

#[test]
fn test_classify_ffi_type_uint64() {
    let ty = Expr::const_str("UInt64");
    assert_eq!(classify_ffi_type(&ty), FfiType::UInt64);
}

#[test]
fn test_classify_ffi_type_usize() {
    let ty = Expr::const_str("USize");
    assert_eq!(classify_ffi_type(&ty), FfiType::USize);
}

#[test]
fn test_classify_ffi_type_float() {
    let ty = Expr::const_str("Float");
    assert_eq!(classify_ffi_type(&ty), FfiType::Float);
}

#[test]
fn test_classify_ffi_type_float32() {
    let ty = Expr::const_str("Float32");
    assert_eq!(classify_ffi_type(&ty), FfiType::Float32);
}

#[test]
fn test_classify_ffi_type_unit() {
    let ty = Expr::const_str("Unit");
    assert_eq!(classify_ffi_type(&ty), FfiType::Unit);
}

#[test]
fn test_classify_ffi_type_punit() {
    let ty = Expr::const_str("PUnit");
    assert_eq!(classify_ffi_type(&ty), FfiType::Unit);
}

#[test]
fn test_classify_ffi_type_nat_is_object() {
    let ty = Expr::const_str("Nat");
    assert_eq!(classify_ffi_type(&ty), FfiType::Object);
}

#[test]
fn test_classify_ffi_type_string_is_object() {
    let ty = Expr::const_str("String");
    assert_eq!(classify_ffi_type(&ty), FfiType::Object);
}

#[test]
fn test_classify_ffi_type_bvar_is_object() {
    let ty = Expr::bvar(0);
    assert_eq!(classify_ffi_type(&ty), FfiType::Object);
}

// ============================================================================
// extract_ffi_signature tests
// ============================================================================

#[test]
fn test_extract_ffi_signature_no_params() {
    // Unit (no-arg function returning Unit)
    let ty = Expr::const_str("Unit");
    let (params, ret) = extract_ffi_signature(&ty);
    assert!(params.is_empty());
    assert_eq!(ret, FfiType::Unit);
}

#[test]
fn test_extract_ffi_signature_single_param() {
    // UInt32 -> UInt64
    let ty = Expr::arrow(Expr::const_str("UInt32"), Expr::const_str("UInt64"));
    let (params, ret) = extract_ffi_signature(&ty);
    assert_eq!(params, vec![FfiType::UInt32]);
    assert_eq!(ret, FfiType::UInt64);
}

#[test]
fn test_extract_ffi_signature_multiple_params() {
    // UInt32 -> UInt64 -> Bool
    let inner = Expr::arrow(Expr::const_str("UInt64"), Expr::const_str("Bool"));
    let ty = Expr::arrow(Expr::const_str("UInt32"), inner);
    let (params, ret) = extract_ffi_signature(&ty);
    assert_eq!(params, vec![FfiType::UInt32, FfiType::UInt64]);
    assert_eq!(ret, FfiType::UInt8); // Bool -> UInt8
}

#[test]
fn test_extract_ffi_signature_object_params() {
    // Nat -> String -> Unit
    let inner = Expr::arrow(Expr::const_str("String"), Expr::const_str("Unit"));
    let ty = Expr::arrow(Expr::const_str("Nat"), inner);
    let (params, ret) = extract_ffi_signature(&ty);
    assert_eq!(params, vec![FfiType::Object, FfiType::Object]);
    assert_eq!(ret, FfiType::Unit);
}

// ============================================================================
// parse_extern_attr tests
// ============================================================================

#[test]
fn test_parse_extern_attr_simple_name() {
    let entries = parse_extern_attr("lean_io_handle_mk").expect("should parse");
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].backend, "all");
    assert_eq!(entries[0].name, "lean_io_handle_mk");
}

#[test]
fn test_parse_extern_attr_multi_backend() {
    let entries = parse_extern_attr("c lean_box llvm lean_box_llvm").expect("should parse");
    assert_eq!(entries.len(), 2);
    assert_eq!(entries[0].backend, "c");
    assert_eq!(entries[0].name, "lean_box");
    assert_eq!(entries[1].backend, "llvm");
    assert_eq!(entries[1].name, "lean_box_llvm");
}

#[test]
fn test_parse_extern_attr_empty_fails() {
    let result = parse_extern_attr("");
    assert!(result.is_err());
}

#[test]
fn test_parse_extern_attr_whitespace_only_fails() {
    let result = parse_extern_attr("   ");
    assert!(result.is_err());
}

#[test]
fn test_parse_extern_attr_odd_tokens_fails() {
    let result = parse_extern_attr("c lean_box llvm");
    assert!(result.is_err());
}

// ============================================================================
// validate_extern_signature tests
// ============================================================================

#[test]
fn test_validate_extern_signature_valid() {
    let ty = Expr::arrow(Expr::const_str("UInt32"), Expr::const_str("UInt64"));
    let decl =
        validate_extern_signature(&name("my_func"), "my_c_func", &ty).expect("should validate");
    assert_eq!(decl.lean_name, name("my_func"));
    assert_eq!(decl.extern_name, "my_c_func");
    assert_eq!(decl.param_types, vec![FfiType::UInt32]);
    assert_eq!(decl.return_type, FfiType::UInt64);
}

#[test]
fn test_validate_extern_signature_empty_name_fails() {
    let ty = Expr::const_str("Unit");
    let result = validate_extern_signature(&name("my_func"), "", &ty);
    assert!(result.is_err());
}

// ============================================================================
// validate_implemented_by tests
// ============================================================================

#[test]
fn test_validate_implemented_by_empty_impl_fails() {
    let env = Environment::new();
    let result = validate_implemented_by(&name("Foo.bar"), "", &env);
    assert!(result.is_err());
}

#[test]
fn test_validate_implemented_by_missing_decl_fails() {
    let env = Environment::new();
    let result = validate_implemented_by(&name("NonExistent"), "some_impl", &env);
    assert!(result.is_err());
}

// ============================================================================
// process_extern_attr tests
// ============================================================================

#[test]
fn test_process_extern_attr_single_backend() {
    let ty = Expr::arrow(Expr::const_str("USize"), Expr::const_str("Bool"));
    let decls = process_extern_attr(&name("is_valid"), "my_is_valid", &ty).expect("should process");
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].extern_name, "my_is_valid");
    assert_eq!(decls[0].backend, "all");
    assert_eq!(decls[0].param_types, vec![FfiType::USize]);
    assert_eq!(decls[0].return_type, FfiType::UInt8);
}

#[test]
fn test_process_extern_attr_multi_backend() {
    let ty = Expr::const_str("Nat");
    let decls = process_extern_attr(&name("alloc"), "c lean_alloc llvm lean_alloc_ll", &ty)
        .expect("should process");
    assert_eq!(decls.len(), 2);
    assert_eq!(decls[0].backend, "c");
    assert_eq!(decls[0].extern_name, "lean_alloc");
    assert_eq!(decls[1].backend, "llvm");
    assert_eq!(decls[1].extern_name, "lean_alloc_ll");
}

// ============================================================================
// is_ffi_scalar / requires_boxing tests
// ============================================================================

#[test]
fn test_is_ffi_scalar_uint32() {
    assert!(is_ffi_scalar(&Expr::const_str("UInt32")));
}

#[test]
fn test_is_ffi_scalar_nat_false() {
    assert!(!is_ffi_scalar(&Expr::const_str("Nat")));
}

#[test]
fn test_requires_boxing_string() {
    assert!(requires_boxing(&Expr::const_str("String")));
}

#[test]
fn test_requires_boxing_uint64_false() {
    assert!(!requires_boxing(&Expr::const_str("UInt64")));
}

// ============================================================================
// validate_extern_name tests
// ============================================================================

#[test]
fn test_validate_extern_name_valid_c_ident() {
    validate_extern_name("clean_io_handle_mk").expect("should be valid");
}

#[test]
fn test_validate_extern_name_underscore_prefix() {
    validate_extern_name("_init").expect("should be valid");
}

#[test]
fn test_validate_extern_name_empty_fails() {
    assert!(validate_extern_name("").is_err());
}

#[test]
fn test_validate_extern_name_starts_with_digit_fails() {
    assert!(validate_extern_name("3func").is_err());
}

#[test]
fn test_validate_extern_name_contains_space_fails() {
    assert!(validate_extern_name("my func").is_err());
}

#[test]
fn test_validate_extern_name_contains_dash_fails() {
    assert!(validate_extern_name("my-func").is_err());
}

// ============================================================================
// FfiType::c_type_name tests
// ============================================================================

#[test]
fn test_ffi_type_c_type_names() {
    assert_eq!(FfiType::UInt8.c_type_name(), "uint8_t");
    assert_eq!(FfiType::UInt16.c_type_name(), "uint16_t");
    assert_eq!(FfiType::UInt32.c_type_name(), "uint32_t");
    assert_eq!(FfiType::UInt64.c_type_name(), "uint64_t");
    assert_eq!(FfiType::USize.c_type_name(), "size_t");
    assert_eq!(FfiType::Float.c_type_name(), "double");
    assert_eq!(FfiType::Float32.c_type_name(), "float");
    assert_eq!(FfiType::Unit.c_type_name(), "void");
    assert_eq!(FfiType::Object.c_type_name(), "lean_object*");
}
