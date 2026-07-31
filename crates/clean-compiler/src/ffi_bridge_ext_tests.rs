// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended FFI bridge module.

use super::ffi_bridge_ext::*;
use crate::ir::{IRBody, IRDecl, IRType, VarId};
use clean_kernel::Name;

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn make_ffi_func(lean: &str, ext: &str, params: Vec<FfiParam>, ret: FfiType) -> FfiFunction {
    FfiFunction {
        lean_name: name(lean),
        extern_name: ext.to_owned(),
        params,
        return_type: ret,
        abi: AbiKind::C,
        is_unsafe: false,
    }
}

fn make_param(n: &str, ty: FfiType) -> FfiParam {
    FfiParam {
        name: n.to_owned(),
        ffi_type: ty,
        is_borrowed: false,
    }
}

fn make_ir_decl(n: &str, params: Vec<(VarId, IRType)>, ret: IRType) -> IRDecl {
    IRDecl {
        name: name(n),
        params,
        return_type: ret,
        body: IRBody::Ret(crate::ir::IRArg::Erased),
    }
}

// ════════════════════════════════════════════════════════════════════
// ir_type_to_ffi
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_ir_type_to_ffi_bool() {
    assert_eq!(ir_type_to_ffi(&IRType::Bool), FfiType::Bool);
}

#[test]
fn test_ir_type_to_ffi_uint8() {
    assert_eq!(ir_type_to_ffi(&IRType::UInt8), FfiType::UInt8);
}

#[test]
fn test_ir_type_to_ffi_uint16() {
    assert_eq!(ir_type_to_ffi(&IRType::UInt16), FfiType::UInt16);
}

#[test]
fn test_ir_type_to_ffi_uint32() {
    assert_eq!(ir_type_to_ffi(&IRType::UInt32), FfiType::UInt32);
}

#[test]
fn test_ir_type_to_ffi_uint64() {
    assert_eq!(ir_type_to_ffi(&IRType::UInt64), FfiType::UInt64);
}

#[test]
fn test_ir_type_to_ffi_usize_maps_to_uint64() {
    assert_eq!(ir_type_to_ffi(&IRType::USize), FfiType::UInt64);
}

#[test]
fn test_ir_type_to_ffi_float32() {
    assert_eq!(ir_type_to_ffi(&IRType::Float32), FfiType::Float);
}

#[test]
fn test_ir_type_to_ffi_float64() {
    assert_eq!(ir_type_to_ffi(&IRType::Float64), FfiType::Double);
}

#[test]
fn test_ir_type_to_ffi_object() {
    assert_eq!(ir_type_to_ffi(&IRType::Object), FfiType::LeanObj);
}

#[test]
fn test_ir_type_to_ffi_tobject() {
    assert_eq!(ir_type_to_ffi(&IRType::TObject), FfiType::LeanObj);
}

#[test]
fn test_ir_type_to_ffi_struct_is_lean_obj() {
    let s = IRType::Struct(vec![IRType::UInt32]);
    assert_eq!(ir_type_to_ffi(&s), FfiType::LeanObj);
}

#[test]
fn test_ir_type_to_ffi_erased_is_unit() {
    assert_eq!(ir_type_to_ffi(&IRType::Erased), FfiType::Unit);
}

#[test]
fn test_ir_type_to_ffi_void_is_unit() {
    assert_eq!(ir_type_to_ffi(&IRType::Void), FfiType::Unit);
}

// ════════════════════════════════════════════════════════════════════
// ffi_type_to_c
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_ffi_type_to_c_lean_obj() {
    assert_eq!(ffi_type_to_c(&FfiType::LeanObj), "clean_obj*");
}

#[test]
fn test_ffi_type_to_c_nat() {
    assert_eq!(ffi_type_to_c(&FfiType::Nat), "clean_obj*");
}

#[test]
fn test_ffi_type_to_c_uint32() {
    assert_eq!(ffi_type_to_c(&FfiType::UInt32), "uint32_t");
}

#[test]
fn test_ffi_type_to_c_double() {
    assert_eq!(ffi_type_to_c(&FfiType::Double), "double");
}

#[test]
fn test_ffi_type_to_c_string() {
    assert_eq!(ffi_type_to_c(&FfiType::String), "clean_obj*");
}

#[test]
fn test_ffi_type_to_c_bool() {
    assert_eq!(ffi_type_to_c(&FfiType::Bool), "uint8_t");
}

#[test]
fn test_ffi_type_to_c_unit() {
    assert_eq!(ffi_type_to_c(&FfiType::Unit), "void");
}

#[test]
fn test_ffi_type_to_c_ptr() {
    let t = FfiType::Ptr(Box::new(FfiType::UInt8));
    assert_eq!(ffi_type_to_c(&t), "uint8_t*");
}

#[test]
fn test_ffi_type_to_c_array() {
    let t = FfiType::Array(Box::new(FfiType::Double));
    assert_eq!(ffi_type_to_c(&t), "double*");
}

#[test]
fn test_ffi_type_to_c_opaque() {
    let t = FfiType::Opaque("my_struct_t".into());
    assert_eq!(ffi_type_to_c(&t), "my_struct_t");
}

// ════════════════════════════════════════════════════════════════════
// ffi_type_to_rust
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_ffi_type_to_rust_lean_obj() {
    assert_eq!(ffi_type_to_rust(&FfiType::LeanObj), "*mut clean_obj");
}

#[test]
fn test_ffi_type_to_rust_uint64() {
    assert_eq!(ffi_type_to_rust(&FfiType::UInt64), "u64");
}

#[test]
fn test_ffi_type_to_rust_float() {
    assert_eq!(ffi_type_to_rust(&FfiType::Float), "f32");
}

#[test]
fn test_ffi_type_to_rust_unit() {
    assert_eq!(ffi_type_to_rust(&FfiType::Unit), "()");
}

#[test]
fn test_ffi_type_to_rust_ptr() {
    let t = FfiType::Ptr(Box::new(FfiType::UInt32));
    assert_eq!(ffi_type_to_rust(&t), "*mut u32");
}

// ════════════════════════════════════════════════════════════════════
// generate_marshaling_code
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_marshaling_empty_params() {
    let func = make_ffi_func("f", "ext_f", vec![], FfiType::Unit);
    let steps = generate_marshaling_code(&func);
    assert!(steps.is_empty());
}

#[test]
fn test_marshaling_scalar_identity() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("x", FfiType::UInt32)],
        FfiType::UInt32,
    );
    let steps = generate_marshaling_code(&func);
    assert_eq!(steps, vec![MarshalingStep::Identity]);
}

#[test]
fn test_marshaling_lean_obj_box() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("x", FfiType::LeanObj)],
        FfiType::LeanObj,
    );
    let steps = generate_marshaling_code(&func);
    assert_eq!(steps, vec![MarshalingStep::BoxToPtr]);
}

#[test]
fn test_marshaling_nat_to_uint() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("n", FfiType::Nat)],
        FfiType::UInt64,
    );
    let steps = generate_marshaling_code(&func);
    assert_eq!(steps, vec![MarshalingStep::NatToUint]);
}

#[test]
fn test_marshaling_string_to_ptr() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("s", FfiType::String)],
        FfiType::Unit,
    );
    let steps = generate_marshaling_code(&func);
    assert_eq!(steps, vec![MarshalingStep::StringToPtr]);
}

#[test]
fn test_marshaling_mixed_params() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![
            make_param("a", FfiType::UInt64),
            make_param("b", FfiType::LeanObj),
            make_param("c", FfiType::String),
            make_param("d", FfiType::Bool),
        ],
        FfiType::Unit,
    );
    let steps = generate_marshaling_code(&func);
    assert_eq!(
        steps,
        vec![
            MarshalingStep::Identity,
            MarshalingStep::BoxToPtr,
            MarshalingStep::StringToPtr,
            MarshalingStep::Identity,
        ]
    );
}

#[test]
fn test_marshaling_ptr_param() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("p", FfiType::Ptr(Box::new(FfiType::UInt8)))],
        FfiType::Unit,
    );
    let steps = generate_marshaling_code(&func);
    assert_eq!(steps, vec![MarshalingStep::BoxToPtr]);
}

#[test]
fn test_reverse_marshaling_steps_are_distinct() {
    assert_ne!(MarshalingStep::PtrToBox, MarshalingStep::UintToNat);
    assert_ne!(MarshalingStep::UintToNat, MarshalingStep::PtrToString);
}

// ════════════════════════════════════════════════════════════════════
// check_abi_compatibility
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_abi_compat_matching_scalars() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("x", FfiType::UInt32)],
        FfiType::Bool,
    );
    let decl = make_ir_decl("f", vec![(VarId(0), IRType::UInt32)], IRType::Bool);
    assert!(check_abi_compatibility(&func, &decl).is_ok());
}

#[test]
fn test_abi_compat_object_variants_compatible() {
    // LeanObj, Nat, Int, String are all clean_obj* — they should be compatible.
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("x", FfiType::Nat)],
        FfiType::String,
    );
    let decl = make_ir_decl("f", vec![(VarId(0), IRType::Object)], IRType::Object);
    assert!(check_abi_compatibility(&func, &decl).is_ok());
}

#[test]
fn test_abi_compat_param_count_mismatch() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![
            make_param("x", FfiType::UInt32),
            make_param("y", FfiType::UInt32),
        ],
        FfiType::Unit,
    );
    let decl = make_ir_decl("f", vec![(VarId(0), IRType::UInt32)], IRType::Erased);
    let err = check_abi_compatibility(&func, &decl).unwrap_err();
    assert_eq!(err.len(), 1);
    assert_eq!(err[0].severity, MismatchSeverity::Error);
    assert!(err[0].expected.contains("2 params"));
}

#[test]
fn test_abi_compat_param_type_mismatch() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("x", FfiType::Double)],
        FfiType::Unit,
    );
    let decl = make_ir_decl("f", vec![(VarId(0), IRType::UInt32)], IRType::Erased);
    let err = check_abi_compatibility(&func, &decl).unwrap_err();
    assert_eq!(err.len(), 1);
    assert!(err[0].param_index.is_some());
    assert_eq!(err[0].param_index.unwrap(), 0);
}

#[test]
fn test_abi_compat_return_type_mismatch() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("x", FfiType::UInt32)],
        FfiType::Double,
    );
    let decl = make_ir_decl("f", vec![(VarId(0), IRType::UInt32)], IRType::Bool);
    let err = check_abi_compatibility(&func, &decl).unwrap_err();
    // Return type mismatch should have param_index = None
    assert!(err.iter().any(|m| m.param_index.is_none()));
}

#[test]
fn test_abi_compat_empty_params() {
    let func = make_ffi_func("f", "ext_f", vec![], FfiType::Unit);
    let decl = make_ir_decl("f", vec![], IRType::Erased);
    assert!(check_abi_compatibility(&func, &decl).is_ok());
}

// ════════════════════════════════════════════════════════════════════
// generate_ffi_wrappers
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_wrappers_disabled_returns_empty() {
    let config = FfiBridgeExtConfig {
        generate_wrappers: false,
        ..FfiBridgeExtConfig::default()
    };
    let func = make_ffi_func("f", "ext_f", vec![], FfiType::Unit);
    let wrappers = generate_ffi_wrappers(&[func], &config);
    assert!(wrappers.is_empty());
}

#[test]
fn test_wrappers_empty_input() {
    let config = FfiBridgeExtConfig::default();
    let wrappers = generate_ffi_wrappers(&[], &config);
    assert!(wrappers.is_empty());
}

#[test]
fn test_wrappers_single_void_function() {
    let config = FfiBridgeExtConfig::default();
    let func = make_ffi_func("init", "clean_init", vec![], FfiType::Unit);
    let wrappers = generate_ffi_wrappers(&[func], &config);
    assert_eq!(wrappers.len(), 1);
    assert_eq!(wrappers[0].name, name("init"));
    assert!(wrappers[0].params.is_empty());
}

#[test]
fn test_wrappers_preserves_param_count() {
    let config = FfiBridgeExtConfig::default();
    let func = make_ffi_func(
        "add",
        "clean_add",
        vec![
            make_param("a", FfiType::UInt64),
            make_param("b", FfiType::UInt64),
        ],
        FfiType::UInt64,
    );
    let wrappers = generate_ffi_wrappers(&[func], &config);
    assert_eq!(wrappers.len(), 1);
    assert_eq!(wrappers[0].params.len(), 2);
    assert_eq!(wrappers[0].return_type, IRType::UInt64);
}

#[test]
fn test_wrappers_multiple_functions() {
    let config = FfiBridgeExtConfig::default();
    let funcs = vec![
        make_ffi_func("f1", "ext_f1", vec![], FfiType::Unit),
        make_ffi_func("f2", "ext_f2", vec![], FfiType::Bool),
        make_ffi_func("f3", "ext_f3", vec![], FfiType::UInt32),
    ];
    let wrappers = generate_ffi_wrappers(&funcs, &config);
    assert_eq!(wrappers.len(), 3);
}

#[test]
fn test_wrappers_object_return_with_safety_checks() {
    let config = FfiBridgeExtConfig {
        emit_safety_checks: true,
        ..FfiBridgeExtConfig::default()
    };
    let func = make_ffi_func(
        "alloc",
        "clean_alloc",
        vec![make_param("n", FfiType::UInt64)],
        FfiType::LeanObj,
    );
    let wrappers = generate_ffi_wrappers(&[func], &config);
    assert_eq!(wrappers.len(), 1);
    assert_eq!(wrappers[0].return_type, IRType::Object);
}

#[test]
fn test_wrappers_void_return_uses_erased() {
    let config = FfiBridgeExtConfig {
        emit_safety_checks: false,
        ..FfiBridgeExtConfig::default()
    };
    let func = make_ffi_func("deinit", "clean_deinit", vec![], FfiType::Unit);
    let wrappers = generate_ffi_wrappers(&[func], &config);
    assert_eq!(wrappers[0].return_type, IRType::Erased);
}

// ════════════════════════════════════════════════════════════════════
// Config and enum coverage
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_default_config() {
    let config = FfiBridgeExtConfig::default();
    assert!(config.generate_wrappers);
    assert!(config.check_abi_compat);
    assert!(config.emit_safety_checks);
    assert_eq!(config.target_abi, AbiKind::C);
}

#[test]
fn test_abi_kind_eq() {
    assert_eq!(AbiKind::C, AbiKind::C);
    assert_ne!(AbiKind::C, AbiKind::Stdcall);
    assert_ne!(AbiKind::Fastcall, AbiKind::System);
    assert_eq!(AbiKind::Cdecl, AbiKind::Cdecl);
}

#[test]
fn test_mismatch_severity_eq() {
    assert_eq!(MismatchSeverity::Error, MismatchSeverity::Error);
    assert_ne!(MismatchSeverity::Error, MismatchSeverity::Warning);
    assert_ne!(MismatchSeverity::Warning, MismatchSeverity::Info);
}

#[test]
fn test_ffi_param_borrowed_flag() {
    let p = FfiParam {
        name: "x".to_owned(),
        ffi_type: FfiType::LeanObj,
        is_borrowed: true,
    };
    assert!(p.is_borrowed);
}

#[test]
fn test_ffi_function_unsafe_flag() {
    let f = FfiFunction {
        lean_name: name("dangerous"),
        extern_name: "c_dangerous".to_owned(),
        params: vec![],
        return_type: FfiType::Ptr(Box::new(FfiType::UInt8)),
        abi: AbiKind::C,
        is_unsafe: true,
    };
    assert!(f.is_unsafe);
}

// ════════════════════════════════════════════════════════════════════
// Edge cases
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_ffi_type_to_c_nested_ptr() {
    let t = FfiType::Ptr(Box::new(FfiType::Ptr(Box::new(FfiType::UInt8))));
    assert_eq!(ffi_type_to_c(&t), "uint8_t**");
}

#[test]
fn test_ffi_type_to_rust_nested_ptr() {
    let t = FfiType::Ptr(Box::new(FfiType::Ptr(Box::new(FfiType::Double))));
    assert_eq!(ffi_type_to_rust(&t), "*mut *mut f64");
}

#[test]
fn test_marshaling_int_uses_nat_to_uint() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("i", FfiType::Int)],
        FfiType::Unit,
    );
    let steps = generate_marshaling_code(&func);
    assert_eq!(steps, vec![MarshalingStep::NatToUint]);
}

#[test]
fn test_marshaling_opaque_is_identity() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("h", FfiType::Opaque("handle_t".into()))],
        FfiType::Unit,
    );
    let steps = generate_marshaling_code(&func);
    assert_eq!(steps, vec![MarshalingStep::Identity]);
}

#[test]
fn test_ir_type_to_ffi_union_is_lean_obj() {
    let u = IRType::Union(vec![IRType::UInt32, IRType::UInt64]);
    assert_eq!(ir_type_to_ffi(&u), FfiType::LeanObj);
}

#[test]
fn test_abi_compat_multiple_mismatches() {
    // Both param type and return type are wrong.
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("x", FfiType::Double)],
        FfiType::Float,
    );
    let decl = make_ir_decl("f", vec![(VarId(0), IRType::Bool)], IRType::UInt64);
    let err = check_abi_compatibility(&func, &decl).unwrap_err();
    assert!(
        err.len() >= 2,
        "expected at least 2 mismatches, got {}",
        err.len()
    );
}

#[test]
fn test_ffi_type_to_c_int_is_obj() {
    assert_eq!(ffi_type_to_c(&FfiType::Int), "clean_obj*");
}

#[test]
fn test_ffi_type_to_c_uint8() {
    assert_eq!(ffi_type_to_c(&FfiType::UInt8), "uint8_t");
}

#[test]
fn test_ffi_type_to_c_uint16() {
    assert_eq!(ffi_type_to_c(&FfiType::UInt16), "uint16_t");
}

#[test]
fn test_ffi_type_to_c_uint64() {
    assert_eq!(ffi_type_to_c(&FfiType::UInt64), "uint64_t");
}

#[test]
fn test_ffi_type_to_c_float() {
    assert_eq!(ffi_type_to_c(&FfiType::Float), "float");
}

#[test]
fn test_ffi_type_to_rust_bool() {
    assert_eq!(ffi_type_to_rust(&FfiType::Bool), "u8");
}

#[test]
fn test_ffi_type_to_rust_string() {
    assert_eq!(ffi_type_to_rust(&FfiType::String), "*mut clean_obj");
}

#[test]
fn test_ffi_type_to_rust_double() {
    assert_eq!(ffi_type_to_rust(&FfiType::Double), "f64");
}

#[test]
fn test_ffi_type_to_rust_opaque() {
    let t = FfiType::Opaque("CustomType".into());
    assert_eq!(ffi_type_to_rust(&t), "CustomType");
}

#[test]
fn test_marshaling_array_param() {
    let func = make_ffi_func(
        "f",
        "ext_f",
        vec![make_param("arr", FfiType::Array(Box::new(FfiType::UInt32)))],
        FfiType::Unit,
    );
    let steps = generate_marshaling_code(&func);
    assert_eq!(steps, vec![MarshalingStep::BoxToPtr]);
}

#[test]
fn test_wrappers_param_var_ids_sequential() {
    let config = FfiBridgeExtConfig::default();
    let func = make_ffi_func(
        "triple",
        "ext_triple",
        vec![
            make_param("a", FfiType::UInt32),
            make_param("b", FfiType::UInt64),
            make_param("c", FfiType::Bool),
        ],
        FfiType::UInt32,
    );
    let wrappers = generate_ffi_wrappers(&[func], &config);
    let decl = &wrappers[0];
    assert_eq!(decl.params[0].0, VarId(0));
    assert_eq!(decl.params[1].0, VarId(1));
    assert_eq!(decl.params[2].0, VarId(2));
}
