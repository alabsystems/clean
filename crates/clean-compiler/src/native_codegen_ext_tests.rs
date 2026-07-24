// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended native code generation infrastructure.
//!
//! Part of #3084 - IO/FFI/Native code generation infrastructure.

use crate::ir::{IRBody, IRDecl, IRType, VarId};
use crate::native_codegen_ext::*;
use clean_kernel::Name;

// ---------------------------------------------------------------------------
// Helper constructors
// ---------------------------------------------------------------------------

fn default_config() -> NativeCodegenConfig {
    NativeCodegenConfig::default()
}

fn config_for(target: NativeTarget, platform: Platform) -> NativeCodegenConfig {
    NativeCodegenConfig {
        target,
        platform,
        ..default_config()
    }
}

fn make_decl(name: &str, params: Vec<IRType>, ret: IRType) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params: params
            .into_iter()
            .enumerate()
            .map(|(i, ty)| (VarId(i as u32), ty))
            .collect(),
        return_type: ret,
        body: IRBody::Unreachable,
    }
}

// ===========================================================================
// ir_type_to_native
// ===========================================================================

#[test]
fn test_ir_type_to_native_bool() {
    let cfg = default_config();
    assert_eq!(ir_type_to_native(&IRType::Bool, &cfg), ExtNativeType::Bool);
}

#[test]
fn test_ir_type_to_native_uint8() {
    let cfg = default_config();
    assert_eq!(
        ir_type_to_native(&IRType::UInt8, &cfg),
        ExtNativeType::UInt8
    );
}

#[test]
fn test_ir_type_to_native_uint16() {
    let cfg = default_config();
    assert_eq!(
        ir_type_to_native(&IRType::UInt16, &cfg),
        ExtNativeType::UInt16
    );
}

#[test]
fn test_ir_type_to_native_uint32() {
    let cfg = default_config();
    assert_eq!(
        ir_type_to_native(&IRType::UInt32, &cfg),
        ExtNativeType::UInt32
    );
}

#[test]
fn test_ir_type_to_native_uint64() {
    let cfg = default_config();
    assert_eq!(
        ir_type_to_native(&IRType::UInt64, &cfg),
        ExtNativeType::UInt64
    );
}

#[test]
fn test_ir_type_to_native_usize_linux() {
    let cfg = config_for(NativeTarget::C, Platform::Linux);
    assert_eq!(
        ir_type_to_native(&IRType::USize, &cfg),
        ExtNativeType::UInt64
    );
}

#[test]
fn test_ir_type_to_native_usize_wasm() {
    let cfg = config_for(NativeTarget::C, Platform::Wasm);
    assert_eq!(
        ir_type_to_native(&IRType::USize, &cfg),
        ExtNativeType::UInt32
    );
}

#[test]
fn test_ir_type_to_native_float32() {
    let cfg = default_config();
    assert_eq!(
        ir_type_to_native(&IRType::Float32, &cfg),
        ExtNativeType::Float
    );
}

#[test]
fn test_ir_type_to_native_float64() {
    let cfg = default_config();
    assert_eq!(
        ir_type_to_native(&IRType::Float64, &cfg),
        ExtNativeType::Double
    );
}

#[test]
fn test_ir_type_to_native_object() {
    let cfg = default_config();
    assert_eq!(
        ir_type_to_native(&IRType::Object, &cfg),
        ExtNativeType::LeanObj
    );
}

#[test]
fn test_ir_type_to_native_tobject() {
    let cfg = default_config();
    assert_eq!(
        ir_type_to_native(&IRType::TObject, &cfg),
        ExtNativeType::LeanObj
    );
}

#[test]
fn test_ir_type_to_native_void() {
    let cfg = default_config();
    assert_eq!(ir_type_to_native(&IRType::Void, &cfg), ExtNativeType::Void);
}

#[test]
fn test_ir_type_to_native_erased() {
    let cfg = default_config();
    assert_eq!(
        ir_type_to_native(&IRType::Erased, &cfg),
        ExtNativeType::LeanObj
    );
}

#[test]
fn test_ir_type_to_native_struct() {
    let cfg = default_config();
    let st = IRType::Struct(vec![IRType::Object, IRType::UInt32]);
    assert_eq!(ir_type_to_native(&st, &cfg), ExtNativeType::LeanObj);
}

#[test]
fn test_ir_type_to_native_union() {
    let cfg = default_config();
    let u = IRType::Union(vec![IRType::UInt8]);
    assert_eq!(ir_type_to_native(&u, &cfg), ExtNativeType::LeanObj);
}

// ===========================================================================
// generate_runtime_decls
// ===========================================================================

#[test]
fn test_runtime_decls_count_with_checks() {
    let cfg = NativeCodegenConfig {
        runtime_checks: true,
        ..default_config()
    };
    let decls = generate_runtime_decls(&cfg);
    // 9 base + 1 assert_rc
    assert_eq!(decls.len(), 10);
}

#[test]
fn test_runtime_decls_count_without_checks() {
    let cfg = NativeCodegenConfig {
        runtime_checks: false,
        ..default_config()
    };
    let decls = generate_runtime_decls(&cfg);
    assert_eq!(decls.len(), 9);
}

#[test]
fn test_runtime_decls_all_extern() {
    let cfg = default_config();
    let decls = generate_runtime_decls(&cfg);
    assert!(decls.iter().all(|d| d.is_extern));
}

#[test]
fn test_runtime_decls_contain_inc_dec() {
    let cfg = default_config();
    let decls = generate_runtime_decls(&cfg);
    let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
    assert!(names.contains(&"clean_inc"));
    assert!(names.contains(&"clean_dec"));
}

#[test]
fn test_runtime_decls_contain_alloc_ctor() {
    let cfg = default_config();
    let decls = generate_runtime_decls(&cfg);
    let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
    assert!(names.contains(&"clean_alloc_ctor"));
}

#[test]
fn test_runtime_decls_contain_box_unbox() {
    let cfg = default_config();
    let decls = generate_runtime_decls(&cfg);
    let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
    assert!(names.contains(&"clean_box"));
    assert!(names.contains(&"clean_unbox"));
}

// ===========================================================================
// generate_header (C)
// ===========================================================================

#[test]
fn test_header_c_includes_pragma() {
    let cfg = config_for(NativeTarget::C, Platform::Linux);
    let decls = vec![make_decl("foo", vec![IRType::UInt32], IRType::Bool)];
    let header = generate_header(&decls, &cfg);
    assert!(header.contains("#pragma once"));
    assert!(header.contains("#include <stdint.h>"));
}

#[test]
fn test_header_c_function_declaration() {
    let cfg = config_for(NativeTarget::C, Platform::Linux);
    let decls = vec![make_decl(
        "Nat.add",
        vec![IRType::UInt64, IRType::UInt64],
        IRType::UInt64,
    )];
    let header = generate_header(&decls, &cfg);
    assert!(header.contains("uint64_t l5_Nat__add(uint64_t, uint64_t);"));
}

#[test]
fn test_header_c_void_params() {
    let cfg = config_for(NativeTarget::C, Platform::Linux);
    let decls = vec![make_decl("get_unit", vec![], IRType::Object)];
    let header = generate_header(&decls, &cfg);
    assert!(header.contains("clean_obj* l5_get_unit(void);"));
}

// ===========================================================================
// generate_header (Rust)
// ===========================================================================

#[test]
fn test_header_rust_extern_block() {
    let cfg = config_for(NativeTarget::Rust, Platform::Linux);
    let decls = vec![make_decl("foo", vec![IRType::Bool], IRType::Void)];
    let header = generate_header(&decls, &cfg);
    assert!(header.starts_with("extern \"C\" {"));
    assert!(header.contains("fn l5_foo(arg0: u8);\n"));
    assert!(header.ends_with("}\n"));
}

#[test]
fn test_header_rust_return_type() {
    let cfg = config_for(NativeTarget::Rust, Platform::Linux);
    let decls = vec![make_decl("bar", vec![IRType::Object], IRType::UInt64)];
    let header = generate_header(&decls, &cfg);
    assert!(header.contains("-> u64"));
}

// ===========================================================================
// generate_header (LLVM)
// ===========================================================================

#[test]
fn test_header_llvm_declares() {
    let cfg = config_for(NativeTarget::Llvm, Platform::Linux);
    let decls = vec![make_decl("baz", vec![], IRType::Void)];
    let header = generate_header(&decls, &cfg);
    assert!(header.contains("declare void @l5_baz()"));
}

// ===========================================================================
// generate_type_decl
// ===========================================================================

#[test]
fn test_type_decl_c_struct() {
    let cfg = config_for(NativeTarget::C, Platform::Linux);
    let fields = vec![
        ("x".to_owned(), ExtNativeType::UInt32),
        ("y".to_owned(), ExtNativeType::Double),
    ];
    let decl = generate_type_decl("Point", &fields, &cfg);
    assert!(decl.contains("typedef struct Point {"));
    assert!(decl.contains("uint32_t x;"));
    assert!(decl.contains("double y;"));
    assert!(decl.contains("} Point;"));
}

#[test]
fn test_type_decl_rust_struct() {
    let cfg = config_for(NativeTarget::Rust, Platform::Linux);
    let fields = vec![
        ("tag".to_owned(), ExtNativeType::UInt8),
        ("data".to_owned(), ExtNativeType::LeanObj),
    ];
    let decl = generate_type_decl("Node", &fields, &cfg);
    assert!(decl.contains("#[repr(C)]"));
    assert!(decl.contains("pub struct Node {"));
    assert!(decl.contains("pub tag: u8,"));
    assert!(decl.contains("pub data: *mut CleanObj,"));
}

#[test]
fn test_type_decl_llvm() {
    let cfg = config_for(NativeTarget::Llvm, Platform::Linux);
    let fields = vec![
        ("a".to_owned(), ExtNativeType::Int64),
        ("b".to_owned(), ExtNativeType::Int64),
    ];
    let decl = generate_type_decl("Pair", &fields, &cfg);
    assert!(decl.contains("%Pair = type { i64, i64 }"));
}

// ===========================================================================
// mangle_for_target
// ===========================================================================

#[test]
fn test_mangle_c_replaces_dots() {
    assert_eq!(
        mangle_for_target("Nat.add", &NativeTarget::C),
        "l5_Nat__add"
    );
}

#[test]
fn test_mangle_rust_replaces_dots() {
    assert_eq!(
        mangle_for_target("List.map", &NativeTarget::Rust),
        "l5_List_map"
    );
}

#[test]
fn test_mangle_llvm_replaces_dots() {
    assert_eq!(
        mangle_for_target("IO.println", &NativeTarget::Llvm),
        "l5_IO$println"
    );
}

#[test]
fn test_mangle_no_dots() {
    assert_eq!(mangle_for_target("main", &NativeTarget::C), "l5_main");
    assert_eq!(mangle_for_target("main", &NativeTarget::Rust), "l5_main");
    assert_eq!(mangle_for_target("main", &NativeTarget::Llvm), "l5_main");
}

#[test]
fn test_mangle_multiple_dots() {
    assert_eq!(
        mangle_for_target("A.B.C.D", &NativeTarget::C),
        "l5_A__B__C__D"
    );
}

// ===========================================================================
// sizeof_native
// ===========================================================================

#[test]
fn test_sizeof_void() {
    assert_eq!(sizeof_native(&ExtNativeType::Void, &Platform::Linux), 0);
}

#[test]
fn test_sizeof_scalars() {
    let p = Platform::Linux;
    assert_eq!(sizeof_native(&ExtNativeType::Bool, &p), 1);
    assert_eq!(sizeof_native(&ExtNativeType::UInt8, &p), 1);
    assert_eq!(sizeof_native(&ExtNativeType::Int8, &p), 1);
    assert_eq!(sizeof_native(&ExtNativeType::UInt16, &p), 2);
    assert_eq!(sizeof_native(&ExtNativeType::Int16, &p), 2);
    assert_eq!(sizeof_native(&ExtNativeType::UInt32, &p), 4);
    assert_eq!(sizeof_native(&ExtNativeType::Int32, &p), 4);
    assert_eq!(sizeof_native(&ExtNativeType::Float, &p), 4);
    assert_eq!(sizeof_native(&ExtNativeType::UInt64, &p), 8);
    assert_eq!(sizeof_native(&ExtNativeType::Int64, &p), 8);
    assert_eq!(sizeof_native(&ExtNativeType::Double, &p), 8);
}

#[test]
fn test_sizeof_pointer_linux() {
    let p = Platform::Linux;
    assert_eq!(
        sizeof_native(&ExtNativeType::Ptr(Box::new(ExtNativeType::UInt8)), &p),
        8
    );
    assert_eq!(sizeof_native(&ExtNativeType::LeanObj, &p), 8);
    assert_eq!(sizeof_native(&ExtNativeType::LeanBox, &p), 8);
}

#[test]
fn test_sizeof_pointer_wasm() {
    let p = Platform::Wasm;
    assert_eq!(sizeof_native(&ExtNativeType::LeanObj, &p), 4);
    assert_eq!(sizeof_native(&ExtNativeType::LeanBox, &p), 4);
    assert_eq!(
        sizeof_native(&ExtNativeType::Ptr(Box::new(ExtNativeType::Double)), &p),
        4
    );
}

#[test]
fn test_sizeof_array() {
    let p = Platform::MacOs;
    assert_eq!(
        sizeof_native(&ExtNativeType::Array(Box::new(ExtNativeType::UInt32)), &p),
        8
    );
}

#[test]
fn test_sizeof_struct_opaque() {
    assert_eq!(
        sizeof_native(&ExtNativeType::Struct("Foo".to_owned()), &Platform::Linux),
        8
    );
}

// ===========================================================================
// alignof_native
// ===========================================================================

#[test]
fn test_alignof_scalars() {
    let p = Platform::Linux;
    assert_eq!(alignof_native(&ExtNativeType::Void, &p), 1);
    assert_eq!(alignof_native(&ExtNativeType::Bool, &p), 1);
    assert_eq!(alignof_native(&ExtNativeType::UInt16, &p), 2);
    assert_eq!(alignof_native(&ExtNativeType::UInt32, &p), 4);
    assert_eq!(alignof_native(&ExtNativeType::Double, &p), 8);
}

#[test]
fn test_alignof_pointer_linux() {
    let p = Platform::Linux;
    assert_eq!(alignof_native(&ExtNativeType::LeanObj, &p), 8);
}

#[test]
fn test_alignof_pointer_wasm() {
    let p = Platform::Wasm;
    assert_eq!(alignof_native(&ExtNativeType::LeanObj, &p), 4);
}

// ===========================================================================
// is_boxed_type
// ===========================================================================

#[test]
fn test_is_boxed_object() {
    assert!(is_boxed_type(&IRType::Object));
}

#[test]
fn test_is_boxed_tobject() {
    assert!(is_boxed_type(&IRType::TObject));
}

#[test]
fn test_is_boxed_struct() {
    assert!(is_boxed_type(&IRType::Struct(vec![IRType::UInt32])));
}

#[test]
fn test_is_boxed_union() {
    assert!(is_boxed_type(&IRType::Union(vec![IRType::Bool])));
}

#[test]
fn test_is_not_boxed_scalars() {
    assert!(!is_boxed_type(&IRType::Bool));
    assert!(!is_boxed_type(&IRType::UInt8));
    assert!(!is_boxed_type(&IRType::UInt16));
    assert!(!is_boxed_type(&IRType::UInt32));
    assert!(!is_boxed_type(&IRType::UInt64));
    assert!(!is_boxed_type(&IRType::USize));
    assert!(!is_boxed_type(&IRType::Float32));
    assert!(!is_boxed_type(&IRType::Float64));
}

#[test]
fn test_is_not_boxed_erased() {
    assert!(!is_boxed_type(&IRType::Erased));
}

#[test]
fn test_is_not_boxed_void() {
    assert!(!is_boxed_type(&IRType::Void));
}

// ===========================================================================
// ExtNativeType display names
// ===========================================================================

#[test]
fn test_c_name_pointer() {
    let ty = ExtNativeType::Ptr(Box::new(ExtNativeType::UInt8));
    assert_eq!(ty.c_name(), "uint8_t*");
}

#[test]
fn test_rust_name_pointer() {
    let ty = ExtNativeType::Ptr(Box::new(ExtNativeType::Int32));
    assert_eq!(ty.rust_name(), "*mut i32");
}

#[test]
fn test_c_name_lean_obj() {
    assert_eq!(ExtNativeType::LeanObj.c_name(), "clean_obj*");
}

#[test]
fn test_rust_name_lean_obj() {
    assert_eq!(ExtNativeType::LeanObj.rust_name(), "*mut CleanObj");
}

#[test]
fn test_c_name_struct() {
    let ty = ExtNativeType::Struct("MyStruct".to_owned());
    assert_eq!(ty.c_name(), "struct MyStruct");
}

#[test]
fn test_rust_name_struct() {
    let ty = ExtNativeType::Struct("MyStruct".to_owned());
    assert_eq!(ty.rust_name(), "MyStruct");
}

// ===========================================================================
// Platform pointer_size
// ===========================================================================

#[test]
fn test_platform_pointer_size() {
    assert_eq!(Platform::Linux.pointer_size(), 8);
    assert_eq!(Platform::MacOs.pointer_size(), 8);
    assert_eq!(Platform::Windows.pointer_size(), 8);
    assert_eq!(Platform::Wasm.pointer_size(), 4);
}

// ===========================================================================
// NativeTarget Display
// ===========================================================================

#[test]
fn test_native_target_display() {
    assert_eq!(format!("{}", NativeTarget::C), "C");
    assert_eq!(format!("{}", NativeTarget::Rust), "Rust");
    assert_eq!(format!("{}", NativeTarget::Llvm), "LLVM");
}

// ===========================================================================
// NativeCodegenConfig defaults
// ===========================================================================

#[test]
fn test_config_default() {
    let cfg = NativeCodegenConfig::default();
    assert_eq!(cfg.target, NativeTarget::C);
    assert!(!cfg.optimize);
    assert!(!cfg.debug_info);
    assert!(cfg.runtime_checks);
    assert_eq!(cfg.platform, Platform::Linux);
}

// ===========================================================================
// Edge cases
// ===========================================================================

#[test]
fn test_generate_header_empty_decls() {
    let cfg = config_for(NativeTarget::C, Platform::Linux);
    let header = generate_header(&[], &cfg);
    assert!(header.contains("#pragma once"));
    // No function declarations
    assert!(!header.contains("l5_"));
}

#[test]
fn test_generate_type_decl_empty_fields() {
    let cfg = config_for(NativeTarget::C, Platform::Linux);
    let decl = generate_type_decl("Empty", &[], &cfg);
    assert!(decl.contains("typedef struct Empty {"));
    assert!(decl.contains("} Empty;"));
}
