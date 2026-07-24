// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended Rust code emitter.
//!
//! Part of #3084 - IO/FFI/Native.

use crate::emit_rust_ext::{
    default_ownership, rust_type_borrowed, rust_type_boxed, rust_type_owned, Ownership,
    RustExtConfig, RustExtEmitter, RustExtStats, RustFfiFunc,
};
use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use clean_kernel::Name;

// ── Helpers ──

fn mk_name(s: &str) -> Name {
    Name::from_string(s)
}

fn mk_fn_id(s: &str) -> FnId {
    FnId(mk_name(s))
}

fn mk_ctor(name: &str, tag: u32, num_objects: u32, field_types: Vec<IRType>) -> CtorInfo {
    let num_scalars = field_types.iter().filter(|t| t.is_scalar()).count() as u32;
    CtorInfo {
        name: mk_name(name),
        tag,
        num_scalars,
        num_objects,
        field_types,
    }
}

fn simple_decl(name: &str, params: Vec<(VarId, IRType)>, ret_ty: IRType, body: IRBody) -> IRDecl {
    IRDecl {
        name: mk_name(name),
        params,
        return_type: ret_ty,
        body,
    }
}

fn ret_body(arg: IRArg) -> IRBody {
    IRBody::Ret(arg)
}

// ── Type mapping tests ──

#[test]
fn test_map_type_bool() {
    assert_eq!(RustExtEmitter::map_type(&IRType::Bool), "u8");
}

#[test]
fn test_map_type_uint8() {
    assert_eq!(RustExtEmitter::map_type(&IRType::UInt8), "u8");
}

#[test]
fn test_map_type_uint16() {
    assert_eq!(RustExtEmitter::map_type(&IRType::UInt16), "u16");
}

#[test]
fn test_map_type_uint32() {
    assert_eq!(RustExtEmitter::map_type(&IRType::UInt32), "u32");
}

#[test]
fn test_map_type_uint64() {
    assert_eq!(RustExtEmitter::map_type(&IRType::UInt64), "u64");
}

#[test]
fn test_map_type_usize() {
    assert_eq!(RustExtEmitter::map_type(&IRType::USize), "usize");
}

#[test]
fn test_map_type_float32() {
    assert_eq!(RustExtEmitter::map_type(&IRType::Float32), "f32");
}

#[test]
fn test_map_type_float64() {
    assert_eq!(RustExtEmitter::map_type(&IRType::Float64), "f64");
}

#[test]
fn test_map_type_object() {
    assert_eq!(RustExtEmitter::map_type(&IRType::Object), "LeanObj");
}

#[test]
fn test_map_type_tobject() {
    assert_eq!(RustExtEmitter::map_type(&IRType::TObject), "LeanObj");
}

#[test]
fn test_map_type_struct() {
    let ty = IRType::Struct(vec![IRType::UInt32]);
    assert_eq!(RustExtEmitter::map_type(&ty), "LeanObj");
}

#[test]
fn test_map_type_erased() {
    assert_eq!(RustExtEmitter::map_type(&IRType::Erased), "LeanObj");
}

#[test]
fn test_map_type_void() {
    assert_eq!(RustExtEmitter::map_type(&IRType::Void), "()");
}

// ── Ownership type mapping ──

#[test]
fn test_rust_type_owned_object() {
    assert_eq!(rust_type_owned(&IRType::Object), "LeanObj");
}

#[test]
fn test_rust_type_borrowed_object() {
    assert_eq!(rust_type_borrowed(&IRType::Object), "&LeanObj");
}

#[test]
fn test_rust_type_borrowed_scalar() {
    // Scalars are Copy, so borrowed == owned
    assert_eq!(rust_type_borrowed(&IRType::UInt64), "u64");
}

#[test]
fn test_rust_type_boxed_object() {
    assert_eq!(rust_type_boxed(&IRType::Object), "Box<LeanObj>");
}

#[test]
fn test_rust_type_boxed_scalar() {
    assert_eq!(rust_type_boxed(&IRType::UInt32), "u32");
}

#[test]
fn test_default_ownership_scalar() {
    assert_eq!(default_ownership(&IRType::UInt64), Ownership::Owned);
}

#[test]
fn test_default_ownership_object() {
    assert_eq!(default_ownership(&IRType::Object), Ownership::Owned);
}

#[test]
fn test_map_type_with_ownership_borrowed() {
    let ty = RustExtEmitter::map_type_with_ownership(&IRType::Object, Ownership::Borrowed);
    assert_eq!(ty, "&LeanObj");
}

#[test]
fn test_map_type_with_ownership_borrowed_mut() {
    let ty = RustExtEmitter::map_type_with_ownership(&IRType::Object, Ownership::BorrowedMut);
    assert_eq!(ty, "&mut LeanObj");
}

// ── Function declaration emission ──

#[test]
fn test_emit_function_identity() {
    let decl = simple_decl(
        "test.id",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        ret_body(IRArg::Var(VarId(0))),
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("pub unsafe fn"), "output: {}", output);
    assert!(output.contains("LeanObj"), "output: {}", output);
    assert!(output.contains("return _x0;"), "output: {}", output);
}

#[test]
fn test_emit_function_no_params() {
    let decl = simple_decl("test.noop", vec![], IRType::Object, ret_body(IRArg::Erased));
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("()"), "empty params, output: {}", output);
}

#[test]
fn test_emit_function_multi_params() {
    let decl = simple_decl(
        "test.add",
        vec![(VarId(0), IRType::UInt64), (VarId(1), IRType::UInt64)],
        IRType::UInt64,
        ret_body(IRArg::Var(VarId(0))),
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("_x0: u64"), "output: {}", output);
    assert!(output.contains("_x1: u64"), "output: {}", output);
}

#[test]
fn test_emit_function_stats_count() {
    let d1 = simple_decl("test.f1", vec![], IRType::Object, ret_body(IRArg::Erased));
    let d2 = simple_decl("test.f2", vec![], IRType::Object, ret_body(IRArg::Erased));
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&d1).unwrap();
    emitter.emit_function(&d2).unwrap();
    assert_eq!(emitter.stats().functions_emitted, 2);
}

// ── Body emission with let bindings ──

#[test]
fn test_emit_body_let_binding() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = simple_decl("test.lit", vec![], IRType::UInt64, body);
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    assert_eq!(emitter.stats().let_bindings_emitted, 1);
    let output = emitter.finish();
    assert!(
        output.contains("let _x1: u64 = 42u64;"),
        "output: {}",
        output
    );
}

// ── Body emission with match expressions ──

#[test]
fn test_emit_body_match() {
    let ctor0 = mk_ctor("Bool.false", 0, 0, vec![]);
    let ctor1 = mk_ctor("Bool.true", 1, 0, vec![]);
    let body = IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![
            IRAlt {
                ctor: ctor0,
                body: Box::new(IRBody::Ret(IRArg::Erased)),
            },
            IRAlt {
                ctor: ctor1,
                body: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
            },
        ],
        default: None,
    };
    let decl = simple_decl(
        "test.case",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        body,
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    assert_eq!(emitter.stats().match_exprs_emitted, 1);
    let output = emitter.finish();
    assert!(
        output.contains("match clean_obj_tag("),
        "output: {}",
        output
    );
    assert!(output.contains("0 => {"), "output: {}", output);
    assert!(output.contains("1 => {"), "output: {}", output);
}

#[test]
fn test_emit_body_match_with_default() {
    let ctor0 = mk_ctor("Option.some", 0, 1, vec![IRType::Object]);
    let body = IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![IRAlt {
            ctor: ctor0,
            body: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        }],
        default: Some(Box::new(IRBody::Ret(IRArg::Erased))),
    };
    let decl = simple_decl(
        "test.case_default",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        body,
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("_ => {"), "output: {}", output);
}

#[test]
fn test_emit_body_unreachable() {
    let decl = simple_decl(
        "test.unreachable",
        vec![],
        IRType::Void,
        IRBody::Unreachable,
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("unreachable!(\"IR unreachable\")"),
        "output: {}",
        output
    );
}

// ── RC operations ──

#[test]
fn test_emit_rc_inc() {
    let body = IRBody::Inc {
        var: VarId(0),
        n: 1,
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let decl = simple_decl(
        "test.inc",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        body,
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("clean_inc_ref(_x0)"), "output: {}", output);
}

#[test]
fn test_emit_rc_inc_multi() {
    let body = IRBody::Inc {
        var: VarId(0),
        n: 3,
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let decl = simple_decl(
        "test.inc_n",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        body,
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("clean_inc_ref_n(_x0, 3)"),
        "output: {}",
        output
    );
}

#[test]
fn test_emit_rc_dec() {
    let body = IRBody::Dec {
        var: VarId(0),
        rest: Box::new(IRBody::Ret(IRArg::Erased)),
    };
    let decl = simple_decl(
        "test.dec",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        body,
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("clean_dec_ref(_x0)"), "output: {}", output);
}

// ── Closure emission ──

#[test]
fn test_emit_closure_alloc() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: mk_fn_id("Nat.add"),
            arity: 2,
            args: vec![IRArg::Var(VarId(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = simple_decl(
        "test.pap",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        body,
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    assert_eq!(emitter.stats().closures_emitted, 1);
    let output = emitter.finish();
    assert!(
        output.contains("clean_alloc_closure("),
        "output: {}",
        output
    );
}

#[test]
fn test_emit_closure_apply() {
    let body = IRBody::VDecl {
        var: VarId(2),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(VarId(0)),
            args: vec![IRArg::Var(VarId(1))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
    };
    let decl = simple_decl(
        "test.capp",
        vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        IRType::Object,
        body,
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("clean_closure_apply(_x0, &[_x1])"),
        "output: {}",
        output
    );
}

#[test]
fn test_emit_closure_struct() {
    let mut emitter = RustExtEmitter::new();
    emitter.emit_closure_struct(
        "my_func",
        &[(VarId(0), IRType::Object)],
        &[(VarId(1), IRType::UInt64)],
        &IRType::Object,
    );
    assert_eq!(emitter.stats().closures_emitted, 1);
    let output = emitter.finish();
    assert!(
        output.contains("struct Closure_my_func"),
        "output: {}",
        output
    );
    assert!(output.contains("_x0: LeanObj"), "output: {}", output);
    assert!(
        output.contains("fn call(&self, _x1: u64) -> LeanObj"),
        "output: {}",
        output
    );
}

// ── Trait implementation emission ──

#[test]
fn test_emit_drop_impl() {
    let mut emitter = RustExtEmitter::new();
    emitter.emit_drop_impl("RcWrapper");
    assert_eq!(emitter.stats().trait_impls_emitted, 1);
    let output = emitter.finish();
    assert!(
        output.contains("impl Drop for RcWrapper"),
        "output: {}",
        output
    );
    assert!(
        output.contains("clean_dec_ref(self.ptr)"),
        "output: {}",
        output
    );
}

#[test]
fn test_emit_from_impl() {
    let mut emitter = RustExtEmitter::new();
    emitter.emit_from_impl("RcWrapper");
    assert_eq!(emitter.stats().trait_impls_emitted, 1);
    let output = emitter.finish();
    assert!(
        output.contains("impl From<*mut LeanObj> for RcWrapper"),
        "output: {}",
        output
    );
    assert!(output.contains("RcWrapper { ptr }"), "output: {}", output);
}

#[test]
fn test_emit_both_trait_impls() {
    let mut emitter = RustExtEmitter::new();
    emitter.emit_drop_impl("MyObj");
    emitter.emit_from_impl("MyObj");
    assert_eq!(emitter.stats().trait_impls_emitted, 2);
}

// ── Module structure emission ──

#[test]
fn test_emit_module_header() {
    let mut emitter = RustExtEmitter::new();
    emitter.emit_module_header();
    let output = emitter.finish();
    assert!(
        output.contains("Generated module: clean_generated"),
        "output: {}",
        output
    );
    assert!(output.contains("#![allow("), "output: {}", output);
    assert!(
        output.contains("use clean_runtime::*;"),
        "output: {}",
        output
    );
}

#[test]
fn test_emit_mod_decl() {
    let mut emitter = RustExtEmitter::new();
    emitter.emit_mod_decl("my_sub");
    let output = emitter.finish();
    assert!(output.contains("pub mod my_sub;"), "output: {}", output);
}

#[test]
fn test_emit_use_stmt() {
    let mut emitter = RustExtEmitter::new();
    emitter.emit_use_stmt("crate::types::LeanObj");
    let output = emitter.finish();
    assert!(
        output.contains("use crate::types::LeanObj;"),
        "output: {}",
        output
    );
}

// ── FFI bridge emission ──

#[test]
fn test_emit_ffi_bridge() {
    let func = RustFfiFunc {
        lean_name: "IO.println".to_string(),
        extern_name: "clean_io_println".to_string(),
        param_types: vec![IRType::Object],
        return_type: IRType::Object,
    };
    let mut emitter = RustExtEmitter::new();
    emitter.emit_ffi_bridge(&func);
    assert_eq!(emitter.stats().ffi_bridges_emitted, 1);
    let output = emitter.finish();
    assert!(output.contains("#[no_mangle]"), "output: {}", output);
    assert!(
        output.contains("pub unsafe extern \"C\" fn clean_io_println"),
        "output: {}",
        output
    );
    assert!(output.contains("_a0: LeanObj"), "output: {}", output);
}

#[test]
fn test_emit_ffi_bridge_no_params() {
    let func = RustFfiFunc {
        lean_name: "IO.getStdin".to_string(),
        extern_name: "clean_io_get_stdin".to_string(),
        param_types: vec![],
        return_type: IRType::Object,
    };
    let mut emitter = RustExtEmitter::new();
    emitter.emit_ffi_bridge(&func);
    let output = emitter.finish();
    assert!(
        output.contains("fn clean_io_get_stdin() -> LeanObj"),
        "output: {}",
        output
    );
}

#[test]
fn test_emit_ffi_bridge_multi_params() {
    let func = RustFfiFunc {
        lean_name: "test.add".to_string(),
        extern_name: "clean_test_add".to_string(),
        param_types: vec![IRType::UInt64, IRType::UInt64],
        return_type: IRType::UInt64,
    };
    let mut emitter = RustExtEmitter::new();
    emitter.emit_ffi_bridge(&func);
    let output = emitter.finish();
    assert!(output.contains("_a0: u64"), "output: {}", output);
    assert!(output.contains("_a1: u64"), "output: {}", output);
    assert!(output.contains("-> u64"), "output: {}", output);
}

// ── Cargo.toml snippet generation ──

#[test]
fn test_cargo_toml_snippet() {
    let emitter = RustExtEmitter::new();
    let snippet = emitter.cargo_toml_snippet();
    assert!(snippet.contains("[package]"), "snippet: {}", snippet);
    assert!(
        snippet.contains("name = \"clean_generated\""),
        "snippet: {}",
        snippet
    );
    assert!(snippet.contains("[dependencies]"), "snippet: {}", snippet);
    assert!(snippet.contains("clean-runtime"), "snippet: {}", snippet);
}

#[test]
fn test_cargo_toml_snippet_custom_name() {
    let config = RustExtConfig {
        module_name: "my_project".into(),
        ..RustExtConfig::default()
    };
    let emitter = RustExtEmitter::with_config(config);
    let snippet = emitter.cargo_toml_snippet();
    assert!(
        snippet.contains("name = \"my_project\""),
        "snippet: {}",
        snippet
    );
}

// ── Statistics ──

#[test]
fn test_stats_default() {
    let stats = RustExtStats::default();
    assert_eq!(stats.functions_emitted, 0);
    assert_eq!(stats.closures_emitted, 0);
    assert_eq!(stats.trait_impls_emitted, 0);
    assert_eq!(stats.ffi_bridges_emitted, 0);
    assert_eq!(stats.let_bindings_emitted, 0);
    assert_eq!(stats.match_exprs_emitted, 0);
}

// ── Full module emission ──

#[test]
fn test_emit_module_no_ffi() {
    let decl = simple_decl(
        "test.id",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        ret_body(IRArg::Var(VarId(0))),
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_module(&[decl], &[]).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("use clean_runtime::*;"),
        "output: {}",
        output
    );
    assert!(output.contains("return _x0;"), "output: {}", output);
    assert!(
        !output.contains("FFI bridges"),
        "should not have FFI section"
    );
}

#[test]
fn test_emit_module_with_ffi() {
    let decl = simple_decl(
        "test.id",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        ret_body(IRArg::Var(VarId(0))),
    );
    let ffi = RustFfiFunc {
        lean_name: "IO.read".to_string(),
        extern_name: "clean_io_read".to_string(),
        param_types: vec![IRType::Object],
        return_type: IRType::Object,
    };
    let mut emitter = RustExtEmitter::new();
    emitter.emit_module(&[decl], &[ffi]).unwrap();
    let output = emitter.finish();
    assert!(output.contains("FFI bridges"), "output: {}", output);
    assert!(output.contains("#[no_mangle]"), "output: {}", output);
    assert!(output.contains("clean_io_read"), "output: {}", output);
}

// ── Config ──

#[test]
fn test_config_default() {
    let config = RustExtConfig::default();
    assert_eq!(config.module_name, "clean_generated");
    assert!(config.emit_trait_impls);
    assert!(!config.emit_cargo_snippet);
    assert_eq!(config.indent, "    ");
}

#[test]
fn test_custom_config_module_name() {
    let config = RustExtConfig {
        module_name: "custom_mod".into(),
        ..RustExtConfig::default()
    };
    let mut emitter = RustExtEmitter::with_config(config);
    emitter.emit_module_header();
    let output = emitter.finish();
    assert!(
        output.contains("Generated module: custom_mod"),
        "output: {}",
        output
    );
}

// ── Expression edge cases ──

#[test]
fn test_emit_ctor_boxed_tag() {
    let ctor = mk_ctor("Bool.true", 1, 0, vec![]);
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor,
            args: vec![],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let decl = simple_decl("test.true", vec![], IRType::Object, body);
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("clean_box(1)"), "output: {}", output);
}

#[test]
fn test_emit_box_uint64() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::Box {
            ty: IRType::UInt64,
            arg: IRArg::Var(VarId(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = simple_decl(
        "test.box",
        vec![(VarId(0), IRType::UInt64)],
        IRType::Object,
        body,
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("clean_box_uint64(_x0)"),
        "output: {}",
        output
    );
}

#[test]
fn test_emit_unbox_float64() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Float64,
        value: IRExpr::Unbox {
            ty: IRType::Float64,
            arg: IRArg::Var(VarId(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = simple_decl(
        "test.unbox",
        vec![(VarId(0), IRType::Object)],
        IRType::Float64,
        body,
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("clean_unbox_float(_x0)"),
        "output: {}",
        output
    );
}

#[test]
fn test_emit_is_shared() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Bool,
        value: IRExpr::IsShared(VarId(0)),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = simple_decl(
        "test.shared",
        vec![(VarId(0), IRType::Object)],
        IRType::Bool,
        body,
    );
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("(!clean_is_exclusive(_x0)) as u8"),
        "output: {}",
        output
    );
}

#[test]
fn test_emit_string_literal() {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::String("hello".to_string()),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let decl = simple_decl("test.str", vec![], IRType::Object, body);
    let mut emitter = RustExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("clean_mk_string(\"hello\")"),
        "output: {}",
        output
    );
}
