// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended C code emitter.
//!
//! Part of #3084 - IO/FFI/Native.

use crate::emit_c_ext::{CExtEmitConfig, CExtEmitter, EmitStats, FfiFunc};
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId};
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
    assert_eq!(CExtEmitter::map_type(&IRType::Bool), "uint8_t");
}

#[test]
fn test_map_type_uint8() {
    assert_eq!(CExtEmitter::map_type(&IRType::UInt8), "uint8_t");
}

#[test]
fn test_map_type_uint16() {
    assert_eq!(CExtEmitter::map_type(&IRType::UInt16), "uint16_t");
}

#[test]
fn test_map_type_uint32() {
    assert_eq!(CExtEmitter::map_type(&IRType::UInt32), "uint32_t");
}

#[test]
fn test_map_type_uint64() {
    assert_eq!(CExtEmitter::map_type(&IRType::UInt64), "uint64_t");
}

#[test]
fn test_map_type_usize() {
    assert_eq!(CExtEmitter::map_type(&IRType::USize), "size_t");
}

#[test]
fn test_map_type_float32() {
    assert_eq!(CExtEmitter::map_type(&IRType::Float32), "float");
}

#[test]
fn test_map_type_float64() {
    assert_eq!(CExtEmitter::map_type(&IRType::Float64), "double");
}

#[test]
fn test_map_type_object() {
    assert_eq!(CExtEmitter::map_type(&IRType::Object), "lean_object*");
}

#[test]
fn test_map_type_tobject() {
    assert_eq!(CExtEmitter::map_type(&IRType::TObject), "lean_object*");
}

#[test]
fn test_map_type_struct() {
    let ty = IRType::Struct(vec![IRType::UInt32]);
    assert_eq!(CExtEmitter::map_type(&ty), "lean_object*");
}

#[test]
fn test_map_type_erased() {
    assert_eq!(CExtEmitter::map_type(&IRType::Erased), "lean_object*");
}

#[test]
fn test_map_type_void() {
    assert_eq!(CExtEmitter::map_type(&IRType::Void), "void");
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
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("lean_object*"), "output: {}", output);
    assert!(output.contains("return _x0;"), "output: {}", output);
    assert!(output.contains("{"), "missing opening brace");
    assert!(output.contains("}"), "missing closing brace");
}

#[test]
fn test_emit_function_void_params() {
    let decl = simple_decl("test.noop", vec![], IRType::Object, ret_body(IRArg::Erased));
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("(void)"), "output: {}", output);
}

#[test]
fn test_emit_function_multi_params() {
    let decl = simple_decl(
        "test.add",
        vec![(VarId(0), IRType::UInt64), (VarId(1), IRType::UInt64)],
        IRType::UInt64,
        ret_body(IRArg::Var(VarId(0))),
    );
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("uint64_t _x0"), "output: {}", output);
    assert!(output.contains("uint64_t _x1"), "output: {}", output);
}

#[test]
fn test_emit_functions_forward_decls() {
    let d1 = simple_decl(
        "test.f1",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        ret_body(IRArg::Var(VarId(0))),
    );
    let d2 = simple_decl("test.f2", vec![], IRType::UInt32, ret_body(IRArg::Erased));
    let mut emitter = CExtEmitter::new();
    emitter.emit_functions(&[d1, d2]).unwrap();
    let output = emitter.finish();
    // Should have both forward declarations and definitions
    let semicolons_before_braces = output.find('{').unwrap();
    let forward_section = &output[..semicolons_before_braces];
    assert!(forward_section.contains(';'), "no forward decl semicolons");
}

// ── Body emission with control flow ──

#[test]
fn test_emit_body_case_switch() {
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
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("switch (lean_obj_tag("),
        "output: {}",
        output
    );
    assert!(output.contains("case 0:"), "output: {}", output);
    assert!(output.contains("case 1:"), "output: {}", output);
}

#[test]
fn test_emit_body_case_with_default() {
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
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("default:"), "output: {}", output);
}

#[test]
fn test_emit_body_unreachable() {
    let decl = simple_decl(
        "test.unreachable",
        vec![],
        IRType::Void,
        IRBody::Unreachable,
    );
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("__builtin_unreachable()"),
        "output: {}",
        output
    );
}

// ── Reference counting emission ──

#[test]
fn test_emit_rc_inc_single() {
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
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let rc_ops_emitted = emitter.stats().rc_ops_emitted;
    let output = emitter.finish();
    assert!(output.contains("lean_inc_ref(_x0)"), "output: {}", output);
    assert_eq!(rc_ops_emitted, 1);
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
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("lean_inc_ref_n(_x0, 3)"),
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
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("lean_dec_ref(_x0)"), "output: {}", output);
}

#[test]
fn test_emit_rc_inc_dec_stats() {
    let body = IRBody::Inc {
        var: VarId(0),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: VarId(0),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        }),
    };
    let decl = simple_decl(
        "test.incdec",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        body,
    );
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    assert_eq!(emitter.stats().rc_ops_emitted, 2);
}

// ── Closure representation ──

#[test]
fn test_emit_closure_alloc_no_args() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: mk_fn_id("Nat.add"),
            arity: 2,
            args: vec![],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = simple_decl("test.pap0", vec![], IRType::Object, body);
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let closures_emitted = emitter.stats().closures_emitted;
    let output = emitter.finish();
    assert!(
        output.contains("lean_alloc_closure((void*)"),
        "output: {}",
        output
    );
    assert!(output.contains(", 2, 0)"), "output: {}", output);
    assert_eq!(closures_emitted, 1);
}

#[test]
fn test_emit_closure_alloc_with_args() {
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
        "test.pap1",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        body,
    );
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("lean_alloc_closure((void*)"),
        "output: {}",
        output
    );
    assert!(output.contains(", 2, 1, _x0)"), "output: {}", output);
}

#[test]
fn test_emit_closure_apply_small() {
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
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("lean_apply_1(_x0, _x1)"),
        "output: {}",
        output
    );
}

// ── String / Array literal emission ──

#[test]
fn test_emit_string_literal() {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::String("hello".to_string()),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let decl = simple_decl("test.str", vec![], IRType::Object, body);
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let string_literals_emitted = emitter.stats().string_literals_emitted;
    let output = emitter.finish();
    assert!(
        output.contains("lean_mk_string(\"hello\")"),
        "output: {}",
        output
    );
    assert_eq!(string_literals_emitted, 1);
}

#[test]
fn test_emit_string_literal_escape() {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::String("line1\nline2".to_string()),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let decl = simple_decl("test.str_esc", vec![], IRType::Object, body);
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("\\n"),
        "should escape newline, output: {}",
        output
    );
}

#[test]
fn test_emit_array_literal() {
    let mut emitter = CExtEmitter::new();
    let result =
        emitter.emit_array_literal(VarId(5), &[IRArg::Var(VarId(0)), IRArg::Var(VarId(1))]);
    assert!(
        result.contains("lean_alloc_array(2, 2)"),
        "result: {}",
        result
    );
    assert!(
        result.contains("lean_array_set_core(_x5, 0, _x0)"),
        "result: {}",
        result
    );
    assert!(
        result.contains("lean_array_set_core(_x5, 1, _x1)"),
        "result: {}",
        result
    );
    assert_eq!(emitter.stats().array_literals_emitted, 1);
}

// ── FFI wrapper emission ──

#[test]
fn test_emit_extern_c_decl() {
    let func = FfiFunc {
        lean_name: "IO.println".to_string(),
        c_name: "lean_io_println".to_string(),
        param_types: vec![IRType::Object],
        return_type: IRType::Object,
    };
    assert_eq!(func.lean_name, "IO.println");
    let mut emitter = CExtEmitter::new();
    emitter.emit_extern_c_decl(&func);
    let output = emitter.finish();
    assert!(
        output.contains("extern lean_object* lean_io_println(lean_object*)"),
        "output: {}",
        output
    );
}

#[test]
fn test_emit_extern_c_decl_void_params() {
    let func = FfiFunc {
        lean_name: "IO.getStdin".to_string(),
        c_name: "lean_io_get_stdin".to_string(),
        param_types: vec![],
        return_type: IRType::Object,
    };
    let mut emitter = CExtEmitter::new();
    emitter.emit_extern_c_decl(&func);
    let output = emitter.finish();
    assert!(output.contains("(void)"), "output: {}", output);
}

#[test]
fn test_emit_ffi_wrapper() {
    let func = FfiFunc {
        lean_name: "IO.println".to_string(),
        c_name: "lean_io_println".to_string(),
        param_types: vec![IRType::Object],
        return_type: IRType::Object,
    };
    let mut emitter = CExtEmitter::new();
    emitter.emit_ffi_wrapper(&func);
    let ffi_wrappers_emitted = emitter.stats().ffi_wrappers_emitted;
    let output = emitter.finish();
    assert!(
        output.contains("l_lean_io_println"),
        "wrapper name, output: {}",
        output
    );
    assert!(
        output.contains("return lean_io_println(_a0)"),
        "output: {}",
        output
    );
    assert_eq!(ffi_wrappers_emitted, 1);
}

#[test]
fn test_emit_ffi_wrapper_void_return() {
    let func = FfiFunc {
        lean_name: "IO.print_raw".to_string(),
        c_name: "lean_io_print_raw".to_string(),
        param_types: vec![IRType::Object],
        return_type: IRType::Void,
    };
    let mut emitter = CExtEmitter::new();
    emitter.emit_ffi_wrapper(&func);
    let output = emitter.finish();
    assert!(
        !output.contains("return lean_io_print_raw"),
        "void should not have return"
    );
    assert!(
        output.contains("lean_io_print_raw(_a0);"),
        "output: {}",
        output
    );
}

// ── Header file generation ──

#[test]
fn test_emit_header_file_pragma_once() {
    let decl = simple_decl(
        "test.id",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        ret_body(IRArg::Var(VarId(0))),
    );
    let mut emitter = CExtEmitter::new();
    emitter.emit_header_file(&[decl]);
    let output = emitter.finish();
    assert!(output.starts_with("#pragma once"), "output: {}", output);
}

#[test]
fn test_emit_header_file_includes() {
    let mut emitter = CExtEmitter::new();
    emitter.emit_header_file(&[]);
    let output = emitter.finish();
    assert!(output.contains("#include <stdint.h>"), "output: {}", output);
    assert!(output.contains("#include <stddef.h>"), "output: {}", output);
    assert!(output.contains("lean_runtime.h"), "output: {}", output);
}

#[test]
fn test_emit_header_file_forward_decls() {
    let d1 = simple_decl(
        "test.f",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        ret_body(IRArg::Var(VarId(0))),
    );
    let mut emitter = CExtEmitter::new();
    emitter.emit_header_file(&[d1]);
    let output = emitter.finish();
    assert!(output.contains("uint64_t"), "output: {}", output);
    assert!(output.contains(';'), "should have prototype semicolon");
    assert!(!output.contains('{'), "header should not contain bodies");
}

// ── Source header / include guard ──

#[test]
fn test_emit_source_header_includes() {
    let mut emitter = CExtEmitter::new();
    emitter.emit_source_header();
    let output = emitter.finish();
    assert!(output.contains("#include <stdint.h>"), "output: {}", output);
    assert!(output.contains("#include <stddef.h>"), "output: {}", output);
    assert!(
        output.contains("#include <stdbool.h>"),
        "output: {}",
        output
    );
    assert!(output.contains("#include <string.h>"), "output: {}", output);
    assert!(output.contains("lean_runtime.h"), "output: {}", output);
}

#[test]
fn test_emit_source_header_comment() {
    let mut emitter = CExtEmitter::new();
    emitter.emit_source_header();
    let output = emitter.finish();
    assert!(
        output.contains("Generated by clean compiler"),
        "output: {}",
        output
    );
}

// ── Statistics ──

#[test]
fn test_stats_default() {
    let stats = EmitStats::default();
    assert_eq!(stats.functions_emitted, 0);
    assert_eq!(stats.closures_emitted, 0);
    assert_eq!(stats.ffi_wrappers_emitted, 0);
    assert_eq!(stats.rc_ops_emitted, 0);
    assert_eq!(stats.string_literals_emitted, 0);
    assert_eq!(stats.array_literals_emitted, 0);
}

#[test]
fn test_stats_function_count() {
    let d1 = simple_decl("test.f1", vec![], IRType::Object, ret_body(IRArg::Erased));
    let d2 = simple_decl("test.f2", vec![], IRType::Object, ret_body(IRArg::Erased));
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&d1).unwrap();
    emitter.emit_function(&d2).unwrap();
    assert_eq!(emitter.stats().functions_emitted, 2);
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
    let mut emitter = CExtEmitter::new();
    emitter.emit_module(&[decl], &[]).unwrap();
    let output = emitter.finish();
    assert!(output.contains("#include"), "output: {}", output);
    assert!(output.contains("return _x0;"), "output: {}", output);
}

#[test]
fn test_emit_module_with_ffi() {
    let decl = simple_decl(
        "test.id",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        ret_body(IRArg::Var(VarId(0))),
    );
    let ffi = FfiFunc {
        lean_name: "IO.read".to_string(),
        c_name: "lean_io_read".to_string(),
        param_types: vec![IRType::Object],
        return_type: IRType::Object,
    };
    let mut emitter = CExtEmitter::new();
    emitter.emit_module(&[decl], &[ffi]).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("Extern (FFI) declarations"),
        "output: {}",
        output
    );
    assert!(output.contains("FFI wrappers"), "output: {}", output);
    assert!(output.contains("l_lean_io_read"), "output: {}", output);
}

// ── Config ──

#[test]
fn test_config_default() {
    let config = CExtEmitConfig::default();
    assert_eq!(config.module_name, "clean_module");
    assert!(!config.debug);
    assert_eq!(config.indent, "  ");
}

#[test]
fn test_custom_config() {
    let config = CExtEmitConfig {
        module_name: "my_module".to_string(),
        debug: true,
        indent: "    ".to_string(),
    };
    let emitter = CExtEmitter::with_config(config);
    let output = emitter.finish();
    assert!(output.is_empty());
}

// ── Expression emission edge cases ──

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
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("lean_box(1)"), "output: {}", output);
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
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("lean_box_uint64(_x0)"),
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
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("lean_unbox_float(_x0)"),
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
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(
        output.contains("!lean_is_exclusive(_x0)"),
        "output: {}",
        output
    );
}

#[test]
fn test_emit_jmp() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(VarId(1), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        rest: Box::new(IRBody::Jmp {
            jp: JoinPointId(0),
            args: vec![IRArg::Var(VarId(0))],
        }),
    };
    let decl = simple_decl(
        "test.jmp",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        body,
    );
    let mut emitter = CExtEmitter::new();
    emitter.emit_function(&decl).unwrap();
    let output = emitter.finish();
    assert!(output.contains("goto _jp0;"), "output: {}", output);
    assert!(output.contains("_jp0:"), "output: {}", output);
}
