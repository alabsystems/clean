// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

mod ctor_reuse;
#[path = "ir_construct_tests.rs"]
mod ir_construct_tests;
mod roundtrip;

use super::*;
use crate::ir::{CtorInfo, IRAlt, IRBody, JoinPointId};
use clean_kernel::Name;

fn var(n: u32) -> VarId {
    VarId(n)
}

fn jp(n: u32) -> JoinPointId {
    JoinPointId(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

// ── Type emission ──────────────────────────────────────────────────

#[test]
fn test_emit_type_scalars() {
    let emitter = RustEmitter::new();
    assert_eq!(emitter.emit_type(&IRType::Bool), "u8");
    assert_eq!(emitter.emit_type(&IRType::UInt8), "u8");
    assert_eq!(emitter.emit_type(&IRType::UInt16), "u16");
    assert_eq!(emitter.emit_type(&IRType::UInt32), "u32");
    assert_eq!(emitter.emit_type(&IRType::UInt64), "u64");
    assert_eq!(emitter.emit_type(&IRType::USize), "usize");
    assert_eq!(emitter.emit_type(&IRType::Float32), "f32");
    assert_eq!(emitter.emit_type(&IRType::Float64), "f64");
}

#[test]
fn test_emit_type_objects() {
    let emitter = RustEmitter::new();
    assert_eq!(emitter.emit_type(&IRType::Object), "*mut CleanObj");
    assert_eq!(emitter.emit_type(&IRType::TObject), "*mut CleanObj");
    assert_eq!(emitter.emit_type(&IRType::Erased), "*mut CleanObj");
}

#[test]
fn test_emit_type_void() {
    let emitter = RustEmitter::new();
    assert_eq!(emitter.emit_type(&IRType::Void), "()");
}

// ── Variable and literal emission ──────────────────────────────────

#[test]
fn test_emit_var() {
    let emitter = RustEmitter::new();
    assert_eq!(emitter.emit_var(var(0)), "_x0");
    assert_eq!(emitter.emit_var(var(42)), "_x42");
}

#[test]
fn test_emit_literal() {
    let emitter = RustEmitter::new();
    assert_eq!(emitter.emit_literal(&IRLiteral::Bool(true)), "1u8");
    assert_eq!(emitter.emit_literal(&IRLiteral::Bool(false)), "0u8");
    assert_eq!(emitter.emit_literal(&IRLiteral::UInt64(42)), "42u64");
    assert_eq!(emitter.emit_literal(&IRLiteral::USize(100)), "100usize");
}

// ── Default value emission ─────────────────────────────────────────

#[test]
fn test_emit_default() {
    let emitter = RustEmitter::new();
    assert_eq!(emitter.emit_default(&IRType::UInt64), "0u64");
    assert_eq!(
        emitter.emit_default(&IRType::Object),
        "std::ptr::null_mut()"
    );
    assert_eq!(emitter.emit_default(&IRType::Void), "()");
    assert_eq!(emitter.emit_default(&IRType::Float64), "0.0f64");
}

// ── Simple body emission ───────────────────────────────────────────

#[test]
fn test_emit_simple_return() {
    let decl = IRDecl {
        name: name("id"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("pub unsafe fn l_id(_x0: *mut CleanObj) -> *mut CleanObj"),
        "function signature missing, got:\n{}",
        code
    );
    assert!(
        code.contains("return _x0;"),
        "return statement missing, got:\n{}",
        code
    );
}

#[test]
fn test_emit_inc_dec() {
    let body = IRBody::Inc {
        var: var(0),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(1),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        }),
    };

    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_inc(_x0);"),
        "inc missing, got:\n{}",
        code
    );
    assert!(
        code.contains("clean_dec(_x1);"),
        "dec missing, got:\n{}",
        code
    );
}

#[test]
fn test_emit_inc_n() {
    let body = IRBody::Inc {
        var: var(0),
        n: 3,
        rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
    };

    let decl = IRDecl {
        name: name("test_inc_n"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_inc_n(_x0, 3);"),
        "inc_n missing, got:\n{}",
        code
    );
}

#[test]
fn test_emit_vdecl() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("const42"),
        params: vec![],
        return_type: IRType::UInt64,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("let _x1: u64 = 42u64;"),
        "vdecl missing, got:\n{}",
        code
    );
}

#[test]
fn test_emit_case() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![
            IRAlt {
                ctor: CtorInfo {
                    name: name("Nat.zero"),
                    tag: 0,
                    num_scalars: 0,
                    num_objects: 0,
                    field_types: vec![],
                },
                body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            },
            IRAlt {
                ctor: CtorInfo {
                    name: name("Nat.succ"),
                    tag: 1,
                    num_scalars: 0,
                    num_objects: 1,
                    field_types: vec![IRType::Object],
                },
                body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            },
        ],
        default: None,
    };

    let decl = IRDecl {
        name: name("match_nat"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("match clean_obj_tag(_x0)"),
        "match missing, got:\n{}",
        code
    );
    assert!(code.contains("0 => {"), "case 0 missing, got:\n{}", code);
    assert!(code.contains("1 => {"), "case 1 missing, got:\n{}", code);
    // No explicit default in IR → emitter adds unreachable default
    assert!(
        code.contains("_ => {"),
        "default arm missing, got:\n{}",
        code
    );
}

#[test]
fn test_emit_case_with_default() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: CtorInfo {
                name: name("Bool.true"),
                tag: 1,
                num_scalars: 0,
                num_objects: 0,
                field_types: vec![],
            },
            body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        }],
        default: Some(Box::new(IRBody::Unreachable)),
    };

    let decl = IRDecl {
        name: name("test_default"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("_ => {"),
        "default arm missing, got:\n{}",
        code
    );
    assert!(
        code.contains("clean_panic(\"unreachable\");"),
        "unreachable in default missing, got:\n{}",
        code
    );
}

#[test]
fn test_emit_function_call() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: FnId(name("Nat.add")),
            args: vec![IRArg::Var(var(0)), IRArg::Var(var(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("double"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("l_Nat_add(_x0, _x0)"),
        "function call missing, got:\n{}",
        code
    );
}

#[test]
fn test_emit_set() {
    let body = IRBody::Set {
        var: var(0),
        idx: 1,
        value: var(1),
        rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
    };

    let decl = IRDecl {
        name: name("test_set"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_ctor_set(_x0, 1, _x1);"),
        "ctor_set missing, got:\n{}",
        code
    );
}

// ── Join point emission ────────────────────────────────────────────

#[test]
fn test_emit_join_point_simple() {
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(2), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
        rest: Box::new(IRBody::Jmp {
            jp: jp(0),
            args: vec![IRArg::Var(var(0))],
        }),
    };

    let decl = IRDecl {
        name: name("jp_simple"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("let mut _x2: *mut CleanObj = std::ptr::null_mut();"),
        "mutable param slot missing, got:\n{}",
        code
    );
    assert!(
        code.contains("'_jp0_init: {"),
        "init label missing, got:\n{}",
        code
    );
    assert!(
        code.contains("break '_jp0_init;"),
        "break init missing, got:\n{}",
        code
    );
    assert!(
        code.contains("'_jp0: loop {"),
        "loop label missing, got:\n{}",
        code
    );
    assert!(
        code.contains("return _x2;"),
        "return in jp body missing, got:\n{}",
        code
    );
    assert!(
        code.contains("_x2 = _x0;"),
        "param assignment missing, got:\n{}",
        code
    );
}

#[test]
fn test_emit_join_point_with_case() {
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(3), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(var(3)))),
        rest: Box::new(IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: CtorInfo {
                        name: name("Bool.false"),
                        tag: 0,
                        num_scalars: 0,
                        num_objects: 0,
                        field_types: vec![],
                    },
                    body: Box::new(IRBody::Jmp {
                        jp: jp(0),
                        args: vec![IRArg::Var(var(1))],
                    }),
                },
                IRAlt {
                    ctor: CtorInfo {
                        name: name("Bool.true"),
                        tag: 1,
                        num_scalars: 0,
                        num_objects: 0,
                        field_types: vec![],
                    },
                    body: Box::new(IRBody::Jmp {
                        jp: jp(0),
                        args: vec![IRArg::Var(var(2))],
                    }),
                },
            ],
            default: None,
        }),
    };

    let decl = IRDecl {
        name: name("jp_case"),
        params: vec![
            (var(0), IRType::Object),
            (var(1), IRType::Object),
            (var(2), IRType::Object),
        ],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("_x3 = _x1;"),
        "alt0 assignment missing, got:\n{}",
        code
    );
    assert!(
        code.contains("_x3 = _x2;"),
        "alt1 assignment missing, got:\n{}",
        code
    );
    assert!(
        code.contains("match clean_obj_tag(_x0)"),
        "match in init missing, got:\n{}",
        code
    );
}

#[test]
fn test_emit_join_point_recursive() {
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(2), IRType::UInt64)],
        body: Box::new(IRBody::VDecl {
            var: var(3),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(1)),
            rest: Box::new(IRBody::Jmp {
                jp: jp(0),
                args: vec![IRArg::Var(var(3))],
            }),
        }),
        rest: Box::new(IRBody::Jmp {
            jp: jp(0),
            args: vec![IRArg::Var(var(0))],
        }),
    };

    let decl = IRDecl {
        name: name("jp_recursive"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("break '_jp0_init;"),
        "break init missing, got:\n{}",
        code
    );
    assert!(
        code.contains("continue '_jp0;"),
        "continue loop missing, got:\n{}",
        code
    );
    assert!(
        code.contains("let mut _x2: u64 = 0u64;"),
        "mutable u64 param slot missing, got:\n{}",
        code
    );
}

#[test]
fn test_emit_nested_join_points() {
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(3), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(var(3)))),
        rest: Box::new(IRBody::JDecl {
            jp: jp(1),
            params: vec![(var(4), IRType::Object)],
            body: Box::new(IRBody::Jmp {
                jp: jp(0),
                args: vec![IRArg::Var(var(4))],
            }),
            rest: Box::new(IRBody::Jmp {
                jp: jp(1),
                args: vec![IRArg::Var(var(0))],
            }),
        }),
    };

    let decl = IRDecl {
        name: name("nested_jp"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("let mut _x3: *mut CleanObj = std::ptr::null_mut();"),
        "jp0 param slot missing, got:\n{}",
        code
    );
    assert!(
        code.contains("let mut _x4: *mut CleanObj = std::ptr::null_mut();"),
        "jp1 param slot missing, got:\n{}",
        code
    );
    assert!(
        code.contains("'_jp0_init: {"),
        "jp0 init label missing, got:\n{}",
        code
    );
    assert!(
        code.contains("'_jp1_init: {"),
        "jp1 init label missing, got:\n{}",
        code
    );
    assert!(
        code.contains("'_jp0: loop {"),
        "jp0 loop label missing, got:\n{}",
        code
    );
    assert!(
        code.contains("'_jp1: loop {"),
        "jp1 loop label missing, got:\n{}",
        code
    );
    assert!(
        code.contains("break '_jp0_init;"),
        "cross-JP break missing, got:\n{}",
        code
    );
}

// ── IR checker integration ─────────────────────────────────────────

#[test]
fn test_ir_checker_integration_valid() {
    let decl = IRDecl {
        name: name("valid"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };

    let config = RustEmitConfig {
        check_ir: true,
        ..Default::default()
    };
    let code = emit_rust_with_config(&[decl], config)
        .expect("IR checker should accept valid IR and emit Rust code");
    assert!(
        code.contains("pub unsafe fn l_valid"),
        "emitted Rust should include the validated function signature, got:\n{}",
        code
    );
}

#[test]
fn test_ir_checker_integration_invalid() {
    let decl = IRDecl {
        name: name("invalid"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };

    let config = RustEmitConfig {
        check_ir: true,
        ..Default::default()
    };
    let result = emit_rust_with_config(&[decl], config);
    assert!(result.is_err(), "should reject undefined variable");

    match result {
        Err(IRError::UndefinedVariable(_)) => {}
        other => panic!("Expected UndefinedVariable error, got {:?}", other),
    }
}

#[test]
fn test_ir_checker_disabled() {
    let decl = IRDecl {
        name: name("unchecked"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_rust_with_config(&[decl], config)
        .expect("IR emission should proceed when checker is disabled");
    assert!(
        code.contains("l_unchecked("),
        "unchecked IR should still emit a function definition, got:\n{}",
        code
    );
}

// ── Header emission ────────────────────────────────────────────────

#[test]
fn test_emit_header() {
    let mut emitter = RustEmitter::new();
    emitter.emit_header();
    let code = emitter.finish();
    assert!(
        code.contains("// Generated by clean compiler"),
        "header comment missing"
    );
    assert!(
        code.contains("use clean_runtime::*;"),
        "runtime import missing"
    );
}

// ── Expression emission ────────────────────────────────────────────

#[test]
fn test_emit_nullary_ctor() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: CtorInfo {
                name: name("Bool.true"),
                tag: 1,
                num_scalars: 0,
                num_objects: 0,
                field_types: vec![],
            },
            args: vec![],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("mk_true"),
        params: vec![],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_box(1)"),
        "nullary ctor should use clean_box, got:\n{}",
        code
    );
}

#[test]
fn test_emit_erased_arg() {
    let body = IRBody::Ret(IRArg::Erased);

    let decl = IRDecl {
        name: name("erased"),
        params: vec![],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("return clean_box(0);"),
        "erased should emit clean_box(0), got:\n{}",
        code
    );
}

#[test]
fn test_emit_string_literal() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: IRExpr::String("hello".to_string()),
        rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
    };

    let decl = IRDecl {
        name: name("mk_str"),
        params: vec![],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_mk_string(\"hello\")"),
        "string literal missing, got:\n{}",
        code
    );
}

// ── Multi-decl emission ────────────────────────────────────────────

#[test]
fn test_emit_multiple_decls() {
    let decls = vec![
        IRDecl {
            name: name("f"),
            params: vec![(var(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::Ret(IRArg::Var(var(0))),
        },
        IRDecl {
            name: name("g"),
            params: vec![(var(0), IRType::UInt64)],
            return_type: IRType::UInt64,
            body: IRBody::Ret(IRArg::Var(var(0))),
        },
    ];

    let code = emit_rust(&decls).unwrap();
    assert!(
        code.contains("pub unsafe fn l_f("),
        "first function missing, got:\n{}",
        code
    );
    assert!(
        code.contains("pub unsafe fn l_g("),
        "second function missing, got:\n{}",
        code
    );
}

// ── Box/Unbox type dispatch ─────────────────────────────────────────

#[test]
fn test_emit_unbox_float64() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Float64,
        value: IRExpr::Unbox {
            ty: IRType::Float64,
            arg: IRArg::Var(var(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("unbox_f64"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Float64,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_unbox_float(_x0)"),
        "Float64 unbox should use clean_unbox_float, got:\n{}",
        code
    );
}

#[test]
fn test_emit_unbox_uint64() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Unbox {
            ty: IRType::UInt64,
            arg: IRArg::Var(var(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("unbox_u64"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt64,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_unbox_uint64(_x0)"),
        "UInt64 unbox should use clean_unbox_uint64, got:\n{}",
        code
    );
}

#[test]
fn test_emit_unbox_uint32() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt32,
        value: IRExpr::Unbox {
            ty: IRType::UInt32,
            arg: IRArg::Var(var(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("unbox_u32"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt32,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_unbox_uint32(_x0)"),
        "UInt32 unbox should use clean_unbox_uint32, got:\n{}",
        code
    );
}

#[test]
fn test_emit_unbox_small_type_uses_clean_unbox() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::USize,
        value: IRExpr::Unbox {
            ty: IRType::USize,
            arg: IRArg::Var(var(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("unbox_usize"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::USize,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_unbox(_x0)"),
        "USize unbox should use clean_unbox, got:\n{}",
        code
    );
    assert!(
        !code.contains("clean_unbox_float"),
        "USize should NOT use clean_unbox_float, got:\n{}",
        code
    );
}

// ── No-param function ──────────────────────────────────────────────

#[test]
fn test_emit_no_params() {
    let decl = IRDecl {
        name: name("unit"),
        params: vec![],
        return_type: IRType::Void,
        body: IRBody::Ret(IRArg::Erased),
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("pub unsafe fn l_unit() -> ()"),
        "no-param signature should have empty parens, got:\n{}",
        code
    );
}

// ── PartialApply arity emission ──────────────────────────────────

#[test]
fn test_partial_apply_emits_total_arity_not_args_len() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: FnId(name("f")),
            arity: 3,
            args: vec![IRArg::Var(var(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_pap"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code =
        emit_rust_with_config(&[decl], config).expect("PartialApply emission should succeed");
    assert!(
        code.contains("clean_alloc_closure(l_f as *const (), 3, &[_x0])"),
        "PartialApply should emit (fn, arity=3, &[captured_args]). Got:\n{}",
        code
    );
}

// ── Float special value emission ─────────────────────────────────
// NOTE: ClosureApply emission tests are in tests/closure_apply_tests.rs (integration tests).

#[test]
fn test_emit_float_nan_produces_valid_rust() {
    let emitter = RustEmitter::new();
    assert_eq!(
        emitter.emit_literal(&IRLiteral::Float64(f64::NAN)),
        "f64::NAN"
    );
    assert_eq!(
        emitter.emit_literal(&IRLiteral::Float32(f32::NAN)),
        "f32::NAN"
    );
}

#[test]
fn test_emit_float_infinity_produces_valid_rust() {
    let emitter = RustEmitter::new();
    assert_eq!(
        emitter.emit_literal(&IRLiteral::Float64(f64::INFINITY)),
        "f64::INFINITY"
    );
    assert_eq!(
        emitter.emit_literal(&IRLiteral::Float64(f64::NEG_INFINITY)),
        "f64::NEG_INFINITY"
    );
    assert_eq!(
        emitter.emit_literal(&IRLiteral::Float32(f32::INFINITY)),
        "f32::INFINITY"
    );
    assert_eq!(
        emitter.emit_literal(&IRLiteral::Float32(f32::NEG_INFINITY)),
        "f32::NEG_INFINITY"
    );
}

#[test]
fn test_emit_float_normal_values_unchanged() {
    let emitter = RustEmitter::new();
    assert_eq!(emitter.emit_literal(&IRLiteral::Float64(1.23)), "1.23f64");
    assert_eq!(emitter.emit_literal(&IRLiteral::Float32(2.5)), "2.5f32");
}

// ── Reuse/Ctor emission tests moved to tests/ctor_reuse.rs ──────────
