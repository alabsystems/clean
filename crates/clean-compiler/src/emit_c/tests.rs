// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#[path = "ir_construct_tests.rs"]
mod ir_construct_tests;

use super::*;
use crate::ir::{CtorInfo, IRAlt, IRBody};

fn var(n: u32) -> VarId {
    VarId(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

#[test]
fn test_emit_type() {
    let emitter = CEmitter::new();
    assert_eq!(emitter.emit_type(&IRType::UInt64), "uint64_t");
    assert_eq!(emitter.emit_type(&IRType::Object), "clean_obj*");
    assert_eq!(emitter.emit_type(&IRType::Bool), "uint8_t");
}

#[test]
fn test_emit_var() {
    let emitter = CEmitter::new();
    assert_eq!(emitter.emit_var(var(0)), "_x0");
    assert_eq!(emitter.emit_var(var(42)), "_x42");
}

#[test]
fn test_emit_literal() {
    let emitter = CEmitter::new();
    assert_eq!(emitter.emit_literal(&IRLiteral::UInt64(42)), "UINT64_C(42)");
    assert_eq!(emitter.emit_literal(&IRLiteral::Bool(true)), "1");
    assert_eq!(emitter.emit_literal(&IRLiteral::Bool(false)), "0");
}

#[test]
fn test_emit_simple_return() {
    let decl = IRDecl {
        name: name("id"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };

    let code = emit_c(&[decl]).unwrap();
    assert!(code.contains("clean_obj* l_id(clean_obj* _x0)"));
    assert!(code.contains("return _x0;"));
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

    let code = emit_c(&[decl]).unwrap();
    assert!(code.contains("clean_inc(_x0);"));
    assert!(code.contains("clean_dec(_x1);"));
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

    let code = emit_c(&[decl]).unwrap();
    assert!(code.contains("uint64_t _x1 = UINT64_C(42);"));
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

    let code = emit_c(&[decl]).unwrap();
    assert!(code.contains("switch (clean_obj_tag(_x0))"));
    assert!(code.contains("case 0:"));
    assert!(code.contains("case 1:"));
    // Verify break; is emitted after each case body to prevent C fall-through
    assert!(
        code.contains("break;"),
        "switch cases must emit break; to prevent fall-through: {}",
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

    let code = emit_c(&[decl]).unwrap();
    assert!(code.contains("l_Nat_add(_x0, _x0)"));
}

#[test]
fn test_ir_checker_integration_valid() {
    // Valid IR should pass the checker
    let decl = IRDecl {
        name: name("valid"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };

    let config = CEmitConfig {
        check_ir: true,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config)
        .expect("IR checker should accept valid IR and emit C code");
    assert!(
        code.contains("clean_obj* l_valid(clean_obj* _x0)"),
        "emitted C should include the validated function signature"
    );
    assert!(
        code.contains("return _x0;"),
        "emitted C should preserve function body"
    );
}

#[test]
fn test_ir_checker_integration_invalid() {
    // Invalid IR: using undefined variable x0 when no params
    let decl = IRDecl {
        name: name("invalid"),
        params: vec![], // No params!
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))), // x0 not defined
    };

    let config = CEmitConfig {
        check_ir: true,
        ..Default::default()
    };
    let result = emit_c_with_config(&[decl], config);
    // Should be UndefinedVariable error
    assert!(
        matches!(result, Err(IRError::UndefinedVariable(_))),
        "expected UndefinedVariable error, got: {result:?}"
    );
}

#[test]
fn test_emit_c_default_config_checks_ir() {
    let decl = IRDecl {
        name: name("invalid_default"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };

    let result = emit_c(&[decl]);
    assert!(result.is_err(), "emit_c should return Err for invalid IR");
    assert!(
        matches!(result, Err(IRError::UndefinedVariable(_))),
        "expected UndefinedVariable error, got: {result:?}",
    );
}

#[test]
fn test_ir_checker_disabled() {
    // With checker disabled, invalid IR should emit (but produce invalid C)
    let decl = IRDecl {
        name: name("unchecked"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config)
        .expect("IR emission should proceed when checker is disabled");
    assert!(
        code.contains("l_unchecked("),
        "unchecked IR should still emit a function definition"
    );
    assert!(
        code.contains("return _x0;"),
        "unchecked emission should preserve IR body even if it is invalid"
    );
}

#[test]
fn test_partial_apply_emits_total_arity_not_args_len() {
    // Regression test for #1924: PartialApply must emit the function's
    // total arity, not args.len() (the number of captured arguments).
    // f(a, b, c) partially applied as f(x) should produce arity=3.
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: FnId(name("f")),
            arity: 3,                       // total arity of f
            args: vec![IRArg::Var(var(0))], // 1 captured arg
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_pap"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("PartialApply emission should succeed");
    assert!(
        code.contains("clean_alloc_closure((void*)l_f, 3, 1, _x0)"),
        "PartialApply should emit (fn, arity=3, num_fixed=1, args). Got:\n{}",
        code
    );
}

#[test]
fn test_emit_float_nan_produces_valid_c() {
    let emitter = CEmitter::new();
    assert_eq!(emitter.emit_literal(&IRLiteral::Float64(f64::NAN)), "NAN");
    assert_eq!(
        emitter.emit_literal(&IRLiteral::Float32(f32::NAN)),
        "((float)NAN)"
    );
}

#[test]
fn test_emit_float_infinity_produces_valid_c() {
    let emitter = CEmitter::new();
    assert_eq!(
        emitter.emit_literal(&IRLiteral::Float64(f64::INFINITY)),
        "INFINITY"
    );
    assert_eq!(
        emitter.emit_literal(&IRLiteral::Float64(f64::NEG_INFINITY)),
        "(-INFINITY)"
    );
    assert_eq!(
        emitter.emit_literal(&IRLiteral::Float32(f32::INFINITY)),
        "((float)INFINITY)"
    );
    assert_eq!(
        emitter.emit_literal(&IRLiteral::Float32(f32::NEG_INFINITY)),
        "(-(float)INFINITY)"
    );
}

#[test]
fn test_emit_float_normal_values_unchanged() {
    let emitter = CEmitter::new();
    assert_eq!(emitter.emit_literal(&IRLiteral::Float64(1.23)), "1.23");
    assert_eq!(emitter.emit_literal(&IRLiteral::Float32(2.5)), "2.5f");
}

#[test]
fn test_emit_header_includes_math_h() {
    let mut emitter = CEmitter::new();
    emitter.emit_header();
    let code = emitter.finish();
    assert!(
        code.contains("#include <math.h>"),
        "Header should include math.h for NAN/INFINITY macros. Got:\n{}",
        code
    );
}

// ── ClosureApply boundary tests ─────────────────────────────────
// Runtime closure_apply.rs dispatches arities 1..=16. The compiler
// must emit positional clean_apply_N for n <= 16, falling back to
// clean_apply_n only above 16. Part of #1959.

#[test]
fn test_closure_apply_arity_9_uses_specialized() {
    // Arity 9 → clean_apply_9 (within 1..=16 runtime range)
    let args: Vec<IRArg> = (1..=9).map(|i| IRArg::Var(var(i))).collect();
    let params: Vec<(VarId, IRType)> = (0..=9).map(|i| (var(i), IRType::Object)).collect();

    let body = IRBody::VDecl {
        var: var(10),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(0)),
            args,
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(10)))),
    };

    let decl = IRDecl {
        name: name("test_ca_9"),
        params,
        return_type: IRType::Object,
        body,
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("ClosureApply emission should succeed");
    assert!(
        code.contains("clean_apply_9("),
        "ClosureApply with 9 args should use clean_apply_9. Got:\n{}",
        code
    );
    assert!(
        !code.contains("clean_apply_n("),
        "ClosureApply with 9 args should NOT use clean_apply_n. Got:\n{}",
        code
    );
}

#[test]
fn test_closure_apply_at_boundary_16_uses_specialized() {
    // Exactly 16 args → clean_apply_16 (max specialized boundary)
    let args: Vec<IRArg> = (1..=16).map(|i| IRArg::Var(var(i))).collect();
    let params: Vec<(VarId, IRType)> = (0..=16).map(|i| (var(i), IRType::Object)).collect();

    let body = IRBody::VDecl {
        var: var(17),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(0)),
            args,
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(17)))),
    };

    let decl = IRDecl {
        name: name("test_ca_16"),
        params,
        return_type: IRType::Object,
        body,
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("ClosureApply emission should succeed");
    assert!(
        code.contains("clean_apply_16("),
        "ClosureApply with exactly 16 args should use clean_apply_16. Got:\n{}",
        code
    );
    assert!(
        !code.contains("clean_apply_n("),
        "ClosureApply with 16 args should NOT use clean_apply_n. Got:\n{}",
        code
    );
}

#[test]
fn test_closure_apply_arity_17_uses_varargs() {
    // Arity 17 → clean_apply_n (exceeds 16-arity specialized range)
    let args: Vec<IRArg> = (1..=17).map(|i| IRArg::Var(var(i))).collect();
    let params: Vec<(VarId, IRType)> = (0..=17).map(|i| (var(i), IRType::Object)).collect();

    let body = IRBody::VDecl {
        var: var(18),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(0)),
            args,
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(18)))),
    };

    let decl = IRDecl {
        name: name("test_ca_17"),
        params,
        return_type: IRType::Object,
        body,
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("ClosureApply emission should succeed");
    assert!(
        code.contains("clean_apply_n(_x0, 17,"),
        "ClosureApply with 17 args should use clean_apply_n. Got:\n{}",
        code
    );
    assert!(
        !code.contains("clean_apply_17("),
        "ClosureApply with 17 args should NOT use clean_apply_17. Got:\n{}",
        code
    );
}

#[test]
fn test_closure_apply_zero_args_emits_apply_0() {
    // Zero args → clean_apply_0 (thunk forcing)
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(0)),
            args: vec![],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_ca_0"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("ClosureApply emission should succeed");
    assert!(
        code.contains("clean_apply_0(_x0)"),
        "ClosureApply with 0 args should emit clean_apply_0. Got:\n{}",
        code
    );
}

#[test]
fn test_closure_apply_with_erased_args_emits_box_zero() {
    // ClosureApply(closure=x0, args=[Erased]) → clean_apply_1(_x0, clean_box(0))
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(0)),
            args: vec![IRArg::Erased],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_ca_erased"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("ClosureApply emission should succeed");
    assert!(
        code.contains("clean_apply_1(_x0, clean_box(0))"),
        "Erased arg should emit clean_box(0). Got:\n{}",
        code
    );
}

// ── Box/Unbox type dispatch (Part of #1999) ──────────────────────────

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

    let code = emit_c(&[decl]).unwrap();
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

    let code = emit_c(&[decl]).unwrap();
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

    let code = emit_c(&[decl]).unwrap();
    assert!(
        code.contains("clean_unbox_uint32(_x0)"),
        "UInt32 unbox should use clean_unbox_uint32, got:\n{}",
        code
    );
}

#[test]
fn test_emit_unbox_usize_uses_clean_unbox_uint64() {
    // USize (64-bit) joins UInt64 on the tagged-or-heap `clean_unbox_uint64`
    // (parity with emit_trust_ir's `UInt64 | USize` arm) so the USize.ofNatLT
    // Nat-carrier decode is faithful; the old `_` fallthrough to tagged-only
    // `clean_unbox` read garbage off a heap-boxed carrier.
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

    let code = emit_c(&[decl]).unwrap();
    assert!(
        code.contains("clean_unbox_uint64(_x0)"),
        "USize unbox should use tagged-or-heap clean_unbox_uint64, got:\n{}",
        code
    );
    assert!(
        !code.contains("clean_unbox_float"),
        "USize should NOT use clean_unbox_float, got:\n{}",
        code
    );
}

// ── Float32 Box/Unbox/Proj dispatch (Part of #1966) ─────────────────

#[test]
fn test_emit_box_float32_widens_to_float64() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Box {
            ty: IRType::Float32,
            arg: IRArg::Var(var(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("box_f32"),
        params: vec![(var(0), IRType::Float32)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_c(&[decl]).unwrap();
    assert!(
        code.contains("clean_box_float((double)_x0)"),
        "Float32 box should widen to double via clean_box_float, got:\n{}",
        code
    );
    assert!(
        !code.contains("clean_box((size_t)"),
        "Float32 should NOT fall through to clean_box((size_t)...), got:\n{}",
        code
    );
}

#[test]
fn test_emit_unbox_float32_narrows_from_float64() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Float32,
        value: IRExpr::Unbox {
            ty: IRType::Float32,
            arg: IRArg::Var(var(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("unbox_f32"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Float32,
        body,
    };

    let code = emit_c(&[decl]).unwrap();
    assert!(
        code.contains("(float)clean_unbox_float(_x0)"),
        "Float32 unbox should narrow from clean_unbox_float, got:\n{}",
        code
    );
    assert!(
        !code.contains("clean_unbox(_x0)") || code.contains("clean_unbox_float(_x0)"),
        "Float32 should NOT fall through to generic clean_unbox, got:\n{}",
        code
    );
}

#[test]
fn test_emit_proj_float32_uses_typed_getter() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Float32,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::Float32,
            arg: IRArg::Var(var(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("proj_f32"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Float32,
        body,
    };

    let code = emit_c(&[decl]).unwrap();
    assert!(
        code.contains("clean_ctor_get_float32(_x0, 0)"),
        "Float32 proj should use clean_ctor_get_float32, got:\n{}",
        code
    );
    assert!(
        !code.contains("clean_ctor_get(_x0, 0)"),
        "Float32 should NOT fall through to generic clean_ctor_get, got:\n{}",
        code
    );
}

// ════════════════════════════════════════════════════════════════════
// FFI extern declaration emission
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_emit_extern_decls_with_bridge() {
    use crate::ffi_bridge::FfiBridge;

    let mut env = clean_kernel::Environment::new();
    let decl_name = Name::from_string("IO.Handle.mk");
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: decl_name.clone(),
        level_params: vec![],
        type_: clean_kernel::Expr::prop(),
    })
    .expect("should add axiom");
    env.register_extern(decl_name, "clean_io_handle_mk".to_owned());

    let bridge = FfiBridge::from_env(&env);

    let mut emitter = CEmitter::new();
    emitter.emit_header();
    emitter.emit_extern_decls(&bridge);

    let code = emitter.finish();
    assert!(
        code.contains("extern"),
        "should contain extern keyword, got:\n{}",
        code
    );
    assert!(
        code.contains("clean_io_handle_mk"),
        "should contain the C symbol name, got:\n{}",
        code
    );
    assert!(
        code.contains("IO.Handle.mk"),
        "should contain the Lean name in comment, got:\n{}",
        code
    );
}

#[test]
fn test_emit_extern_decls_empty_bridge_no_output() {
    use crate::ffi_bridge::FfiBridge;

    let env = clean_kernel::Environment::new();
    let bridge = FfiBridge::from_env(&env);

    let mut emitter = CEmitter::new();
    emitter.emit_extern_decls(&bridge);

    let code = emitter.finish();
    assert!(
        !code.contains("extern"),
        "empty bridge should not produce extern declarations, got:\n{}",
        code
    );
}
