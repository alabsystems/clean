// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ClosureApply proof_coverage tests.
//!
//! Tests for ClosureApply across IR checker, C emission, and to_ir lowering.
//! These cover code paths that had zero test coverage after ClosureApply was
//! added in W1-707 (#1936).
//!
//! Part of #1936, Re: #1945

use clean_compiler::emit_c::{emit_c, emit_c_with_config, CEmitConfig};
use clean_compiler::emit_rust::{emit_rust, emit_rust_with_config, RustEmitConfig};
use clean_compiler::ir::{IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_compiler::ir_checker::{check_decl, IRError};
use clean_kernel::Name;

fn var(n: u32) -> VarId {
    VarId(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

// ════════════════════════════════════════════════════════════════════════════
// IR Checker: ClosureApply validation
// ════════════════════════════════════════════════════════════════════════════

/// Part of #1936 - ClosureApply with valid args passes checker.
#[test]
fn test_valid_closure_apply() {
    // let result := ClosureApply(closure=x0, args=[x1])
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(var(0)),
                args: vec![IRArg::Var(var(1))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
        },
    };

    check_decl(&decl, &[]).expect("valid ClosureApply should pass checker");
}

/// Part of #1936 - ClosureApply with undefined closure var fails.
#[test]
fn test_closure_apply_undefined_closure() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(var(99)), // undefined
                args: vec![IRArg::Var(var(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(
        matches!(result, Err(IRError::UndefinedVariable(VarId(99)))),
        "Expected UndefinedVariable(99), got {:?}",
        result
    );
}

/// Part of #1936 - ClosureApply with undefined arg fails.
#[test]
fn test_closure_apply_undefined_arg() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(var(0)),
                args: vec![IRArg::Var(var(77))], // undefined
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(
        matches!(result, Err(IRError::UndefinedVariable(VarId(77)))),
        "Expected UndefinedVariable(77), got {:?}",
        result
    );
}

/// Part of #1936 - ClosureApply with zero args valid (thunk invocation).
#[test]
fn test_closure_apply_zero_args() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(var(0)),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };

    check_decl(&decl, &[]).expect("ClosureApply with 0 args should be valid");
}

// ════════════════════════════════════════════════════════════════════════════
// C Emission: ClosureApply dispatch
// ════════════════════════════════════════════════════════════════════════════

/// Part of #1936 - ClosureApply emits clean_apply_N for N<=8.
#[test]
fn test_emit_closure_apply_small() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(0)),
            args: vec![IRArg::Var(var(1))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
    };

    let decl = IRDecl {
        name: name("test_ca"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_c(&[decl]).unwrap();
    assert!(
        code.contains("clean_apply_1(_x0, _x1)"),
        "ClosureApply with 1 arg should emit clean_apply_1. Got:\n{}",
        code
    );
}

/// Part of #1936, Part of #1959 - ClosureApply with >16 args emits clean_apply_n varargs.
#[test]
fn test_emit_closure_apply_large() {
    // Arity 17 exceeds the runtime's 1..=16 specialized dispatch range.
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
        name: name("test_ca_large"),
        params,
        return_type: IRType::Object,
        body,
    };

    let code = emit_c(&[decl]).unwrap();
    assert!(
        code.contains("clean_apply_n(_x0, 17,"),
        "ClosureApply with 17 args should emit clean_apply_n. Got:\n{}",
        code
    );
}

/// Part of #1959 - ClosureApply with 9 args now uses specialized clean_apply_9.
#[test]
fn test_emit_closure_apply_arity_9_specialized() {
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
        name: name("test_ca_9_spec"),
        params,
        return_type: IRType::Object,
        body,
    };

    let code = emit_c(&[decl]).unwrap();
    assert!(
        code.contains("clean_apply_9("),
        "ClosureApply with 9 args should emit clean_apply_9. Got:\n{}",
        code
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Rust Emission: ClosureApply (P1-686 algorithm_audit)
// ════════════════════════════════════════════════════════════════════════════

/// Part of #1936 - ClosureApply emits clean_closure_apply with single arg.
#[test]
fn test_rust_emit_closure_apply_single_arg() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(0)),
            args: vec![IRArg::Var(var(1))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
    };

    let decl = IRDecl {
        name: name("test_ca"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_closure_apply(_x0, &[_x1])"),
        "ClosureApply with 1 arg should emit clean_closure_apply(closure, &[arg]). Got:\n{}",
        code
    );
}

/// Part of #1936 - ClosureApply emits comma-separated args in slice.
#[test]
fn test_rust_emit_closure_apply_multiple_args() {
    let body = IRBody::VDecl {
        var: var(4),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(0)),
            args: vec![IRArg::Var(var(1)), IRArg::Var(var(2)), IRArg::Var(var(3))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(4)))),
    };

    let decl = IRDecl {
        name: name("test_ca_multi"),
        params: vec![
            (var(0), IRType::Object),
            (var(1), IRType::Object),
            (var(2), IRType::Object),
            (var(3), IRType::Object),
        ],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_closure_apply(_x0, &[_x1, _x2, _x3])"),
        "ClosureApply with 3 args should emit comma-separated args in slice. Got:\n{}",
        code
    );
}

/// Part of #1936 - ClosureApply zero-arg (thunk forcing) emits empty slice.
#[test]
fn test_rust_emit_closure_apply_zero_args() {
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
        name: name("test_ca_zero"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_closure_apply(_x0, &[])"),
        "ClosureApply with 0 args should emit empty slice. Got:\n{}",
        code
    );
}

/// Part of #1936 - ClosureApply with erased arg emits clean_box(0).
#[test]
fn test_rust_emit_closure_apply_with_erased_args() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(0)),
            args: vec![IRArg::Erased, IRArg::Var(var(1))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
    };

    let decl = IRDecl {
        name: name("test_ca_erased"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_closure_apply(_x0, &[clean_box(0), _x1])"),
        "ClosureApply with erased arg should emit clean_box(0) for erased. Got:\n{}",
        code
    );
}

// =============================================================================
// Proj / UProj / IsShared type dispatch tests (P1-687 audit)
// Part of #1936 — verifies emitter output for typed field access.
// NOTE: scalar typed getters (clean_ctor_get_uint64 etc.) do NOT exist
// in the runtime yet — see P1-687 audit finding on #1936.
// =============================================================================

#[test]
fn test_proj_type_dispatch_emits_correct_c_getter() {
    let cases: Vec<(IRType, &str)> = vec![
        (IRType::Object, "clean_ctor_get("),
        (IRType::UInt8, "clean_ctor_get_uint8("),
        (IRType::UInt16, "clean_ctor_get_uint16("),
        (IRType::UInt32, "clean_ctor_get_uint32("),
        (IRType::UInt64, "clean_ctor_get_uint64("),
        (IRType::USize, "clean_ctor_get_usize("),
        (IRType::Float64, "clean_ctor_get_float("),
    ];

    for (ty, expected_fn) in &cases {
        // Use idx=3 (not 0) to verify the idx value propagates into output
        let decl = IRDecl {
            name: name("test_proj"),
            params: vec![(var(0), IRType::Object)],
            return_type: ty.clone(),
            body: IRBody::VDecl {
                var: var(1),
                ty: ty.clone(),
                value: IRExpr::Proj {
                    idx: 3,
                    ty: ty.clone(),
                    arg: IRArg::Var(var(0)),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            },
        };

        let config = CEmitConfig {
            check_ir: false,
            ..Default::default()
        };
        let code = emit_c_with_config(&[decl], config)
            .unwrap_or_else(|e| panic!("Proj({:?}) C emission failed: {}", ty, e));
        assert!(
            code.contains(expected_fn),
            "Proj({:?}) should emit {}. Got:\n{}",
            ty,
            expected_fn,
            code
        );
        // Verify idx=3 appears in the emitted getter call
        assert!(
            code.contains(&format!("{}_x0, 3)", expected_fn)),
            "Proj({:?}) should include idx=3 in output. Got:\n{}",
            ty,
            code
        );
    }
}

// Rust emitter parity: same Proj type dispatch as C emitter.
#[test]
fn test_proj_type_dispatch_emits_correct_rust_getter() {
    let cases: Vec<(IRType, &str)> = vec![
        (IRType::Object, "clean_ctor_get("),
        (IRType::UInt64, "clean_ctor_get_uint64("),
        (IRType::USize, "clean_ctor_get_usize("),
    ];

    for (ty, expected_fn) in &cases {
        let decl = IRDecl {
            name: name("test_proj"),
            params: vec![(var(0), IRType::Object)],
            return_type: ty.clone(),
            body: IRBody::VDecl {
                var: var(1),
                ty: ty.clone(),
                value: IRExpr::Proj {
                    idx: 2,
                    ty: ty.clone(),
                    arg: IRArg::Var(var(0)),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            },
        };

        let config = RustEmitConfig {
            check_ir: false,
            ..Default::default()
        };
        let code = emit_rust_with_config(&[decl], config)
            .unwrap_or_else(|e| panic!("Proj({:?}) Rust emission failed: {}", ty, e));
        assert!(
            code.contains(expected_fn),
            "Rust Proj({:?}) should emit {}. Got:\n{}",
            ty,
            expected_fn,
            code
        );
    }
}

// NOTE: UProj and IsShared tests deferred — these IRExpr variants exist in
// the working tree but are not committed yet. Add tests once Worker commits
// the UProj/SProj/IsShared production code. See P1-687 audit on #1936.
