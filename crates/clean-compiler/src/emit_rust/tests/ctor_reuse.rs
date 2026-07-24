// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Ctor/Reuse emission with scalar field handling (#1974).

use super::*;

#[test]
fn test_emit_reset_reuse() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Reset(var(0)),
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::Reuse {
                var: var(1),
                ctor: CtorInfo {
                    name: name("Nat.succ"),
                    tag: 1,
                    num_scalars: 0,
                    num_objects: 1,
                    field_types: vec![IRType::Object],
                },
                args: vec![IRArg::Var(var(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
        }),
    };
    let decl = IRDecl {
        name: name("reset_reuse"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };
    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_reset(_x0)"),
        "reset should emit clean_reset. Got:\n{}",
        code
    );
    assert!(
        code.contains("clean_reuse(_x1, 1, 0, &[_x0])"),
        "reuse should emit clean_reuse(slot, tag=1, scalar_sz=0, &[args]). Got:\n{}",
        code
    );
}

// Part of #1974 — Reuse with scalar fields must emit clean_reuse with
// correct scalar_size and all args in the slice.
#[test]
fn test_emit_reuse_with_scalar_fields() {
    // Reuse args only contain object-pointer fields; scalars are set via SSet.
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Reset(var(0)),
        rest: Box::new(IRBody::VDecl {
            var: var(4),
            ty: IRType::Object,
            value: IRExpr::Reuse {
                var: var(1),
                ctor: CtorInfo {
                    name: name("Pair.mk"),
                    tag: 0,
                    num_scalars: 1,
                    num_objects: 1,
                    field_types: vec![IRType::Object, IRType::UInt64],
                },
                args: vec![IRArg::Var(var(2))],
            },
            rest: Box::new(IRBody::SSet {
                var: var(4),
                n: 0,
                offset: 0,
                value: var(3),
                ty: IRType::UInt64,
                rest: Box::new(IRBody::Ret(IRArg::Var(var(4)))),
            }),
        }),
    };
    let decl = IRDecl {
        name: name("reuse_scalar"),
        params: vec![
            (var(0), IRType::Object),
            (var(2), IRType::Object),
            (var(3), IRType::UInt64),
        ],
        return_type: IRType::Object,
        body,
    };
    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_reuse(_x1, 0, 8, &[_x2])"),
        "Reuse with scalar must emit clean_reuse(slot, tag=0, scalar_sz=8, &[obj_args]). Got:\n{}",
        code
    );
}

// Part of #1974 — Ctor with scalar fields emits clean_alloc_ctor with
// num_objects and scalar_size parameters. Scalar args are set via SSet,
// not passed in the Ctor args (IR checker C3 rule).
#[test]
fn test_emit_ctor_with_scalar_fields() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: CtorInfo {
                name: name("Pair.mk"),
                tag: 0,
                num_scalars: 1,
                num_objects: 1,
                field_types: vec![IRType::Object, IRType::UInt64],
            },
            args: vec![IRArg::Var(var(0))],
        },
        rest: Box::new(IRBody::SSet {
            var: var(2),
            n: 0,
            offset: 0,
            value: var(1),
            ty: IRType::UInt64,
            rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
        }),
    };
    let decl = IRDecl {
        name: name("ctor_scalar"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::UInt64)],
        return_type: IRType::Object,
        body,
    };
    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_alloc_ctor(0, 1, 8, &[_x0])"),
        "Ctor with scalars must emit clean_alloc_ctor(tag=0, num_objs=1, scalar_sz=8, &[obj_args]). Got:\n{}",
        code
    );
    assert!(
        code.contains("clean_ctor_set_uint64("),
        "Scalar field must be set via SSet (clean_ctor_set_uint64). Got:\n{}",
        code
    );
}

// Fixed: Unbox now dispatches to clean_unbox_float() for Float64.
#[test]
fn test_emit_unbox_float64_correct_function() {
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
        code.contains("clean_unbox_float("),
        "Float64 Unbox should emit clean_unbox_float(). Got:\n{}",
        code
    );
}

// Fixed: Unbox now dispatches to clean_unbox_uint64() for UInt64.
#[test]
fn test_emit_unbox_uint64_correct_function() {
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
        code.contains("clean_unbox_uint64("),
        "UInt64 Unbox should emit clean_unbox_uint64(). Got:\n{}",
        code
    );
}

// Part of #1999 — Float32 Unbox dispatches to clean_unbox_float (widened to f64).
#[test]
fn test_emit_unbox_float32_correct_function() {
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
    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_unbox_float("),
        "Float32 Unbox should emit clean_unbox_float(). Got:\n{}",
        code
    );
}

// ── Reuse slice syntax (moved from tests.rs, self-audit #1944) ──────

#[test]
fn test_reuse_emits_slice_syntax() {
    // Rust emitter must emit clean_reuse(slot, tag, scalar_sz, &[fields...]).
    // Part of #1974, #1985: scalar_sz for correct allocation sizing.
    // Rust runtime derives num_objs from fields.len(); C uses explicit num_objs.
    let e = RustEmitter::new();
    let mk_reuse = |tag, args: Vec<IRArg>| IRExpr::Reuse {
        var: var(0),
        ctor: CtorInfo {
            name: name("C"),
            tag,
            num_scalars: 0,
            num_objects: args.len() as u32,
            field_types: args.iter().map(|_| IRType::Object).collect(),
        },
        args,
    };
    let r = e
        .emit_expr(&mk_reuse(0, vec![IRArg::Var(var(1)), IRArg::Var(var(0))]))
        .unwrap();
    assert_eq!(r, "clean_reuse(_x0, 0, 0, &[_x1, _x0])");
    let r = e.emit_expr(&mk_reuse(0, vec![])).unwrap();
    assert_eq!(r, "clean_reuse(_x0, 0, 0, &[])");
}

// Part of #1974: scalar-only Ctor must emit alloc_ctor without trailing comma.
#[test]
fn test_ctor_scalar_only_emits_alloc_not_box() {
    let e = RustEmitter::new();
    let ctor_expr = IRExpr::Ctor {
        info: CtorInfo {
            name: name("PackedU64.mk"),
            tag: 0,
            num_scalars: 1,
            num_objects: 0,
            field_types: vec![IRType::UInt64],
        },
        args: vec![], // Scalar fields set via SSet
    };
    let r = e.emit_expr(&ctor_expr).unwrap();
    assert!(
        !r.contains("clean_box("),
        "Scalar-only Ctor should NOT emit clean_box. Got: {r}"
    );
    assert_eq!(r, "clean_alloc_ctor(0, 0, 8, &[])");
}

// P1 performance_proofs #694 — Unbounded recursion in emit_body (both emitters).
#[test]
fn test_emit_body_recursive_depth_200_both_emitters() {
    use crate::emit_c::{emit_c_with_config, CEmitConfig};
    let depth = 200;
    let make_chain = || {
        let mut body = IRBody::Ret(IRArg::Var(var(0)));
        for i in 1..=depth {
            body = IRBody::VDecl {
                var: var(i),
                ty: IRType::UInt64,
                value: IRExpr::Lit(IRLiteral::UInt64(i as u64)),
                rest: Box::new(body),
            };
        }
        IRDecl {
            name: name("deep_fn"),
            params: vec![(var(0), IRType::UInt64)],
            return_type: IRType::UInt64,
            body,
        }
    };
    let rust_code = emit_rust(&[make_chain()]).unwrap();
    assert!(rust_code.contains("_x200"), "Rust: should emit 200 VDecls");
    assert!(rust_code.contains("return _x0"), "Rust: should return _x0");
    let c_config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let c_code = emit_c_with_config(&[make_chain()], c_config).unwrap();
    assert!(c_code.contains("_x200"), "C: should emit 200 VDecls");
}
