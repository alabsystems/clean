// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for IR construct emission: UProj, SProj, IsShared, SetTag, USet, SSet,
//! and typed Proj emission (verifying W2-139 env-aware field type lookup).

use crate::emit_rust::*;
use crate::ir::{IRBody, IRDecl};
use clean_kernel::Name;

fn var(n: u32) -> VarId {
    VarId(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

// ── UProj / SProj / IsShared expression emission ─────────────────

#[test]
fn test_uproj_emits_ctor_get_usize() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::USize,
        value: IRExpr::UProj {
            idx: 2,
            var: var(0),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_uproj"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::USize,
        body,
    };

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_rust_with_config(&[decl], config).expect("UProj emission should succeed");
    assert!(
        code.contains("clean_ctor_get_usize(_x0, 2)"),
        "UProj should emit clean_ctor_get_usize(var, idx). Got:\n{}",
        code
    );
}

#[test]
fn test_sproj_emits_typed_scalar_getter() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::SProj {
            n: 1,
            offset: 4,
            var: var(0),
            ty: IRType::UInt64,
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_sproj"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt64,
        body,
    };

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_rust_with_config(&[decl], config).expect("SProj emission should succeed");
    assert!(
        code.contains("clean_ctor_get_uint64(_x0, core::mem::size_of::<*const ()>() * 1 + 4)"),
        "SProj(UInt64) should emit typed getter with byte offset. Got:\n{}",
        code
    );
}

#[test]
fn test_sproj_uint8_emits_correct_getter() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt8,
        value: IRExpr::SProj {
            n: 0,
            offset: 3,
            var: var(0),
            ty: IRType::UInt8,
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_sproj_u8"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt8,
        body,
    };

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_rust_with_config(&[decl], config).expect("SProj UInt8 emission should succeed");
    assert!(
        code.contains("clean_ctor_get_uint8(_x0, core::mem::size_of::<*const ()>() * 0 + 3)"),
        "SProj(UInt8) should use clean_ctor_get_uint8. Got:\n{}",
        code
    );
}

#[test]
fn test_is_shared_emits_exclusive_check() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt8,
        value: IRExpr::IsShared(var(0)),
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_is_shared"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt8,
        body,
    };

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_rust_with_config(&[decl], config).expect("IsShared emission should succeed");
    assert!(
        code.contains("(!clean_is_exclusive(_x0)) as u8"),
        "IsShared should emit (!clean_is_exclusive(var)) as u8 (bool→u8 cast). Got:\n{}",
        code
    );
}

// ── Tag expression emission (VDecl context, not match scrutinee) ─

#[test]
fn test_tag_emits_obj_tag_with_u32_cast() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt32,
        value: IRExpr::Tag(IRArg::Var(var(0))),
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_tag"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt32,
        body,
    };

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_rust_with_config(&[decl], config).expect("Tag emission should succeed");
    assert!(
        code.contains("clean_obj_tag(_x0) as u32"),
        "Tag should emit clean_obj_tag(var) as u32 (u8→u32 cast). Got:\n{}",
        code
    );
}

// ── SetTag / USet / SSet body emission ───────────────────────────

#[test]
fn test_set_tag_emits_ctor_set_tag() {
    let body = IRBody::SetTag {
        var: var(0),
        tag: 3,
        rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
    };

    let decl = IRDecl {
        name: name("test_set_tag"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_rust_with_config(&[decl], config).expect("SetTag emission should succeed");
    assert!(
        code.contains("clean_ctor_set_tag(_x0, 3);"),
        "SetTag should emit clean_ctor_set_tag(var, tag). Got:\n{}",
        code
    );
}

#[test]
fn test_uset_emits_ctor_set_usize() {
    let body = IRBody::USet {
        var: var(0),
        idx: 5,
        value: var(1),
        rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
    };

    let decl = IRDecl {
        name: name("test_uset"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::USize)],
        return_type: IRType::Object,
        body,
    };

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_rust_with_config(&[decl], config).expect("USet emission should succeed");
    assert!(
        code.contains("clean_ctor_set_usize(_x0, 5, _x1);"),
        "USet should emit clean_ctor_set_usize(var, idx, value). Got:\n{}",
        code
    );
}

#[test]
fn test_sset_emits_typed_scalar_setter() {
    let body = IRBody::SSet {
        var: var(0),
        n: 1,
        offset: 2,
        value: var(1),
        ty: IRType::UInt32,
        rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
    };

    let decl = IRDecl {
        name: name("test_sset"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::UInt32)],
        return_type: IRType::Object,
        body,
    };

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_rust_with_config(&[decl], config).expect("SSet emission should succeed");
    assert!(
        code.contains(
            "clean_ctor_set_uint32(_x0, core::mem::size_of::<*const ()>() * 1 + 2, _x1);"
        ),
        "SSet(UInt32) should emit typed setter with byte offset. Got:\n{}",
        code
    );
}

// ── End-to-end Proj typed emission (verifies W2-139 emitter output) ──

#[test]
fn test_proj_uint64_type_emits_typed_getter() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::UInt64,
            arg: IRArg::Var(var(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_proj_typed"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt64,
        body,
    };

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_rust_with_config(&[decl], config).expect("Proj typed emission should succeed");
    assert!(
        code.contains("clean_ctor_get_uint64(_x0, 0)"),
        "Proj with ty: UInt64 should emit clean_ctor_get_uint64. Got:\n{}",
        code
    );
    assert!(
        !code.contains("clean_ctor_get(_x0, 0)"),
        "Proj with ty: UInt64 should NOT emit generic clean_ctor_get. Got:\n{}",
        code
    );
}

#[test]
fn test_proj_object_type_emits_generic_getter() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx: 2,
            ty: IRType::Object,
            arg: IRArg::Var(var(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_proj_obj"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_rust_with_config(&[decl], config).expect("Proj Object emission should succeed");
    assert!(
        code.contains("clean_ctor_get(_x0, 2)"),
        "Proj with ty: Object should emit generic clean_ctor_get. Got:\n{}",
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

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_box_float(_x0 as f64)"),
        "Float32 box should widen to f64 via clean_box_float, got:\n{}",
        code
    );
    assert!(
        !code.contains("clean_box(_x0 as usize)"),
        "Float32 should NOT fall through to clean_box(... as usize), got:\n{}",
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

    let code = emit_rust(&[decl]).unwrap();
    assert!(
        code.contains("clean_unbox_float(_x0) as f32"),
        "Float32 unbox should narrow from clean_unbox_float, got:\n{}",
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

    let config = RustEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code =
        emit_rust_with_config(&[decl], config).expect("Float32 Proj emission should succeed");
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
