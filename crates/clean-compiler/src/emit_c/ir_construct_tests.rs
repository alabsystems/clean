// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for IR construct emission: UProj, SProj, IsShared, SetTag, USet, SSet,
//! and typed Proj emission (verifying W2-139 emitter output).

use crate::emit_c::*;
use crate::ir::{CtorInfo, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
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

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("UProj emission should succeed");
    assert!(
        code.contains("clean_ctor_get_usize(_x0, 2)"),
        "UProj should emit clean_ctor_get_usize(var, idx). Got:\n{}",
        code
    );
}

#[test]
fn test_sproj_emits_typed_scalar_getter() {
    // SProj with UInt64: clean_ctor_get_uint64(var, sizeof(void*)*n + offset)
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

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("SProj emission should succeed");
    assert!(
        code.contains("clean_ctor_get_uint64(_x0, sizeof(void*)*1 + 4)"),
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

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("SProj UInt8 emission should succeed");
    assert!(
        code.contains("clean_ctor_get_uint8(_x0, sizeof(void*)*0 + 3)"),
        "SProj(UInt8) should use clean_ctor_get_uint8. Got:\n{}",
        code
    );
}

#[test]
fn test_sproj_float64_emits_float_getter() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Float64,
        value: IRExpr::SProj {
            n: 2,
            offset: 0,
            var: var(0),
            ty: IRType::Float64,
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_sproj_f64"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Float64,
        body,
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("SProj Float64 emission should succeed");
    assert!(
        code.contains("clean_ctor_get_float(_x0, sizeof(void*)*2 + 0)"),
        "SProj(Float64) should use clean_ctor_get_float. Got:\n{}",
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

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("IsShared emission should succeed");
    assert!(
        code.contains("!clean_is_exclusive(_x0)"),
        "IsShared should emit !clean_is_exclusive(var). Got:\n{}",
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

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("SetTag emission should succeed");
    assert!(
        code.contains("clean_ctor_set_tag(_x0, 3);"),
        "SetTag should emit clean_ctor_set_tag(var, tag). Got:\n{}",
        code
    );
}

#[test]
fn test_uset_emits_ctor_set_usize() {
    // USet: store USize value at position idx in object
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

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("USet emission should succeed");
    assert!(
        code.contains("clean_ctor_set_usize(_x0, 5, _x1);"),
        "USet should emit clean_ctor_set_usize(var, idx, value). Got:\n{}",
        code
    );
}

#[test]
fn test_sset_emits_typed_scalar_setter() {
    // SSet with UInt32: clean_ctor_set_uint32(var, sizeof(void*)*n + offset, value)
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

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("SSet emission should succeed");
    assert!(
        code.contains("clean_ctor_set_uint32(_x0, sizeof(void*)*1 + 2, _x1);"),
        "SSet(UInt32) should emit typed setter with byte offset. Got:\n{}",
        code
    );
}

#[test]
fn test_sset_float64_emits_float_setter() {
    let body = IRBody::SSet {
        var: var(0),
        n: 0,
        offset: 0,
        value: var(1),
        ty: IRType::Float64,
        rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
    };

    let decl = IRDecl {
        name: name("test_sset_f64"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Float64)],
        return_type: IRType::Object,
        body,
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("SSet Float64 emission should succeed");
    assert!(
        code.contains("clean_ctor_set_float(_x0, sizeof(void*)*0 + 0, _x1);"),
        "SSet(Float64) should use clean_ctor_set_float. Got:\n{}",
        code
    );
}

// ── End-to-end Proj typed emission (verifies W2-139 emitter output) ──

#[test]
fn test_proj_uint64_type_emits_typed_getter() {
    // When Proj has ty: UInt64 (from inductive_env lookup), the C emitter
    // should emit clean_ctor_get_uint64 instead of generic clean_ctor_get.
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

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("Proj typed emission should succeed");
    assert!(
        code.contains("clean_ctor_get_uint64(_x0, 0)"),
        "Proj with ty: UInt64 should emit clean_ctor_get_uint64, not clean_ctor_get. Got:\n{}",
        code
    );
    assert!(
        !code.contains("clean_ctor_get(_x0, 0)"),
        "Proj with ty: UInt64 should NOT emit generic clean_ctor_get. Got:\n{}",
        code
    );
}

// ── Reuse emission (Part of #1944 F3) ──────────────────────────

#[test]
fn test_reuse_emits_num_objs_parameter() {
    // Regression (#1944 F3): clean_reuse must pass num_objs so the fresh
    // allocation path allocates the correct number of fields.
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::Reuse {
            var: var(0),
            ctor: CtorInfo {
                name: name("Pair.mk"),
                tag: 0,
                num_scalars: 0,
                num_objects: 2,
                field_types: vec![IRType::Object, IRType::Object],
            },
            args: vec![IRArg::Var(var(1)), IRArg::Var(var(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
    };

    let decl = IRDecl {
        name: name("test_reuse"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("Reuse emission should succeed");
    assert!(
        code.contains("clean_reuse(_x0, 0, 2, 0, _x1, _x0)"),
        "Reuse should emit clean_reuse(slot, tag, num_objs, scalar_sz, args...). Got:\n{}",
        code
    );
}

#[test]
fn test_reuse_zero_fields_emits_num_objs_zero() {
    // Reuse with 0 fields (e.g., Nat.zero) should emit num_objs=0
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Reuse {
            var: var(0),
            ctor: CtorInfo {
                name: name("Nat.zero"),
                tag: 0,
                num_scalars: 0,
                num_objects: 0,
                field_types: vec![],
            },
            args: vec![],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_reuse_empty"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("Reuse empty emission should succeed");
    assert!(
        code.contains("clean_reuse(_x0, 0, 0, 0)"),
        "Reuse with 0 fields should emit clean_reuse(slot, tag, 0, 0). Got:\n{}",
        code
    );
}

#[test]
fn test_reuse_scalar_ctor_emits_scalar_size() {
    // Part of #1974: Reuse with scalar-bearing ctor must pass scalar_size
    // so the fresh-alloc fallback reserves scalar storage space.
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::Reuse {
            var: var(0),
            ctor: CtorInfo {
                name: name("WithUInt64.mk"),
                tag: 0,
                num_scalars: 1,
                num_objects: 1,
                field_types: vec![IRType::Object, IRType::UInt64],
            },
            args: vec![IRArg::Var(var(1))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
    };

    let decl = IRDecl {
        name: name("test_reuse_scalar"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code =
        emit_c_with_config(&[decl], config).expect("Reuse scalar ctor emission should succeed");
    // num_objects=1, scalar_size=8 (UInt64)
    assert!(
        code.contains("clean_reuse(_x0, 0, 1, 8, _x1)"),
        "Reuse with scalar ctor should emit scalar_size=8. Got:\n{}",
        code
    );
}

// Part of #1974: scalar-only Ctor (0 object args, nonzero scalar_size)
// must emit clean_alloc_ctor, not clean_box. W2-727 fixed the gate
// condition but this test verifies the emitted code is syntactically
// valid (no trailing comma from empty args list).
#[test]
fn test_ctor_scalar_only_emits_alloc_not_box() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: CtorInfo {
                name: name("PackedU64.mk"),
                tag: 0,
                num_scalars: 1,
                num_objects: 0,
                field_types: vec![IRType::UInt64],
            },
            args: vec![], // Scalar fields set via SSet, not passed as args
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    };

    let decl = IRDecl {
        name: name("test_scalar_only_ctor"),
        params: vec![],
        return_type: IRType::Object,
        body,
    };

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code =
        emit_c_with_config(&[decl], config).expect("Scalar-only Ctor emission should succeed");
    // Must NOT emit clean_box (tagged integer) — needs heap allocation
    // for scalar storage. Must emit clean_alloc_ctor with valid syntax.
    assert!(
        !code.contains("clean_box(0)"),
        "Scalar-only Ctor should NOT emit clean_box. Got:\n{}",
        code
    );
    assert!(
        code.contains("clean_alloc_ctor(0, 0, 8"),
        "Scalar-only Ctor should emit clean_alloc_ctor(tag, 0, 8...). Got:\n{}",
        code
    );
    // Verify no trailing comma before closing paren (C syntax error)
    assert!(
        !code.contains("clean_alloc_ctor(0, 0, 8, )"),
        "Scalar-only Ctor should not have trailing comma. Got:\n{}",
        code
    );
}

#[test]
fn test_proj_object_type_emits_generic_getter() {
    // Proj with ty: Object (default/fallback) should still emit clean_ctor_get.
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

    let config = CEmitConfig {
        check_ir: false,
        ..Default::default()
    };
    let code = emit_c_with_config(&[decl], config).expect("Proj Object emission should succeed");
    assert!(
        code.contains("clean_ctor_get(_x0, 2)"),
        "Proj with ty: Object should emit generic clean_ctor_get. Got:\n{}",
        code
    );
}
