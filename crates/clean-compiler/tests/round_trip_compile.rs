// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Level 2: Compilation validation tests for the Rust emitter.
//!
//! Emits Rust code from IR declarations, writes to a temp file, and
//! invokes `rustc` to verify the output compiles. Catches syntax errors,
//! missing imports, and type mismatches that string-matching can't detect.
//!
//! Feature-gated behind `round-trip-compile` so default `cargo test` is
//! not blocked by `rustc` availability.
//!
//! Part of #1978, Part of #1340

#![cfg(feature = "round-trip-compile")]

mod test_helpers;

use clean_compiler::emit_rust::emit_rust;
use clean_compiler::ir::{FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId};
use test_helpers::{arg, mixed_ctor, name, obj_ctor, var};

/// Runtime stubs with signatures matching the real clean-runtime crate.
/// These validate type correctness of emitted code against the actual API.
/// Prepended to emitted code so `rustc` can resolve all symbols.
/// See clean-runtime/src/runtime/public_api.rs and src/lib.rs for the real implementations.
const RUNTIME_STUBS: &str = r#"
#![allow(unused_variables, unused_assignments, unreachable_code, dead_code, non_snake_case, unused_unsafe)]

#[repr(C)]
pub struct CleanObj { _opaque: [u8; 0] }

pub type LeanObjPtr = *mut CleanObj;

pub unsafe fn clean_alloc_ctor(tag: u8, _num_objs: u8, scalar_sz: u8, fields: &[*mut CleanObj]) -> *mut CleanObj { core::ptr::null_mut() }
pub unsafe fn clean_box(n: usize) -> *mut CleanObj { core::ptr::null_mut() }
pub unsafe fn clean_ctor_get(obj: *mut CleanObj, idx: usize) -> *mut CleanObj { core::ptr::null_mut() }
pub unsafe fn clean_ctor_get_uint8(obj: *mut CleanObj, offset: usize) -> u8 { 0 }
pub unsafe fn clean_ctor_get_uint16(obj: *mut CleanObj, offset: usize) -> u16 { 0 }
pub unsafe fn clean_ctor_get_uint32(obj: *mut CleanObj, offset: usize) -> u32 { 0 }
pub unsafe fn clean_ctor_get_uint64(obj: *mut CleanObj, offset: usize) -> u64 { 0 }
pub unsafe fn clean_ctor_get_usize(obj: *mut CleanObj, idx: usize) -> usize { 0 }
pub unsafe fn clean_ctor_get_float(obj: *mut CleanObj, offset: usize) -> f64 { 0.0 }
pub unsafe fn clean_ctor_get_float32(obj: *mut CleanObj, offset: usize) -> f32 { 0.0 }
pub unsafe fn clean_ctor_set(obj: *mut CleanObj, idx: usize, val: *mut CleanObj) {}
pub unsafe fn clean_ctor_set_tag(obj: *mut CleanObj, new_tag: u8) {}
pub unsafe fn clean_ctor_set_uint8(obj: *mut CleanObj, offset: usize, val: u8) {}
pub unsafe fn clean_ctor_set_uint16(obj: *mut CleanObj, offset: usize, val: u16) {}
pub unsafe fn clean_ctor_set_uint32(obj: *mut CleanObj, offset: usize, val: u32) {}
pub unsafe fn clean_ctor_set_uint64(obj: *mut CleanObj, offset: usize, val: u64) {}
pub unsafe fn clean_ctor_set_usize(obj: *mut CleanObj, idx: usize, val: usize) {}
pub unsafe fn clean_ctor_set_float(obj: *mut CleanObj, offset: usize, val: f64) {}
pub unsafe fn clean_ctor_set_float32(obj: *mut CleanObj, offset: usize, val: f32) {}
pub unsafe fn clean_obj_tag(obj: *mut CleanObj) -> u8 { 0 }
pub unsafe fn clean_box_uint32(val: u32) -> *mut CleanObj { core::ptr::null_mut() }
pub unsafe fn clean_box_uint64(val: u64) -> *mut CleanObj { core::ptr::null_mut() }
pub unsafe fn clean_box_float(val: f64) -> *mut CleanObj { core::ptr::null_mut() }
pub unsafe fn clean_unbox(obj: *mut CleanObj) -> usize { 0 }
pub unsafe fn clean_unbox_uint32(obj: *mut CleanObj) -> u32 { 0 }
pub unsafe fn clean_unbox_uint64(obj: *mut CleanObj) -> u64 { 0 }
pub unsafe fn clean_unbox_float(obj: *mut CleanObj) -> f64 { 0.0 }
pub unsafe fn clean_inc(obj: *mut CleanObj) {}
pub unsafe fn clean_inc_n(obj: *mut CleanObj, n: u32) {}
pub unsafe fn clean_dec(obj: *mut CleanObj) {}
pub unsafe fn clean_is_exclusive(obj: *mut CleanObj) -> bool { true }
pub unsafe fn clean_reset(obj: *mut CleanObj) -> *mut CleanObj { core::ptr::null_mut() }
pub unsafe fn clean_reuse(slot: *mut CleanObj, tag: u8, scalar_sz: u8, fields: &[*mut CleanObj]) -> *mut CleanObj { core::ptr::null_mut() }
pub unsafe fn clean_alloc_closure(fp: *const (), arity: u16, args: &[*mut CleanObj]) -> *mut CleanObj { core::ptr::null_mut() }
pub unsafe fn clean_closure_apply(closure: *mut CleanObj, args: &[*mut CleanObj]) -> *mut CleanObj { core::ptr::null_mut() }
pub unsafe fn clean_mk_string(s: &str) -> *mut CleanObj { core::ptr::null_mut() }
pub unsafe fn clean_panic(msg: &str) -> ! { core::hint::unreachable_unchecked() }
"#;

/// Compile emitted Rust code by substituting our stubs for the
/// `use clean_runtime::*;` import. Optional `extra_stubs` are appended
/// after the runtime stubs (e.g., forward declarations for called functions).
fn assert_rust_compiles_with(decl: &IRDecl, extra_stubs: &str) {
    let emitted = emit_rust(std::slice::from_ref(decl)).unwrap();
    let stubs = format!("{}\n{}", RUNTIME_STUBS, extra_stubs);
    let code = emitted.replace("use clean_runtime::*;", &stubs);

    let dir = tempfile::tempdir().expect("failed to create temp dir");
    let src_path = dir.path().join("test_emit.rs");
    std::fs::write(&src_path, &code).expect("failed to write temp file");

    let output = std::process::Command::new("rustc")
        .args(["--edition", "2021", "--crate-type", "lib"])
        .arg("--out-dir")
        .arg(dir.path())
        .arg(&src_path)
        .output()
        .expect("rustc not found — is Rust installed?");

    assert!(
        output.status.success(),
        "rustc failed for decl '{}':\nstdout: {}\nstderr: {}\n\n---emitted code---\n{}",
        decl.name,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
        code,
    );
}

fn assert_rust_compiles(decl: &IRDecl) {
    assert_rust_compiles_with(decl, "");
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 1: Proj + Tag + Box
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_proj_tag_box() {
    // Project field 0, get tag, box a scalar — no variadic alloc_ctor needed
    let decl = IRDecl {
        name: name("compile.projtagbox"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Proj {
                idx: 0,
                ty: IRType::Object,
                arg: arg(0),
            },
            rest: Box::new(IRBody::VDecl {
                var: var(11),
                ty: IRType::UInt32,
                value: IRExpr::Tag(arg(10)),
                rest: Box::new(IRBody::VDecl {
                    var: var(12),
                    ty: IRType::Object,
                    value: IRExpr::Box {
                        ty: IRType::UInt32,
                        arg: arg(11),
                    },
                    rest: Box::new(IRBody::Ret(arg(12))),
                }),
            }),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 2: Box + Unbox round-trip
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_box_unbox() {
    let decl = IRDecl {
        name: name("compile.boxunbox"),
        params: vec![(var(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::UInt32,
                arg: arg(0),
            },
            rest: Box::new(IRBody::VDecl {
                var: var(11),
                ty: IRType::UInt32,
                value: IRExpr::Unbox {
                    ty: IRType::UInt32,
                    arg: arg(10),
                },
                rest: Box::new(IRBody::Ret(arg(11))),
            }),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 3: Inc/Dec + Case + Apply
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_rc_case_apply() {
    // Inc x0; Case(x0) { 0 => Apply(callee, x0); 1 => Dec(x0); ret x1 }
    let decl = IRDecl {
        name: name("compile.rccase"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::Case {
                scrutinee: var(0),
                alts: vec![
                    IRAlt {
                        ctor: obj_ctor(0, 0),
                        body: Box::new(IRBody::VDecl {
                            var: var(10),
                            ty: IRType::Object,
                            value: IRExpr::Apply {
                                fn_id: FnId(name("callee")),
                                args: vec![arg(0)],
                            },
                            rest: Box::new(IRBody::Ret(arg(10))),
                        }),
                    },
                    IRAlt {
                        ctor: obj_ctor(1, 0),
                        body: Box::new(IRBody::Dec {
                            var: var(0),
                            rest: Box::new(IRBody::Ret(arg(1))),
                        }),
                    },
                ],
                default: None,
            }),
        },
    };
    assert_rust_compiles_with(
        &decl,
        "pub unsafe fn l_callee(_x0: *mut CleanObj) -> *mut CleanObj { core::ptr::null_mut() }",
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 4: Simple return (identity function)
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_simple_return() {
    let decl = IRDecl {
        name: name("compile.id"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(arg(0)),
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 5-7: Box + Unbox for remaining scalar types
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_box_unbox_uint64() {
    let decl = IRDecl {
        name: name("compile.boxunbox.u64"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::UInt64,
                arg: arg(0),
            },
            rest: Box::new(IRBody::VDecl {
                var: var(11),
                ty: IRType::UInt64,
                value: IRExpr::Unbox {
                    ty: IRType::UInt64,
                    arg: arg(10),
                },
                rest: Box::new(IRBody::Ret(arg(11))),
            }),
        },
    };
    assert_rust_compiles(&decl);
}

#[test]
fn test_compile_box_unbox_float64() {
    let decl = IRDecl {
        name: name("compile.boxunbox.f64"),
        params: vec![(var(0), IRType::Float64)],
        return_type: IRType::Float64,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::Float64,
                arg: arg(0),
            },
            rest: Box::new(IRBody::VDecl {
                var: var(11),
                ty: IRType::Float64,
                value: IRExpr::Unbox {
                    ty: IRType::Float64,
                    arg: arg(10),
                },
                rest: Box::new(IRBody::Ret(arg(11))),
            }),
        },
    };
    assert_rust_compiles(&decl);
}

#[test]
fn test_compile_box_unbox_float32() {
    let decl = IRDecl {
        name: name("compile.boxunbox.f32"),
        params: vec![(var(0), IRType::Float32)],
        return_type: IRType::Float32,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::Float32,
                arg: arg(0),
            },
            rest: Box::new(IRBody::VDecl {
                var: var(11),
                ty: IRType::Float32,
                value: IRExpr::Unbox {
                    ty: IRType::Float32,
                    arg: arg(10),
                },
                rest: Box::new(IRBody::Ret(arg(11))),
            }),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 8: Constructor allocation with object fields
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_ctor_alloc() {
    let decl = IRDecl {
        name: name("compile.ctor"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: obj_ctor(0, 2),
                args: vec![arg(0), arg(1)],
            },
            rest: Box::new(IRBody::Ret(arg(10))),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 9: SProj — typed scalar getter for each type
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_sproj_all_scalar_types() {
    let test_cases: &[(IRType, &str)] = &[
        (IRType::UInt8, "u8"),
        (IRType::UInt16, "u16"),
        (IRType::UInt32, "u32"),
        (IRType::UInt64, "u64"),
        (IRType::Float64, "f64"),
        (IRType::Float32, "f32"),
    ];

    for (i, (ty, suffix)) in test_cases.iter().enumerate() {
        let result_var = 10 + i as u32;
        let decl = IRDecl {
            name: name(&format!("compile.sproj.{}", suffix)),
            params: vec![(var(0), IRType::Object)],
            return_type: ty.clone(),
            body: IRBody::VDecl {
                var: var(result_var),
                ty: ty.clone(),
                value: IRExpr::SProj {
                    n: 1,
                    offset: 0,
                    var: var(0),
                    ty: ty.clone(),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(result_var)))),
            },
        };
        assert_rust_compiles(&decl);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 10: UProj — clean_ctor_get_usize
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_uproj() {
    let decl = IRDecl {
        name: name("compile.uproj"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::USize,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::USize,
            value: IRExpr::UProj {
                idx: 2,
                var: var(0),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(10)))),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 11: IsShared — clean_is_exclusive
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_is_shared() {
    let decl = IRDecl {
        name: name("compile.isshared"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt8,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Bool,
            value: IRExpr::IsShared(var(0)),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(10)))),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 12: SetTag — clean_ctor_set_tag
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_set_tag() {
    let decl = IRDecl {
        name: name("compile.settag"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::SetTag {
            var: var(0),
            tag: 3,
            rest: Box::new(IRBody::Ret(arg(0))),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 13: USet — clean_ctor_set_usize
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_uset() {
    let decl = IRDecl {
        name: name("compile.uset"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::USize)],
        return_type: IRType::Object,
        body: IRBody::USet {
            var: var(0),
            idx: 2,
            value: var(1),
            rest: Box::new(IRBody::Ret(arg(0))),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 14-15: SSet — typed scalar setters
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_sset_uint32() {
    let decl = IRDecl {
        name: name("compile.sset.u32"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::UInt32)],
        return_type: IRType::Object,
        body: IRBody::SSet {
            var: var(0),
            n: 1,
            offset: 0,
            value: var(1),
            ty: IRType::UInt32,
            rest: Box::new(IRBody::Ret(arg(0))),
        },
    };
    assert_rust_compiles(&decl);
}

#[test]
fn test_compile_sset_float64() {
    let decl = IRDecl {
        name: name("compile.sset.f64"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Float64)],
        return_type: IRType::Object,
        body: IRBody::SSet {
            var: var(0),
            n: 0,
            offset: 0,
            value: var(1),
            ty: IRType::Float64,
            rest: Box::new(IRBody::Ret(arg(0))),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 16: PartialApply — clean_alloc_closure
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_partial_apply() {
    let decl = IRDecl {
        name: name("compile.pap"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: FnId(name("target.fn")),
                arity: 3,
                args: vec![arg(0)],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(10)))),
        },
    };
    assert_rust_compiles_with(
        &decl,
        "pub unsafe fn l_target_fn(_x0: *mut CleanObj, _x1: *mut CleanObj, _x2: *mut CleanObj) -> *mut CleanObj { core::ptr::null_mut() }",
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 17-18: ClosureApply — 1 arg and 0 args
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_closure_apply_1() {
    let decl = IRDecl {
        name: name("compile.capply1"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: arg(0),
                args: vec![arg(1)],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(10)))),
        },
    };
    assert_rust_compiles(&decl);
}

#[test]
fn test_compile_closure_apply_0() {
    let decl = IRDecl {
        name: name("compile.capply0"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: arg(0),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(10)))),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 19: Reset/Reuse — clean_reset and clean_reuse
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_reset_reuse() {
    let decl = IRDecl {
        name: name("compile.resetreuse"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Reset(var(0)),
            rest: Box::new(IRBody::VDecl {
                var: var(11),
                ty: IRType::Object,
                value: IRExpr::Reuse {
                    var: var(10),
                    ctor: obj_ctor(0, 1),
                    args: vec![arg(1)],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(11)))),
            }),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 20: String literal — clean_mk_string
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_string_literal() {
    let decl = IRDecl {
        name: name("compile.mkstr"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::String("hello".to_string()),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(10)))),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 21: Mixed ctor + SSet + SProj round-trip
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_scalar_ctor_write_read() {
    let decl = IRDecl {
        name: name("compile.scalar.roundtrip"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: mixed_ctor(0, 1, &[IRType::UInt64]),
                args: vec![arg(0)],
            },
            rest: Box::new(IRBody::SSet {
                var: var(10),
                n: 1,
                offset: 0,
                value: var(1),
                ty: IRType::UInt64,
                rest: Box::new(IRBody::VDecl {
                    var: var(11),
                    ty: IRType::UInt64,
                    value: IRExpr::SProj {
                        n: 1,
                        offset: 0,
                        var: var(10),
                        ty: IRType::UInt64,
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(var(11)))),
                }),
            }),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 22: Reuse with scalar fields
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_reuse_with_scalars() {
    let decl = IRDecl {
        name: name("compile.reuse.scalar"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Reset(var(0)),
            rest: Box::new(IRBody::VDecl {
                var: var(11),
                ty: IRType::Object,
                value: IRExpr::Reuse {
                    var: var(10),
                    ctor: mixed_ctor(0, 1, &[IRType::UInt64]),
                    args: vec![arg(1)],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(11)))),
            }),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 23: Scalar-only ctor (0 object fields)
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_scalar_only_ctor() {
    let decl = IRDecl {
        name: name("compile.scalaronly"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: mixed_ctor(0, 0, &[IRType::UInt64]),
                args: vec![],
            },
            rest: Box::new(IRBody::SSet {
                var: var(10),
                n: 0,
                offset: 0,
                value: var(0),
                ty: IRType::UInt64,
                rest: Box::new(IRBody::Ret(IRArg::Var(var(10)))),
            }),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 24: ClosureApply with >8 args — clean_closure_apply slice
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_closure_apply_large_arity() {
    let args: Vec<IRArg> = (1..=10).map(|i| IRArg::Var(var(i))).collect();
    let params: Vec<(clean_compiler::ir::VarId, IRType)> =
        (0..=10).map(|i| (var(i), IRType::Object)).collect();

    let decl = IRDecl {
        name: name("compile.capply.large"),
        params,
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(20),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: arg(0),
                args,
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(20)))),
        },
    };
    assert_rust_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Compilation test 25: JDecl + Jmp (no params) — join point control flow
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_compile_join_point_no_params() {
    let decl = IRDecl {
        name: name("compile.joinpoint"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![],
            body: Box::new(IRBody::Ret(arg(1))),
            rest: Box::new(IRBody::Case {
                scrutinee: var(0),
                alts: vec![IRAlt {
                    ctor: obj_ctor(0, 0),
                    body: Box::new(IRBody::Jmp {
                        jp: JoinPointId(0),
                        args: vec![],
                    }),
                }],
                default: Some(Box::new(IRBody::Ret(arg(0)))),
            }),
        },
    };
    assert_rust_compiles(&decl);
}
