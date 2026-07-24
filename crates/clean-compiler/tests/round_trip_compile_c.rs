// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Level 2: Compilation validation tests for the C emitter.
//!
//! Emits C code from IR declarations, writes to a temp file, and
//! invokes `cc` to verify the output compiles against the real
//! `clean_runtime.h` header. Catches type errors, missing declarations,
//! and ABI mismatches that string-matching tests can't detect.
//!
//! Feature-gated behind `round-trip-compile` so default `cargo test` is
//! not blocked by `cc` availability.
//!
//! Part of #2005 Phase 4 (end-to-end verification)

#![cfg(feature = "round-trip-compile")]

mod test_helpers;

use clean_compiler::emit_c::emit_c;
use clean_compiler::ir::{FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId};
use test_helpers::{arg, mixed_ctor, name, obj_ctor, var};

/// Path to clean_runtime.h include directory, relative to clean-compiler crate root.
fn runtime_include_dir() -> std::path::PathBuf {
    let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest.join("../clean-runtime/include")
}

/// Compile emitted C code against the real clean_runtime.h.
///
/// Uses `cc -c` (compile only, no link) since we don't have the runtime .c
/// compiled as a library. This validates that every function the emitter
/// calls is declared in the header with compatible types.
fn assert_c_compiles_with(decl: &IRDecl, extra_decls: &[IRDecl]) {
    let mut all_decls = extra_decls.to_vec();
    all_decls.push(decl.clone());
    let emitted = emit_c(&all_decls).unwrap();

    let dir = tempfile::tempdir().expect("failed to create temp dir");
    let src_path = dir.path().join("test_emit.c");
    std::fs::write(&src_path, &emitted).expect("failed to write temp file");

    let include_dir = runtime_include_dir();
    assert!(
        include_dir.join("clean_runtime.h").exists(),
        "clean_runtime.h not found at {:?}",
        include_dir
    );

    let output = std::process::Command::new("cc")
        .args([
            "-c",
            "-std=c11",
            "-Wall",
            "-Werror",
            "-Wno-unused-parameter",
        ])
        .arg(format!("-I{}", include_dir.display()))
        .arg("-o")
        .arg(dir.path().join("test_emit.o"))
        .arg(&src_path)
        .output()
        .expect("cc not found — is a C compiler installed?");

    assert!(
        output.status.success(),
        "cc failed for decl '{}':\nstderr: {}\n\n---emitted code---\n{}",
        decl.name,
        String::from_utf8_lossy(&output.stderr),
        emitted,
    );
}

fn assert_c_compiles(decl: &IRDecl) {
    assert_c_compiles_with(decl, &[]);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 1: Simple return — identity function
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_simple_return() {
    let decl = IRDecl {
        name: name("id"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(arg(0)),
    };
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 2: Proj + Tag + Box chain
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_proj_tag_box() {
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
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 3: Box + Unbox round-trip for each scalar type
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_box_unbox_uint32() {
    let decl = IRDecl {
        name: name("compile.boxunbox.u32"),
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
    assert_c_compiles(&decl);
}

#[test]
fn test_c_compile_box_unbox_uint64() {
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
    assert_c_compiles(&decl);
}

#[test]
fn test_c_compile_box_unbox_float64() {
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
    assert_c_compiles(&decl);
}

#[test]
fn test_c_compile_box_unbox_float32() {
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
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 4: Inc/Dec + Case + Apply
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_rc_case_apply() {
    // Forward-declare callee function
    let callee = IRDecl {
        name: name("callee"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(arg(0)),
    };

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
                default: Some(Box::new(IRBody::Ret(arg(1)))),
            }),
        },
    };
    assert_c_compiles_with(&decl, &[callee]);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 5: Constructor allocation with object fields
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_ctor_alloc() {
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
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 6: Typed scalar Proj (SProj) — validates clean_ctor_get_* type compat
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_sproj_all_scalar_types() {
    // SProj emits clean_ctor_get_uint8/16/32/64/float/float32 with byte offset.
    // This test verifies all getter return types match the C header declarations.
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
                    n: 1, // 1 object field before scalar region
                    offset: 0,
                    var: var(0),
                    ty: ty.clone(),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(result_var)))),
            },
        };
        assert_c_compiles(&decl);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Test 7: UProj — validates clean_ctor_get_usize return type
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_uproj() {
    let decl = IRDecl {
        name: name("compile.uproj"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::USize,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::USize,
            value: IRExpr::UProj {
                idx: 2, // slot index >= num_objs
                var: var(0),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(10)))),
        },
    };
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 8: IsShared — validates clean_is_exclusive signature
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_is_shared() {
    let decl = IRDecl {
        name: name("compile.isshared"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt8, // Bool maps to uint8_t in C
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Bool,
            value: IRExpr::IsShared(var(0)),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(10)))),
        },
    };
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 9: SetTag — validates clean_ctor_set_tag signature
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_set_tag() {
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
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 10: USet — validates clean_ctor_set_usize signature
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_uset() {
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
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 11: SSet — validates typed scalar setter signatures
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_sset_uint32() {
    let decl = IRDecl {
        name: name("compile.sset.u32"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::UInt32)],
        return_type: IRType::Object,
        body: IRBody::SSet {
            var: var(0),
            n: 1, // 1 object field before scalar region
            offset: 0,
            value: var(1),
            ty: IRType::UInt32,
            rest: Box::new(IRBody::Ret(arg(0))),
        },
    };
    assert_c_compiles(&decl);
}

#[test]
fn test_c_compile_sset_float64() {
    let decl = IRDecl {
        name: name("compile.sset.f64"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Float64)],
        return_type: IRType::Object,
        body: IRBody::SSet {
            var: var(0),
            n: 0, // 0 object fields (all-scalar ctor)
            offset: 0,
            value: var(1),
            ty: IRType::Float64,
            rest: Box::new(IRBody::Ret(arg(0))),
        },
    };
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 12: PartialApply — validates clean_alloc_closure signature
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_partial_apply() {
    // Forward-declare the target function
    let target = IRDecl {
        name: name("target.fn"),
        params: vec![
            (var(0), IRType::Object),
            (var(1), IRType::Object),
            (var(2), IRType::Object),
        ],
        return_type: IRType::Object,
        body: IRBody::Ret(arg(0)),
    };

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
    assert_c_compiles_with(&decl, &[target]);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 13: ClosureApply — validates clean_apply_N signatures
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_closure_apply_1() {
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
    assert_c_compiles(&decl);
}

#[test]
fn test_c_compile_closure_apply_0() {
    // Thunk forcing: apply_0
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
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 14: Reset/Reuse — validates clean_reset and clean_reuse signatures
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_reset_reuse() {
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
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 15: String literal — validates clean_mk_string signature
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_string_literal() {
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
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 16: Mixed ctor with scalar fields + SSet + SProj round-trip
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_scalar_ctor_write_read() {
    // Allocate a ctor with 1 object field + 1 uint64 scalar,
    // write the scalar via SSet, read it back via SProj.
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
                n: 1,      // 1 object field before scalar region
                offset: 0, // first scalar at offset 0 within scalar region
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
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 17: Reuse with scalar fields — validates scalar_sz propagation
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_reuse_with_scalars() {
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
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 18: Scalar-only ctor (0 object fields) — validates alloc_ctor(tag,0,sz)
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_scalar_only_ctor() {
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
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 19: ClosureApply with 10 args — validates clean_apply_10 specialized dispatch
// (runtime supports 1..=16; this was upgraded from varargs to positional in #1959)
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_closure_apply_large_arity() {
    // 10 args: within 1..=16 specialized range, emits clean_apply_10.
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
    assert_c_compiles(&decl);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 20: JDecl + Jmp (no params) — validates goto label mechanism
//
// The parameterless case tests the goto/label mechanism.
// JDecl with params is tested in round_trip_parity (test_parity_join_point_with_params).
// Part of #2040.
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_c_compile_join_point_no_params() {
    // Parameterless join point: JDecl body returns a function parameter
    // directly (no join point params to bind). Tests goto/label in C.
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
    assert_c_compiles(&decl);
}
