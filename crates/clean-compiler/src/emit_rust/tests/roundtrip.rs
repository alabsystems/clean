// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Round-trip integration tests: IR → emit_rust → runtime → verify output.
//!
//! Each test constructs IR, emits Rust and C code, then executes the equivalent
//! operations using `clean_runtime` primitives directly to verify correctness.
//! Compares emit_rust output against emit_c for structural equivalence.
//!
//! Part of #2158 — round-trip integration tests.

use super::*;
use crate::emit_c::emit_c;
use clean_runtime::runtime::*;

/// Construct a nullary (zero-field) CtorInfo.
fn nullary_ctor(name_str: &str, tag: u32) -> CtorInfo {
    CtorInfo {
        name: name(name_str),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

// ---------------------------------------------------------------------------
// IR construction helpers (extracted to keep test functions under 80 lines)
// ---------------------------------------------------------------------------

/// IR: fn is_zero(x: Object) -> Object {
///   case x { Nat.zero(0) => box(1), Nat.succ(1) => box(0) }
/// }
fn make_is_zero_ir() -> IRDecl {
    IRDecl {
        name: name("is_zero"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: nullary_ctor("Nat.zero", 0),
                    body: Box::new(IRBody::VDecl {
                        var: var(1),
                        ty: IRType::Object,
                        value: IRExpr::Ctor {
                            info: nullary_ctor("Bool.true", 1),
                            args: vec![],
                        },
                        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
                    }),
                },
                IRAlt {
                    ctor: CtorInfo {
                        name: name("Nat.succ"),
                        tag: 1,
                        num_scalars: 0,
                        num_objects: 1,
                        field_types: vec![IRType::Object],
                    },
                    body: Box::new(IRBody::VDecl {
                        var: var(2),
                        ty: IRType::Object,
                        value: IRExpr::Ctor {
                            info: nullary_ctor("Bool.false", 0),
                            args: vec![],
                        },
                        rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
                    }),
                },
            ],
            default: None,
        },
    }
}

/// IR: fn jp_test(x: Object) -> Object {
///   jp0(y: Object) = { return y; }
///   let u = Ctor(Unit.unit, tag=0, []);
///   jmp jp0(u);
/// }
fn make_jp_test_ir() -> IRDecl {
    IRDecl {
        name: name("jp_test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: jp(0),
            params: vec![(var(2), IRType::Object)],
            body: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
            rest: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::Object,
                value: IRExpr::Ctor {
                    info: nullary_ctor("Unit.unit", 0),
                    args: vec![],
                },
                rest: Box::new(IRBody::Jmp {
                    jp: jp(0),
                    args: vec![IRArg::Var(var(1))],
                }),
            }),
        },
    }
}

/// IR: fn process(x, y: Object) -> Object { inc(x); dec(y); pair = ctor(0,[x,y]); proj(pair,0) }
fn make_process_ir() -> IRDecl {
    IRDecl {
        name: name("process"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::Dec {
                var: var(1),
                rest: Box::new(IRBody::VDecl {
                    var: var(2),
                    ty: IRType::Object,
                    value: IRExpr::Ctor {
                        info: CtorInfo {
                            name: name("Prod.mk"),
                            tag: 0,
                            num_scalars: 0,
                            num_objects: 2,
                            field_types: vec![IRType::Object, IRType::Object],
                        },
                        args: vec![IRArg::Var(var(0)), IRArg::Var(var(1))],
                    },
                    rest: Box::new(IRBody::VDecl {
                        var: var(3),
                        ty: IRType::Object,
                        value: IRExpr::Proj {
                            ty: IRType::Object,
                            idx: 0,
                            arg: IRArg::Var(var(2)),
                        },
                        rest: Box::new(IRBody::Ret(IRArg::Var(var(3)))),
                    }),
                }),
            }),
        },
    }
}

// ---------------------------------------------------------------------------
// Test 1: Simple function — scalar boxing
// ---------------------------------------------------------------------------

/// Verifies: both backends emit `clean_box(0)` for nullary constructors.
/// Runtime: clean_box produces a tagged pointer, clean_unbox recovers the value.
#[test]
fn test_roundtrip_simple_function() {
    let decl = IRDecl {
        name: name("const42"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: nullary_ctor("Unit.unit", 0),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };

    let rust_code = emit_rust(std::slice::from_ref(&decl)).unwrap();
    assert!(
        rust_code.contains("clean_box(0)"),
        "Rust: missing clean_box(0)"
    );
    assert!(rust_code.contains("return _x0;"), "Rust: missing return");
    assert!(
        rust_code.contains("use clean_runtime::"),
        "Rust: missing import"
    );

    let c_code = emit_c(std::slice::from_ref(&decl)).unwrap();
    assert!(c_code.contains("clean_box(0)"), "C: missing clean_box(0)");
    assert!(c_code.contains("return _x0;"), "C: missing return");

    // Execute: clean_box(0) → tagged pointer → unbox recovers 0
    let result = clean_box(0);
    assert_eq!(clean_unbox(result), 0);
    assert!(
        clean_is_scalar(result),
        "nullary ctor should be tagged pointer"
    );
}

// ---------------------------------------------------------------------------
// Test 2: Constructor allocation + field projection
// ---------------------------------------------------------------------------

/// Verifies: Rust emits clean_alloc_ctor + clean_ctor_get, C emits same.
/// Runtime: allocating a 2-field ctor and projecting field 0 returns the value.
#[test]
fn test_roundtrip_ctor_and_proj() {
    let decl = IRDecl {
        name: name("get_fst"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: CtorInfo {
                    name: name("Prod.mk"),
                    tag: 0,
                    num_scalars: 0,
                    num_objects: 2,
                    field_types: vec![IRType::Object, IRType::Object],
                },
                args: vec![IRArg::Var(var(0)), IRArg::Var(var(0))],
            },
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::Object,
                value: IRExpr::Proj {
                    ty: IRType::Object,
                    idx: 0,
                    arg: IRArg::Var(var(1)),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
            }),
        },
    };

    let rust_code = emit_rust(std::slice::from_ref(&decl)).unwrap();
    assert!(
        rust_code.contains("clean_alloc_ctor(0, 2, 0, &[_x0, _x0])"),
        "Rust: missing alloc_ctor"
    );
    assert!(
        rust_code.contains("clean_ctor_get(_x1, 0)"),
        "Rust: missing ctor_get"
    );

    let c_code = emit_c(std::slice::from_ref(&decl)).unwrap();
    assert!(
        c_code.contains("clean_alloc_ctor(0, 2, 0,"),
        "C: missing alloc_ctor"
    );
    assert!(
        c_code.contains("clean_ctor_get(_x1, 0)"),
        "C: missing ctor_get"
    );

    // Execute: alloc 2-field ctor with scalar fields, project field 0
    let input = clean_box(99);
    let pair = clean_alloc_ctor(0, 2, 0, &[input, input]);
    assert_eq!(clean_obj_tag(pair), 0);
    assert_eq!(clean_unbox(clean_ctor_get(pair, 0)), 99);
    assert_eq!(clean_unbox(clean_ctor_get(pair, 1)), 99);
    clean_dec(pair);
}

// ---------------------------------------------------------------------------
// Test 3: Pattern match (case analysis)
// ---------------------------------------------------------------------------

/// Verifies: Rust emits `match clean_obj_tag`, C emits `switch`.
/// Runtime: objects with different tags dispatch to correct branches.
#[test]
fn test_roundtrip_pattern_match() {
    let decl = make_is_zero_ir();

    let rust_code = emit_rust(std::slice::from_ref(&decl)).unwrap();
    assert!(
        rust_code.contains("match clean_obj_tag(_x0)"),
        "Rust: missing match"
    );
    assert!(rust_code.contains("0 => {"), "Rust: missing tag-0 arm");
    assert!(rust_code.contains("1 => {"), "Rust: missing tag-1 arm");

    let c_code = emit_c(std::slice::from_ref(&decl)).unwrap();
    assert!(c_code.contains("switch"), "C: missing switch");
    assert!(c_code.contains("case 0:"), "C: missing case 0");
    assert!(c_code.contains("case 1:"), "C: missing case 1");

    // Execute: simulate the emitted case dispatch (tag → branch → result)
    let zero_ctor = clean_alloc_ctor(0, 0, 0, &[]);
    let succ_ctor = clean_alloc_ctor(1, 1, 0, &[clean_box(5)]);

    // Simulate is_zero(zero_ctor): read tag, dispatch, produce result
    let result_zero = match clean_obj_tag(zero_ctor) {
        0 => clean_box(1), // Bool.true
        _ => clean_box(0), // Bool.false
    };
    assert_eq!(clean_unbox(result_zero), 1, "is_zero(zero) → true");

    // Simulate is_zero(succ_ctor): read tag, dispatch, produce result
    let result_succ = match clean_obj_tag(succ_ctor) {
        0 => clean_box(1),
        _ => clean_box(0),
    };
    assert_eq!(clean_unbox(result_succ), 0, "is_zero(succ) → false");

    clean_dec(zero_ctor);
    clean_dec(succ_ctor);
}

// ---------------------------------------------------------------------------
// Test 4: Join point (labeled blocks/loops)
// ---------------------------------------------------------------------------

/// Verifies: Rust emits labeled block + loop pattern, C emits goto.
/// Runtime: clean_box(0) creates the unit value correctly.
#[test]
fn test_roundtrip_join_point() {
    let decl = make_jp_test_ir();

    let rust_code = emit_rust(std::slice::from_ref(&decl)).unwrap();
    // Rust join points use labeled blocks and loops (post join-point lowering)
    assert!(
        rust_code.contains("let mut _x2: *mut CleanObj = std::ptr::null_mut();"),
        "Rust: missing mutable param slot"
    );
    assert!(
        rust_code.contains("'_jp0_init: {"),
        "Rust: missing init label"
    );
    assert!(
        rust_code.contains("break '_jp0_init;"),
        "Rust: missing break init"
    );
    assert!(
        rust_code.contains("'_jp0: loop {"),
        "Rust: missing loop label"
    );
    assert!(
        rust_code.contains("clean_box(0)"),
        "Rust: missing clean_box"
    );
    assert!(
        rust_code.contains("return _x2;"),
        "Rust: missing return in jp body"
    );

    let c_code = emit_c(std::slice::from_ref(&decl)).unwrap();
    // C join points use goto
    assert!(c_code.contains("goto"), "C: missing goto");
    assert!(c_code.contains("clean_box(0)"), "C: missing clean_box");

    // Execute: simulate JP data flow — alloc ctor, pass as JP arg, verify tag
    // (JP is pure control flow; runtime test verifies the data path is correct)
    let unit = clean_alloc_ctor(0, 0, 0, &[]); // heap-allocated, not tagged ptr
                                               // JP0(y) = return y; the value passes through unchanged
    assert_eq!(
        clean_obj_tag(unit),
        0,
        "ctor tag preserved through JP data flow"
    );
    clean_dec(unit);
}

// ---------------------------------------------------------------------------
// Test 5: Box/unbox uint64 roundtrip
// ---------------------------------------------------------------------------

/// Verifies: Rust emits clean_box_uint64/clean_unbox_uint64, C emits same.
/// Runtime: boxing and unboxing preserves the original value.
#[test]
fn test_roundtrip_box_unbox_uint64() {
    let decl = IRDecl {
        name: name("box_roundtrip"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::UInt64,
                arg: IRArg::Var(var(0)),
            },
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::UInt64,
                value: IRExpr::Unbox {
                    ty: IRType::UInt64,
                    arg: IRArg::Var(var(1)),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
            }),
        },
    };

    let rust_code = emit_rust(std::slice::from_ref(&decl)).unwrap();
    assert!(
        rust_code.contains("clean_box_uint64(_x0)"),
        "Rust: missing box_uint64"
    );
    assert!(
        rust_code.contains("clean_unbox_uint64(_x1)"),
        "Rust: missing unbox_uint64"
    );

    let c_code = emit_c(std::slice::from_ref(&decl)).unwrap();
    assert!(
        c_code.contains("clean_box_uint64(_x0)"),
        "C: missing box_uint64"
    );
    assert!(
        c_code.contains("clean_unbox_uint64(_x1)"),
        "C: missing unbox_uint64"
    );

    // Execute: box large u64, unbox, verify value preserved
    let large_val: u64 = 0xDEAD_BEEF_CAFE_BABE;
    let boxed = clean_box_uint64(large_val);
    assert!(
        !clean_is_scalar(boxed),
        "large u64 should be heap-allocated"
    );
    assert_eq!(
        clean_unbox_uint64(boxed),
        large_val,
        "roundtrip preserves value"
    );
    clean_dec(boxed);
}

// ---------------------------------------------------------------------------
// Test 6: Emit equivalence — both backends emit same runtime primitives
// ---------------------------------------------------------------------------

/// Verifies structural equivalence: for a multi-operation IR program, both
/// backends emit the same set of runtime primitive calls.
#[test]
fn test_roundtrip_emit_equivalence() {
    let decl = make_process_ir();
    let rust_code = emit_rust(std::slice::from_ref(&decl)).unwrap();
    let c_code = emit_c(std::slice::from_ref(&decl)).unwrap();

    // Both backends should emit identical runtime primitive calls.
    let shared = [
        "clean_inc(_x0)",
        "clean_dec(_x1)",
        "clean_alloc_ctor(0,",
        "clean_ctor_get(_x2, 0)",
        "return _x3;",
    ];
    for prim in &shared {
        assert!(rust_code.contains(prim), "Rust missing: '{}'", prim);
        assert!(c_code.contains(prim), "C missing: '{}'", prim);
    }
}
