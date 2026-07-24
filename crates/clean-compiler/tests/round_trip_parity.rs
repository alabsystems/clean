// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Level 1: Structural parity tests for C and Rust emitters.
//!
//! Feeds the same IRDecl to both `emit_c` and `emit_rust`, then verifies
//! that both contain the expected structural elements. Catches missing
//! cases, wrong runtime function names, and wrong argument counts.
//!
//! Part of #1978, Part of #1340

mod test_helpers;

use clean_compiler::emit_c::emit_c;
use clean_compiler::emit_rust::emit_rust;
use clean_compiler::ir::{FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId};
use test_helpers::{arg, assert_both_contain, mixed_ctor, name, obj_ctor, simple_fn, var};

/// Helper: emit both C and Rust from the same decl.
fn emit_both(decl: &IRDecl) -> (String, String) {
    let c = emit_c(std::slice::from_ref(decl)).unwrap();
    let r = emit_rust(std::slice::from_ref(decl)).unwrap();
    (c, r)
}

// ════════════════════════════════════════════════════════════════════════════
// Test 1: Ctor (no scalars) — allocation + tag
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_ctor_no_scalars() {
    // let r = Ctor(tag=2, obj_fields=[x0, x1])
    let decl = simple_fn(
        "parity.ctor.noscalar",
        &[(0, IRType::Object), (1, IRType::Object)],
        IRType::Object,
        10,
        IRExpr::Ctor {
            info: obj_ctor(2, 2),
            args: vec![arg(0), arg(1)],
        },
    );

    let (c, r) = emit_both(&decl);

    // Both must emit alloc_ctor with tag=2, num_objs=2, scalar_sz=0
    assert_both_contain(&c, &r, "clean_alloc_ctor(2, 2, 0");
}

// ════════════════════════════════════════════════════════════════════════════
// Test 2: Ctor (with scalars) — scalar_size in allocation
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_ctor_with_scalars() {
    // Ctor with 1 object + 1 UInt32 scalar field → scalar_size = 4
    let info = mixed_ctor(3, 1, &[IRType::UInt32]);
    let decl = simple_fn(
        "parity.ctor.scalar",
        &[(0, IRType::Object)],
        IRType::Object,
        10,
        IRExpr::Ctor {
            info,
            args: vec![arg(0)],
        },
    );

    let (c, r) = emit_both(&decl);

    // Both: alloc_ctor(tag=3, num_objs=1, scalar_sz=4, args...)
    assert_both_contain(&c, &r, "clean_alloc_ctor(3, 1, 4");
}

// ════════════════════════════════════════════════════════════════════════════
// Test 3: Proj (object field) — clean_ctor_get
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_proj_object() {
    // let r = Proj(obj, idx=1, ty=Object)
    let decl = simple_fn(
        "parity.proj.obj",
        &[(0, IRType::Object)],
        IRType::Object,
        10,
        IRExpr::Proj {
            idx: 1,
            ty: IRType::Object,
            arg: arg(0),
        },
    );

    let (c, r) = emit_both(&decl);

    assert_both_contain(&c, &r, "clean_ctor_get(_x0, 1)");
}

// ════════════════════════════════════════════════════════════════════════════
// Test 4: Proj (scalar field) — typed getter with byte offset
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_proj_scalar() {
    // Proj on UInt32 field at idx=0 → calls clean_ctor_get_uint32
    let decl = simple_fn(
        "parity.proj.scalar",
        &[(0, IRType::Object)],
        IRType::UInt32,
        10,
        IRExpr::Proj {
            idx: 0,
            ty: IRType::UInt32,
            arg: arg(0),
        },
    );

    let (c, r) = emit_both(&decl);

    assert_both_contain(&c, &r, "clean_ctor_get_uint32(_x0, 0)");
}

// ════════════════════════════════════════════════════════════════════════════
// Test 5: Apply (direct function call) — function name + args
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_apply() {
    // let r = Apply(fn=callee, args=[x0, x1])
    let decl = simple_fn(
        "parity.apply",
        &[(0, IRType::Object), (1, IRType::Object)],
        IRType::Object,
        10,
        IRExpr::Apply {
            fn_id: FnId(name("callee")),
            args: vec![arg(0), arg(1)],
        },
    );

    let (c, r) = emit_both(&decl);

    // Both emit: l_callee(_x0, _x1) (mangled name + args)
    assert_both_contain(&c, &r, "l_callee(_x0, _x1)");
}

// ════════════════════════════════════════════════════════════════════════════
// Test 6: PartialApply — closure allocation
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_partial_apply() {
    // let r = PartialApply(fn=target, arity=3, captured=[x0])
    let decl = simple_fn(
        "parity.papply",
        &[(0, IRType::Object)],
        IRType::Object,
        10,
        IRExpr::PartialApply {
            fn_id: FnId(name("target")),
            arity: 3,
            args: vec![arg(0)],
        },
    );

    let (c, r) = emit_both(&decl);

    // C: clean_alloc_closure((void*)l_target, 3, 1, _x0)
    assert!(
        c.contains("clean_alloc_closure((void*)l_target, 3, 1, _x0)"),
        "C emitter partial apply mismatch:\n{}",
        c
    );
    // Rust: clean_alloc_closure(l_target as *const (), 3, &[_x0])
    assert!(
        r.contains("clean_alloc_closure(l_target as *const (), 3, &[_x0])"),
        "Rust emitter partial apply mismatch:\n{}",
        r
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Test 7: ClosureApply — closure invocation
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_closure_apply() {
    // let r = ClosureApply(closure=x0, args=[x1, x2])
    let decl = simple_fn(
        "parity.capply",
        &[
            (0, IRType::Object),
            (1, IRType::Object),
            (2, IRType::Object),
        ],
        IRType::Object,
        10,
        IRExpr::ClosureApply {
            closure: arg(0),
            args: vec![arg(1), arg(2)],
        },
    );

    let (c, r) = emit_both(&decl);

    // C: clean_apply_2(_x0, _x1, _x2) (arity-dispatched)
    assert!(
        c.contains("clean_apply_2(_x0, _x1, _x2)"),
        "C emitter closure apply mismatch:\n{}",
        c
    );
    // Rust: clean_closure_apply(_x0, &[_x1, _x2]) (slice-based)
    assert!(
        r.contains("clean_closure_apply(_x0, &[_x1, _x2])"),
        "Rust emitter closure apply mismatch:\n{}",
        r
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Test 8: Box/Unbox (UInt32) — typed box/unbox functions
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_box_unbox() {
    // Two VDecls: box then unbox
    let decl = IRDecl {
        name: name("parity.box"),
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

    let (c, r) = emit_both(&decl);

    assert_both_contain(&c, &r, "clean_box_uint32(_x0)");
    assert_both_contain(&c, &r, "clean_unbox_uint32(_x10)");
}

// ════════════════════════════════════════════════════════════════════════════
// Test 9: Reuse — reuse slot with tag + scalar_size
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_reuse() {
    // let slot = Reset(x0); let r = Reuse(slot, ctor, [x1])
    let ctor = obj_ctor(5, 1);
    let decl = IRDecl {
        name: name("parity.reuse"),
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
                    ctor,
                    args: vec![arg(1)],
                },
                rest: Box::new(IRBody::Ret(arg(11))),
            }),
        },
    };

    let (c, r) = emit_both(&decl);

    // Both emit clean_reset
    assert_both_contain(&c, &r, "clean_reset(_x0)");

    // C: clean_reuse(_x10, 5, 1, 0, _x1)
    // Rust: clean_reuse(_x10, 5, 0, &[_x1])
    assert!(
        c.contains("clean_reuse(_x10, 5, 1, 0, _x1)"),
        "C emitter reuse mismatch:\n{}",
        c
    );
    assert!(
        r.contains("clean_reuse(_x10, 5, 0, &[_x1])"),
        "Rust emitter reuse mismatch:\n{}",
        r
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Test 10: Inc/Dec — reference counting
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_inc_dec() {
    // Inc(x0, n=1); Inc(x1, n=3); Dec(x0); return x1
    let decl = IRDecl {
        name: name("parity.rc"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::Inc {
                var: var(1),
                n: 3,
                rest: Box::new(IRBody::Dec {
                    var: var(0),
                    rest: Box::new(IRBody::Ret(arg(1))),
                }),
            }),
        },
    };

    let (c, r) = emit_both(&decl);

    assert_both_contain(&c, &r, "clean_inc(_x0)");
    assert_both_contain(&c, &r, "clean_inc_n(_x1, 3)");
    assert_both_contain(&c, &r, "clean_dec(_x0)");
}

// ════════════════════════════════════════════════════════════════════════════
// Test 11: JoinPoint — join point declaration + jump
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_join_point() {
    // JDecl jp0(p0: Object) { return p0 }; rest: Jmp jp0([x0])
    let decl = IRDecl {
        name: name("parity.jp"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![(var(10), IRType::Object)],
            body: Box::new(IRBody::Ret(arg(10))),
            rest: Box::new(IRBody::Jmp {
                jp: JoinPointId(0),
                args: vec![arg(0)],
            }),
        },
    };

    let (c, r) = emit_both(&decl);

    // C uses goto labels, Rust uses labeled blocks/loops.
    // C: goto _jp0; ... _jp0: ... return _x10;
    assert!(c.contains("goto _jp0"), "C missing goto:\n{}", c);
    assert!(c.contains("_jp0:"), "C missing label:\n{}", c);

    // Rust: '_jp0_init: { ... } followed by '_jp0: loop { ... return _x10; }
    assert!(
        r.contains("'_jp0_init:"),
        "Rust missing JP init label:\n{}",
        r
    );
    assert!(
        r.contains("'_jp0: loop"),
        "Rust missing JP loop label:\n{}",
        r
    );
    assert!(r.contains("return _x10"), "Rust missing return:\n{}", r);
}

// ════════════════════════════════════════════════════════════════════════════
// Test 12: Cases (2-way switch) — tag dispatch + branches
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_cases() {
    // Case(x0) { tag 0 → return x1; tag 1 → return x2 }
    let decl = IRDecl {
        name: name("parity.case"),
        params: vec![
            (var(0), IRType::Object),
            (var(1), IRType::Object),
            (var(2), IRType::Object),
        ],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: obj_ctor(0, 0),
                    body: Box::new(IRBody::Ret(arg(1))),
                },
                IRAlt {
                    ctor: obj_ctor(1, 0),
                    body: Box::new(IRBody::Ret(arg(2))),
                },
            ],
            default: None,
        },
    };

    let (c, r) = emit_both(&decl);

    // Both dispatch on tag
    assert_both_contain(&c, &r, "clean_obj_tag(_x0)");

    // C uses switch/case, Rust uses match
    assert!(c.contains("switch"), "C missing switch:\n{}", c);
    assert!(c.contains("case 0:"), "C missing case 0:\n{}", c);
    assert!(c.contains("case 1:"), "C missing case 1:\n{}", c);

    assert!(r.contains("match"), "Rust missing match:\n{}", r);
    assert!(r.contains("0 =>"), "Rust missing arm 0:\n{}", r);
    assert!(r.contains("1 =>"), "Rust missing arm 1:\n{}", r);

    // Both branches return correct vars
    assert_both_contain(&c, &r, "return _x1");
    assert_both_contain(&c, &r, "return _x2");
}

// ════════════════════════════════════════════════════════════════════════════
// Test 15: JDecl + Jmp with parameters — variable declarations + assignments
// Part of #2040
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parity_join_point_with_params() {
    // JDecl with one Object param (_x2), body returns that param.
    // Jmp passes _x1 as the argument.
    let decl = IRDecl {
        name: name("jp.params"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![(var(2), IRType::Object)],
            body: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
            rest: Box::new(IRBody::Jmp {
                jp: JoinPointId(0),
                args: vec![arg(1)],
            }),
        },
    };

    let (c, _r) = emit_both(&decl);

    // C must declare the join point parameter variable
    assert!(
        c.contains("clean_obj* _x2;"),
        "C emitter must declare join point param _x2:\n{}",
        c
    );
    // C Jmp must assign to the declared VarId, not _jp0_arg0
    assert!(
        c.contains("_x2 = _x1;"),
        "C emitter Jmp must assign to _x2 (not _jp0_arg0):\n{}",
        c
    );
    assert!(
        !c.contains("_jp0_arg0"),
        "C emitter should not use _jp0_arg0 naming:\n{}",
        c
    );
}
