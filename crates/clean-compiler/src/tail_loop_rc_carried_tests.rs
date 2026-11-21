// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R5's back-edge renaming on its own: exclusivity a loop parameter carries
//! into the next iteration survives that iteration's rebinding of the
//! variable that made the object.

use super::*;

/// A loop whose parameter `p` (10) carries the object an earlier iteration
/// made: on `t = 1` it binds `x := mk()` (12), probes it (when `probe`),
/// releases `p` and jumps back with `x` as `p` and `t := 0`; on `t = 0` it
/// binds a NEW `x := mk()` and only then steals field 0 of `p` and refills
/// it. The engine names an object by the variable that bound it, so unless
/// the back edge renames `p`'s object to `p`, that object is still named
/// `x`, and the second binding of `x` forgets its exclusivity.
fn carried_exclusive_loop(probe: bool) -> IRDecl {
    let lit = |n: u32, value: u8, rest: IRBody| {
        vdecl(n, IRType::UInt8, IRExpr::Lit(IRLiteral::UInt8(value)), rest)
    };
    let jmp = |args: Vec<IRArg>| IRBody::Jmp {
        jp: crate::ir::JoinPointId(0),
        args,
    };
    // t = 0: steal field 0 of p, with no probe in this iteration, and refill it.
    let steal = vdecl(
        15,
        IRType::Object,
        IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: var(10),
        },
        dec(
            15,
            vdecl(
                16,
                IRType::Object,
                apply("mk", vec![]),
                IRBody::Set {
                    var: v(10),
                    idx: 0,
                    value: v(16),
                    rest: Box::new(dec(12, ret(10))),
                },
            ),
        ),
    );
    // t = 1: release p and jump back with x as p.
    let back = dec(10, lit(14, 0, jmp(vec![var(12), var(14)])));
    let first = if probe {
        vdecl(
            13,
            IRType::UInt8,
            IRExpr::IsShared(v(12)),
            case2(13, "Bool", back, dec(12, ret(10))),
        )
    } else {
        back
    };
    let loop_body = vdecl(
        12,
        IRType::Object,
        apply("mk", vec![]),
        case2(11, "Bool", steal, first),
    );
    decl(
        "carried",
        vec![(0, IRType::Object)],
        IRType::Object,
        lit(
            1,
            1,
            IRBody::JDecl {
                jp: crate::ir::JoinPointId(0),
                params: vec![(v(10), IRType::Object), (v(11), IRType::UInt8)],
                body: Box::new(loop_body),
                rest: Box::new(jmp(vec![var(0), var(1)])),
            },
        ),
    )
}

#[test]
fn test_rc_linearity_keeps_a_carried_parameters_exclusivity_across_a_rebinding() {
    verify_rc_linearity(&[carried_exclusive_loop(true)])
        .expect("p's object was probed in the iteration that made it and is not shared since");
}

#[test]
fn test_rc_linearity_refuses_the_carried_steal_without_a_probe() {
    // Control: without the earlier iteration's probe the same steal is
    // refused, so the acceptance above rests on the carried exclusivity.
    let err = verify_rc_linearity(&[carried_exclusive_loop(false)])
        .expect_err("p's object was never probed");
    let text = err.to_string();
    assert!(text.contains("carried"), "{text}");
}
