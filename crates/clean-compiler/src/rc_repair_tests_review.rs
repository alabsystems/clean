// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.2 second review (adversarial): shapes the linearity verifier ACCEPTED
//! although they are not linear. Each was measured accepted before the fix
//! that names it; each has an honest twin that must stay accepted. Module
//! path: `rc_repair::tests::review`.

use super::*;

/// The fast-path steal, then the object ESCAPES while its field slot is
/// still taken: `a := g(y)` gave the old field object away, and the slot is
/// refilled only afterwards. Whoever receives `x` in between reads (and may
/// release) a field reference the frame no longer owns — a use after free.
/// Before the fix the escape was accepted whenever the frame still held a
/// second reference (`inc x` first), because the taken-slot check fired only
/// once the frame held NO reference to `x`.
fn escape_while_taken(escape: impl FnOnce(IRBody) -> IRBody) -> IRDecl {
    let fast = vdecl(
        3,
        IRType::Object,
        apply("g", vec![var(1)]),
        escape(set(0, 0, 3, IRBody::Ret(var(0)))),
    );
    fast_path_decl(|b| b, fast, IRBody::Unreachable)
}

#[test]
fn an_object_with_a_taken_slot_cannot_be_shared_by_inc() {
    // `inc x; b := h(x); dec b` between the steal and the refill.
    let d = escape_while_taken(|rest| {
        inc(
            0,
            vdecl(4, IRType::Object, apply("h", vec![var(0)]), dec(4, rest)),
        )
    });
    let msg = refusal(&[d]);
    assert!(
        msg.contains("RC linearity violation in f: object %0"),
        "{msg}"
    );
    assert!(msg.contains("field 0's reference was taken"), "{msg}");
}

#[test]
fn an_object_with_a_taken_slot_cannot_be_read_by_a_borrowing_callee() {
    // `r := hb(x)` with `hb`'s parameter BORROWED: no inc, no consumption,
    // yet `hb` reads `x` while field 0 points at a given-away object.
    let d = escape_while_taken(|rest| {
        vdecl(4, IRType::Object, apply("hb", vec![var(0)]), dec(4, rest))
    });
    let mut sigs = BorrowMap::new();
    sigs.insert(
        name("hb"),
        FnBorrow {
            params: vec![Ownership::Borrowed],
        },
    );
    let msg = verify_rc_linearity_with_borrows(std::slice::from_ref(&d), &sigs)
        .expect_err("a borrowing callee must not see a taken slot")
        .to_string();
    assert!(msg.contains("object %0"), "{msg}");
    assert!(msg.contains("field 0's reference was taken"), "{msg}");
}

#[test]
fn an_object_whose_taken_slot_was_refilled_may_escape() {
    // Honest twin: the SAME escape AFTER `set x[0] := a` is linear.
    let fast = vdecl(
        3,
        IRType::Object,
        apply("g", vec![var(1)]),
        set(
            0,
            0,
            3,
            inc(
                0,
                vdecl(
                    4,
                    IRType::Object,
                    apply("h", vec![var(0)]),
                    dec(4, IRBody::Ret(var(0))),
                ),
            ),
        ),
    );
    verify_rc_linearity(&[fast_path_decl(|b| b, fast, IRBody::Unreachable)])
        .expect("after the refill the object is whole and may be shared");
}

#[test]
fn rebinding_a_variable_that_still_holds_a_reference_is_refused() {
    // `b := box a; b := box a; u := unbox b; dec b; ret u` — the first
    // box's reference is overwritten, never released. Before the fix the
    // second binding silently replaced the first one's count.
    let d = decl(
        vec![(0, IRType::UInt64)],
        IRType::UInt64,
        vdecl(
            1,
            IRType::Object,
            box_u64(0),
            vdecl(
                1,
                IRType::Object,
                box_u64(0),
                vdecl(2, IRType::UInt64, unbox_u64(1), dec(1, IRBody::Ret(var(2)))),
            ),
        ),
    );
    let msg = refusal(&[d]);
    assert!(
        msg.contains("object %1 is consumed 0 times with 0 incs on path entry"),
        "{msg}"
    );
    assert!(msg.contains("rebound"), "{msg}");
}

#[test]
fn an_object_passed_to_a_scalar_join_point_parameter_is_refused() {
    // `jp k(p : UInt64) := ret p; b := box a; jmp k(b)` — the object's one
    // reference is handed to a parameter that carries no reference: a leak
    // (and a pointer read as an integer). Before the fix the move simply
    // dropped the reference.
    let jp = |arg_ty: IRType, arg: IRBody| IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(v(9), arg_ty)],
        body: Box::new(IRBody::Ret(var(9))),
        rest: Box::new(arg),
    };
    let d = decl(
        vec![(0, IRType::UInt64)],
        IRType::UInt64,
        jp(
            IRType::UInt64,
            vdecl(
                1,
                IRType::Object,
                box_u64(0),
                IRBody::Jmp {
                    jp: JoinPointId(0),
                    args: vec![var(1)],
                },
            ),
        ),
    );
    let msg = refusal(&[d]);
    assert!(msg.contains("object %1"), "{msg}");
    assert!(msg.contains("non-object parameter"), "{msg}");

    // Honest twin: the object parameter takes the reference and returns it.
    let honest = decl(
        vec![(0, IRType::UInt64)],
        IRType::Object,
        jp(
            IRType::Object,
            vdecl(
                1,
                IRType::Object,
                box_u64(0),
                IRBody::Jmp {
                    jp: JoinPointId(0),
                    args: vec![var(1)],
                },
            ),
        ),
    );
    verify_rc_linearity(&[honest]).expect("an object parameter owns what it is passed");
}
