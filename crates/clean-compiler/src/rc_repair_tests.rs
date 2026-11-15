// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.2 unit tests: the RC linearity verifier on hand-built final IR, and
//! the post-boxing repair on the `sqLet` / `twiceApply` shapes.

use super::*;
use crate::ir::{CtorInfo, IRAlt, IRLiteral};
use crate::rc::borrow::FnBorrow;

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn v(n: u32) -> VarId {
    VarId(n)
}

fn var(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}

fn vdecl(n: u32, ty: IRType, value: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: v(n),
        ty,
        value,
        rest: Box::new(rest),
    }
}

fn inc(n: u32, rest: IRBody) -> IRBody {
    IRBody::Inc {
        var: v(n),
        n: 1,
        rest: Box::new(rest),
    }
}

fn dec(n: u32, rest: IRBody) -> IRBody {
    IRBody::Dec {
        var: v(n),
        rest: Box::new(rest),
    }
}

fn apply(f: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: FnId(name(f)),
        args,
    }
}

fn box_u64(n: u32) -> IRExpr {
    IRExpr::Box {
        ty: IRType::UInt64,
        arg: var(n),
    }
}

fn unbox_u64(n: u32) -> IRExpr {
    IRExpr::Unbox {
        ty: IRType::UInt64,
        arg: var(n),
    }
}

fn decl(params: Vec<(u32, IRType)>, return_type: IRType, body: IRBody) -> IRDecl {
    IRDecl {
        name: name("f"),
        params: params.into_iter().map(|(n, t)| (v(n), t)).collect(),
        return_type,
        body,
    }
}

fn refusal(decls: &[IRDecl]) -> String {
    match verify_rc_linearity(decls) {
        Err(err) => err.to_string(),
        Ok(()) => panic!("expected an RC linearity refusal"),
    }
}

/// `f(a : UInt64) := let b := box a; let r := g(b, b); r`: one boxed var
/// passed twice to a consuming call with no `inc` — REFUSED, by name.
fn double_consume_decl(with_inc: bool) -> IRDecl {
    let call = vdecl(
        2,
        IRType::Object,
        apply("g", vec![var(1), var(1)]),
        IRBody::Ret(var(2)),
    );
    let call = if with_inc { inc(1, call) } else { call };
    decl(
        vec![(0, IRType::UInt64)],
        IRType::Object,
        vdecl(1, IRType::Object, box_u64(0), call),
    )
}

#[test]
fn boxed_var_consumed_twice_without_inc_is_refused() {
    let msg = refusal(&[double_consume_decl(false)]);
    assert!(
        msg.contains(
            "RC linearity violation in f: object %1 is consumed 2 times with 0 incs on path entry"
        ),
        "{msg}"
    );
    assert!(msg.contains("needs an inc"), "{msg}");
}

#[test]
fn boxed_var_consumed_twice_with_one_inc_is_accepted() {
    verify_rc_linearity(&[double_consume_decl(true)])
        .expect("one inc pays for the second consumption");
}

#[test]
fn boxed_var_never_consumed_nor_decd_is_refused_as_a_leak() {
    // `let b := box a; let u := unbox b; u` — `b` is never released.
    let d = decl(
        vec![(0, IRType::UInt64)],
        IRType::UInt64,
        vdecl(
            1,
            IRType::Object,
            box_u64(0),
            vdecl(2, IRType::UInt64, unbox_u64(1), IRBody::Ret(var(2))),
        ),
    );
    let msg = refusal(std::slice::from_ref(&d));
    assert!(
        msg.contains("object %1 is consumed 0 times with 0 incs on path entry"),
        "{msg}"
    );
    assert!(msg.contains("never released at return"), "{msg}");

    // Control: the same body with the death `dec` is linear.
    let fixed = decl(
        vec![(0, IRType::UInt64)],
        IRType::UInt64,
        vdecl(
            1,
            IRType::Object,
            box_u64(0),
            vdecl(2, IRType::UInt64, unbox_u64(1), dec(1, IRBody::Ret(var(2)))),
        ),
    );
    verify_rc_linearity(&[fixed]).expect("a dec at the death point balances the binding");
}

#[test]
fn borrowed_param_that_is_decd_is_refused() {
    let d = decl(
        vec![(0, IRType::Object)],
        IRType::UInt64,
        dec(
            0,
            vdecl(
                1,
                IRType::UInt64,
                IRExpr::Lit(IRLiteral::UInt64(0)),
                IRBody::Ret(var(1)),
            ),
        ),
    );
    let mut sigs = BorrowMap::new();
    sigs.insert(
        name("f"),
        FnBorrow {
            params: vec![Ownership::Borrowed],
        },
    );
    let msg = verify_rc_linearity_with_borrows(std::slice::from_ref(&d), &sigs)
        .expect_err("a borrowed parameter holds no reference to release")
        .to_string();
    assert!(
        msg.contains("RC linearity violation in f: object %0"),
        "{msg}"
    );
    assert!(msg.contains("dec of a borrowed parameter"), "{msg}");

    // Mutation control: the SAME body under the all-owned ABI is linear
    // (the owned param's one reference is exactly what the dec releases),
    // so the refusal above is caused by the borrow signature alone.
    verify_rc_linearity(&[d]).expect("an owned parameter may be dec'd once");
}

#[test]
fn use_after_the_last_consumption_is_refused() {
    // `let b := box a; let r := g(b); let u := unbox b; dec r; u`
    let d = decl(
        vec![(0, IRType::UInt64)],
        IRType::UInt64,
        vdecl(
            1,
            IRType::Object,
            box_u64(0),
            vdecl(
                2,
                IRType::Object,
                apply("g", vec![var(1)]),
                vdecl(3, IRType::UInt64, unbox_u64(1), dec(2, IRBody::Ret(var(3)))),
            ),
        ),
    );
    let msg = refusal(&[d]);
    assert!(
        msg.contains("object %1 is consumed 1 times with 0 incs on path entry"),
        "{msg}"
    );
    assert!(msg.contains("use after the final consumption"), "{msg}");
}

#[test]
fn a_leak_on_one_branch_names_that_branch() {
    // `let b := box a; case c of | 0 => dec b; ret 0 | 1 => ret 0`
    let ctor = |tag| CtorInfo {
        name: name("Bool"),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    };
    let ret0 = || {
        vdecl(
            3,
            IRType::UInt64,
            IRExpr::Lit(IRLiteral::UInt64(0)),
            IRBody::Ret(var(3)),
        )
    };
    let d = decl(
        vec![(0, IRType::UInt64), (2, IRType::Bool)],
        IRType::UInt64,
        vdecl(
            1,
            IRType::Object,
            box_u64(0),
            IRBody::Case {
                scrutinee: v(2),
                alts: vec![
                    IRAlt {
                        ctor: ctor(0),
                        body: Box::new(dec(1, ret0())),
                    },
                    IRAlt {
                        ctor: ctor(1),
                        body: Box::new(ret0()),
                    },
                ],
                default: None,
            },
        ),
    );
    let msg = refusal(&[d]);
    assert!(msg.contains("on path entry/alt1"), "{msg}");
}

// ── Review (adversarial): the reset/reuse fast-path model ─────────────────

fn cell_ctor(tag: u32, num_objects: u32) -> CtorInfo {
    CtorInfo {
        name: name("Cell"),
        tag,
        num_scalars: 0,
        num_objects,
        field_types: vec![IRType::Object; num_objects as usize],
    }
}

fn set(obj: u32, idx: u32, value: u32, rest: IRBody) -> IRBody {
    IRBody::Set {
        var: v(obj),
        idx,
        value: v(value),
        rest: Box::new(rest),
    }
}

/// `f(x) := y := proj[0] x; <pre>; s := isShared x; <pre_case>;
/// case s of | 0 => <fast> | 1 => <slow>` — the shape `rc::expand` gives a
/// `reset`: the exclusive arm steals `x`'s field slot through `y`.
fn fast_path_decl(pre_case: impl FnOnce(IRBody) -> IRBody, fast: IRBody, slow: IRBody) -> IRDecl {
    let bool_ctor = |tag| CtorInfo {
        name: name("Bool"),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    };
    let case = IRBody::Case {
        scrutinee: v(2),
        alts: vec![
            IRAlt {
                ctor: bool_ctor(0),
                body: Box::new(fast),
            },
            IRAlt {
                ctor: bool_ctor(1),
                body: Box::new(slow),
            },
        ],
        default: None,
    };
    decl(
        vec![(0, IRType::Object)],
        IRType::Object,
        vdecl(
            1,
            IRType::Object,
            IRExpr::Proj {
                idx: 0,
                ty: IRType::Object,
                arg: var(0),
            },
            vdecl(2, IRType::UInt8, IRExpr::IsShared(v(0)), pre_case(case)),
        ),
    )
}

/// The honest fast path: `a := g(y); set x[0] := a; ret x` on the
/// exclusive arm, `inc y; dec x; a := g(y); ret ctor(a)` on the shared arm.
#[test]
fn the_reset_fast_path_steal_is_accepted() {
    let fast = vdecl(
        3,
        IRType::Object,
        apply("g", vec![var(1)]),
        set(0, 0, 3, IRBody::Ret(var(0))),
    );
    let slow = inc(
        1,
        dec(
            0,
            vdecl(
                3,
                IRType::Object,
                apply("g", vec![var(1)]),
                vdecl(
                    4,
                    IRType::Object,
                    IRExpr::Ctor {
                        info: cell_ctor(0, 1),
                        args: vec![var(3)],
                    },
                    IRBody::Ret(var(4)),
                ),
            ),
        ),
    );
    verify_rc_linearity(&[fast_path_decl(|b| b, fast, slow)])
        .expect("the exclusive arm may steal the field slot once and refill it");
}

/// Adversarial (review): a projection that already TOOK its slot is spent.
/// Refilling the slot with `Set` must not make it takeable again —
/// `g(y); set x[0] := a; g(y)` hands the old field object away TWICE (the
/// first cut accepted it: the second `g(y)` re-took the refilled slot).
#[test]
fn a_spent_projection_cannot_retake_a_refilled_slot() {
    let fast = vdecl(
        3,
        IRType::Object,
        apply("g", vec![var(1)]),
        set(
            0,
            0,
            3,
            vdecl(
                4,
                IRType::Object,
                apply("g", vec![var(1)]),
                set(0, 0, 4, IRBody::Ret(var(0))),
            ),
        ),
    );
    let msg = refusal(&[fast_path_decl(|b| b, fast, IRBody::Unreachable)]);
    assert!(
        msg.contains("RC linearity violation in f: object %1 is consumed 2 times with 0 incs on path entry/alt0"),
        "{msg}"
    );
    assert!(
        msg.contains("a duplicate consumption needs an inc"),
        "{msg}"
    );
}

/// Adversarial (review): once the slot is refilled, ANOTHER projection of it
/// (`y2`, taken before the steal) still names the OLD field object, so even
/// a borrowed read of it is a use after that object was handed away (the
/// first cut let the refilled slot back it again).
#[test]
fn a_projection_is_not_backed_by_a_refilled_slot() {
    let fast = vdecl(
        6,
        IRType::Object,
        IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: var(0),
        },
        vdecl(
            3,
            IRType::Object,
            apply("g", vec![var(1)]),
            set(
                0,
                0,
                3,
                vdecl(5, IRType::UInt64, unbox_u64(6), IRBody::Ret(var(0))),
            ),
        ),
    );
    let msg = refusal(&[fast_path_decl(|b| b, fast, IRBody::Unreachable)]);
    assert!(msg.contains("object %6"), "{msg}");
    assert!(msg.contains("use after the final consumption"), "{msg}");
}

/// Adversarial (review): an `IsShared` answer taken BEFORE an `inc` of the
/// object is stale — `s := isShared x; inc x; case s of 0 => steal` mutates
/// an object with two references (the first cut marked it exclusive).
#[test]
fn an_inc_after_the_sharing_probe_voids_exclusivity() {
    let fast = vdecl(
        3,
        IRType::Object,
        apply("g", vec![var(1)]),
        set(
            0,
            0,
            3,
            vdecl(
                4,
                IRType::Object,
                IRExpr::Ctor {
                    info: cell_ctor(0, 2),
                    args: vec![var(0), var(0)],
                },
                IRBody::Ret(var(4)),
            ),
        ),
    );
    let msg = refusal(&[fast_path_decl(|b| inc(0, b), fast, IRBody::Unreachable)]);
    assert!(
        msg.contains("object %1 is consumed 1 times with 0 incs on path entry/alt0"),
        "{msg}"
    );
    // Control: without the `inc` (and with `x` consumed once) the same
    // steal is the honest fast path.
    let honest = vdecl(
        3,
        IRType::Object,
        apply("g", vec![var(1)]),
        set(0, 0, 3, IRBody::Ret(var(0))),
    );
    verify_rc_linearity(&[fast_path_decl(|b| b, honest, IRBody::Unreachable)])
        .expect("the probe is fresh without the inc");
}

/// Adversarial (review): a jump must pass exactly one argument per
/// join-point parameter. A missing argument used to enter as an untracked
/// placeholder, so the join point's body was never checked for it.
#[test]
fn a_jump_with_the_wrong_arity_is_refused() {
    // `jp k(p : obj) := ret p; b := box a; jmp k()` — `b` leaks and `p`
    // would be an unchecked placeholder.
    let d = decl(
        vec![(0, IRType::UInt64)],
        IRType::Object,
        IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![(v(9), IRType::Object)],
            body: Box::new(IRBody::Ret(var(9))),
            rest: Box::new(vdecl(
                1,
                IRType::Object,
                box_u64(0),
                dec(
                    1,
                    IRBody::Jmp {
                        jp: JoinPointId(0),
                        args: vec![],
                    },
                ),
            )),
        },
    );
    let msg = refusal(&[d]);
    assert!(
        msg.contains("jump to jp0 passes 0 argument(s) for 1 parameter(s)"),
        "{msg}"
    );
}

/// Adversarial (review): a join-point id declared twice in one body is
/// refused — the id → body map would check the wrong body at one of them.
#[test]
fn a_duplicate_join_point_id_is_refused() {
    let jdecl = |rest: IRBody| IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![],
        body: Box::new(IRBody::Unreachable),
        rest: Box::new(rest),
    };
    let d = decl(
        vec![(0, IRType::UInt64)],
        IRType::UInt64,
        jdecl(jdecl(IRBody::Ret(var(0)))),
    );
    let msg = refusal(&[d]);
    assert!(
        msg.contains("join point jp0 is declared more than once"),
        "{msg}"
    );
}

/// The boxed `sqLet` body as the pipeline emits it (measured at -O0):
/// `t := HAdd.hAdd(.., inst, box a, one)` is an OBJECT whose LCNF type is
/// `UInt64`, so LCNF RC never managed it; it is passed twice to the
/// consuming `HMul.hMul`, and the product is unboxed and never released.
fn sqlet_boxed() -> (IRDecl, IRDecl, RcUnmanagedVars) {
    let pre = decl(
        vec![(0, IRType::UInt64)],
        IRType::UInt64,
        vdecl(
            1,
            IRType::Object,
            apply("instHAddUInt64", vec![]),
            vdecl(
                3,
                IRType::Object,
                apply("UInt64.ofNat", vec![]),
                vdecl(
                    4,
                    IRType::Object,
                    apply("HAdd.hAdd", vec![IRArg::Erased, var(1), var(0), var(3)]),
                    vdecl(
                        5,
                        IRType::Object,
                        apply("instHMulUInt64", vec![]),
                        vdecl(
                            6,
                            IRType::Object,
                            apply("HMul.hMul", vec![IRArg::Erased, var(5), var(4), var(4)]),
                            vdecl(7, IRType::UInt64, unbox_u64(6), IRBody::Ret(var(7))),
                        ),
                    ),
                ),
            ),
        ),
    );
    let boxed = decl(
        vec![(0, IRType::UInt64)],
        IRType::UInt64,
        vdecl(
            1,
            IRType::Object,
            apply("instHAddUInt64", vec![]),
            vdecl(
                3,
                IRType::Object,
                apply("UInt64.ofNat", vec![]),
                vdecl(
                    8,
                    IRType::Object,
                    box_u64(0),
                    vdecl(
                        4,
                        IRType::Object,
                        apply("HAdd.hAdd", vec![IRArg::Erased, var(1), var(8), var(3)]),
                        vdecl(
                            5,
                            IRType::Object,
                            apply("instHMulUInt64", vec![]),
                            vdecl(
                                6,
                                IRType::Object,
                                apply("HMul.hMul", vec![IRArg::Erased, var(5), var(4), var(4)]),
                                vdecl(7, IRType::UInt64, unbox_u64(6), IRBody::Ret(var(7))),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    let mut unmanaged = RcUnmanagedVars::new();
    unmanaged.insert(name("f"), [v(3), v(4), v(6), v(7)].into_iter().collect());
    (pre, boxed, unmanaged)
}

#[test]
fn sqlet_boxed_shape_is_refused_without_the_repair() {
    let (_, boxed, _) = sqlet_boxed();
    let msg = refusal(&[boxed]);
    assert!(
        msg.contains("object %4 is consumed 2 times with 0 incs on path entry"),
        "{msg}"
    );
}

#[test]
fn sqlet_boxed_shape_is_linear_after_the_repair() {
    let (pre, boxed, unmanaged) = sqlet_boxed();
    let repaired = rc_repair_boxed(&[pre], vec![boxed], &unmanaged);
    verify_rc_linearity(&repaired).expect("the repair makes every object linear");
    let printed = format!("{:?}", repaired[0].body);
    // Exactly one inc, before the double consumption, and one dec, after the
    // product's only (borrowed) use; nothing touches the LCNF-managed
    // instance objects %1 / %5.
    assert_eq!(printed.matches("Inc {").count(), 1, "{printed}");
    assert!(printed.contains("Inc { var: VarId(4), n: 1"), "{printed}");
    assert_eq!(printed.matches("Dec {").count(), 1, "{printed}");
    assert!(printed.contains("Dec { var: VarId(6)"), "{printed}");
}

#[test]
fn a_deficit_outside_the_repair_domain_is_never_repaired() {
    // Same shape, but `%4` is NOT recorded as LCNF-scalar and is bound in the
    // pre-boxing twin: it is an LCNF-managed variable, so its missing inc is
    // an LCNF RC defect the repair must not paper over.
    let (pre, boxed, mut unmanaged) = sqlet_boxed();
    unmanaged.insert(name("f"), [v(6), v(7)].into_iter().collect());
    let repaired = rc_repair_boxed(&[pre], vec![boxed], &unmanaged);
    let msg = refusal(&repaired);
    assert!(
        msg.contains("object %4 is consumed 2 times with 0 incs on path entry"),
        "{msg}"
    );
}

#[test]
fn twice_apply_closure_shape_is_repaired() {
    // `twiceApply f a := let t := a + 1; f t t` — the `ClosureApply` arm:
    // the owned closure param is inc'd/dec'd by LCNF RC; `t` is not.
    let body = || {
        vdecl(
            5,
            IRType::Object,
            apply("HAdd.hAdd", vec![IRArg::Erased, var(1)]),
            inc(
                0,
                vdecl(
                    6,
                    IRType::Object,
                    IRExpr::ClosureApply {
                        closure: var(0),
                        args: vec![var(5), var(5)],
                    },
                    dec(
                        0,
                        vdecl(7, IRType::UInt64, unbox_u64(6), IRBody::Ret(var(7))),
                    ),
                ),
            ),
        )
    };
    let d = decl(
        vec![(0, IRType::Object), (1, IRType::UInt64)],
        IRType::UInt64,
        body(),
    );
    let msg = refusal(std::slice::from_ref(&d));
    assert!(
        msg.contains("object %5 is consumed 2 times with 0 incs"),
        "{msg}"
    );
    let mut unmanaged = RcUnmanagedVars::new();
    unmanaged.insert(name("f"), [v(5), v(6), v(7)].into_iter().collect());
    let repaired = rc_repair_boxed(std::slice::from_ref(&d), vec![d.clone()], &unmanaged);
    verify_rc_linearity(&repaired).expect("the repaired closure application is linear");
}

/// The object→scalar direction: boxing casts an LCNF-MANAGED object to a
/// scalar return with `u := unbox v; ret u`. The pre-boxing `ret v` consumed
/// `v`; the unbox only reads it. The shape of `Bool.xor`'s
/// `ret (Bool.not b)` — one of 118 prelude roots that leaked this way.
fn cast_at(consuming: bool) -> (IRDecl, IRDecl) {
    let tail = |u: u32| {
        if consuming {
            IRBody::Ret(var(u))
        } else {
            // Twin: the cast feeds a `case` scrutinee — a READ in both
            // representations, so nothing was consumed there.
            IRBody::Case {
                scrutinee: v(u),
                alts: vec![],
                default: Some(Box::new(IRBody::Ret(var(u)))),
            }
        }
    };
    let pre = decl(
        vec![(0, IRType::Bool)],
        IRType::Bool,
        vdecl(
            2,
            IRType::Object,
            apply("Bool.not", vec![var(0)]),
            IRBody::Ret(var(2)),
        ),
    );
    let boxed = decl(
        vec![(0, IRType::Bool)],
        IRType::Bool,
        vdecl(
            4,
            IRType::Object,
            IRExpr::Box {
                ty: IRType::Bool,
                arg: var(0),
            },
            vdecl(
                2,
                IRType::Object,
                apply("Bool.not", vec![var(4)]),
                vdecl(
                    3,
                    IRType::Bool,
                    IRExpr::Unbox {
                        ty: IRType::Bool,
                        arg: var(2),
                    },
                    tail(3),
                ),
            ),
        ),
    );
    (pre, boxed)
}

#[test]
fn an_unbox_that_replaced_a_consumption_releases_the_object() {
    let (pre, boxed) = cast_at(true);
    let msg = refusal(std::slice::from_ref(&boxed));
    assert!(
        msg.contains("object %2 is consumed 0 times with 0 incs"),
        "{msg}"
    );
    let repaired = rc_repair_boxed(&[pre], vec![boxed], &RcUnmanagedVars::new());
    verify_rc_linearity(&repaired).expect("the consuming unbox releases what `ret` consumed");
    let printed = format!("{:?}", repaired[0].body);
    assert!(printed.contains("Dec { var: VarId(2)"), "{printed}");
}

#[test]
fn an_unbox_feeding_a_case_is_a_read_and_releases_nothing() {
    // Mutation control for the rule above: the SAME cast feeding a case
    // scrutinee gets no release from it, so the (hand-built, LCNF-managed)
    // object stays unreleased and the verifier refuses it.
    let (pre, boxed) = cast_at(false);
    let repaired = rc_repair_boxed(&[pre], vec![boxed], &RcUnmanagedVars::new());
    let printed = format!("{:?}", repaired[0].body);
    assert!(!printed.contains("Dec { var: VarId(2)"), "{printed}");
    let msg = refusal(&repaired);
    assert!(msg.contains("object %2"), "{msg}");
}

/// Regression pins, one prelude root per class of pre-existing RC defect the
/// linearity verifier surfaced (measured over the 1002 computable prelude
/// roots: 118 refused before the fixes, 0 after), each compiled through the
/// full default pipeline, which runs `verify_rc_linearity`.
#[test]
fn prelude_roots_that_leaked_now_pass_verify_rc_linearity() {
    use crate::pass_manager::{compile_lcnf_decls, PipelineConfig};
    use crate::to_lcnf::constant_to_decl;
    let mut env = clean_kernel::Environment::with_prelude();
    env.init_io_ops().expect("IO prelude");
    for (root, class) in [
        ("Bool.xor", "boxing's unbox at a consuming position"),
        ("Nat.max", "a dead case scrutinee"),
        ("List.get", "a local dead in one branch"),
        (
            "List.instGetElem?NatLtLength",
            "a projection as the structure's last use",
        ),
        (
            "UInt32.ofNat",
            "to_ir's decode dropping its operand's consumption",
        ),
        (
            "Char.ofNatAux",
            "to_ir's decode dropping its operand's consumption",
        ),
    ] {
        let info = env.get_const(&name(root)).expect("prelude root");
        let lcnf = constant_to_decl(&env, info)
            .expect("lowers")
            .expect("computable");
        for pipeline in [PipelineConfig::default(), e2e_support::o0()] {
            compile_lcnf_decls(std::slice::from_ref(&lcnf), &env, &pipeline)
                .unwrap_or_else(|e| panic!("{root} ({class}) must compile linear: {e}"));
        }
    }
}

// ── End to end: real source, full pipeline, executed ─────────────────────

#[path = "rc_repair_tests_e2e.rs"]
mod end_to_end;

// ── Second review (adversarial): verifier holes ──────────────────────────

#[path = "rc_repair_tests_review.rs"]
mod review;
