// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `tail_loop` (X4 R2) and the linearity engine's loop model (R5) on
//! hand-built final L5IR.

use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use crate::ir_checker::check_decls;
use crate::rc_repair::verify_rc_linearity;
use crate::tail_loop::loop_self_tail_calls;
use clean_kernel::Name;

fn v(n: u32) -> VarId {
    VarId(n)
}

fn var(n: u32) -> IRArg {
    IRArg::Var(v(n))
}

fn apply(f: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: FnId(Name::from_string(f)),
        args,
    }
}

fn vdecl(n: u32, ty: IRType, value: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: v(n),
        ty,
        value,
        rest: Box::new(rest),
    }
}

fn dec(n: u32, rest: IRBody) -> IRBody {
    IRBody::Dec {
        var: v(n),
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

fn ret(n: u32) -> IRBody {
    IRBody::Ret(var(n))
}

fn ctor(name: &str, tag: u32, num_objects: u32) -> CtorInfo {
    CtorInfo {
        name: Name::from_string(name),
        tag,
        num_scalars: 0,
        num_objects,
        field_types: vec![IRType::Object; num_objects as usize],
    }
}

fn case2(scrutinee: u32, ty: &str, zero: IRBody, one: IRBody) -> IRBody {
    IRBody::Case {
        scrutinee: v(scrutinee),
        alts: vec![
            IRAlt {
                ctor: ctor(ty, 0, 0),
                body: Box::new(zero),
            },
            IRAlt {
                ctor: ctor(ty, 1, 0),
                body: Box::new(one),
            },
        ],
        default: None,
    }
}

fn decl(name: &str, params: Vec<(u32, IRType)>, ret_ty: IRType, body: IRBody) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params: params.into_iter().map(|(n, t)| (v(n), t)).collect(),
        return_type: ret_ty,
        body,
    }
}

/// The calls to `f` anywhere in `body`.
fn calls_to(body: &IRBody, f: &str) -> usize {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            let here = matches!(value, IRExpr::Apply { fn_id, .. } if fn_id.0.to_string() == f);
            usize::from(here) + calls_to(rest, f)
        }
        IRBody::JDecl { body, rest, .. } => calls_to(body, f) + calls_to(rest, f),
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => calls_to(rest, f),
        IRBody::Case { alts, default, .. } => {
            alts.iter().map(|a| calls_to(&a.body, f)).sum::<usize>()
                + default.as_ref().map_or(0, |d| calls_to(d, f))
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 0,
    }
}

/// The scalar counter `count n acc := if n = 0 then acc else count (n-1) (acc+1)`.
fn scalar_count() -> IRDecl {
    let step = vdecl(
        3,
        IRType::UInt64,
        apply("dec64", vec![var(0)]),
        vdecl(
            4,
            IRType::UInt64,
            apply("inc64", vec![var(1)]),
            vdecl(
                5,
                IRType::UInt64,
                apply("count", vec![var(3), var(4)]),
                ret(5),
            ),
        ),
    );
    decl(
        "count",
        vec![(0, IRType::UInt64), (1, IRType::UInt64)],
        IRType::UInt64,
        vdecl(
            2,
            IRType::UInt8,
            apply("isZero64", vec![var(0)]),
            case2(2, "Bool", step, IRBody::Ret(var(1))),
        ),
    )
}

#[test]
fn test_tail_loop_scalar_counter_becomes_a_loop() {
    let mut decls = vec![scalar_count()];
    assert_eq!(loop_self_tail_calls(&mut decls), 1);
    let d = &decls[0];
    assert_eq!(calls_to(&d.body, "count"), 0, "{:#?}", d.body);
    let IRBody::JDecl {
        jp, params, rest, ..
    } = &d.body
    else {
        panic!("the body becomes a loop join point: {:#?}", d.body);
    };
    assert_eq!(params.len(), 2);
    assert!(
        params.iter().all(|(q, _)| q.0 > 5),
        "loop parameters are fresh"
    );
    assert_eq!(
        **rest,
        IRBody::Jmp {
            jp: *jp,
            args: vec![var(0), var(1)],
        }
    );
    check_decls(&decls).expect("the loop is well-formed L5IR");
    verify_rc_linearity(&decls).expect("the loop is linear");
}

#[test]
fn test_tail_loop_non_tail_and_foreign_calls_stay_calls() {
    // `r := count(a, b); s := succ(r); ret s` — the self call is not returned.
    let not_tail = decl(
        "count",
        vec![(0, IRType::UInt64), (1, IRType::UInt64)],
        IRType::UInt64,
        vdecl(
            2,
            IRType::UInt64,
            apply("count", vec![var(1), var(0)]),
            vdecl(3, IRType::UInt64, apply("succ", vec![var(2)]), ret(3)),
        ),
    );
    // A tail call to ANOTHER function, a partial application and a closure
    // application of the function itself.
    let foreign = decl(
        "f",
        vec![(0, IRType::Object)],
        IRType::Object,
        vdecl(1, IRType::Object, apply("g", vec![var(0)]), ret(1)),
    );
    let pap = decl(
        "f",
        vec![(0, IRType::Object), (1, IRType::Object)],
        IRType::Object,
        vdecl(
            2,
            IRType::Object,
            IRExpr::PartialApply {
                fn_id: FnId(Name::from_string("f")),
                arity: 2,
                args: vec![var(0)],
            },
            dec(1, ret(2)),
        ),
    );
    let closure = decl(
        "f",
        vec![(0, IRType::Object), (1, IRType::Object)],
        IRType::Object,
        vdecl(
            2,
            IRType::Object,
            IRExpr::ClosureApply {
                closure: var(0),
                args: vec![var(1)],
            },
            ret(2),
        ),
    );
    for d in [not_tail, foreign, pap, closure] {
        let mut decls = vec![d.clone()];
        assert_eq!(loop_self_tail_calls(&mut decls), 0);
        assert_eq!(decls[0], d, "unchanged");
    }
}

#[test]
fn test_tail_loop_refuses_a_box_or_binding_after_the_call() {
    let boxed = decl(
        "f",
        vec![(0, IRType::UInt64)],
        IRType::Object,
        vdecl(
            1,
            IRType::UInt64,
            apply("f", vec![var(0)]),
            vdecl(
                2,
                IRType::Object,
                IRExpr::Box {
                    ty: IRType::UInt64,
                    arg: var(1),
                },
                ret(2),
            ),
        ),
    );
    let mut decls = vec![boxed.clone()];
    assert_eq!(loop_self_tail_calls(&mut decls), 0);
    assert_eq!(decls[0], boxed);
}

/// `walk x y := case x of | leaf => dec y; ret x | node => walk y x`, with
/// RC already inserted (all-owned): the swap passes both parameters.
fn object_swap() -> IRDecl {
    decl(
        "walk",
        vec![(0, IRType::Object), (1, IRType::Object)],
        IRType::Object,
        IRBody::Case {
            scrutinee: v(0),
            alts: vec![
                IRAlt {
                    ctor: ctor("T", 0, 0),
                    body: Box::new(dec(1, ret(0))),
                },
                IRAlt {
                    ctor: ctor("T", 1, 0),
                    body: Box::new(vdecl(
                        2,
                        IRType::Object,
                        apply("walk", vec![var(1), var(0)]),
                        ret(2),
                    )),
                },
            ],
            default: None,
        },
    )
}

#[test]
fn test_tail_loop_swap_jumps_with_both_parameters_and_stays_linear() {
    let mut decls = vec![object_swap()];
    assert_eq!(loop_self_tail_calls(&mut decls), 1);
    let IRBody::JDecl { params, body, .. } = &decls[0].body else {
        panic!("loop expected");
    };
    let (q0, q1) = (params[0].0, params[1].0);
    let IRBody::Case { alts, .. } = body.as_ref() else {
        panic!("case expected");
    };
    let IRBody::Jmp { args, .. } = alts[1].body.as_ref() else {
        panic!("the self tail call is a jump: {:#?}", alts[1].body);
    };
    assert_eq!(args, &vec![IRArg::Var(q1), IRArg::Var(q0)]);
    check_decls(&decls).expect("well-formed");
    verify_rc_linearity(&decls).expect("linear");

    // Both source emitters assign the swap in parallel (R4).
    let c = crate::emit_c::emit_c(&decls).expect("C emits");
    assert!(c.contains("_tmp_"), "C swap goes through temporaries:\n{c}");
    assert!(c.contains("goto _jp"), "C back edge:\n{c}");
    let r = crate::emit_rust::emit_rust(&decls).expect("Rust emits");
    assert!(
        r.contains("let _tmp_"),
        "Rust swap goes through temporaries:\n{r}"
    );
}

#[test]
fn test_tail_loop_moves_the_release_before_the_jump() {
    // `inc y; r := walk(y, x); dec y; ret r` (y passed AND released).
    let mut d = object_swap();
    let IRBody::Case { alts, .. } = &mut d.body else {
        unreachable!()
    };
    *alts[1].body = inc(
        1,
        vdecl(
            2,
            IRType::Object,
            apply("walk", vec![var(1), var(0)]),
            dec(1, ret(2)),
        ),
    );
    let mut decls = vec![d];
    assert_eq!(loop_self_tail_calls(&mut decls), 1);
    let IRBody::JDecl { params, body, .. } = &decls[0].body else {
        panic!("loop expected");
    };
    let q1 = params[1].0;
    let IRBody::Case { alts, .. } = body.as_ref() else {
        panic!("case expected");
    };
    let IRBody::Inc { rest, .. } = alts[1].body.as_ref() else {
        panic!("inc first: {:#?}", alts[1].body);
    };
    let IRBody::Dec { var, rest } = rest.as_ref() else {
        panic!("the release moves before the jump: {rest:#?}");
    };
    assert_eq!(*var, q1);
    assert!(matches!(rest.as_ref(), IRBody::Jmp { .. }));
    verify_rc_linearity(&decls).expect("linear");
}

#[test]
fn test_tail_loop_refuses_inc_of_an_argument_after_the_call() {
    let mut d = object_swap();
    let IRBody::Case { alts, .. } = &mut d.body else {
        unreachable!()
    };
    *alts[1].body = vdecl(
        2,
        IRType::Object,
        apply("walk", vec![var(1), var(0)]),
        inc(1, ret(2)),
    );
    let mut decls = vec![d.clone()];
    assert_eq!(loop_self_tail_calls(&mut decls), 0);
    assert_eq!(decls[0], d);
}

/// `f x := let a := proj[0] x; [inc a;] let r := f(a); dec x; ret r`.
fn proj_then_release(with_inc: bool) -> IRDecl {
    let call = vdecl(2, IRType::Object, apply("f", vec![var(1)]), dec(0, ret(2)));
    let after_proj = if with_inc { inc(1, call) } else { call };
    decl(
        "f",
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
            after_proj,
        ),
    )
}

#[test]
fn test_tail_loop_refuses_a_borrowed_projection_of_a_released_parent() {
    let mut decls = vec![proj_then_release(false)];
    assert_eq!(
        loop_self_tail_calls(&mut decls),
        0,
        "releasing the parent first could free the field the next iteration reads"
    );
    let mut decls = vec![proj_then_release(true)];
    assert_eq!(
        loop_self_tail_calls(&mut decls),
        1,
        "an inc'd field owns itself"
    );
    verify_rc_linearity(&decls).expect("linear");
}

// ---- R5: the linearity engine's loop model -----------------------------

/// A loop that probes a fresh `x := g(q)` for exclusivity on its first
/// iteration (`t = 1`), jumps back with it, and on the next iteration (`t =
/// 0`) steals a field of a NEW `x := g(q)` it never probed. Without the
/// back-edge model the engine named both objects `x`, kept the first one's
/// exclusivity, and accepted the steal.
fn stale_exclusive_loop() -> IRDecl {
    let lit = |n: u32, value: u8, rest: IRBody| {
        vdecl(n, IRType::UInt8, IRExpr::Lit(IRLiteral::UInt8(value)), rest)
    };
    let jmp = |args: Vec<IRArg>| IRBody::Jmp {
        jp: crate::ir::JoinPointId(0),
        args,
    };
    // t = 1: probe, then jump back with x (exclusive) and t := 0.
    let first = vdecl(
        13,
        IRType::UInt8,
        IRExpr::IsShared(v(12)),
        case2(13, "Bool", lit(14, 0, jmp(vec![var(12), var(14)])), ret(12)),
    );
    // t = 0: steal field 0 of x and refill it, with no probe of THIS x.
    let second = vdecl(
        15,
        IRType::Object,
        IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: var(12),
        },
        dec(
            15,
            vdecl(
                16,
                IRType::Object,
                apply("mk", vec![]),
                IRBody::Set {
                    var: v(12),
                    idx: 0,
                    value: v(16),
                    rest: Box::new(ret(12)),
                },
            ),
        ),
    );
    let loop_body = vdecl(
        12,
        IRType::Object,
        apply("g", vec![var(10)]),
        case2(11, "Bool", second, first),
    );
    decl(
        "stale",
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
fn test_rc_linearity_refuses_exclusivity_carried_into_the_next_iteration() {
    let err = verify_rc_linearity(&[stale_exclusive_loop()])
        .expect_err("the second iteration's x was never probed");
    let text = err.to_string();
    assert!(text.contains("stale"), "{text}");
}

#[test]
fn test_rc_linearity_accepts_the_probed_steal_inside_one_iteration() {
    // Control: probing the SAME iteration's x makes the steal legal, so the
    // refusal above is about the iteration, not about the steal.
    let mut d = stale_exclusive_loop();
    let IRBody::VDecl { rest: entry, .. } = &mut d.body else {
        unreachable!()
    };
    let IRBody::JDecl { body, .. } = entry.as_mut() else {
        unreachable!()
    };
    let IRBody::VDecl { rest, .. } = body.as_mut() else {
        unreachable!()
    };
    let IRBody::Case { alts, .. } = rest.as_mut() else {
        unreachable!()
    };
    let steal = std::mem::replace(&mut alts[0].body, Box::new(IRBody::Unreachable));
    *alts[0].body = vdecl(
        17,
        IRType::UInt8,
        IRExpr::IsShared(v(12)),
        case2(17, "Bool", *steal, ret(12)),
    );
    verify_rc_linearity(&[d]).expect("a steal after this iteration's probe is linear");
}

#[test]
fn test_rc_linearity_refuses_a_dec_duplicated_in_a_loop() {
    let mut d = object_swap();
    let IRBody::Case { alts, .. } = &mut d.body else {
        unreachable!()
    };
    *alts[1].body = inc(
        1,
        vdecl(
            2,
            IRType::Object,
            apply("walk", vec![var(1), var(0)]),
            dec(1, dec(1, ret(2))),
        ),
    );
    let mut decls = vec![d];
    assert_eq!(loop_self_tail_calls(&mut decls), 1);
    verify_rc_linearity(&decls).expect_err("one dec too many in the loop body");
}

// ---- R4 on trust-ir: an erased argument on a back edge -----------------

/// `poly(t : erased, x, flag) := case flag of 0 => ret x | 1 => poly(◾, x, 0)`:
/// a polymorphic loop whose back edge passes its erased type argument.
#[cfg(feature = "trust-ir-backend")]
fn erased_arg_loop() -> IRDecl {
    let again = vdecl(
        3,
        IRType::UInt8,
        IRExpr::Lit(IRLiteral::UInt8(0)),
        vdecl(
            4,
            IRType::Object,
            apply("poly", vec![IRArg::Erased, var(1), var(3)]),
            ret(4),
        ),
    );
    decl(
        "poly",
        vec![(0, IRType::Erased), (1, IRType::Object), (2, IRType::UInt8)],
        IRType::Object,
        case2(2, "Bool", ret(1), again),
    )
}

/// The back-edge `jmp` of a looped declaration.
#[cfg(feature = "trust-ir-backend")]
fn back_edge(body: &IRBody) -> Option<&Vec<IRArg>> {
    match body {
        IRBody::JDecl { body, .. } => back_edge(body),
        IRBody::Case { alts, .. } => alts.iter().find_map(|a| back_edge(&a.body)),
        IRBody::VDecl { rest, .. } => back_edge(rest),
        IRBody::Jmp { args, .. } => Some(args),
        _ => None,
    }
}

#[cfg(feature = "trust-ir-backend")]
#[test]
fn test_tail_loop_emit_trust_ir_materializes_an_erased_back_edge_argument() {
    let mut decls = vec![erased_arg_loop()];
    assert_eq!(loop_self_tail_calls(&mut decls), 1);
    let args = back_edge(&decls[0].body).expect("a back edge");
    assert!(
        args.contains(&IRArg::Erased),
        "the back edge passes the erased argument: {args:?}"
    );
    // `emit_trust_ir` validates the module it returns; the branch back to the
    // loop block must carry one value per block parameter.
    let module = crate::emit_trust_ir::emit_trust_ir(&decls)
        .expect("a loop with an erased back-edge argument lowers to trust-ir");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");
}

#[path = "tail_loop_rc_carried_tests.rs"]
mod carried;
