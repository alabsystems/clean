// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for [`super::sink_ih`].
//!
//! Each test builds the arm shape `build_rec_arm_body` produces and asserts
//! where the IH binding ends up. The end-to-end order assertion — the printed
//! bytes of a recursive `IO` do-block — lives in `clean-cli`'s `cmd_run` suite,
//! which is where the eager-effect model is actually executed.

use super::sink_ih::sink_ih_bindings;
use crate::lcnf::{Alt, Arg, Code, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Name};

fn fv(n: u64) -> FVarId {
    FVarId::new(n)
}

fn obj() -> Expr {
    Expr::const_str("Object")
}

/// `let v := go(arg)` — the shape `build_rec_arm_body` binds an IH with.
fn ih_let(v: u64, go: u64, arg: u64) -> LetDecl {
    LetDecl::new(
        fv(v),
        Name::anon(),
        obj(),
        LetValue::FVar {
            fvar: fv(go),
            args: vec![Arg::FVar(fv(arg))],
        },
    )
}

/// `let v := f(args..)` — stands in for an effectful call such as `IO.println`.
fn call_let(v: u64, f: &str, args: &[u64]) -> LetDecl {
    LetDecl::new(
        fv(v),
        Name::anon(),
        obj(),
        LetValue::Const {
            name: Name::from_string(f),
            levels: Vec::new(),
            args: args.iter().map(|a| Arg::FVar(fv(*a))).collect(),
        },
    )
}

fn lambda(id: u64, param: u64, body: Code) -> FunDecl {
    FunDecl::new(
        fv(id),
        Name::from_string("_lambda"),
        vec![Param::new(fv(param), Name::anon(), obj())],
        obj(),
        body,
    )
}

/// The chain of `fvar_id`s bound by top-level `Let`s, outermost first.
fn top_level_lets(code: &Code) -> Vec<u64> {
    let mut ids = Vec::new();
    let mut curr = code;
    loop {
        match curr {
            Code::Let(decl, rest) => {
                ids.push(decl.fvar_id.as_u64());
                curr = rest;
            }
            Code::Fun(_, rest) | Code::JoinPoint(_, rest) => curr = rest,
            _ => return ids,
        }
    }
}

fn find_fun(code: &Code, id: u64) -> Option<&FunDecl> {
    let mut curr = code;
    loop {
        match curr {
            Code::Let(_, rest) => curr = rest,
            Code::Fun(decl, rest) | Code::JoinPoint(decl, rest) => {
                if decl.fvar_id == fv(id) {
                    return Some(decl);
                }
                curr = rest;
            }
            _ => return None,
        }
    }
}

/// The reported defect, at the IR level: `do IO.println s; dump rest`.
///
/// Before: `let ih := go(rest)` runs ahead of `IO.println s`. After: the IH
/// binding is inside the bind continuation, so nothing recurses until the
/// continuation is entered.
#[test]
fn test_sink_ih_recursive_bind_continuation_moves_ih_into_the_lambda() {
    // let ih  := go(rest)
    // let msg := IO.println(head)
    // fun k (_) := return ih
    // let r   := Bind.bind(msg, k)
    // return r
    let code = Code::let_bind(
        ih_let(7, 1, 6),
        Code::let_bind(
            call_let(8, "IO.println", &[5]),
            Code::fun(
                lambda(9, 10, Code::ret(fv(7))),
                Code::let_bind(call_let(11, "Bind.bind", &[8, 9]), Code::ret(fv(11))),
            ),
        ),
    );

    let sunk = sink_ih_bindings(code, &[fv(7)]);

    assert_eq!(
        top_level_lets(&sunk),
        vec![8, 11],
        "the IH must leave the arm's top-level chain; the println must stay"
    );
    let k = find_fun(&sunk, 9).expect("the continuation survives");
    assert_eq!(
        *k.body,
        Code::let_bind(ih_let(7, 1, 6), Code::ret(fv(7))),
        "the IH is bound inside the continuation, ahead of its use"
    );
}

/// Nested `do`: the IH belongs in the INNERMOST continuation that uses it.
#[test]
fn test_sink_ih_nested_continuations_reaches_the_innermost_user() {
    // let ih := go(rest)
    // let a  := IO.println(head)
    // fun k1 (_) :=
    //   let b := readLine()
    //   fun k2 (_) := return ih
    //   let r2 := Bind.bind(b, k2)
    //   return r2
    // let r1 := Bind.bind(a, k1)
    // return r1
    let inner = Code::let_bind(
        call_let(20, "IO.getLine", &[]),
        Code::fun(
            lambda(21, 22, Code::ret(fv(7))),
            Code::let_bind(call_let(23, "Bind.bind", &[20, 21]), Code::ret(fv(23))),
        ),
    );
    let code = Code::let_bind(
        ih_let(7, 1, 6),
        Code::let_bind(
            call_let(8, "IO.println", &[5]),
            Code::fun(
                lambda(9, 10, inner),
                Code::let_bind(call_let(11, "Bind.bind", &[8, 9]), Code::ret(fv(11))),
            ),
        ),
    );

    let sunk = sink_ih_bindings(code, &[fv(7)]);

    assert_eq!(top_level_lets(&sunk), vec![8, 11]);
    let k1 = find_fun(&sunk, 9).expect("outer continuation");
    assert_eq!(
        top_level_lets(&k1.body),
        vec![20, 23],
        "the IH does not stop in the outer continuation"
    );
    let k2 = find_fun(&k1.body, 21).expect("inner continuation");
    assert_eq!(
        *k2.body,
        Code::let_bind(ih_let(7, 1, 6), Code::ret(fv(7))),
        "the IH lands in the innermost continuation that uses it"
    );
}

/// A pure arm consuming the IH directly (`x + sum rest`) must not move: the
/// binding already dominates its use in the arm's own chain.
#[test]
fn test_sink_ih_direct_use_in_arm_body_is_left_in_place() {
    let code = Code::let_bind(
        ih_let(7, 1, 6),
        Code::let_bind(call_let(8, "Nat.add", &[5, 7]), Code::ret(fv(8))),
    );
    let sunk = sink_ih_bindings(code.clone(), &[fv(7)]);
    assert_eq!(sunk, code, "a directly-consumed IH is not relocated");
}

/// Uses split between the arm body and a lambda: the IH stays outside, because
/// the outer use needs it too.
#[test]
fn test_sink_ih_split_uses_stay_outside_the_lambda() {
    let code = Code::let_bind(
        ih_let(7, 1, 6),
        Code::fun(
            lambda(9, 10, Code::ret(fv(7))),
            Code::let_bind(call_let(11, "Prod.mk", &[7, 9]), Code::ret(fv(11))),
        ),
    );
    let sunk = sink_ih_bindings(code.clone(), &[fv(7)]);
    assert_eq!(sunk, code, "a split-use IH is not relocated");
}

/// A join point may be entered more than once, so a binding is never moved
/// inside one — it stops in front of it.
#[test]
fn test_sink_ih_join_point_body_is_not_a_sink_target() {
    let jp = FunDecl::new(
        fv(9),
        Name::from_string("_jp"),
        vec![Param::new(fv(10), Name::anon(), obj())],
        obj(),
        Code::ret(fv(7)),
    );
    let code = Code::let_bind(
        ih_let(7, 1, 6),
        Code::let_bind(
            call_let(8, "IO.println", &[5]),
            Code::join_point(jp, Code::jmp(fv(9), vec![Arg::FVar(fv(8))])),
        ),
    );
    let sunk = sink_ih_bindings(code, &[fv(7)]);
    assert_eq!(
        top_level_lets(&sunk),
        vec![8, 7],
        "the IH sinks past the println but stops at the join point"
    );
}

/// An unused IH is left exactly where it was: removing a self-call is a
/// semantic change under the eager-effect model, not a cleanup.
#[test]
fn test_sink_ih_unused_binding_is_not_moved_or_dropped() {
    let code = Code::let_bind(
        ih_let(7, 1, 6),
        Code::let_bind(call_let(8, "IO.println", &[5]), Code::ret(fv(8))),
    );
    let sunk = sink_ih_bindings(code.clone(), &[fv(7)]);
    assert_eq!(sunk, code, "an unused IH keeps its position");
}

/// A `Cases` in the way is a hard stop: making the recursive call conditional
/// on a branch is a bigger move than restoring a source position.
#[test]
fn test_sink_ih_cases_alternative_is_not_a_sink_target() {
    let cases = Code::cases(
        Name::from_string("Bool"),
        obj(),
        fv(5),
        vec![
            Alt::ctor(
                Name::from_string("Bool.false"),
                Vec::new(),
                Code::ret(fv(7)),
            ),
            Alt::ctor(Name::from_string("Bool.true"), Vec::new(), Code::ret(fv(7))),
        ],
    );
    let code = Code::let_bind(ih_let(7, 1, 6), cases);
    let sunk = sink_ih_bindings(code.clone(), &[fv(7)]);
    assert_eq!(sunk, code, "the IH stays in front of the Cases");
}

/// Two recursive fields (a binary tree) each sink into their own continuation.
#[test]
fn test_sink_ih_two_hypotheses_each_reach_their_own_lambda() {
    // let ihl := go(left)
    // let ihr := go(right)
    // fun kl (_) := return ihl
    // fun kr (_) := return ihr
    // let r := Bind.bind(kl, kr)
    // return r
    let code = Code::let_bind(
        ih_let(7, 1, 5),
        Code::let_bind(
            ih_let(8, 1, 6),
            Code::fun(
                lambda(9, 10, Code::ret(fv(7))),
                Code::fun(
                    lambda(11, 12, Code::ret(fv(8))),
                    Code::let_bind(call_let(13, "Bind.bind", &[9, 11]), Code::ret(fv(13))),
                ),
            ),
        ),
    );

    let sunk = sink_ih_bindings(code, &[fv(7), fv(8)]);

    assert_eq!(top_level_lets(&sunk), vec![13]);
    assert_eq!(
        *find_fun(&sunk, 9).expect("left continuation").body,
        Code::let_bind(ih_let(7, 1, 5), Code::ret(fv(7)))
    );
    assert_eq!(
        *find_fun(&sunk, 11).expect("right continuation").body,
        Code::let_bind(ih_let(8, 1, 6), Code::ret(fv(8)))
    );
}
