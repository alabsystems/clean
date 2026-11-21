// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! X4 R6: CSE never merges two runs of an action.

use super::*;
use clean_kernel::{BinderInfo, Expr, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn io(ty: Expr) -> Expr {
    Expr::app(Expr::const_str("IO"), ty)
}

/// `_1 := v; _2 := v; _3 := Prod.mk _1 _2; return _3`, both bindings at `ty`.
fn twice(ty: Expr, value: LetValue) -> Code {
    let bind = |id: u64, rest: Code| {
        Code::Let(
            LetDecl::new(fvar(id), Name::anon(), ty.clone(), value.clone()),
            Box::new(rest),
        )
    };
    bind(
        1,
        bind(
            2,
            Code::Let(
                LetDecl::new(
                    fvar(3),
                    Name::anon(),
                    Expr::const_str("_"),
                    LetValue::Const {
                        name: Name::from_string("Prod.mk"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Box::new(Code::Return(fvar(3))),
            ),
        ),
    )
}

/// The number of `Let`s in a straight-line chain.
fn lets(code: &Code) -> usize {
    match code {
        Code::Let(_, rest) => 1 + lets(rest),
        _ => 0,
    }
}

fn println_hi() -> LetValue {
    LetValue::Const {
        name: Name::from_string("IO.println"),
        levels: vec![],
        args: vec![Arg::FVar(fvar(0))],
    }
}

#[test]
fn test_cse_two_printlns_both_run() {
    let code = twice(io(Expr::const_str("Unit")), println_hi());
    let out = eliminate_common_subexpressions_in_code(&code);
    assert_eq!(lets(&out), 3, "both prints stay:\n{out}");
}

#[test]
fn test_cse_two_runs_of_an_action_ih_both_run() {
    // `ih (); ih ()` after R1.2: two `go(pred, unit)` calls at `IO Nat`, and
    // the thunked spelling `Unit → IO Nat`.
    let call = LetValue::FVar {
        fvar: fvar(9),
        args: vec![Arg::FVar(fvar(0)), Arg::Erased],
    };
    for ty in [
        io(Expr::const_str("Nat")),
        Expr::pi(
            BinderInfo::Default,
            Expr::const_str("Unit"),
            io(Expr::const_str("Nat")),
        ),
    ] {
        let out = eliminate_common_subexpressions_in_code(&twice(ty, call.clone()));
        assert_eq!(lets(&out), 3, "both runs stay:\n{out}");
    }
}

#[test]
fn test_cse_pure_calls_still_merge() {
    // Control: the same two calls at a pure type are one.
    let out = eliminate_common_subexpressions_in_code(&twice(Expr::const_str("Nat"), println_hi()));
    assert_eq!(lets(&out), 2, "a pure duplicate merges:\n{out}");
}
