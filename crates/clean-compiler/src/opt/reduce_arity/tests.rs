// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Level, Name};

/// Helper: create a simple parameter.
fn param(id: u64, name: &str) -> Param {
    Param::new(
        FVarId::new(id),
        Name::from_string(name),
        Expr::sort(Level::zero()),
    )
}

#[test]
fn test_all_params_used() {
    // def f (x y : Nat) : Nat := let r := Nat.add x y; return r
    let x = FVarId::new(1);
    let y = FVarId::new(2);
    let r = FVarId::new(3);
    let body = Code::Let(
        LetDecl::new(
            r,
            Name::from_string("r"),
            Expr::sort(Level::zero()),
            LetValue::Const {
                name: Name::from_string("Nat.add"),
                levels: vec![],
                args: vec![Arg::FVar(x), Arg::FVar(y)],
            },
        ),
        Box::new(Code::Return(r)),
    );
    let decl = Decl::new(
        Name::from_string("f"),
        vec![],
        Expr::sort(Level::zero()),
        vec![param(1, "x"), param(2, "y")],
        body,
        false,
    );

    let result = reduce_arity(&decl);
    assert_eq!(result.len(), 1, "no reduction when all params used");
    assert_eq!(result[0].name, decl.name);
}

#[test]
fn test_one_param_unused() {
    // def f (x y : Nat) : Nat := let r := Nat.add x x; return r
    // y is unused -> should produce f._redArg + wrapper
    let x = FVarId::new(1);
    let r = FVarId::new(3);
    let body = Code::Let(
        LetDecl::new(
            r,
            Name::from_string("r"),
            Expr::sort(Level::zero()),
            LetValue::Const {
                name: Name::from_string("Nat.add"),
                levels: vec![],
                args: vec![Arg::FVar(x), Arg::FVar(x)],
            },
        ),
        Box::new(Code::Return(r)),
    );
    let decl = Decl::new(
        Name::from_string("f"),
        vec![],
        Expr::sort(Level::zero()),
        vec![param(1, "x"), param(2, "y")],
        body,
        false,
    );

    let result = reduce_arity(&decl);
    assert_eq!(result.len(), 2, "should produce aux + wrapper");

    let aux = &result[0];
    assert_eq!(aux.name, Name::from_string("f").str("_redArg"));
    assert_eq!(aux.params.len(), 1, "aux has only used params");
    assert_eq!(aux.params[0].fvar_id, x);

    let wrapper = &result[1];
    assert_eq!(wrapper.name, Name::from_string("f"));
    assert_eq!(wrapper.params.len(), 2, "wrapper keeps all params");
}

#[test]
fn test_recursive_pass_through() {
    // def f (x y : Nat) : Nat :=
    //   cases x
    //   | zero => return x
    //   | succ k =>
    //     let _1 := f k y   -- y is pass-through
    //     let _2 := Nat.mul _1 _1
    //     return _2
    let x = FVarId::new(1);
    let y = FVarId::new(2);
    let k = FVarId::new(10);
    let t1 = FVarId::new(11);
    let t2 = FVarId::new(12);

    let succ_body = Code::Let(
        LetDecl::new(
            t1,
            Name::from_string("_1"),
            Expr::sort(Level::zero()),
            LetValue::Const {
                name: Name::from_string("f"),
                levels: vec![],
                args: vec![Arg::FVar(k), Arg::FVar(y)],
            },
        ),
        Box::new(Code::Let(
            LetDecl::new(
                t2,
                Name::from_string("_2"),
                Expr::sort(Level::zero()),
                LetValue::Const {
                    name: Name::from_string("Nat.mul"),
                    levels: vec![],
                    args: vec![Arg::FVar(t1), Arg::FVar(t1)],
                },
            ),
            Box::new(Code::Return(t2)),
        )),
    );

    let body = Code::Cases(Cases::new(
        Name::from_string("Nat"),
        Expr::sort(Level::zero()),
        x,
        vec![
            Alt::ctor(Name::from_string("Nat.zero"), vec![], Code::Return(x)),
            Alt::ctor(
                Name::from_string("Nat.succ"),
                vec![param(10, "k")],
                succ_body,
            ),
        ],
    ));

    let decl = Decl::new(
        Name::from_string("f"),
        vec![],
        Expr::sort(Level::zero()),
        vec![param(1, "x"), param(2, "y")],
        body,
        true,
    );

    let result = reduce_arity(&decl);
    assert_eq!(result.len(), 2, "y is pass-through, should reduce");

    let aux = &result[0];
    assert_eq!(aux.params.len(), 1);
    assert_eq!(aux.params[0].fvar_id, x);

    // Verify recursive call in aux body targets f._redArg
    fn find_self_call(code: &Code) -> Option<Name> {
        match code {
            Code::Let(decl, body) => {
                if let LetValue::Const { name, .. } = &decl.value {
                    if name.to_string().contains("_redArg") {
                        return Some(name.clone());
                    }
                }
                find_self_call(body)
            }
            Code::Cases(cases) => {
                for alt in &cases.alts {
                    match alt {
                        Alt::Ctor { body, .. } | Alt::Default(body) => {
                            if let Some(n) = find_self_call(body) {
                                return Some(n);
                            }
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    let call_name = find_self_call(match &aux.body {
        DeclValue::Code(c) => c,
        _ => panic!("expected code body"),
    });
    assert!(call_name.is_some(), "recursive call should target _redArg");
}

#[test]
fn test_no_params() {
    let body = Code::Return(FVarId::new(1));
    let decl = Decl::new(
        Name::from_string("f"),
        vec![],
        Expr::sort(Level::zero()),
        vec![],
        body,
        false,
    );

    let result = reduce_arity(&decl);
    assert_eq!(result.len(), 1);
}

#[test]
fn test_extern_decl() {
    let decl = Decl::extern_decl(
        Name::from_string("g"),
        vec![],
        Expr::sort(Level::zero()),
        vec![param(1, "x")],
        vec![],
    );
    let result = reduce_arity(&decl);
    assert_eq!(result.len(), 1);
}

#[test]
fn test_batch_reduce() {
    // Two decls, one with unused param, one without.
    let x = FVarId::new(1);
    let y = FVarId::new(2);
    let r = FVarId::new(3);

    let body1 = Code::Let(
        LetDecl::new(
            r,
            Name::from_string("r"),
            Expr::sort(Level::zero()),
            LetValue::Const {
                name: Name::from_string("Nat.add"),
                levels: vec![],
                args: vec![Arg::FVar(x), Arg::FVar(x)],
            },
        ),
        Box::new(Code::Return(r)),
    );
    let decl1 = Decl::new(
        Name::from_string("f"),
        vec![],
        Expr::sort(Level::zero()),
        vec![param(1, "x"), param(2, "y")],
        body1,
        false,
    );

    let body2 = Code::Let(
        LetDecl::new(
            r,
            Name::from_string("r"),
            Expr::sort(Level::zero()),
            LetValue::Const {
                name: Name::from_string("Nat.add"),
                levels: vec![],
                args: vec![Arg::FVar(x), Arg::FVar(y)],
            },
        ),
        Box::new(Code::Return(r)),
    );
    let decl2 = Decl::new(
        Name::from_string("g"),
        vec![],
        Expr::sort(Level::zero()),
        vec![param(1, "x"), param(2, "y")],
        body2,
        false,
    );

    let result = reduce_arity_all(&[decl1, decl2]);
    // decl1 expands to 2, decl2 stays 1
    assert_eq!(result.len(), 3);
}

#[test]
fn test_all_params_unused_no_reduction() {
    // def f (x y : Nat) : Nat := return 42
    // Neither x nor y is used. Per Lean 4 spec, if used.len() == 0
    // we do NOT reduce (would promote to constant, possibly executing
    // unreachable code).
    let r = FVarId::new(99);
    let body = Code::Return(r);
    let decl = Decl::new(
        Name::from_string("f"),
        vec![],
        Expr::sort(Level::zero()),
        vec![param(1, "x"), param(2, "y")],
        body,
        false,
    );

    let result = reduce_arity(&decl);
    assert_eq!(result.len(), 1, "no reduction when zero params used");
}
