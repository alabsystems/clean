// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::{LetDecl, LetValue, Param};
use clean_kernel::{Expr, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

#[test]
fn test_extend_small_literal_into_jp() {
    // let x := 42
    // jp j (a) := Nat.add x a; ret _1
    // jmp j y
    // -> x duplicated into jp as extra param

    let x_decl = LetDecl::new(fvar(1), name("x"), nat_type(), LetValue::nat(42));

    let jp_body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("_1"),
            nat_type(),
            LetValue::Const {
                name: Name::from_string("Nat.add"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(20))],
            },
        ),
        Code::ret(fvar(10)),
    );

    let jp_decl = FunDecl::new(
        fvar(2),
        name("j"),
        vec![Param::new(fvar(20), name("a"), nat_type())],
        nat_type(),
        jp_body,
    );

    let jmp = Code::jmp(fvar(2), vec![Arg::FVar(fvar(30))]);
    let code = Code::let_bind(x_decl, Code::join_point(jp_decl, jmp));
    let result = extend_jp_context_in_code(&code);

    match &result {
        Code::Let(x_let, rest) => {
            assert_eq!(x_let.fvar_id, fvar(1));
            match rest.as_ref() {
                Code::JoinPoint(jp, body) => {
                    assert_eq!(jp.params.len(), 2, "expected 2 params after extension");
                    assert_eq!(jp.params[1].fvar_id, fvar(20));
                    assert_ne!(jp.params[0].fvar_id, fvar(1));

                    // jp body starts with duplicated let
                    match jp.body.as_ref() {
                        Code::Let(dup, _) => {
                            assert_eq!(dup.fvar_id, jp.params[0].fvar_id);
                            assert_eq!(dup.value, LetValue::nat(42));
                        }
                        other => panic!("expected Let, got {:?}", other),
                    }

                    // Jmp has extra arg prepended
                    match body.as_ref() {
                        Code::Jmp { args, .. } => {
                            assert_eq!(args.len(), 2);
                            assert_eq!(args[0], Arg::FVar(fvar(1)));
                            assert_eq!(args[1], Arg::FVar(fvar(30)));
                        }
                        other => panic!("expected Jmp, got {:?}", other),
                    }
                }
                other => panic!("expected JoinPoint, got {:?}", other),
            }
        }
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_no_extension_for_large_value() {
    // let x := f a b c (not small)
    // jp j (a) := ... uses x ...
    // -> should NOT extend

    let x_decl = LetDecl::new(
        fvar(1),
        name("x"),
        nat_type(),
        LetValue::FVar {
            fvar: fvar(50),
            args: vec![Arg::FVar(fvar(51)), Arg::FVar(fvar(52))],
        },
    );

    let jp_body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("_1"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(1),
                args: vec![],
            },
        ),
        Code::ret(fvar(10)),
    );

    let jp_decl = FunDecl::new(
        fvar(2),
        name("j"),
        vec![Param::new(fvar(20), name("a"), nat_type())],
        nat_type(),
        jp_body,
    );

    let code = Code::let_bind(
        x_decl,
        Code::join_point(jp_decl, Code::jmp(fvar(2), vec![Arg::FVar(fvar(30))])),
    );
    let result = extend_jp_context_in_code(&code);

    match &result {
        Code::Let(_, rest) => match rest.as_ref() {
            Code::JoinPoint(jp, _) => {
                assert_eq!(jp.params.len(), 1, "should NOT extend large values");
            }
            other => panic!("expected JoinPoint, got {:?}", other),
        },
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_no_extension_when_binding_unused() {
    let x_decl = LetDecl::new(fvar(1), name("x"), nat_type(), LetValue::nat(42));
    let jp_decl = FunDecl::new(
        fvar(2),
        name("j"),
        vec![Param::new(fvar(20), name("a"), nat_type())],
        nat_type(),
        Code::ret(fvar(20)),
    );

    let code = Code::let_bind(
        x_decl,
        Code::join_point(jp_decl, Code::jmp(fvar(2), vec![Arg::FVar(fvar(30))])),
    );
    let result = extend_jp_context_in_code(&code);

    match &result {
        Code::Let(_, rest) => match rest.as_ref() {
            Code::JoinPoint(jp, _) => {
                assert_eq!(jp.params.len(), 1, "should NOT extend unused binding");
            }
            other => panic!("expected JoinPoint, got {:?}", other),
        },
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_fun_boundary_clears_candidates() {
    // let x := 42; fun f (a) := { jp j (b) := uses x; jmp j a }; ret 99
    // x should NOT be extended into j (fun boundary)

    let jp_body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("_1"),
            nat_type(),
            LetValue::Const {
                name: Name::from_string("Nat.add"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(21))],
            },
        ),
        Code::ret(fvar(10)),
    );
    let jp_decl = FunDecl::new(
        fvar(3),
        name("j"),
        vec![Param::new(fvar(21), name("b"), nat_type())],
        nat_type(),
        jp_body,
    );
    let fun_body = Code::join_point(jp_decl, Code::jmp(fvar(3), vec![Arg::FVar(fvar(20))]));
    let fun_decl = FunDecl::new(
        fvar(2),
        name("f"),
        vec![Param::new(fvar(20), name("a"), nat_type())],
        nat_type(),
        fun_body,
    );
    let x_decl = LetDecl::new(fvar(1), name("x"), nat_type(), LetValue::nat(42));
    let code = Code::let_bind(x_decl, Code::fun(fun_decl, Code::ret(fvar(99))));
    let result = extend_jp_context_in_code(&code);

    match &result {
        Code::Let(_, rest) => match rest.as_ref() {
            Code::Fun(fd, _) => match fd.body.as_ref() {
                Code::JoinPoint(jp, _) => {
                    assert_eq!(jp.params.len(), 1, "should NOT extend across fun boundary");
                }
                other => panic!("expected JoinPoint, got {:?}", other),
            },
            other => panic!("expected Fun, got {:?}", other),
        },
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_projection_is_small() {
    // The projection `x := proj Pair 0 p` depends on `p`, which is
    // a parameter of the join point so it's in scope.
    let x_decl = LetDecl::new(
        fvar(1),
        name("x"),
        nat_type(),
        LetValue::Proj {
            type_name: Name::from_string("Pair"),
            idx: 0,
            structure: fvar(20),
        },
    );
    let jp_body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("_1"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(1),
                args: vec![],
            },
        ),
        Code::ret(fvar(10)),
    );
    let jp_decl = FunDecl::new(
        fvar(2),
        name("j"),
        vec![Param::new(fvar(20), name("a"), nat_type())],
        nat_type(),
        jp_body,
    );
    let code = Code::let_bind(
        x_decl,
        Code::join_point(jp_decl, Code::jmp(fvar(2), vec![Arg::FVar(fvar(30))])),
    );
    let result = extend_jp_context_in_code(&code);

    match &result {
        Code::Let(_, rest) => match rest.as_ref() {
            Code::JoinPoint(jp, _) => {
                assert_eq!(jp.params.len(), 2, "projection should be extended");
            }
            other => panic!("expected JoinPoint, got {:?}", other),
        },
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_multiple_jmp_sites_all_get_extra_args() {
    let x_decl = LetDecl::new(fvar(1), name("x"), nat_type(), LetValue::nat(42));
    let jp_body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("_1"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(1),
                args: vec![],
            },
        ),
        Code::ret(fvar(10)),
    );
    let jp_decl = FunDecl::new(
        fvar(2),
        name("j"),
        vec![Param::new(fvar(20), name("a"), nat_type())],
        nat_type(),
        jp_body,
    );
    let cases_code = Code::Cases(Cases {
        type_name: Name::from_string("Bool"),
        result_type: nat_type(),
        scrutinee: fvar(40),
        alts: vec![
            Alt::ctor(
                Name::from_string("Bool.true"),
                vec![],
                Code::jmp(fvar(2), vec![Arg::FVar(fvar(30))]),
            ),
            Alt::ctor(
                Name::from_string("Bool.false"),
                vec![],
                Code::jmp(fvar(2), vec![Arg::FVar(fvar(31))]),
            ),
        ],
    });
    let code = Code::let_bind(x_decl, Code::join_point(jp_decl, cases_code));
    let result = extend_jp_context_in_code(&code);

    match &result {
        Code::Let(_, rest) => match rest.as_ref() {
            Code::JoinPoint(jp, body) => {
                assert_eq!(jp.params.len(), 2);
                match body.as_ref() {
                    Code::Cases(cases) => {
                        for alt in &cases.alts {
                            match alt {
                                Alt::Ctor { body, .. } => match body.as_ref() {
                                    Code::Jmp { args, .. } => {
                                        assert_eq!(args.len(), 2);
                                        assert_eq!(args[0], Arg::FVar(fvar(1)));
                                    }
                                    other => panic!("expected Jmp, got {:?}", other),
                                },
                                _ => panic!("expected Ctor alt"),
                            }
                        }
                    }
                    other => panic!("expected Cases, got {:?}", other),
                }
            }
            other => panic!("expected JoinPoint, got {:?}", other),
        },
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_decl_level_entry_point() {
    let code = Code::ret(fvar(1));
    let decl = Decl::new(
        Name::from_string("test"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(1), name("x"), nat_type())],
        code.clone(),
        false,
    );
    let result = extend_jp_context(&decl);
    assert_eq!(result.name, Name::from_string("test"));
    match &result.body {
        DeclValue::Code(c) => assert_eq!(c.as_ref(), &code),
        _ => panic!("expected Code body"),
    }
}

#[test]
fn test_extern_decl_unchanged() {
    let decl = Decl::extern_decl(Name::from_string("ext"), vec![], nat_type(), vec![], vec![]);
    let result = extend_jp_context(&decl);
    assert!(result.is_extern());
}
