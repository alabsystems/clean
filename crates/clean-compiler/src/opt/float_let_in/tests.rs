// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::lcnf::{Cases, Param};
use clean_kernel::{Expr, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

#[test]
fn test_float_single_binding_into_arm() {
    // let _1 := 42
    // let _2 := 10
    // cases _0 of
    // | True  => return _1
    // | False => return _2
    //
    // Expected: both _1 and _2 float into their respective arms.
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("Nat"),
                LetValue::nat(10),
            ),
            Box::new(Code::Cases(Cases {
                type_name: name("Bool"),
                result_type: Expr::const_str("Nat"),
                scrutinee: fvar(0),
                alts: vec![
                    Alt::Ctor {
                        ctor_name: name("Bool.true"),
                        params: vec![],
                        body: Box::new(Code::Return(fvar(1))),
                    },
                    Alt::Ctor {
                        ctor_name: name("Bool.false"),
                        params: vec![],
                        body: Box::new(Code::Return(fvar(2))),
                    },
                ],
            })),
        )),
    );

    let result = float_let_in_code(&code);
    let s = result.to_string();

    // _1 and _2 should NOT appear before the cases
    // They should be inside their respective arms.
    assert!(
        !s.starts_with("let"),
        "let bindings should be floated into arms, got: {s}"
    );
    assert!(s.contains("Bool.true"), "should have True arm");
    assert!(s.contains("Bool.false"), "should have False arm");
}

#[test]
fn test_keep_binding_used_in_multiple_arms() {
    // let _1 := 42
    // cases _0 of
    // | True  => return _1
    // | False => return _1
    //
    // Expected: _1 stays above the cases (used in both arms).
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Cases(Cases {
            type_name: name("Bool"),
            result_type: Expr::const_str("Nat"),
            scrutinee: fvar(0),
            alts: vec![
                Alt::Ctor {
                    ctor_name: name("Bool.true"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(1))),
                },
                Alt::Ctor {
                    ctor_name: name("Bool.false"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(1))),
                },
            ],
        })),
    );

    let result = float_let_in_code(&code);

    // _1 should be kept above the cases
    if let Code::Let(decl, _) = &result {
        assert_eq!(decl.fvar_id, fvar(1));
    } else {
        panic!("Expected let binding above cases, got: {}", result);
    }
}

#[test]
fn test_scrutinee_not_floated() {
    // let _0 := 42
    // cases _0 of
    // | default => return _0
    //
    // Expected: _0 stays above because it's the scrutinee.
    let code = Code::Let(
        LetDecl::new(
            fvar(0),
            name("_0"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Cases(Cases {
            type_name: name("Nat"),
            result_type: Expr::const_str("Nat"),
            scrutinee: fvar(0),
            alts: vec![Alt::Default(Box::new(Code::Return(fvar(0))))],
        })),
    );

    let result = float_let_in_code(&code);

    if let Code::Let(decl, _) = &result {
        assert_eq!(decl.fvar_id, fvar(0));
    } else {
        panic!("Scrutinee binding should stay above cases");
    }
}

#[test]
fn test_dependency_chain_floats_together() {
    // let _1 := 42
    // let _2 := Nat.succ _1   // _2 depends on _1
    // cases _0 of
    // | True  => return _2
    // | False => return _0
    //
    // Expected: both _1 and _2 float into the True arm.
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("Nat"),
                LetValue::Const {
                    name: name("Nat.succ"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Box::new(Code::Cases(Cases {
                type_name: name("Bool"),
                result_type: Expr::const_str("Nat"),
                scrutinee: fvar(0),
                alts: vec![
                    Alt::Ctor {
                        ctor_name: name("Bool.true"),
                        params: vec![],
                        body: Box::new(Code::Return(fvar(2))),
                    },
                    Alt::Ctor {
                        ctor_name: name("Bool.false"),
                        params: vec![],
                        body: Box::new(Code::Return(fvar(0))),
                    },
                ],
            })),
        )),
    );

    let result = float_let_in_code(&code);
    let s = result.to_string();

    // Neither _1 nor _2 should be at the top level
    assert!(
        !s.starts_with("let"),
        "dependency chain should float into arm, got: {s}"
    );
}

#[test]
fn test_dependency_conflict_keeps_above() {
    // let _1 := 42
    // let _2 := Nat.succ _1   // used in True arm
    // let _3 := Nat.add _1 _1 // used in False arm, also depends on _1
    // cases _0 of
    // | True  => return _2
    // | False => return _3
    //
    // Expected: _1 stays above (used by candidates in different arms).
    // _2 floats into True, _3 floats into False.
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("Nat"),
                LetValue::Const {
                    name: name("Nat.succ"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Box::new(Code::Let(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    Expr::const_str("Nat"),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(1))],
                    },
                ),
                Box::new(Code::Cases(Cases {
                    type_name: name("Bool"),
                    result_type: Expr::const_str("Nat"),
                    scrutinee: fvar(0),
                    alts: vec![
                        Alt::Ctor {
                            ctor_name: name("Bool.true"),
                            params: vec![],
                            body: Box::new(Code::Return(fvar(2))),
                        },
                        Alt::Ctor {
                            ctor_name: name("Bool.false"),
                            params: vec![],
                            body: Box::new(Code::Return(fvar(3))),
                        },
                    ],
                })),
            )),
        )),
    );

    let result = float_let_in_code(&code);

    // _1 should be at the top (kept above, used by both arms indirectly).
    if let Code::Let(decl, rest) = &result {
        assert_eq!(decl.fvar_id, fvar(1), "_1 should be kept above cases");
        // The rest should be a Cases (no more let bindings at top level).
        assert!(
            matches!(rest.as_ref(), Code::Cases(_)),
            "_2 and _3 should be floated into arms, got: {rest}"
        );
    } else {
        panic!("Expected _1 binding above cases, got: {result}");
    }
}

#[test]
fn test_no_cases_passthrough() {
    // let _1 := 42
    // return _1
    //
    // No cases to float into — code unchanged.
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Return(fvar(1))),
    );

    let result = float_let_in_code(&code);
    assert_eq!(result, code);
}

#[test]
fn test_nested_cases_recursion() {
    // let _1 := 42
    // cases _0 of
    // | True =>
    //   let _2 := 10
    //   cases _3 of
    //   | True  => return _2
    //   | False => return _1
    // | False => return _1
    //
    // _1 is used in both outer arms, stays at top.
    // _2 is only used in the inner True arm, floats into it.
    let inner_cases = Code::Cases(Cases {
        type_name: name("Bool"),
        result_type: Expr::const_str("Nat"),
        scrutinee: fvar(3),
        alts: vec![
            Alt::Ctor {
                ctor_name: name("Bool.true"),
                params: vec![],
                body: Box::new(Code::Return(fvar(2))),
            },
            Alt::Ctor {
                ctor_name: name("Bool.false"),
                params: vec![],
                body: Box::new(Code::Return(fvar(1))),
            },
        ],
    });

    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Cases(Cases {
            type_name: name("Bool"),
            result_type: Expr::const_str("Nat"),
            scrutinee: fvar(0),
            alts: vec![
                Alt::Ctor {
                    ctor_name: name("Bool.true"),
                    params: vec![],
                    body: Box::new(Code::Let(
                        LetDecl::new(
                            fvar(2),
                            name("_2"),
                            Expr::const_str("Nat"),
                            LetValue::nat(10),
                        ),
                        Box::new(inner_cases),
                    )),
                },
                Alt::Ctor {
                    ctor_name: name("Bool.false"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(1))),
                },
            ],
        })),
    );

    let result = float_let_in_code(&code);

    // _1 stays at top (used in both outer arms)
    if let Code::Let(decl, _) = &result {
        assert_eq!(decl.fvar_id, fvar(1));
    } else {
        panic!("Expected _1 above outer cases");
    }
}

#[test]
fn test_float_fun_decl_into_arm() {
    // fun _f (a : Nat) := return a
    // cases _0 of
    // | True  => let _1 := _f 42; return _1
    // | False => return _0
    //
    // Expected: _f floats into the True arm.
    let fun_decl = FunDecl::new(
        fvar(10),
        name("_f"),
        vec![Param::new(fvar(11), name("a"), Expr::const_str("Nat"))],
        Expr::const_str("Nat"),
        Code::Return(fvar(11)),
    );

    let code = Code::Fun(
        fun_decl,
        Box::new(Code::Cases(Cases {
            type_name: name("Bool"),
            result_type: Expr::const_str("Nat"),
            scrutinee: fvar(0),
            alts: vec![
                Alt::Ctor {
                    ctor_name: name("Bool.true"),
                    params: vec![],
                    body: Box::new(Code::Let(
                        LetDecl::new(
                            fvar(1),
                            name("_1"),
                            Expr::const_str("Nat"),
                            LetValue::FVar {
                                fvar: fvar(10),
                                args: vec![Arg::FVar(fvar(42))],
                            },
                        ),
                        Box::new(Code::Return(fvar(1))),
                    )),
                },
                Alt::Ctor {
                    ctor_name: name("Bool.false"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(0))),
                },
            ],
        })),
    );

    let result = float_let_in_code(&code);

    // Top-level should be Cases, not Fun.
    assert!(
        matches!(&result, Code::Cases(_)),
        "Fun decl should float into arm, got: {result}"
    );
}

#[test]
fn test_dead_binding_dropped() {
    // let _1 := 42   // not used in any arm
    // cases _0 of
    // | True  => return _0
    // | False => return _0
    //
    // Expected: _1 is dropped (dead code).
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Cases(Cases {
            type_name: name("Bool"),
            result_type: Expr::const_str("Nat"),
            scrutinee: fvar(0),
            alts: vec![
                Alt::Ctor {
                    ctor_name: name("Bool.true"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(0))),
                },
                Alt::Ctor {
                    ctor_name: name("Bool.false"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(0))),
                },
            ],
        })),
    );

    let result = float_let_in_code(&code);
    let s = result.to_string();

    assert!(!s.contains("_x1"), "dead binding should be dropped: {s}");
}
