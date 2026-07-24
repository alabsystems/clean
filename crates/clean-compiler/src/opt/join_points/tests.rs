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
fn test_tail_call_converted_to_join_point() {
    // fun loop (n : Nat) : Nat := return n
    // let _1 := loop 42
    // return _1
    //
    // Should become:
    // jp loop (n : Nat) : Nat := return n
    // jmp loop 42

    let loop_body = Code::ret(fvar(10)); // return n (param)
    let loop_decl = FunDecl::new(
        fvar(1),
        name("loop"),
        vec![Param::new(fvar(10), name("n"), nat_type())],
        nat_type(),
        loop_body,
    );

    let call = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("_1"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(1),
                args: vec![Arg::FVar(fvar(100))], // some arg
            },
        ),
        Code::ret(fvar(2)),
    );

    let code = Code::fun(loop_decl, call);
    let result = find_join_points_in_code(&code);

    // Check it became a join point
    match result {
        Code::JoinPoint(fdecl, body) => {
            assert_eq!(fdecl.fvar_id, fvar(1));
            // Check body is now a jump
            match body.as_ref() {
                Code::Jmp { jp, .. } => {
                    assert_eq!(*jp, fvar(1));
                }
                _ => panic!("Expected Jmp, got {:?}", body),
            }
        }
        _ => panic!("Expected JoinPoint, got {:?}", result),
    }
}

#[test]
fn test_non_tail_call_not_converted() {
    // fun f (n : Nat) : Nat := return n
    // let _1 := f 42
    // let _2 := Nat.add _1 1
    // return _2
    //
    // `f` is NOT in tail position, should remain a Fun

    let f_body = Code::ret(fvar(10));
    let f_decl = FunDecl::new(
        fvar(1),
        name("f"),
        vec![Param::new(fvar(10), name("n"), nat_type())],
        nat_type(),
        f_body,
    );

    let call = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("_1"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(1),
                args: vec![Arg::FVar(fvar(100))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(3),
                name("_2"),
                nat_type(),
                LetValue::Const {
                    name: name("Nat.add"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(101))],
                },
            ),
            Code::ret(fvar(3)),
        ),
    );

    let code = Code::fun(f_decl, call);
    let result = find_join_points_in_code(&code);

    // Should remain a Fun
    match result {
        Code::Fun(fdecl, _) => {
            assert_eq!(fdecl.fvar_id, fvar(1));
        }
        _ => panic!("Expected Fun, got {:?}", result),
    }
}

#[test]
fn test_escaping_function_not_converted() {
    // fun f (n : Nat) : Nat := return n
    // let _1 := g f  -- f escapes as argument
    // return _1
    //
    // `f` escapes, should remain a Fun

    let f_body = Code::ret(fvar(10));
    let f_decl = FunDecl::new(
        fvar(1),
        name("f"),
        vec![Param::new(fvar(10), name("n"), nat_type())],
        nat_type(),
        f_body,
    );

    let call = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("_1"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(50),                 // g
                args: vec![Arg::FVar(fvar(1))], // f passed as arg
            },
        ),
        Code::ret(fvar(2)),
    );

    let code = Code::fun(f_decl, call);
    let result = find_join_points_in_code(&code);

    // Should remain a Fun
    match result {
        Code::Fun(fdecl, _) => {
            assert_eq!(fdecl.fvar_id, fvar(1));
        }
        _ => panic!("Expected Fun, got {:?}", result),
    }
}

#[test]
fn test_multiple_tail_calls_in_branches() {
    // fun loop (n : Nat) : Nat := return n
    // cases x of
    //   | zero => let _1 := loop 0; return _1
    //   | succ => let _2 := loop 1; return _2
    //
    // Both calls are in tail position, should convert

    let loop_body = Code::ret(fvar(10));
    let loop_decl = FunDecl::new(
        fvar(1),
        name("loop"),
        vec![Param::new(fvar(10), name("n"), nat_type())],
        nat_type(),
        loop_body,
    );

    let zero_branch = Code::let_bind(
        LetDecl::new(
            fvar(20),
            name("_1"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(1),
                args: vec![Arg::FVar(fvar(100))],
            },
        ),
        Code::ret(fvar(20)),
    );

    let succ_branch = Code::let_bind(
        LetDecl::new(
            fvar(21),
            name("_2"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(1),
                args: vec![Arg::FVar(fvar(101))],
            },
        ),
        Code::ret(fvar(21)),
    );

    let cases = Code::Cases(Cases::new(
        name("Nat"),
        nat_type(),
        fvar(50),
        vec![
            Alt::ctor(name("Nat.zero"), vec![], zero_branch),
            Alt::ctor(name("Nat.succ"), vec![], succ_branch),
        ],
    ));

    let code = Code::fun(loop_decl, cases);
    let result = find_join_points_in_code(&code);

    // Should become a join point
    match result {
        Code::JoinPoint(fdecl, body) => {
            assert_eq!(fdecl.fvar_id, fvar(1));
            // Check that case branches became jumps
            if let Code::Cases(cases) = body.as_ref() {
                for alt in &cases.alts {
                    if let Alt::Ctor { body, .. } = alt {
                        assert!(
                            matches!(body.as_ref(), Code::Jmp { jp, .. } if *jp == fvar(1)),
                            "Expected Jmp in branch, got {:?}",
                            body
                        );
                    }
                }
            }
        }
        _ => panic!("Expected JoinPoint, got {:?}", result),
    }
}

#[test]
fn test_partial_application_not_converted() {
    // fun f (x : Nat) (y : Nat) : Nat := return x
    // let _1 := f 42  -- partial application (missing y)
    // return _1
    //
    // `f` is not fully applied, should remain a Fun

    let f_body = Code::ret(fvar(10));
    let f_decl = FunDecl::new(
        fvar(1),
        name("f"),
        vec![
            Param::new(fvar(10), name("x"), nat_type()),
            Param::new(fvar(11), name("y"), nat_type()),
        ],
        nat_type(),
        f_body,
    );

    let call = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("_1"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(1),
                args: vec![Arg::FVar(fvar(100))], // only 1 arg, needs 2
            },
        ),
        Code::ret(fvar(2)),
    );

    let code = Code::fun(f_decl, call);
    let result = find_join_points_in_code(&code);

    // Should remain a Fun due to partial application
    match result {
        Code::Fun(fdecl, _) => {
            assert_eq!(fdecl.fvar_id, fvar(1));
        }
        _ => panic!("Expected Fun due to partial application, got {:?}", result),
    }
}

#[test]
fn test_scrutinee_escape_not_converted() {
    // fun f () : Nat := return 0
    // cases f of  -- f is the scrutinee, escapes
    //   | _ => return 1
    //
    // `f` escapes as scrutinee, should remain a Fun

    let f_body = Code::ret(fvar(10));
    let f_decl = FunDecl::new(fvar(1), name("f"), vec![], nat_type(), f_body);

    let cases = Code::Cases(Cases::new(
        name("Nat"),
        nat_type(),
        fvar(1), // scrutinee is the function itself
        vec![Alt::default(Code::ret(fvar(100)))],
    ));

    let code = Code::fun(f_decl, cases);
    let result = find_join_points_in_code(&code);

    // Should remain a Fun because f escapes as scrutinee
    match result {
        Code::Fun(fdecl, _) => {
            assert_eq!(fdecl.fvar_id, fvar(1));
        }
        _ => panic!("Expected Fun due to scrutinee escape, got {:?}", result),
    }
}

#[test]
fn test_call_in_nested_function_not_converted() {
    // fun outer (n : Nat) : Nat := return n
    // fun inner () : Nat :=
    //   let _1 := outer 42  -- NOT a tail call of the outer scope
    //   return _1
    // let _2 := inner ()
    // return _2
    //
    // `outer` is called from nested function, not in tail position of outer scope

    let outer_body = Code::ret(fvar(10));
    let outer_decl = FunDecl::new(
        fvar(1),
        name("outer"),
        vec![Param::new(fvar(10), name("n"), nat_type())],
        nat_type(),
        outer_body,
    );

    // inner calls outer (looks like tail call inside inner, but not valid jp)
    let inner_body = Code::let_bind(
        LetDecl::new(
            fvar(20),
            name("_1"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(1), // outer
                args: vec![Arg::FVar(fvar(100))],
            },
        ),
        Code::ret(fvar(20)),
    );

    let inner_decl = FunDecl::new(fvar(2), name("inner"), vec![], nat_type(), inner_body);

    // outer scope: call inner in tail position
    let call_inner = Code::let_bind(
        LetDecl::new(
            fvar(30),
            name("_2"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(2), // inner
                args: vec![],
            },
        ),
        Code::ret(fvar(30)),
    );

    let code = Code::fun(outer_decl, Code::fun(inner_decl, call_inner));
    let result = find_join_points_in_code(&code);

    // outer should remain a Fun (called from nested function)
    // inner can become a join point (tail called from outer scope)
    match &result {
        Code::Fun(fdecl, body) => {
            assert_eq!(fdecl.fvar_id, fvar(1), "outer should remain Fun");
            // inner should become a join point
            match body.as_ref() {
                Code::JoinPoint(inner_fdecl, _) => {
                    assert_eq!(
                        inner_fdecl.fvar_id,
                        fvar(2),
                        "inner should become JoinPoint"
                    );
                }
                _ => panic!("inner should become JoinPoint, got {:?}", body),
            }
        }
        _ => panic!("outer should remain Fun, got {:?}", result),
    }
}
