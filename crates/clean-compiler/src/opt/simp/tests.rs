// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::{Alt, Arg, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

fn bool_type() -> Expr {
    Expr::const_str("Bool")
}

/// Trivial case elimination: when the scrutinee is a known constructor,
/// the matching alternative body is inlined with pattern vars substituted.
#[test]
fn test_simp_trivial_case_elimination() {
    // let _1 := Bool.true
    // cases _1 of
    // | Bool.true => return _1
    // | Bool.false => return _1
    // Expected: the Bool.true branch is selected → return _1
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            bool_type(),
            LetValue::Ctor {
                name: name("Bool.true"),
                levels: vec![],
                args: vec![],
            },
        ),
        Code::cases(
            name("Bool"),
            bool_type(),
            fvar(1),
            vec![
                Alt::ctor(name("Bool.true"), vec![], Code::ret(fvar(1))),
                Alt::ctor(name("Bool.false"), vec![], Code::ret(fvar(1))),
            ],
        ),
    );

    let result = simp_in_code(&code);

    // After simplification: let _1 := Bool.true; return _1
    if let Code::Let(decl, body) = &result {
        assert_eq!(decl.fvar_id, fvar(1));
        assert!(matches!(body.as_ref(), Code::Return(fv) if *fv == fvar(1)));
    } else {
        panic!("Expected Let after trivial case elimination, got: {result:?}");
    }
}

/// Trivial case elimination with pattern variable substitution:
/// ctor args are mapped onto the pattern params in the matching alt.
#[test]
fn test_simp_trivial_case_with_pattern_subst() {
    // let _1 := Prod.mk _a _b
    // cases _1 of
    // | Prod.mk x y => return x
    // Expected: return _a (x is substituted with _a)
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            nat_type(),
            LetValue::Ctor {
                name: name("Prod.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
            },
        ),
        Code::cases(
            name("Prod"),
            nat_type(),
            fvar(1),
            vec![Alt::ctor(
                name("Prod.mk"),
                vec![
                    Param::new(fvar(20), name("x"), nat_type()),
                    Param::new(fvar(21), name("y"), nat_type()),
                ],
                Code::ret(fvar(20)),
            )],
        ),
    );

    let result = simp_in_code(&code);

    // After: let _1 := Prod.mk _a _b; return _a
    if let Code::Let(_, body) = &result {
        assert!(
            matches!(body.as_ref(), Code::Return(fv) if *fv == fvar(10)),
            "Expected return _a (fvar 10), got: {body:?}"
        );
    } else {
        panic!("Expected Let wrapping a Return, got: {result:?}");
    }
}

/// Eta reduction: `fun f(x) := g x` simplifies to aliasing f = g in
/// the continuation, so uses of f become uses of g.
#[test]
fn test_simp_eta_reduction() {
    // fun f(x) := let tmp := g x; return tmp
    // let _r := f _a
    // return _r
    // Expected: f is eliminated, _r := g _a
    let fun_body = Code::let_bind(
        LetDecl::new(
            fvar(50),
            name("tmp"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(99),                  // g
                args: vec![Arg::FVar(fvar(30))], // x
            },
        ),
        Code::ret(fvar(50)),
    );
    let code = Code::fun(
        FunDecl::new(
            fvar(40),
            name("f"),
            vec![Param::new(fvar(30), name("x"), nat_type())],
            nat_type(),
            fun_body,
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(60),
                name("_r"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(40),                  // f
                    args: vec![Arg::FVar(fvar(10))], // _a
                },
            ),
            Code::ret(fvar(60)),
        ),
    );

    let result = simp_in_code(&code);

    // After eta reduction, f is replaced by g in the continuation.
    // So we expect: let _r := g _a; return _r
    if let Code::Let(decl, _) = &result {
        if let LetValue::FVar { fvar: callee, .. } = &decl.value {
            assert_eq!(
                *callee,
                fvar(99),
                "Expected call to g (fvar 99) after eta reduction"
            );
            return;
        }
    }
    panic!("Expected eta-reduced code calling g, got: {result:?}");
}

/// Let flattening: lets from nested code are properly chained.
/// `let a := v1; let b := v2; return b` stays flat after simp.
#[test]
fn test_simp_let_flattening_preserves_chain() {
    // let _1 := 42
    // let _2 := Nat.succ _1
    // return _2
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_2"),
                nat_type(),
                LetValue::Const {
                    name: name("Nat.succ"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let result = simp_in_code(&code);

    // Structure should be preserved (no unnecessary changes).
    if let Code::Let(d1, rest) = &result {
        assert_eq!(d1.fvar_id, fvar(1));
        if let Code::Let(d2, rest2) = rest.as_ref() {
            assert_eq!(d2.fvar_id, fvar(2));
            assert!(matches!(rest2.as_ref(), Code::Return(fv) if *fv == fvar(2)));
            return;
        }
    }
    panic!("Expected preserved let chain, got: {result:?}");
}

/// The simp pass applied to a full Decl: verifies the public `simp` API
/// works end-to-end with trivial case elimination.
#[test]
fn test_simp_decl_api() {
    let body = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            bool_type(),
            LetValue::Ctor {
                name: name("Bool.false"),
                levels: vec![],
                args: vec![],
            },
        ),
        Code::cases(
            name("Bool"),
            nat_type(),
            fvar(1),
            vec![
                Alt::ctor(
                    name("Bool.true"),
                    vec![],
                    Code::let_bind(
                        LetDecl::new(fvar(2), name("t"), nat_type(), LetValue::nat(1)),
                        Code::ret(fvar(2)),
                    ),
                ),
                Alt::ctor(
                    name("Bool.false"),
                    vec![],
                    Code::let_bind(
                        LetDecl::new(fvar(3), name("f"), nat_type(), LetValue::nat(0)),
                        Code::ret(fvar(3)),
                    ),
                ),
            ],
        ),
    );

    let decl = Decl::new(name("test_fn"), vec![], nat_type(), vec![], body, false);
    let simplified = simp(&decl);

    // The Bool.false branch should be selected.
    if let DeclValue::Code(code) = &simplified.body {
        if let Code::Let(_, inner) = code.as_ref() {
            if let Code::Let(d, _) = inner.as_ref() {
                assert_eq!(d.fvar_id, fvar(3), "Expected false branch (fvar 3)");
                return;
            }
        }
    }
    panic!("Expected false branch inlined in decl, got: {simplified:?}");
}

/// Simplifying code that is already terminal (Return, Jmp, Unreachable)
/// should return it unchanged.
#[test]
fn test_simp_terminals_unchanged() {
    let ret = Code::ret(fvar(1));
    assert_eq!(simp_in_code(&ret), ret);

    let jmp = Code::jmp(fvar(5), vec![Arg::FVar(fvar(1))]);
    assert_eq!(simp_in_code(&jmp), jmp);

    let unr = Code::Unreachable(nat_type());
    assert_eq!(simp_in_code(&unr), unr);
}

/// No eta reduction when the parameter appears free in the callee
/// (i.e., `fun f(x) := x x` must NOT reduce).
#[test]
fn test_simp_no_eta_when_param_is_callee() {
    // fun f(x) := let tmp := x x; return tmp
    // return f
    // x appears as both callee and arg — no eta reduction.
    let fun_body = Code::let_bind(
        LetDecl::new(
            fvar(50),
            name("tmp"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(30), // x (the param itself)
                args: vec![Arg::FVar(fvar(30))],
            },
        ),
        Code::ret(fvar(50)),
    );
    let code = Code::fun(
        FunDecl::new(
            fvar(40),
            name("f"),
            vec![Param::new(fvar(30), name("x"), nat_type())],
            nat_type(),
            fun_body,
        ),
        Code::ret(fvar(40)),
    );

    let result = simp_in_code(&code);

    // The Fun node must be preserved (no eta reduction).
    assert!(
        matches!(&result, Code::Fun(..)),
        "Expected Fun to be preserved when param is callee, got: {result:?}"
    );
}
