// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::Param;
use clean_kernel::{Expr, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

#[test]
fn test_code_size() {
    // Simple return
    let code = Code::Return(fvar(0));
    assert_eq!(code_size(&code), 1);

    // let x := 42; return x
    let code = Code::Let(
        LetDecl::new(
            fvar(0),
            name("x"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Return(fvar(0))),
    );
    assert_eq!(code_size(&code), 2);
}

#[test]
fn test_inline_simple() {
    // fun f () := return 42
    // let x := f()
    // return x
    //
    // After inlining:
    // let x := 42
    // return x
    let fun_decl = FunDecl {
        fvar_id: fvar(0),
        name: name("f"),
        params: vec![],
        ty: Expr::const_str("Nat"),
        body: Box::new(Code::Let(
            LetDecl::new(
                fvar(10),
                name("_"),
                Expr::const_str("Nat"),
                LetValue::nat(42),
            ),
            Box::new(Code::Return(fvar(10))),
        )),
    };

    let code = Code::Fun(
        fun_decl,
        Box::new(Code::Let(
            LetDecl::new(
                fvar(1),
                name("x"),
                Expr::const_str("Nat"),
                LetValue::FVar {
                    fvar: fvar(0),
                    args: vec![],
                },
            ),
            Box::new(Code::Return(fvar(1))),
        )),
    );

    let decl = Decl::new(
        name("test"),
        vec![],
        Expr::const_str("Nat"),
        vec![],
        code,
        false,
    );

    let result = inline_functions(&decl);

    // The function call should be inlined
    let s = result.to_string();
    assert!(s.contains("42"), "Should contain inlined literal");
}

#[test]
fn test_inline_in_code_simple() {
    // fun f () := return 42
    // let x := f()
    // return x
    let fun_decl = FunDecl {
        fvar_id: fvar(0),
        name: name("f"),
        params: vec![],
        ty: Expr::const_str("Nat"),
        body: Box::new(Code::Let(
            LetDecl::new(
                fvar(10),
                name("_"),
                Expr::const_str("Nat"),
                LetValue::nat(42),
            ),
            Box::new(Code::Return(fvar(10))),
        )),
    };

    let code = Code::Fun(
        fun_decl,
        Box::new(Code::Let(
            LetDecl::new(
                fvar(1),
                name("x"),
                Expr::const_str("Nat"),
                LetValue::FVar {
                    fvar: fvar(0),
                    args: vec![],
                },
            ),
            Box::new(Code::Return(fvar(1))),
        )),
    );

    let config = InlineConfig::default();
    let result = inline_functions_in_code(&code, &config);

    let s = result.to_string();
    assert!(s.contains("42"), "Should contain inlined literal");
}

/// Build a chain of N let-bindings for testing size-based inline rejection.
fn make_let_chain(start_fvar: u64, count: u64) -> Code {
    let last = start_fvar + count - 1;
    let mut body = Code::Return(fvar(last));
    for i in (start_fvar..last).rev() {
        body = Code::Let(
            LetDecl::new(
                fvar(i + 1),
                name(&format!("_{}", i + 1 - start_fvar + 1)),
                Expr::const_str("Nat"),
                LetValue::nat(i - start_fvar + 1),
            ),
            Box::new(body),
        );
    }
    Code::Let(
        LetDecl::new(
            fvar(start_fvar),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(1),
        ),
        Box::new(body),
    )
}

#[test]
fn test_no_inline_large_function() {
    let large_body = make_let_chain(10, 11);

    let code = Code::Fun(
        FunDecl {
            fvar_id: fvar(0),
            name: name("large"),
            params: vec![],
            ty: Expr::const_str("Nat"),
            body: Box::new(large_body),
        },
        Box::new(Code::Let(
            LetDecl::new(
                fvar(1),
                name("x"),
                Expr::const_str("Nat"),
                LetValue::FVar {
                    fvar: fvar(0),
                    args: vec![],
                },
            ),
            Box::new(Code::Return(fvar(1))),
        )),
    );

    let decl = Decl::new(
        name("test"),
        vec![],
        Expr::const_str("Nat"),
        vec![],
        code,
        false,
    );

    // Use a small threshold so the function won't be inlined
    let config = InlineConfig {
        threshold: 5,
        max_depth: 5,
    };
    let result = inline_functions_with_config(&decl, &config);

    // The function should NOT be inlined - it should still have the FVar call
    let s = result.to_string();
    // The fun declaration should still exist
    assert!(s.contains("fun _x0"), "Function should not be inlined");
}

#[test]
fn test_no_inline_non_fvar_arg() {
    let fun_decl = FunDecl {
        fvar_id: fvar(0),
        name: name("f"),
        params: vec![Param::new(fvar(10), name("n"), Expr::const_str("Nat"))],
        ty: Expr::const_str("Nat"),
        body: Box::new(Code::Return(fvar(10))),
    };

    let code = Code::Fun(
        fun_decl,
        Box::new(Code::Let(
            LetDecl::new(
                fvar(1),
                name("x"),
                Expr::const_str("Nat"),
                LetValue::FVar {
                    fvar: fvar(0),
                    args: vec![Arg::Erased],
                },
            ),
            Box::new(Code::Return(fvar(1))),
        )),
    );

    let config = InlineConfig::default();
    let result = inline_functions_in_code(&code, &config);

    let s = result.to_string();
    assert!(s.contains("fun _x0"), "Function should not be inlined");
}

#[test]
fn test_no_inline_arity_mismatch() {
    let fun_decl = FunDecl {
        fvar_id: fvar(0),
        name: name("f"),
        params: vec![Param::new(fvar(10), name("n"), Expr::const_str("Nat"))],
        ty: Expr::const_str("Nat"),
        body: Box::new(Code::Return(fvar(10))),
    };

    let code = Code::Fun(
        fun_decl,
        Box::new(Code::Let(
            LetDecl::new(
                fvar(1),
                name("x"),
                Expr::const_str("Nat"),
                LetValue::FVar {
                    fvar: fvar(0),
                    args: vec![],
                },
            ),
            Box::new(Code::Return(fvar(1))),
        )),
    );

    let config = InlineConfig::default();
    let result = inline_functions_in_code(&code, &config);

    let s = result.to_string();
    assert!(s.contains("fun _x0"), "Function should not be inlined");
}
