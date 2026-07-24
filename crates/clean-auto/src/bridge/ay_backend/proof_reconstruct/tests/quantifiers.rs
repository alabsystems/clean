// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// --- Fix 2: Quantifier binder reconstruction tests (#2357) ---

#[test]
fn test_forall_named_to_debruijn() {
    // forall x : Int . x > 0  →  Pi (Int) (BVar(0) > 0)
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let body = terms.mk_lt(zero, x); // 0 < x

    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    let map = VariableMapping::new();
    let mut ctx = translation_context(&terms, &map);
    let result = ctx
        .translate_term(forall)
        .expect("forall translation should succeed");

    // Should be Pi(BinderInfo::Default, Int, body_with_bvar)
    match result.kind() {
        ExprKind::Pi(_, ty, body) => {
            match ty.kind() {
                ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Int"),
                _ => panic!("expected Int binder type, got {:?}", ty),
            }
            // The body should contain BVar(0) for x
            let body_args = body.get_app_args();
            assert_eq!(body_args.len(), 4, "LT.lt should have 4 args");
            // rhs (arg 3) should be BVar(0) — the bound variable x
            match body_args[3].kind() {
                ExprKind::BVar(idx) => assert_eq!(*idx, 0, "x should be BVar(0)"),
                _ => panic!("expected BVar(0) for x, got {:?}", body_args[3]),
            }
        }
        _ => panic!("expected Pi, got {:?}", result),
    }
}

#[test]
fn test_nested_forall_debruijn() {
    // forall x : Int, y : Int . x < y  →  Pi Int (Pi Int (BVar(1) < BVar(0)))
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let body = terms.mk_lt(x, y);

    let forall = terms.mk_forall(
        vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        body,
    );

    let map = VariableMapping::new();
    let mut ctx = translation_context(&terms, &map);
    let result = ctx
        .translate_term(forall)
        .expect("nested forall translation should succeed");

    // Outermost Pi for x
    match result.kind() {
        ExprKind::Pi(_, _, outer_body) => {
            // Inner Pi for y
            match outer_body.kind() {
                ExprKind::Pi(_, _, inner_body) => {
                    let args = inner_body.get_app_args();
                    assert_eq!(args.len(), 4, "LT.lt should have 4 args");
                    // lhs = x = BVar(1) (outer binder)
                    match args[2].kind() {
                        ExprKind::BVar(idx) => {
                            assert_eq!(*idx, 1, "x should be BVar(1) in nested scope")
                        }
                        _ => panic!("expected BVar(1) for x, got {:?}", args[2]),
                    }
                    // rhs = y = BVar(0) (inner binder)
                    match args[3].kind() {
                        ExprKind::BVar(idx) => {
                            assert_eq!(*idx, 0, "y should be BVar(0) in nested scope")
                        }
                        _ => panic!("expected BVar(0) for y, got {:?}", args[3]),
                    }
                }
                _ => panic!("expected inner Pi, got {:?}", outer_body),
            }
        }
        _ => panic!("expected outer Pi, got {:?}", result),
    }
}

#[test]
fn test_exists_translation() {
    // exists x : Int . x > 0  →  @Exists.{1} Int (fun x : Int => 0 < x)
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let body = terms.mk_lt(zero, x);

    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);

    let map = VariableMapping::new();
    let mut ctx = translation_context(&terms, &map);
    let result = ctx
        .translate_term(exists)
        .expect("exists translation should succeed");

    // Should be App(App(Const("Exists", [u]), Int), Lam(Default, Int, body))
    let args = result.get_app_args();
    assert_eq!(
        args.len(),
        2,
        "Exists should have 2 args: type and predicate"
    );

    // First arg: Int type
    match args[0].kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Int"),
        _ => panic!("expected Int as Exists type, got {:?}", args[0]),
    }

    // Second arg: lambda predicate
    match args[1].kind() {
        ExprKind::Lam(_, ty, lam_body) => {
            match ty.kind() {
                ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Int"),
                _ => panic!("expected Int as lambda binder type, got {:?}", ty),
            }
            // lam_body should contain BVar(0) for x
            let body_args = lam_body.get_app_args();
            assert_eq!(body_args.len(), 4, "LT.lt should have 4 args");
            match body_args[3].kind() {
                ExprKind::BVar(idx) => {
                    assert_eq!(*idx, 0, "x should be BVar(0) in exists body")
                }
                _ => panic!(
                    "expected BVar(0) for x in exists body, got {:?}",
                    body_args[3]
                ),
            }
        }
        _ => panic!("expected Lam for Exists predicate, got {:?}", args[1]),
    }

    // Verify head is Exists constant
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Exists"),
        _ => panic!("expected Exists constant, got {:?}", head),
    }
}
