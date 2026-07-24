// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for kernel-level where clause elaboration.

use super::*;
use clean_kernel::expr::BinderInfo;
use clean_kernel::{Expr, Level};

fn mk_nat() -> Expr {
    Expr::const_str("Nat")
}

fn mk_nat_arrow_nat() -> Expr {
    // Nat → Nat as a Pi type
    Expr::pi(BinderInfo::Default, mk_nat(), mk_nat())
}

// -- lift_where_to_let -------------------------------------------------------

#[test]
fn test_lift_where_to_let_empty_returns_body() {
    let body = Expr::const_str("result");
    let result = lift_where_to_let(body.clone(), &[]);
    // Empty where_decls should return body unchanged
    assert_eq!(format!("{result}"), format!("{body}"));
}

#[test]
fn test_lift_where_to_let_single_decl() {
    let body = Expr::bvar(0); // reference to the let binding
    let name = Name::from_string("bar");
    let ty = mk_nat_arrow_nat();
    let val = Expr::lam(BinderInfo::Default, mk_nat(), Expr::bvar(0));

    let result = lift_where_to_let(body, &[(name.clone(), ty, val)]);

    // Should produce: let bar : Nat → Nat := fun x => x in (bvar 0)
    match result.kind() {
        clean_kernel::expr::ExprKind::Let(let_name, let_ty, let_val, let_body, non_dep) => {
            assert_eq!(let_name.to_string(), "bar");
            assert!(!non_dep, "non_dep should be false");
            // let_ty should be a Pi type (Nat → Nat)
            assert!(matches!(
                let_ty.kind(),
                clean_kernel::expr::ExprKind::Pi(..)
            ));
            // let_val should be a Lambda
            assert!(matches!(
                let_val.kind(),
                clean_kernel::expr::ExprKind::Lam(..)
            ));
            // let_body should be bvar(0)
            assert!(matches!(
                let_body.kind(),
                clean_kernel::expr::ExprKind::BVar(0)
            ));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn test_lift_where_to_let_multiple_decls_nesting_order() {
    let body = Expr::const_str("result");
    let decls = vec![
        (Name::from_string("f"), mk_nat(), Expr::nat_lit(1)),
        (Name::from_string("g"), mk_nat(), Expr::nat_lit(2)),
    ];

    let result = lift_where_to_let(body, &decls);

    // Should produce: let f : Nat := 1 in (let g : Nat := 2 in result)
    // Outer let is "f", inner let is "g"
    match result.kind() {
        clean_kernel::expr::ExprKind::Let(name1, _, _, inner, _) => {
            assert_eq!(name1.to_string(), "f", "outer let should be 'f'");
            match inner.kind() {
                clean_kernel::expr::ExprKind::Let(name2, _, _, innermost, _) => {
                    assert_eq!(name2.to_string(), "g", "inner let should be 'g'");
                    assert!(
                        matches!(innermost.kind(), clean_kernel::expr::ExprKind::Const(n, _) if n.to_string() == "result"),
                        "innermost body should be Const(result)"
                    );
                }
                other => panic!("expected inner Let, got {other:?}"),
            }
        }
        other => panic!("expected outer Let, got {other:?}"),
    }
}

#[test]
fn test_lift_where_to_let_preserves_body_identity() {
    // When there's one decl, the body should be preserved exactly as the let body
    let body = Expr::sort(Level::zero()); // Prop
    let decl = (Name::from_string("x"), mk_nat(), Expr::nat_lit(42));
    let result = lift_where_to_let(body, &[decl]);

    match result.kind() {
        clean_kernel::expr::ExprKind::Let(_, _, _, inner_body, _) => {
            assert!(
                matches!(inner_body.kind(), clean_kernel::expr::ExprKind::Sort(_)),
                "body should be Sort (Prop)"
            );
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn test_lift_where_to_let_three_decls() {
    let body = Expr::nat_lit(0);
    let decls = vec![
        (Name::from_string("a"), mk_nat(), Expr::nat_lit(1)),
        (Name::from_string("b"), mk_nat(), Expr::nat_lit(2)),
        (Name::from_string("c"), mk_nat(), Expr::nat_lit(3)),
    ];

    let result = lift_where_to_let(body, &decls);

    // Verify nesting: let a in (let b in (let c in 0))
    let mut current = &result;
    for expected_name in &["a", "b", "c"] {
        match current.kind() {
            clean_kernel::expr::ExprKind::Let(name, _, _, inner, _) => {
                assert_eq!(
                    name.to_string(),
                    *expected_name,
                    "expected let name '{expected_name}'"
                );
                current = inner;
            }
            other => panic!("expected Let for '{expected_name}', got {other:?}"),
        }
    }
    // Innermost should be nat_lit(0)
    assert!(
        matches!(current.kind(), clean_kernel::expr::ExprKind::Lit(_)),
        "innermost body should be literal"
    );
}

// -- WhereClause struct tests ------------------------------------------------

#[test]
fn test_where_clause_new_is_empty() {
    let wc = WhereClause::new();
    assert!(wc.is_empty());
    assert_eq!(wc.decls.len(), 0);
}

#[test]
fn test_where_clause_from_decls() {
    let decls = vec![WhereDecl {
        name: Name::from_string("foo"),
        type_: Some(mk_nat()),
        value: Expr::nat_lit(42),
    }];
    let wc = WhereClause::from_decls(decls);
    assert!(!wc.is_empty());
    assert_eq!(wc.decls.len(), 1);
    assert_eq!(wc.decls[0].name.to_string(), "foo");
}

#[test]
fn test_where_decl_none_type() {
    let decl = WhereDecl {
        name: Name::from_string("x"),
        type_: None,
        value: Expr::nat_lit(0),
    };
    assert!(decl.type_.is_none());
}
