// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for variable command elaboration and auto-binding.

use super::*;
use clean_kernel::expr::BinderInfo;
use clean_kernel::{Expr, Level};

fn mk_type() -> Expr {
    // Type = Sort(1)
    Expr::sort(Level::succ(Level::zero()))
}

fn mk_nat() -> Expr {
    Expr::const_str("Nat")
}

// -- VariableDecl construction ------------------------------------------------

#[test]
fn test_variable_decl_new_single() {
    let decl = VariableDecl::new(Name::from_string("α"), mk_type(), BinderInfo::Implicit);
    assert_eq!(decl.names.len(), 1);
    assert_eq!(decl.names[0].to_string(), "α");
    assert_eq!(decl.binder_info, BinderInfo::Implicit);
}

#[test]
fn test_variable_decl_multi() {
    let decl = VariableDecl::multi(
        vec![Name::from_string("α"), Name::from_string("β")],
        mk_type(),
        BinderInfo::Implicit,
    );
    assert_eq!(decl.names.len(), 2);
    assert_eq!(decl.names[0].to_string(), "α");
    assert_eq!(decl.names[1].to_string(), "β");
}

// -- collect_const_names ------------------------------------------------------

#[test]
fn test_collect_const_names_single_const() {
    let expr = Expr::const_str("Nat");
    let names = collect_const_names(&expr);
    assert_eq!(names.len(), 1);
    assert_eq!(names[0].to_string(), "Nat");
}

#[test]
fn test_collect_const_names_no_consts() {
    let expr = Expr::sort(Level::zero()); // Prop has no constants
    let names = collect_const_names(&expr);
    assert!(names.is_empty());
}

#[test]
fn test_collect_const_names_app() {
    // List α — represented as App(Const("List"), Const("α"))
    let expr = Expr::app(Expr::const_str("List"), Expr::const_str("α"));
    let names = collect_const_names(&expr);
    assert_eq!(names.len(), 2);
    assert_eq!(names[0].to_string(), "List");
    assert_eq!(names[1].to_string(), "α");
}

#[test]
fn test_collect_const_names_deduplicates() {
    // α → α — Pi(Const("α"), Const("α"))
    let expr = Expr::pi(
        BinderInfo::Default,
        Expr::const_str("α"),
        Expr::const_str("α"),
    );
    let names = collect_const_names(&expr);
    assert_eq!(names.len(), 1, "should deduplicate");
    assert_eq!(names[0].to_string(), "α");
}

#[test]
fn test_collect_const_names_nested() {
    // let x : Nat := Nat.zero in x
    let expr = Expr::let_named(
        Name::from_string("x"),
        Expr::const_str("Nat"),
        Expr::const_str("Nat.zero"),
        Expr::bvar(0),
        false,
    );
    let names = collect_const_names(&expr);
    assert_eq!(names.len(), 2);
    assert_eq!(names[0].to_string(), "Nat");
    assert_eq!(names[1].to_string(), "Nat.zero");
}

// -- auto_bind_variables ------------------------------------------------------

#[test]
fn test_auto_bind_no_match_returns_unchanged() {
    // Expression references "Nat" but section var is "α"
    let expr = Expr::const_str("Nat");
    let section_vars = vec![VariableDecl::new(
        Name::from_string("α"),
        mk_type(),
        BinderInfo::Implicit,
    )];

    let (result, bound) = auto_bind_variables(&expr, &section_vars);
    assert!(bound.is_empty());
    assert_eq!(format!("{result}"), format!("{expr}"));
}

#[test]
fn test_auto_bind_single_implicit() {
    // Expression references "α" — section var {α : Type}
    let expr = Expr::const_str("α");
    let section_vars = vec![VariableDecl::new(
        Name::from_string("α"),
        mk_type(),
        BinderInfo::Implicit,
    )];

    let (result, bound) = auto_bind_variables(&expr, &section_vars);
    assert_eq!(bound.len(), 1);
    assert_eq!(bound[0].to_string(), "α");

    // Result should be: {_ : Type} → α
    // (Pi with Implicit binder)
    match result.kind() {
        clean_kernel::expr::ExprKind::Pi(bd, ty, body) => {
            assert_eq!(bd.info, BinderInfo::Implicit);
            assert!(
                matches!(ty.kind(), clean_kernel::expr::ExprKind::Sort(_)),
                "binder type should be Sort (Type)"
            );
            assert!(
                matches!(body.kind(), clean_kernel::expr::ExprKind::Const(n, _) if n.to_string() == "α"),
                "body should be Const(α)"
            );
        }
        other => panic!("expected Pi, got {other:?}"),
    }
}

#[test]
fn test_auto_bind_explicit() {
    // Expression references "n" — section var (n : Nat)
    let expr = Expr::const_str("n");
    let section_vars = vec![VariableDecl::new(
        Name::from_string("n"),
        mk_nat(),
        BinderInfo::Default,
    )];

    let (result, bound) = auto_bind_variables(&expr, &section_vars);
    assert_eq!(bound.len(), 1);
    assert_eq!(bound[0].to_string(), "n");

    match result.kind() {
        clean_kernel::expr::ExprKind::Pi(bd, _ty, _body) => {
            assert_eq!(bd.info, BinderInfo::Default, "should be explicit");
        }
        other => panic!("expected Pi, got {other:?}"),
    }
}

#[test]
fn test_auto_bind_instance() {
    // variable [inst : Add α]
    let expr = Expr::const_str("inst");
    let section_vars = vec![VariableDecl::new(
        Name::from_string("inst"),
        Expr::app(Expr::const_str("Add"), Expr::const_str("α")),
        BinderInfo::InstImplicit,
    )];

    let (result, bound) = auto_bind_variables(&expr, &section_vars);
    assert_eq!(bound.len(), 1);
    match result.kind() {
        clean_kernel::expr::ExprKind::Pi(bd, _, _) => {
            assert_eq!(bd.info, BinderInfo::InstImplicit);
        }
        other => panic!("expected Pi with InstImplicit, got {other:?}"),
    }
}

#[test]
fn test_auto_bind_multiple_vars_preserves_order() {
    // Expression references both α and β
    // Section vars: {α : Type} {β : Type}
    let expr = Expr::pi(
        BinderInfo::Default,
        Expr::const_str("α"),
        Expr::const_str("β"),
    );
    let section_vars = vec![
        VariableDecl::new(Name::from_string("α"), mk_type(), BinderInfo::Implicit),
        VariableDecl::new(Name::from_string("β"), mk_type(), BinderInfo::Implicit),
    ];

    let (result, bound) = auto_bind_variables(&expr, &section_vars);
    assert_eq!(bound.len(), 2);
    assert_eq!(
        bound[0].to_string(),
        "α",
        "first bound should be α (declaration order)"
    );
    assert_eq!(
        bound[1].to_string(),
        "β",
        "second bound should be β (declaration order)"
    );

    // Result: {_ : Type} → {_ : Type} → (α → β)
    // Outermost Pi is for α (first in declaration order)
    match result.kind() {
        clean_kernel::expr::ExprKind::Pi(bd1, _, inner) => {
            assert_eq!(
                bd1.info,
                BinderInfo::Implicit,
                "α binder should be implicit"
            );
            match inner.kind() {
                clean_kernel::expr::ExprKind::Pi(bd2, _, _) => {
                    assert_eq!(
                        bd2.info,
                        BinderInfo::Implicit,
                        "β binder should be implicit"
                    );
                }
                other => panic!("expected inner Pi for β, got {other:?}"),
            }
        }
        other => panic!("expected outer Pi for α, got {other:?}"),
    }
}

#[test]
fn test_auto_bind_multi_name_decl() {
    // variable {α β : Type} — one VariableDecl with two names
    // Expression references β but not α
    let expr = Expr::const_str("β");
    let section_vars = vec![VariableDecl::multi(
        vec![Name::from_string("α"), Name::from_string("β")],
        mk_type(),
        BinderInfo::Implicit,
    )];

    let (result, bound) = auto_bind_variables(&expr, &section_vars);
    assert_eq!(bound.len(), 1, "only β should be bound");
    assert_eq!(bound[0].to_string(), "β");

    // Should be: {_ : Type} → β
    assert!(matches!(
        result.kind(),
        clean_kernel::expr::ExprKind::Pi(..)
    ));
}

#[test]
fn test_auto_bind_empty_section_vars() {
    let expr = Expr::const_str("anything");
    let (result, bound) = auto_bind_variables(&expr, &[]);
    assert!(bound.is_empty());
    assert_eq!(format!("{result}"), format!("{expr}"));
}
