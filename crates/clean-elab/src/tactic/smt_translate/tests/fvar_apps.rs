// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Callable FVar application-head translation tests.

use super::*;
use clean_kernel::BinderInfo;

fn build_fvar_app(head: FVarId, args: &[Expr]) -> Expr {
    let mut result = Expr::fvar(head);
    for arg in args {
        result = Expr::app(result, arg.clone());
    }
    result
}

fn int_to_prop_type() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("Int"), vec![]),
        Expr::prop(),
    )
}

#[test]
fn test_registered_callable_fvar_emits_single_declare_fun_on_first_use() {
    let mut t = SmtLibTranslator::new();
    let fvar_id = FVarId::new(70);
    let fvar = Expr::fvar(fvar_id);
    let f_ty = int_to_prop_type();

    let smt_name = t.register_callable_fvar(fvar_id, SmtSort::Bool, fvar.clone(), f_ty.clone());
    assert_eq!(smt_name, "fvar_70");
    assert!(
        t.declarations().is_empty(),
        "callable heads should not emit a scalar declaration before first use"
    );

    let first = t
        .translate_expr(&build_fvar_app(fvar_id, &[Expr::nat_lit(5)]))
        .expect("registered callable FVar head should translate");
    assert_eq!(first, "(fvar_70 5)");

    let second = t
        .translate_expr(&build_fvar_app(fvar_id, &[Expr::nat_lit(9)]))
        .expect("reusing the same callable head signature should succeed");
    assert_eq!(second, "(fvar_70 9)");

    assert_eq!(t.declarations().len(), 1);
    assert_eq!(t.declarations()[0], "(declare-fun fvar_70 (Int) Bool)");
    assert!(t.var_declarations().is_empty());
    assert_eq!(t.func_declarations().len(), 1);
    assert_eq!(t.func_declarations()[0].name, smt_name);
    assert_eq!(t.func_declarations()[0].domain_sorts, vec![SmtSort::Int]);
    assert_eq!(t.func_declarations()[0].result_sort, SmtSort::Bool);
    assert_eq!(t.func_declarations()[0].lean_expr, fvar);
    assert_eq!(t.func_declarations()[0].lean_ty, f_ty);
}

#[test]
fn test_registered_callable_fvar_requires_application_head_position() {
    let mut t = SmtLibTranslator::new();
    let fvar_id = FVarId::new(71);
    let fvar = Expr::fvar(fvar_id);

    t.register_callable_fvar(fvar_id, SmtSort::Bool, fvar.clone(), int_to_prop_type());
    let err = t
        .translate_expr(&fvar)
        .expect_err("callable FVars should not translate as first-class SMT terms");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("must appear in application head position")),
        "unexpected error for bare callable FVar: {err:?}"
    );
}

#[test]
fn test_translate_unregistered_fvar_app_head_returns_error() {
    let mut t = SmtLibTranslator::new();
    let err = t
        .translate_expr(&build_fvar_app(FVarId::new(72), &[Expr::nat_lit(1)]))
        .expect_err("unregistered callable heads must fail closed");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("unregistered FVar")),
        "unexpected error for unregistered FVar head: {err:?}"
    );
    assert!(t.declarations().is_empty());
}

#[test]
fn test_translate_callable_fvar_arity_mismatch_returns_error() {
    let mut t = SmtLibTranslator::new();
    let fvar_id = FVarId::new(73);

    t.register_callable_fvar(
        fvar_id,
        SmtSort::Bool,
        Expr::fvar(fvar_id),
        int_to_prop_type(),
    );
    t.translate_expr(&build_fvar_app(fvar_id, &[Expr::nat_lit(1)]))
        .expect("first callable use should establish arity");
    let err = t
        .translate_expr(&build_fvar_app(
            fvar_id,
            &[Expr::nat_lit(1), Expr::nat_lit(2)],
        ))
        .expect_err("arity drift must fail closed");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("previously declared with arity")),
        "unexpected error for callable FVar arity drift: {err:?}"
    );
}

#[test]
fn test_translate_callable_fvar_domain_sort_mismatch_returns_error() {
    let mut t = SmtLibTranslator::new();
    let fvar_id = FVarId::new(74);

    t.register_callable_fvar(
        fvar_id,
        SmtSort::Bool,
        Expr::fvar(fvar_id),
        int_to_prop_type(),
    );
    t.translate_expr(&build_fvar_app(fvar_id, &[Expr::nat_lit(1)]))
        .expect("first callable use should establish domain sorts");
    let err = t
        .translate_expr(&build_fvar_app(
            fvar_id,
            &[Expr::const_(Name::from_string("True"), vec![])],
        ))
        .expect_err("domain sort drift must fail closed");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("incompatible domain sorts")),
        "unexpected error for callable FVar domain drift: {err:?}"
    );
}
