// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Variable-declaration tracking tests.

use super::*;

#[test]
fn test_var_declarations_track_fvar_with_lean_expr() {
    let mut t = SmtLibTranslator::new();
    let fvar_id = FVarId::new(99);
    let fvar = Expr::fvar(fvar_id);
    let smt_name = t.register_fvar(fvar_id, SmtSort::Int, fvar);

    let decls = t.var_declarations();
    assert_eq!(decls.len(), 1);
    assert_eq!(smt_name, "fvar_99");
    assert_eq!(decls[0].name, smt_name);
    assert_eq!(decls[0].sort, SmtSort::Int);
    assert!(
        decls[0].lean_expr.is_some(),
        "FVar should track original Lean expr"
    );
}

#[test]
fn test_registered_prop_fvar_uses_bool_sort() {
    let mut t = SmtLibTranslator::new();
    let fvar_id = FVarId::new(8);
    let fvar = Expr::fvar(fvar_id);

    let smt_name = t.register_fvar(fvar_id, SmtSort::Bool, fvar.clone());
    let translated = t.translate_expr(&fvar).unwrap();

    assert_eq!(
        translated, smt_name,
        "registered Prop FVar should reuse its SMT name"
    );
    assert_eq!(t.declarations().len(), 1);
    assert_eq!(t.declarations()[0], "(declare-const fvar_8 Bool)");
    assert_eq!(t.var_declarations()[0].sort, SmtSort::Bool);
}

#[test]
fn test_registered_real_fvar_uses_real_sort() {
    let mut t = SmtLibTranslator::new();
    let fvar_id = FVarId::new(9);
    let fvar = Expr::fvar(fvar_id);

    let smt_name = t.register_fvar(fvar_id, SmtSort::Real, fvar.clone());
    let translated = t.translate_expr(&fvar).unwrap();

    assert_eq!(
        translated, smt_name,
        "registered Real FVar should reuse its SMT name"
    );
    assert_eq!(t.declarations().len(), 1);
    assert_eq!(t.declarations()[0], "(declare-const fvar_9 Real)");
    assert_eq!(t.var_declarations()[0].sort, SmtSort::Real);
}

#[test]
fn test_unregistered_fvar_returns_error_instead_of_declaring_int() {
    let mut t = SmtLibTranslator::new();
    let fvar_id = FVarId::new(7);
    let fvar = Expr::fvar(fvar_id);

    let err = t
        .translate_expr(&fvar)
        .expect_err("unregistered FVars must fail closed on the verifiable path");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("unregistered FVar")),
        "unexpected error for unregistered FVar: {err:?}"
    );
    assert!(
        t.var_declarations().is_empty(),
        "fail-closed unregistered FVar should not fabricate a declaration"
    );
}

#[test]
fn test_fvar_dedup() {
    let mut t = SmtLibTranslator::new();
    let fvar_id = FVarId::new(7);
    let fvar = Expr::fvar(fvar_id);

    let r1 = t.register_fvar(fvar_id, SmtSort::Int, fvar.clone());
    let r2 = t.translate_expr(&fvar).unwrap();
    assert_eq!(r1, r2, "same FVar should produce same name");
    assert_eq!(
        t.var_declarations().len(),
        1,
        "should not duplicate declaration"
    );
}
