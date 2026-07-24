// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused parity regressions for proof-producing SMT lowering (#2809).

use super::*;
#[cfg(feature = "ay-smt")]
use clean_auto::bridge::ay_contract::{AyBackend, AyError, AyLogic};
use clean_kernel::{BinderInfo, MDataValue};

#[test]
fn test_translate_non_dependent_pi_as_implication() {
    let mut t = SmtLibTranslator::new();
    let expr = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("True"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    );

    assert_eq!(t.translate_expr(&expr).unwrap(), "(=> true false)");
    assert!(
        t.declarations().is_empty(),
        "built-in implication lowering should not fabricate declarations: {:?}",
        t.declarations()
    );
}

#[test]
fn test_translate_dependent_pi_fails_closed() {
    let mut t = SmtLibTranslator::new();
    let expr = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("P"), vec![]),
        Expr::bvar(0),
    );

    let err = t
        .translate_expr(&expr)
        .expect_err("dependent Pi should fail closed on the proof-producing lane");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("dependent Pi")),
        "unexpected error for dependent Pi: {err:?}"
    );
    assert!(
        t.declarations().is_empty(),
        "dependent Pi rejection should not fabricate declarations"
    );
}

#[test]
fn test_translate_direct_gt_and_ge_heads() {
    let mut t = SmtLibTranslator::new();

    let nat_gt = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.gt"), vec![]),
            Expr::nat_lit(7),
        ),
        Expr::nat_lit(2),
    );
    let int_gt = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.gt"), vec![]),
            Expr::nat_lit(8),
        ),
        Expr::nat_lit(3),
    );
    let nat_ge = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.ge"), vec![]),
            Expr::nat_lit(5),
        ),
        Expr::nat_lit(5),
    );
    let int_ge = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.ge"), vec![]),
            Expr::nat_lit(9),
        ),
        Expr::nat_lit(4),
    );

    assert_eq!(t.translate_expr(&nat_gt).unwrap(), "(> 7 2)");
    assert_eq!(t.translate_expr(&int_gt).unwrap(), "(> 8 3)");
    assert_eq!(t.translate_expr(&nat_ge).unwrap(), "(>= 5 5)");
    assert_eq!(t.translate_expr(&int_ge).unwrap(), "(>= 9 4)");
}

#[test]
fn test_translate_mdata_wrapped_app_head() {
    let mut t = SmtLibTranslator::new();
    let metadata = vec![(Name::from_string("pp.universes"), MDataValue::Bool(true))];
    let and_head = Expr::mdata(metadata, Expr::const_(Name::from_string("And"), vec![]));
    let expr = Expr::app(
        Expr::app(and_head, Expr::const_(Name::from_string("True"), vec![])),
        Expr::const_(Name::from_string("False"), vec![]),
    );

    assert_eq!(t.translate_expr(&expr).unwrap(), "(and true false)");
}

#[test]
fn test_translate_top_level_mdata_is_transparent() {
    let mut t = SmtLibTranslator::new();
    let metadata = vec![(Name::from_string("pp.universes"), MDataValue::Bool(true))];
    let expr = Expr::mdata(metadata, Expr::const_(Name::from_string("True"), vec![]));

    assert_eq!(t.translate_expr(&expr).unwrap(), "true");
    assert!(t.declarations().is_empty());
}

#[test]
fn test_translate_exists_non_lambda_bool_predicate_fails_before_declaration() {
    let mut t = SmtLibTranslator::new();
    let exists_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![]),
            Expr::const_(Name::from_string("Bool"), vec![]),
        ),
        Expr::const_(Name::from_string("P"), vec![]),
    );

    let err = t
        .translate_expr(&exists_expr)
        .expect_err("non-lambda Exists predicate should fail closed");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("expected lambda")),
        "unexpected error for non-lambda Exists predicate: {err:?}"
    );
    assert!(t.declarations().is_empty());
    assert!(t.var_declarations().is_empty());
    assert!(t.exists_skolemizations().is_empty());
}

#[test]
fn test_translate_exists_non_lambda_real_predicate_fails_before_declaration() {
    let mut t = SmtLibTranslator::new();
    let exists_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![]),
            Expr::const_(Name::from_string("Real"), vec![]),
        ),
        Expr::const_(Name::from_string("Q"), vec![]),
    );

    let err = t
        .translate_expr(&exists_expr)
        .expect_err("non-lambda Exists predicate should fail closed");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("expected lambda")),
        "unexpected error for non-lambda Exists predicate: {err:?}"
    );
    assert!(t.declarations().is_empty());
    assert!(t.var_declarations().is_empty());
    assert!(t.exists_skolemizations().is_empty());
}

#[test]
fn test_translate_string_literals_are_deduplicated_by_value() {
    let mut t = SmtLibTranslator::new();

    let hello_1 = t.translate_expr(&Expr::str_lit("hello")).unwrap();
    let hello_2 = t.translate_expr(&Expr::str_lit("hello")).unwrap();
    let world = t.translate_expr(&Expr::str_lit("world")).unwrap();

    assert_eq!(
        hello_1, hello_2,
        "same string literal should reuse the SMT symbol"
    );
    assert_ne!(
        hello_1, world,
        "different string literals must not collapse to the same SMT symbol"
    );
    assert_eq!(
        t.declarations(),
        &[
            format!("(declare-const {hello_1} Int)"),
            format!("(declare-const {world} Int)")
        ]
    );
    assert_eq!(t.var_declarations()[0].sort, SmtSort::Int);
    assert_eq!(t.var_declarations()[1].sort, SmtSort::Int);
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_proof_and_native_translators_both_reject_sort_expr() {
    let expr = Expr::sort(Level::zero());

    let mut proof_translator = SmtLibTranslator::new();
    let proof_err = proof_translator
        .translate_expr(&expr)
        .expect_err("proof translator should reject Sort expressions");

    let mut native_backend = AyBackend::new(AyLogic::QfLia);
    let native_err = native_backend
        .translate_expr(&expr)
        .expect_err("native translator should reject Sort expressions");

    assert!(
        matches!(proof_err, TranslateError::UnsupportedExpr(ref message) if message.contains("unsupported expression kind")),
        "unexpected proof-translator error: {proof_err:?}"
    );
    assert!(
        matches!(native_err, AyError::UnsupportedExpr(ref message) if message.contains("unsupported expression kind")),
        "unexpected native translator error: {native_err:?}"
    );
}
