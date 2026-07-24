// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Existential quantifier (Skolemization) translation tests.

use super::*;
use clean_kernel::MDataValue;

// -- Helpers --

fn exists_nat_eq_five() -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty.clone(),
            ),
            Expr::bvar(0),
        ),
        Expr::nat_lit(5),
    );
    let predicate = Expr::lam(clean_kernel::BinderInfo::Default, nat_ty.clone(), body);
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            nat_ty,
        ),
        predicate,
    )
}

/// Build `Exists Nat (fun x => Exists Nat (fun y => Eq Nat x y))`.
fn nested_exists_nat_eq() -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    // Inner body: Eq Nat (BVar 1) (BVar 0)
    let inner_body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty.clone(),
            ),
            Expr::bvar(1), // x (outer)
        ),
        Expr::bvar(0), // y (inner)
    );
    let inner_predicate = Expr::lam(
        clean_kernel::BinderInfo::Default,
        nat_ty.clone(),
        inner_body,
    );
    // Inner Exists: Exists Nat (fun y => Eq Nat (BVar 1) (BVar 0))
    let inner_exists = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            nat_ty.clone(),
        ),
        inner_predicate,
    );
    // Outer predicate: fun x => <inner_exists>
    let outer_predicate = Expr::lam(
        clean_kernel::BinderInfo::Default,
        nat_ty.clone(),
        inner_exists,
    );
    // Outer Exists: Exists Nat (fun x => Exists Nat (fun y => Eq Nat x y))
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            nat_ty,
        ),
        outer_predicate,
    )
}

/// Build `Exists Nat (MData _ (fun x => Eq Nat x 5))`.
fn exists_nat_mdata_lambda_eq_five() -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty.clone(),
            ),
            Expr::bvar(0),
        ),
        Expr::nat_lit(5),
    );
    let predicate = Expr::lam(clean_kernel::BinderInfo::Default, nat_ty.clone(), body);
    let metadata = vec![(Name::from_string("simp"), MDataValue::Bool(true))];
    let wrapped_predicate = Expr::mdata(metadata, predicate);
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            nat_ty,
        ),
        wrapped_predicate,
    )
}

// -- Non-lambda Exists (from original tests.rs) --

#[test]
fn test_translate_exists_non_lambda_returns_error() {
    let mut t = SmtLibTranslator::new();
    // Exists P where P is not a lambda must fail closed.
    let pred = Expr::const_(Name::from_string("P"), vec![]);
    let exists_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![]),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
        pred,
    );
    let err = t
        .translate_expr(&exists_expr)
        .expect_err("non-lambda Exists predicates should be rejected");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("expected lambda")),
        "unexpected error for non-lambda Exists: {err:?}"
    );
    assert!(t.declarations().is_empty());
    assert!(t.var_declarations().is_empty());
}

// -- Lambda-body Skolemization --

#[test]
fn test_translate_exists_lambda_body_reuses_declared_skolem_symbol() {
    let mut t = SmtLibTranslator::new();
    let exists_expr = exists_nat_eq_five();
    let result = t.translate_expr(&exists_expr).unwrap();

    assert_eq!(result, "(= sk_exists_0 5)");
    assert_eq!(t.declarations(), ["(declare-const sk_exists_0 Int)"]);
    assert!(
        t.declarations()
            .iter()
            .all(|decl| !decl.contains("sk_exists_0_")),
        "unexpected placeholder declaration: {:?}",
        t.declarations()
    );
}

#[test]
fn test_translate_exists_lambda_body_var_decls_match_declared_symbol() {
    let mut t = SmtLibTranslator::new();
    let exists_expr = exists_nat_eq_five();

    let _ = t.translate_expr(&exists_expr).unwrap();

    assert_eq!(t.var_declarations().len(), 1);
    assert_eq!(t.var_declarations()[0].name, "sk_exists_0");
    assert_eq!(t.var_declarations()[0].sort, SmtSort::Int);
    assert!(
        t.var_declarations()[0].lean_expr.is_none(),
        "existential skolems should stay out of the raw reconstruction map"
    );
    assert_eq!(t.exists_skolemizations().len(), 1);
    assert_eq!(t.exists_skolemizations()[0].skolem_smt_name, "sk_exists_0");
}

// -- Nested existential tests (coverage gap: #2822 audit) --

#[test]
fn test_translate_nested_exists_produces_two_distinct_skolem_constants() {
    let mut t = SmtLibTranslator::new();
    let expr = nested_exists_nat_eq();
    let result = t.translate_expr(&expr).unwrap();

    // Outer x → sk_exists_0, inner y → sk_exists_1
    assert_eq!(result, "(= sk_exists_0 sk_exists_1)");
}

#[test]
fn test_translate_nested_exists_emits_two_declarations() {
    let mut t = SmtLibTranslator::new();
    let _ = t.translate_expr(&nested_exists_nat_eq()).unwrap();

    assert_eq!(
        t.declarations(),
        [
            "(declare-const sk_exists_0 Int)",
            "(declare-const sk_exists_1 Int)",
        ]
    );
}

#[test]
fn test_translate_nested_exists_records_two_skolemization_entries() {
    let mut t = SmtLibTranslator::new();
    let _ = t.translate_expr(&nested_exists_nat_eq()).unwrap();

    assert_eq!(t.exists_skolemizations().len(), 2);
    assert_eq!(t.exists_skolemizations()[0].skolem_smt_name, "sk_exists_0");
    assert_eq!(t.exists_skolemizations()[1].skolem_smt_name, "sk_exists_1");
}

#[test]
fn test_translate_nested_exists_var_decls_all_have_no_lean_expr() {
    let mut t = SmtLibTranslator::new();
    let _ = t.translate_expr(&nested_exists_nat_eq()).unwrap();

    assert_eq!(t.var_declarations().len(), 2);
    for (i, decl) in t.var_declarations().iter().enumerate() {
        assert_eq!(decl.sort, SmtSort::Int);
        assert!(
            decl.lean_expr.is_none(),
            "skolem var_decl[{i}] should have no lean_expr"
        );
    }
}

// -- Collision regression test (#2848) --

/// A real Lean constant named `sk_exists_0` in the body must fail closed
/// as an unsupported constant, not silently alias the synthesized witness.
#[test]
fn test_translate_exists_body_constant_named_sk_exists_fails_closed() {
    let mut t = SmtLibTranslator::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    // Body: Eq Nat BVar(0) (Const "sk_exists_0")
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty.clone(),
            ),
            Expr::bvar(0),
        ),
        Expr::const_(Name::from_string("sk_exists_0"), vec![]),
    );
    let predicate = Expr::lam(clean_kernel::BinderInfo::Default, nat_ty.clone(), body);
    let exists_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            nat_ty,
        ),
        predicate,
    );

    let result = t.translate_expr(&exists_expr);
    assert!(
        result.is_err(),
        "body constant named sk_exists_0 must fail closed, not alias the witness"
    );
}

// -- MData-wrapped lambda predicate regressions (#2831) --

/// MData-wrapped lambda predicate must produce the same SMT term as bare lambda (#2831).
#[test]
fn test_translate_exists_mdata_lambda_body_reuses_declared_skolem_symbol() {
    let mut t = SmtLibTranslator::new();
    let exists_expr = exists_nat_mdata_lambda_eq_five();
    let result = t.translate_expr(&exists_expr).unwrap();

    assert_eq!(
        result, "(= sk_exists_0 5)",
        "MData-wrapped lambda must produce same SMT term as bare lambda"
    );
    assert_eq!(t.declarations(), ["(declare-const sk_exists_0 Int)"]);
    assert!(
        t.declarations().iter().all(|decl| !decl.contains("expr_")),
        "must not fabricate fallback expr_<n> symbols: {:?}",
        t.declarations()
    );
}

/// MData-wrapped lambda predicate must emit exactly one Skolem declaration (#2831).
#[test]
fn test_translate_exists_mdata_lambda_body_var_decls_match_declared_symbol() {
    let mut t = SmtLibTranslator::new();
    let _ = t
        .translate_expr(&exists_nat_mdata_lambda_eq_five())
        .unwrap();

    assert_eq!(t.var_declarations().len(), 1);
    assert_eq!(t.var_declarations()[0].name, "sk_exists_0");
    assert_eq!(t.var_declarations()[0].sort, SmtSort::Int);
    assert!(
        t.var_declarations()[0].lean_expr.is_none(),
        "existential skolems should stay out of the raw reconstruction map"
    );
    assert_eq!(t.exists_skolemizations().len(), 1);
    assert_eq!(t.exists_skolemizations()[0].skolem_smt_name, "sk_exists_0");
}

// -- UInt*/Float domain rejection in Exists binder types (Part of #2846, #2849) --

/// `Exists UInt8 (fun x => ...)` must fail closed: UInt8 uses modular arithmetic
/// that SMT Int cannot faithfully represent.
#[test]
fn test_translate_exists_uint8_binder_rejected() {
    let mut t = SmtLibTranslator::new();
    let uint8_ty = Expr::const_(Name::from_string("UInt8"), vec![]);
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                uint8_ty.clone(),
            ),
            Expr::bvar(0),
        ),
        Expr::nat_lit(0),
    );
    let predicate = Expr::lam(clean_kernel::BinderInfo::Default, uint8_ty.clone(), body);
    let exists_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            uint8_ty,
        ),
        predicate,
    );

    let result = t.translate_expr(&exists_expr);
    let err = result.expect_err(
        "Exists over UInt8 must fail closed — modular arithmetic is unsound over SMT Int",
    );
    let msg = err.to_string();
    assert!(
        msg.contains("binder type") && msg.contains("UInt8"),
        "error must cite the Exists binder path and the rejected type, got: {msg}"
    );
}

/// `Exists Float (fun x => ...)` must fail closed: Float uses IEEE 754
/// semantics that SMT Real cannot faithfully represent.
#[test]
fn test_translate_exists_float_binder_rejected() {
    let mut t = SmtLibTranslator::new();
    let float_ty = Expr::const_(Name::from_string("Float"), vec![]);
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                float_ty.clone(),
            ),
            Expr::bvar(0),
        ),
        Expr::nat_lit(0),
    );
    let predicate = Expr::lam(clean_kernel::BinderInfo::Default, float_ty.clone(), body);
    let exists_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            float_ty,
        ),
        predicate,
    );

    let result = t.translate_expr(&exists_expr);
    let err = result.expect_err(
        "Exists over Float must fail closed — IEEE 754 semantics are unsound over SMT Real",
    );
    let msg = err.to_string();
    assert!(
        msg.contains("binder type") && msg.contains("Float"),
        "error must cite the Exists binder path and the rejected type, got: {msg}"
    );
}
