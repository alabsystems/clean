// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Defensive regression tests for unreachable translate_negated variants.

use super::super::*;
use crate::bridge::expr_classifier::LogicalForm;
use crate::bridge::BridgeError;
use clean_kernel::Environment;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn assert_translate_negated_unreachable_variant_error(env: &Environment, form: LogicalForm) {
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        let mut bridge = SmtBridge::new(env);
        bridge.translate_negated_classified(&form)
    }));
    if cfg!(debug_assertions) {
        assert!(
            outcome.is_err(),
            "debug builds must trip the defensive assertion for unreachable variants"
        );
        return;
    }

    let result = outcome.expect("release builds should return an error, not panic");
    assert!(
        matches!(result, Err(BridgeError::UnsupportedExpr { ref context })
            if context == "LogicalForm variant not folded by classify_prop"),
        "unreachable LogicalForm variant must fail closed, got: {result:?}"
    );
}

fn unreachable_translate_negated_forms() -> Vec<LogicalForm> {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let lhs = Expr::nat_lit(1);
    let rhs = Expr::nat_lit(2);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    vec![
        LogicalForm::Iff(p.clone(), q.clone()),
        LogicalForm::Add {
            ty: nat_ty.clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            original: lhs.clone(),
        },
        LogicalForm::Sub {
            ty: nat_ty.clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            original: lhs.clone(),
        },
        LogicalForm::Mul {
            ty: nat_ty.clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            original: lhs.clone(),
        },
        LogicalForm::Div {
            ty: nat_ty.clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            original: lhs.clone(),
        },
        LogicalForm::Mod {
            ty: nat_ty.clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            original: lhs.clone(),
        },
        LogicalForm::Neg {
            ty: nat_ty,
            inner: lhs.clone(),
            original: lhs,
        },
    ]
}

#[test]
fn test_translate_negated_unreachable_variants_return_error() {
    let env = Environment::new();
    for form in unreachable_translate_negated_forms() {
        assert_translate_negated_unreachable_variant_error(&env, form);
    }
}
