// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compare canonical Int constructor transport with actual kernel conversion.

use super::*;
use clean_kernel::{BinderInfo, Environment, Expr, Level, LocalContext, Name, TypeChecker};

fn int_constructor(name: &str, value: u128) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(name), vec![]),
        Expr::nat_lit_u128(value),
    )
}

#[test]
fn test_int_constructor_transport_matches_kernel_zero_sign_successor_and_large_values() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for magnitude in [0, 6, u128::from(u64::MAX), 1u128 << 64, (1u128 << 127) - 1] {
        let actual = int_constructor("Int.negSucc", magnitude);
        let correct = Expr::app(
            Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_constructor("Int.ofNat", magnitude + 1),
        );
        let wrong = Expr::app(
            Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_constructor("Int.ofNat", magnitude),
        );
        for (claimed, expected) in [(correct, true), (wrong, false)] {
            assert_eq!(tc.is_def_eq(&actual, &claimed), expected);
            let equality = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [int_ty.clone(), actual.clone(), claimed],
            );
            assert!(tc
                .infer_type_full(&equality)
                .expect("strict kernel checks typed claim")
                .is_prop());
            let mut backend = AyBackend::new(AyLogic::QfLia);
            assert_eq!(
                backend
                    .prove(&equality)
                    .expect("native constructor transport"),
                expected,
                "magnitude {magnitude}"
            );
        }
    }
}

#[test]
fn test_int_constructor_transport_refuses_symbolic_natural_fields() {
    let env = Environment::with_prelude();
    let mut context = LocalContext::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let id = context.push(Name::from_string("n"), nat_ty.clone(), BinderInfo::Default);
    let tc = TypeChecker::with_context(&env, context);
    for head in ["Int.ofNat", "Int.negSucc"] {
        let expr = Expr::app(
            Expr::const_(Name::from_string(head), vec![]),
            Expr::fvar(id),
        );
        assert_eq!(
            tc.infer_type_full(&expr)
                .expect("valid symbolic constructor"),
            Expr::const_(Name::from_string("Int"), vec![])
        );
        let mut backend = AyBackend::new(AyLogic::QfLia);
        backend
            .register_fvar_from_lean_type(id, &nat_ty)
            .expect("registered Nat variable");
        assert!(matches!(
            backend.translate_expr(&expr),
            Err(AyError::UnsupportedExpr(_))
        ));
    }
}
