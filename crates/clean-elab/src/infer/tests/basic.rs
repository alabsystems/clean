// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Basic elaboration tests for core expression types

use super::*;

#[test]
fn test_elab_type() {
    let expr = elab("Type").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Sort(_)));
}

#[test]
fn test_elab_prop() {
    let expr = elab("Prop").unwrap();
    assert!(expr.is_prop());
}

#[test]
fn test_elab_nat_lit() {
    let expr = elab("42").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Lit(Literal::Nat(n)) if n.to_u64() == Some(42)));
}

#[test]
fn test_elab_lambda() {
    let expr = elab("fun (x : Type) => x").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Lam(_, _, _)));
}

#[test]
fn test_elab_pi() {
    let expr = elab("forall (x : Type), x").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Pi(_, _, _)));
}

#[test]
fn test_elab_pi_unannotated_binder() {
    // Regression: unannotated Pi binders previously returned CannotInfer (#2776).
    // Lean 4 creates fresh metavariables for unannotated binders.
    let expr = elab("forall n, Type").unwrap();
    assert!(
        matches!(expr.kind(), ExprKind::Pi(_, _, _)),
        "expected Pi for unannotated forall binder, got: {expr:?}"
    );
}

#[test]
fn test_elab_arrow() {
    let expr = elab("Type -> Type").unwrap();
    match expr.kind() {
        ExprKind::Pi(bd, domain, _) if bd.info == BinderInfo::Default => {
            assert!(matches!(domain.kind(), ExprKind::Sort(_)));
        }
        _ => panic!("expected Pi"),
    }
}

#[test]
fn test_elab_app_unknown() {
    // f is unknown in standalone expression context, should error
    // Auto-implicit (#164) only applies in declaration contexts
    let err = elab("f x").unwrap_err();
    assert!(
        matches!(err, ElabError::UnknownIdent(_)),
        "unknown 'f' in standalone context should produce UnknownIdent, got: {err}"
    );
}

#[test]
fn test_unknown_identifier_reports_nearest_theorem_names() {
    let mut env = Environment::new();
    let prop_name = Name::from_string("myProp");
    env.add_decl(Declaration::Axiom {
        name: prop_name.clone(),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    })
    .expect("prop axiom should register");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("myProof"),
        level_params: vec![],
        type_: Expr::const_(prop_name, vec![]),
    })
    .expect("proof axiom should register");
    env.add_decl_structural(Declaration::Theorem {
        name: Name::from_string("Nat.add_comm"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("myProp"), vec![]),
        value: Expr::const_(Name::from_string("myProof"), vec![]),
    })
    .expect("theorem should register");

    let err = elab_with_env(&env, "Nat.add_com").expect_err("identifier should be unknown");
    let diagnostics = err.agent_diagnostics();
    match err {
        ElabError::UnknownIdentWithSuggestions { name, suggestions } => {
            assert_eq!(name, "Nat.add_com");
            assert_eq!(
                suggestions.first().map(String::as_str),
                Some("Nat.add_comm")
            );
            assert_eq!(diagnostics[0].code, "ident.nearest_theorems");
        }
        other => panic!("expected UnknownIdentWithSuggestions, got {other:?}"),
    }
}

#[test]
fn test_elab_let() {
    let expr = elab("let x : Type := Type in x").unwrap();
    assert!(matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)));
}

#[test]
fn test_elab_hole() {
    let expr = elab("_").unwrap();
    // Hole elaborates to a metavariable (represented as FVar for now)
    assert!(matches!(expr.kind(), ExprKind::FVar(_)));
}

#[test]
fn test_elab_identity_function() {
    let expr = elab("fun (A : Type) (x : A) => x").unwrap();
    match expr.kind() {
        ExprKind::Lam(_, ty1, body1) => {
            assert!(matches!(ty1.kind(), ExprKind::Sort(_)));
            match body1.kind() {
                ExprKind::Lam(_, _, body2) => {
                    // The innermost body should be BVar(0) - referring to x
                    assert!(matches!(body2.kind(), ExprKind::BVar(0)));
                }
                _ => panic!("expected inner lambda"),
            }
        }
        _ => panic!("expected lambda"),
    }
}

#[test]
fn test_too_many_arguments_returns_error() {
    // Apply a one-argument function (Prop → Prop) to two arguments.
    // After consuming the first arg `a`, result type is Prop (not a Pi),
    // so the second `a` should trigger TooManyArguments instead of
    // silently applying (#1720).
    //
    // We use an axiom `a : Prop` to avoid universe cumulativity issues
    // that arise with Sort-typed arguments (e.g., `Type : Type 1`).
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    let err = elab_with_env(&env, "(fun (x : Prop) => x) a a").unwrap_err();
    assert!(
        matches!(
            err,
            ElabError::TooManyArguments {
                remaining_args: 1,
                ..
            }
        ),
        "over-application should produce TooManyArguments, got: {err}"
    );
}
