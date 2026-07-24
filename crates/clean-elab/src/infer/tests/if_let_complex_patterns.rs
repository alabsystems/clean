// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused if-let As/Or pattern regressions for #796.

use super::*;

/// True iff `result` is an "unknown identifier" error for `expected`, regardless of
/// whether the elaborator attached did-you-mean suggestions. Which variant is produced
/// depends on what else is registered in the environment (e.g. nearby theorem names), so
/// tests assert the *name* rather than pinning the exact `UnknownIdent`-vs-`...WithSuggestions`
/// variant.
fn is_unknown_ident<T>(result: &Result<T, ElabError>, expected: &str) -> bool {
    match result {
        Err(ElabError::UnknownIdent(name)) => name == expected,
        Err(ElabError::UnknownIdentWithSuggestions { name, .. }) => name == expected,
        _ => false,
    }
}

fn nat_axiom_env(name: &str) -> Environment {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();
    env
}

fn expr_contains_const(expr: &Expr, needle: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == needle,
        ExprKind::App(f, a) => expr_contains_const(f, needle) || expr_contains_const(a, needle),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, needle) || expr_contains_const(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, needle)
                || expr_contains_const(val, needle)
                || expr_contains_const(body, needle)
        }
        ExprKind::MData(_, inner) | ExprKind::Squash(inner) => expr_contains_const(inner, needle),
        ExprKind::Proj(_, _, inner) => expr_contains_const(inner, needle),
        ExprKind::CubicalPath { ty, left, right } => {
            expr_contains_const(ty, needle)
                || expr_contains_const(left, needle)
                || expr_contains_const(right, needle)
        }
        ExprKind::CubicalPathLam { body } => expr_contains_const(body, needle),
        ExprKind::CubicalPathApp { path, arg } => {
            expr_contains_const(path, needle) || expr_contains_const(arg, needle)
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            expr_contains_const(ty, needle)
                || expr_contains_const(phi, needle)
                || expr_contains_const(u, needle)
                || expr_contains_const(base, needle)
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            expr_contains_const(ty, needle)
                || expr_contains_const(phi, needle)
                || expr_contains_const(base, needle)
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            expr_contains_const(ty, needle)
                || expr_contains_const(r, needle)
                || expr_contains_const(s, needle)
                || expr_contains_const(base, needle)
        }
        ExprKind::ZFCMem { element, set } => {
            expr_contains_const(element, needle) || expr_contains_const(set, needle)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            expr_contains_const(domain, needle) || expr_contains_const(pred, needle)
        }
        ExprKind::Sort(_)
        | ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1
        | ExprKind::ZFCSet(_) => false,
    }
}

#[test]
fn test_if_let_as_pattern_binds_whole_scrutinee_in_then_branch() {
    use clean_parser::{Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env("n");
    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::As(
            "whole".to_string(),
            Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
        ),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "whole".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "As-pattern should elaborate with whole scrutinee bound in then branch, got {result:?}"
    );
}

#[test]
fn test_if_let_as_pattern_does_not_bind_whole_scrutinee_in_else_branch() {
    use clean_parser::{Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env("n");
    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::As(
            "whole".to_string(),
            Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
        ),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "whole".to_string())),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        is_unknown_ident(&result, "whole"),
        "As-pattern should not leak whole scrutinee binding into else branch, got {result:?}"
    );
}

#[test]
fn test_if_let_or_pattern_desugars_without_rejecting_complex_pattern() {
    use clean_parser::{Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env("n");
    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::Or(
            Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
            Box::new(SurfacePattern::NumeralAdd(
                Box::new(SurfacePattern::Wildcard),
                1,
            )),
        ),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "Or-pattern if-let should desugar through recursive if-let elaboration, got {result:?}"
    );
}

#[test]
fn test_if_let_as_pattern_uses_fresh_shared_scrutinee_when_base_name_taken() {
    use clean_parser::{Span, SurfaceExpr, SurfacePattern};

    let mut env = nat_axiom_env("n");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("__iflet_scrutinee"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::As(
            "whole".to_string(),
            Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
        ),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "As-pattern if-let should keep matching on the Nat scrutinee even when __iflet_scrutinee already exists, got {result:?}"
    );
}

#[test]
fn test_if_let_or_pattern_uses_fresh_shared_scrutinee_when_base_name_taken() {
    use clean_parser::{Span, SurfaceExpr, SurfacePattern};

    let mut env = nat_axiom_env("n");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("__iflet_scrutinee"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::Or(
            Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
            Box::new(SurfacePattern::NumeralAdd(
                Box::new(SurfacePattern::Wildcard),
                1,
            )),
        ),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "Or-pattern if-let should keep matching on the Nat scrutinee even when __iflet_scrutinee already exists, got {result:?}"
    );
}

#[test]
fn test_if_let_as_pattern_does_not_capture_outer_shared_scrutinee_name() {
    use clean_parser::{Span, SurfaceExpr, SurfacePattern};

    let mut env = nat_axiom_env("n");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("__iflet_scrutinee"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::As(
            "whole".to_string(),
            Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
        ),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            "__iflet_scrutinee".to_string(),
        )),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elaborate(&surface)
        .expect("As-pattern should not capture unrelated outer identifiers");
    assert!(
        expr_contains_const(&result, "__iflet_scrutinee"),
        "expected elaborated if-let to keep the outer __iflet_scrutinee constant reference, got {result:?}"
    );
}

#[test]
fn test_if_let_as_pattern_supports_nested_ctor_inner_pattern() {
    use clean_parser::{Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env("n");
    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::As(
            "whole".to_string(),
            Box::new(SurfacePattern::Ctor(
                "Nat.succ".to_string(),
                vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
            )),
        ),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "whole".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "expected As-pattern if-let to support nested ctor inner patterns via recursive lowering, got {result:?}"
    );
}

#[test]
fn test_if_let_or_pattern_supports_nested_ctor_left_branch() {
    use clean_parser::{Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env("n");
    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::Or(
            Box::new(SurfacePattern::Ctor(
                "Nat.succ".to_string(),
                vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
            )),
            Box::new(SurfacePattern::Wildcard),
        ),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "expected Or-pattern if-let to support nested ctor left branches via recursive lowering, got {result:?}"
    );
}

#[test]
fn test_if_let_as_pattern_error_cleans_up_shared_scrutinee_local() {
    use clean_parser::{Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env("n");
    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::As(
            "whole".to_string(),
            Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
        ),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "missing".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        is_unknown_ident(&result, "missing"),
        "expected the wrapped then-branch to fail on the missing identifier, got {result:?}"
    );
    let leaked = ctx.elaborate(&SurfaceExpr::Ident(
        Span::dummy(),
        "__iflet_scrutinee".to_string(),
    ));
    assert!(
        is_unknown_ident(&leaked, "__iflet_scrutinee"),
        "shared if-let helper locals should be cleaned up after errors, got {leaked:?}"
    );
}
