// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused constructor-pattern arity regressions for #796.

use super::*;
use clean_parser::{SurfaceExpr, SurfaceLit};

#[test]
fn test_match_ctor_arity_mismatch_excess_subpatterns() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let scrutinee = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("n"));
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    SurfaceName::generated_path("Nat.succ"),
                    vec![
                        SurfacePattern::Var(SurfaceName::generated_path("x")),
                        SurfacePattern::Var(SurfaceName::generated_path("y")),
                    ],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        matches!(
            result,
            Err(ElabError::ConstructorPatternArityMismatch {
                ref ctor_name,
                expected: 1,
                actual: 2,
                ..
            }) if ctor_name == "Nat.succ"
        ),
        "expected constructor arity mismatch for Nat.succ with excess subpatterns, got {result:?}"
    );
}

#[test]
fn test_match_ctor_arity_mismatch_missing_subpatterns() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let scrutinee = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("n"));
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(SurfaceName::generated_path("Nat.succ"), vec![]),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        matches!(
            result,
            Err(ElabError::ConstructorPatternArityMismatch {
                ref ctor_name,
                expected: 1,
                actual: 0,
                ..
            }) if ctor_name == "Nat.succ"
        ),
        "expected constructor arity mismatch for Nat.succ with no subpatterns, got {result:?}"
    );
}

#[test]
fn test_if_let_ctor_arity_mismatch_returns_error() {
    use clean_parser::{Span, SurfaceExpr, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::Ctor(
            SurfaceName::generated_path("Bool.true"),
            vec![SurfacePattern::Var(SurfaceName::generated_path("x"))],
        ),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("b"),
        )),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("x"),
        )),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        matches!(
            result,
            Err(ElabError::ConstructorPatternArityMismatch {
                ref ctor_name,
                expected: 0,
                actual: 1,
                ..
            }) if ctor_name == "Bool.true"
        ),
        "expected constructor arity mismatch for if-let Bool.true pattern, got {result:?}"
    );
}

#[test]
fn test_do_match_ctor_arity_mismatch_returns_error() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(
                Span::dummy(),
                SurfaceName::generated_path("b"),
            )],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Ctor(
                        SurfaceName::generated_path("Bool.true"),
                        vec![SurfacePattern::Var(SurfaceName::generated_path("x"))],
                    )],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(
                            Span::dummy(),
                            SurfaceName::generated_path("x"),
                        )),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(
                            Span::dummy(),
                            SurfaceName::generated_path("b"),
                        )),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        matches!(
            result,
            Err(ElabError::ConstructorPatternArityMismatch {
                ref ctor_name,
                expected: 0,
                actual: 1,
                ..
            }) if ctor_name == "Bool.true"
        ),
        "expected constructor arity mismatch for do-match Bool.true pattern, got {result:?}"
    );
}
