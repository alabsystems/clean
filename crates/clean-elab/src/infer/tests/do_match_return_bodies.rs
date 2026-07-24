// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused do-match return-body regressions for #796.

use super::*;

fn nat_axiom_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();
    env
}

#[test]
fn test_elab_do_match_ctor_pattern_return_body_supported() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();

    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Ctor(
                        "Nat.succ".to_string(),
                        vec![SurfacePattern::Var("k".to_string())],
                    )],
                    body: vec![DoElem::Return(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "k".to_string())),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Return(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);

    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "constructor-pattern do-match should accept return-arm bodies, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_nat_zero_first_arm_return_body_supported() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();

    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
                    body: vec![DoElem::Return(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Return(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);

    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "Nat.zero first-arm do-match should accept return-arm bodies, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_numeral_add_first_arm_return_body_supported() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();

    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::NumeralAdd(
                        Box::new(SurfacePattern::Var("k".to_string())),
                        1,
                    )],
                    body: vec![DoElem::Return(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "k".to_string())),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Return(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);

    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "`n + 1` first-arm do-match should accept return-arm bodies, got {result:?}"
    );
}
