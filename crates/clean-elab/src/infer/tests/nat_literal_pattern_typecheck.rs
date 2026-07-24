// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typechecking regressions for non-zero Nat literal patterns (#796).

use super::*;
use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfaceLit, SurfacePattern};

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

fn assert_surface_typechecks_as_nat(surface: &SurfaceExpr, context: &str) {
    let env = nat_axiom_env("n");
    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elaborate(surface)
        .unwrap_or_else(|err| panic!("{context} should elaborate, got {err:?}"));
    let result_ty = ctx.infer_type(&result).unwrap_or_else(|err| {
        panic!("{context} should typecheck after elaboration, got {err:?}; expr={result:?}")
    });

    assert!(
        ctx.is_def_eq(&result_ty, &Expr::const_(Name::from_string("Nat"), vec![])),
        "{context} should elaborate to a Nat-typed term, got {result_ty:?}; expr={result:?}"
    );
}

fn assert_input_typechecks_as_nat(input: &str, context: &str) {
    let env = nat_axiom_env("n");
    let mut ctx = ElabCtx::new(&env);
    let surface =
        parse_expr(input).unwrap_or_else(|err| panic!("{context} should parse, got {err:?}"));
    let result = ctx
        .elaborate(&surface)
        .unwrap_or_else(|err| panic!("{context} should elaborate, got {err:?}"));
    let result_ty = ctx.infer_type(&result).unwrap_or_else(|err| {
        panic!("{context} should typecheck after elaboration, got {err:?}; expr={result:?}")
    });

    assert!(
        ctx.is_def_eq(&result_ty, &Expr::const_(Name::from_string("Nat"), vec![])),
        "{context} should elaborate to a Nat-typed term, got {result_ty:?}; expr={result:?}"
    );
}

#[test]
fn test_match_nat_literal_one_pattern_typechecks() {
    assert_input_typechecks_as_nat(
        "match n with | 0 => 0 | 1 => 1 | _ => 0",
        "Nat literal 1 match pattern",
    );
}

#[test]
fn test_match_nat_literal_two_pattern_typechecks() {
    assert_input_typechecks_as_nat(
        "match n with | 0 => 0 | 2 => 2 | _ => 0",
        "Nat literal 2 match pattern",
    );
}

#[test]
fn test_if_let_nat_literal_one_pattern_typechecks() {
    assert_input_typechecks_as_nat(
        "if let 1 := n then 1 else 0",
        "Nat literal 1 if-let pattern",
    );
}

#[test]
fn test_if_let_nat_literal_two_pattern_typechecks() {
    assert_input_typechecks_as_nat(
        "if let 2 := n then 1 else 0",
        "Nat literal 2 if-let pattern",
    );
}

#[test]
fn test_do_match_nat_literal_one_pattern_typechecks() {
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Lit(SurfaceLit::Nat(1))],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
            ],
        )],
    );

    assert_surface_typechecks_as_nat(&surface, "Nat literal 1 do-match pattern");
}

#[test]
fn test_do_match_nat_literal_two_pattern_typechecks() {
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Lit(SurfaceLit::Nat(2))],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(2))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
            ],
        )],
    );

    assert_surface_typechecks_as_nat(&surface, "Nat literal 2 do-match pattern");
}

#[test]
fn partial_nat_literal_matches_fail_closed() {
    let env = nat_axiom_env("n");

    let partial =
        parse_expr("match n with | 0 => 0 | 1 => 1").expect("partial plain Nat match should parse");
    let mut plain_ctx = ElabCtx::new(&env);
    let plain = plain_ctx.elaborate(&partial);
    assert!(
        matches!(&plain, Err(ElabError::NotImplemented(message))
            if message.contains("non-exhaustive nested constructor pattern")),
        "partial plain Nat literal match must fail closed, got {plain:?}"
    );

    let partial_do = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Lit(SurfaceLit::Nat(1))],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
                    )],
                },
            ],
        )],
    );
    let mut do_ctx = ElabCtx::new(&env);
    let do_result = do_ctx.elaborate(&partial_do);
    assert!(
        matches!(&do_result, Err(ElabError::NotImplemented(message))
            if message.contains("non-exhaustive nested constructor pattern")),
        "partial do Nat literal match must fail closed, got {do_result:?}"
    );
}
