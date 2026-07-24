// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused nested constructor-subpattern regressions for #796.

use super::*;
use clean_kernel::expr::ExprKind;

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

fn option_nat_axiom_env(name: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let option_nat = Expr::app(
        Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::app(
            Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
            option_nat,
        ),
    })
    .unwrap();
    env
}

fn option_bool_axiom_env(name: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let option_bool = Expr::app(
        Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Bool"), vec![]),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: option_bool,
    })
    .unwrap();
    env
}

fn count_const_occurrences(expr: &Expr, needle: &str) -> usize {
    match expr.kind() {
        ExprKind::Const(name, _) => usize::from(name.to_string() == needle),
        ExprKind::App(func, arg) => {
            count_const_occurrences(func, needle) + count_const_occurrences(arg, needle)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            count_const_occurrences(ty, needle) + count_const_occurrences(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            count_const_occurrences(ty, needle)
                + count_const_occurrences(val, needle)
                + count_const_occurrences(body, needle)
        }
        _ => 0,
    }
}

/// Nat.succ(Nat.zero) literal sub-pattern desugars to nested casesOn (#796).
#[test]
fn test_match_ctor_nested_literal_zero_pattern_elaborates() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = nat_axiom_env();
    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "n".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Nat.succ".to_string(),
                    vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "Nat.succ(Lit(0)) nested ctor pattern should elaborate with nested casesOn, got {result:?}"
    );
}

/// Nat.succ(k + 1) sub-pattern desugars to nested casesOn targeting Nat.succ (#796).
#[test]
fn test_match_ctor_nested_numeral_add_pattern_elaborates() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = nat_axiom_env();
    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "n".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Nat.succ".to_string(),
                    vec![SurfacePattern::NumeralAdd(
                        Box::new(SurfacePattern::Var("k".to_string())),
                        1,
                    )],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "Nat.succ(k + 1) nested ctor numeral-add pattern should elaborate with nested casesOn, got {result:?}"
    );
}

/// Nat.succ(k + 2) sub-pattern desugars to two nested Nat.succ casesOn layers (#796).
#[test]
fn test_match_ctor_nested_numeral_add_offset_two_pattern_elaborates() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = nat_axiom_env();
    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "n".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Nat.succ".to_string(),
                    vec![SurfacePattern::NumeralAdd(
                        Box::new(SurfacePattern::Var("k".to_string())),
                        2,
                    )],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "Nat.succ(k + 2) nested ctor numeral-add pattern should elaborate with nested casesOn, got {result:?}"
    );
}

/// As-pattern with Nat(0) sub-pattern elaborates via alias rewrite + nested casesOn (#796).
#[test]
fn test_match_as_ctor_nested_literal_pattern_elaborates() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = nat_axiom_env();
    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "n".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::As(
                    "whole".to_string(),
                    Box::new(SurfacePattern::Ctor(
                        "Nat.succ".to_string(),
                        vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
                    )),
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "As-pattern whole @ Nat.succ(0) should elaborate with alias rewrite + nested casesOn, got {result:?}"
    );
}

/// As-pattern with NumeralAdd(k+1) sub-pattern elaborates via alias rewrite + nested casesOn (#796).
#[test]
fn test_match_as_ctor_nested_numeral_add_pattern_elaborates() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = nat_axiom_env();
    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "n".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::As(
                    "whole".to_string(),
                    Box::new(SurfacePattern::Ctor(
                        "Nat.succ".to_string(),
                        vec![SurfacePattern::NumeralAdd(
                            Box::new(SurfacePattern::Var("k".to_string())),
                            1,
                        )],
                    )),
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "As-pattern whole @ Nat.succ(k+1) should elaborate with alias rewrite + nested casesOn, got {result:?}"
    );
}

/// Recursive ctor sub-patterns with arguments elaborate via nested casesOn layers (#796).
#[test]
fn test_match_ctor_recursive_nested_ctor_pattern_typechecks() {
    use clean_parser::{Span, SurfaceExpr, SurfaceLit, SurfaceMatchArm, SurfacePattern};

    let env = option_nat_axiom_env("opt");
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(Span::dummy(), "opt".to_string())),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("Option.none".to_string(), vec![]),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Option.some".to_string(),
                    vec![SurfacePattern::Ctor(
                        "Option.some".to_string(),
                        vec![SurfacePattern::Var("x".to_string())],
                    )],
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "x".to_string()),
            },
            // Cover `Option.some Option.none` with a real fallback. The nested
            // constructor regression is about lowering depth, not accepting a
            // partial function via an axiom.
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elaborate(&match_expr)
        .expect("Option.some (Option.some x) should elaborate");
    let result_ty = ctx
        .infer_type(&result)
        .expect("recursive nested ctor match should produce a well-typed term");

    assert!(
        ctx.is_def_eq(&result_ty, &Expr::const_(Name::from_string("Nat"), vec![])),
        "expected recursive nested ctor match to have type Nat, got {result_ty:?}"
    );
    assert!(
        count_const_occurrences(&result, "Option.casesOn") >= 2,
        "expected recursive nested ctor match to lower through two Option.casesOn layers, got {result:?}"
    );
}

#[test]
fn test_match_ctor_nested_numeral_add_non_nat_field_fails_closed() {
    use clean_parser::{Span, SurfaceExpr, SurfaceLit, SurfaceMatchArm, SurfacePattern};

    let env = option_bool_axiom_env("optb");
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(Span::dummy(), "optb".to_string())),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "Option.some".to_string(),
                    vec![SurfacePattern::NumeralAdd(
                        Box::new(SurfacePattern::Var("k".to_string())),
                        2,
                    )],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        matches!(result, Err(ElabError::NotImplemented(ref msg)) if msg.contains("does not belong to field type Bool")),
        "nested `k + 2` on Option Bool should fail closed instead of silently never matching, got {result:?}"
    );
}

/// Nat.succ(1) sub-pattern desugars to nested casesOn: succ → succ → zero (#796).
#[test]
fn test_nested_ctor_nonzero_nat_literal_sub_pattern() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = nat_axiom_env();

    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                // Pattern: Nat.succ(1) — matches exactly 2
                pattern: SurfacePattern::Ctor(
                    "Nat.succ".to_string(),
                    vec![SurfacePattern::Lit(SurfaceLit::Nat(1))],
                ),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elaborate(&match_expr)
        .expect("Nat.succ(1) sub-pattern should elaborate via nested Nat.casesOn");

    // The desugaring generates nested Nat.casesOn:
    // outer for succ/zero, inner for the literal 1 sub-pattern.
    assert!(
        count_const_occurrences(&result, "Nat.casesOn") >= 2,
        "expected Nat.succ(1) to lower through at least 2 Nat.casesOn layers, got {result:?}"
    );
}
