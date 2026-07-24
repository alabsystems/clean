// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused do-match nat-pattern regressions for #796.

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

#[test]
fn test_elab_do_match_nat_zero_pattern_supported() {
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
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "Nat.zero literal pattern should elaborate in do-match, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_numeral_add_one_pattern_supported() {
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
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::NumeralAdd(
                        Box::new(SurfacePattern::Var("k".to_string())),
                        1,
                    )],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "k".to_string())),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "`n + 1` pattern should elaborate in do-match, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_ctor_pattern_return_unit_elaborates() {
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
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "Unit.unit".to_string())),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Return(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "Unit.unit".to_string())),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "constructor-pattern do-match return branch should elaborate without re-inferring Pure.pure arm types, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_nonzero_nat_literal_pattern_supported() {
    // #796: Non-zero Nat literal patterns desugar to nested Nat.succ casesOn.
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

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
                // Keep this literal-pattern feature test exhaustive.  The
                // unlisted successors must be represented by a real branch,
                // never by an elaborator-injected axiom.
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

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "Nat literal 1 pattern should elaborate in do-match, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_numeral_add_offset_two_pattern_supported() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

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
                    patterns: vec![SurfacePattern::NumeralAdd(
                        Box::new(SurfacePattern::Var("k".to_string())),
                        2,
                    )],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "k".to_string())),
                    )],
                },
                // Cover the otherwise-missing `1` case with a real fallback.
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

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "`n + 2` pattern should elaborate in do-match, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_numeral_add_pattern_requires_nat_scrutinee() {
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
            vec![SurfaceExpr::Ident(Span::dummy(), "b".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::NumeralAdd(
                        Box::new(SurfacePattern::Var("k".to_string())),
                        1,
                    )],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "k".to_string())),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "b".to_string())),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        matches!(result, Err(ElabError::NotImplemented(ref msg)) if msg.contains("only supported for Nat scrutinees")),
        "expected fail-closed NotImplemented for do-match numeral-add on Bool, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_ctor_nested_literal_pattern_elaborates() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

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
                        vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
                    )],
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

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "expected nested ctor literal do-match pattern to elaborate via nested casesOn, got {result:?}"
    );
}

/// Nat.succ(k + 1) in do-match desugars to nested casesOn targeting Nat.succ (#796).
#[test]
fn test_elab_do_match_ctor_nested_numeral_add_pattern_elaborates() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

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
                        vec![SurfacePattern::NumeralAdd(
                            Box::new(SurfacePattern::Var("k".to_string())),
                            1,
                        )],
                    )],
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

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "Nat.succ(k + 1) nested ctor numeral-add do-match pattern should elaborate with nested casesOn, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_recursive_nested_ctor_pattern_elaborates() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfaceLit, SurfacePattern};

    let env = option_nat_axiom_env("opt");
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "opt".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Ctor("Option.none".to_string(), vec![])],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Ctor(
                        "Option.some".to_string(),
                        vec![SurfacePattern::Ctor(
                            "Option.some".to_string(),
                            vec![SurfacePattern::Var("x".to_string())],
                        )],
                    )],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "x".to_string())),
                    )],
                },
                // Cover `Option.some Option.none` with a real fallback. The
                // nested constructor regression is about lowering depth, not
                // accepting a partial do-match via an axiom.
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

    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elaborate(&surface)
        .expect("recursive nested ctor do-match should elaborate");
    assert!(
        count_const_occurrences(&result, "Option.casesOn") >= 2,
        "expected recursive nested ctor do-match to lower through two Option.casesOn layers, got {result:?}"
    );
}

/// As-patterns in do-match should elaborate successfully (variable inner pattern).
#[test]
fn test_elab_do_match_as_pattern_var_inner_supported() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();

    // do match n with | h@x => h
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![DoMatchArm {
                span: Span::dummy(),
                patterns: vec![SurfacePattern::As(
                    "h".to_string(),
                    Box::new(SurfacePattern::Var("x".to_string())),
                )],
                body: vec![DoElem::Expr(
                    Span::dummy(),
                    Box::new(SurfaceExpr::Ident(Span::dummy(), "h".to_string())),
                )],
            }],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "do-match as-pattern with variable inner should elaborate, got {result:?}"
    );
}

/// As-patterns in do-match should elaborate successfully (wildcard inner pattern).
#[test]
fn test_elab_do_match_as_pattern_wildcard_inner_supported() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();

    // do match n with | h@_ => h
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![DoMatchArm {
                span: Span::dummy(),
                patterns: vec![SurfacePattern::As(
                    "h".to_string(),
                    Box::new(SurfacePattern::Wildcard),
                )],
                body: vec![DoElem::Expr(
                    Span::dummy(),
                    Box::new(SurfaceExpr::Ident(Span::dummy(), "h".to_string())),
                )],
            }],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "do-match as-pattern with wildcard inner should elaborate, got {result:?}"
    );
}

/// Or-patterns in do-match should be expanded into separate arms.
#[test]
fn test_elab_do_match_or_pattern_expands_to_separate_arms() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();

    // do match n with | Nat.zero | Nat.succ _ => 0
    // The Or-pattern should expand to two arms: | Nat.zero => 0 | Nat.succ _ => 0
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![DoMatchArm {
                span: Span::dummy(),
                patterns: vec![SurfacePattern::Or(
                    Box::new(SurfacePattern::Ctor("Nat.zero".to_string(), vec![])),
                    Box::new(SurfacePattern::Ctor(
                        "Nat.succ".to_string(),
                        vec![SurfacePattern::Wildcard],
                    )),
                )],
                body: vec![DoElem::Expr(
                    Span::dummy(),
                    Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
                )],
            }],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "do-match Or-pattern should expand and elaborate, got {result:?}"
    );
}
