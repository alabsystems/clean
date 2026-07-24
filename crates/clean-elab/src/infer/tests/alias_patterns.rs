// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused alias-pattern regressions for #796.

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

fn option_prod_nat_bool_axiom_env(name: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let option_prod_nat_bool = option_prod_nat_bool_ty();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: option_prod_nat_bool,
    })
    .unwrap();
    env
}

fn option_prod_nat_bool_ty() -> Expr {
    let prod_nat_bool = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Prod"),
                vec![Level::zero(), Level::zero()],
            ),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
        Expr::const_(Name::from_string("Bool"), vec![]),
    );
    Expr::app(
        Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
        prod_nat_bool,
    )
}

#[test]
fn test_def_match_alias_pattern_uses_declared_domain_type() {
    let env = Environment::with_prelude();
    let decl =
        parse_decl_for_elab("def f : List Nat → List Nat\n  | a::xs@(b::bs) => xs\n  | _ => []")
            .expect("Lean 4 compat 220 declaration should parse");
    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elab_decl(&decl)
        .expect("alias-pattern function equation should elaborate");

    match result {
        ElabResult::Definition { ty, val, .. } => {
            let inferred_ty = ctx
                .infer_type(&val)
                .expect("elaborated alias-pattern function should typecheck");
            assert!(
                ctx.is_def_eq(&inferred_ty, &ty),
                "expected alias-pattern function equation to keep declared type, got inferred={inferred_ty:?}, declared={ty:?}, val={val:?}"
            );
            assert!(
                matches!(val.kind(), ExprKind::Lam(_, _, _)),
                "function equation should elaborate to a lambda, got {val:?}"
            );
        }
        other => panic!("expected definition elaboration result, got {other:?}"),
    }
}

#[test]
fn test_match_as_lit_inner_supported() {
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
                    "x".to_string(),
                    Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "x".to_string()),
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
        result.is_ok(),
        "expected match As(name, Lit) to elaborate, got {result:?}"
    );
}

#[test]
fn test_match_as_numeral_add_inner_supported() {
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
                    "x".to_string(),
                    Box::new(SurfacePattern::NumeralAdd(
                        Box::new(SurfacePattern::Var("k".to_string())),
                        1,
                    )),
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "k".to_string()),
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
        "expected match As(name, NumeralAdd) to elaborate, got {result:?}"
    );
}

#[test]
fn test_match_as_numeral_add_offset_two_inner_supported() {
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
                    "x".to_string(),
                    Box::new(SurfacePattern::NumeralAdd(
                        Box::new(SurfacePattern::Var("k".to_string())),
                        2,
                    )),
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "k".to_string()),
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
        "expected match As(name, NumeralAdd(_, 2)) to elaborate, got {result:?}"
    );
}

#[test]
fn test_match_as_ctor_inner_supported() {
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
                        vec![SurfacePattern::Var("k".to_string())],
                    )),
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "k".to_string()),
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
        "expected match As(name, Ctor(...)) to elaborate, got {result:?}"
    );
}

#[test]
fn test_match_as_nested_multifield_ctor_inner_with_bare_names_supported() {
    use clean_parser::{Span, SurfaceExpr, SurfaceMatchArm, SurfacePattern};
    let env = option_prod_nat_bool_axiom_env("opt");
    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "opt".to_string());
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
                        "some".to_string(),
                        vec![SurfacePattern::Ctor(
                            "mk".to_string(),
                            vec![
                                SurfacePattern::Var("x".to_string()),
                                SurfacePattern::Ctor("true".to_string(), vec![]),
                            ],
                        )],
                    )),
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "whole".to_string()),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Ident(Span::dummy(), "opt".to_string()),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr).unwrap_or_else(|err| {
        panic!("expected match As(name, nested multi-field Ctor(...)) to elaborate, got {err:?}")
    });
    let result_ty = ctx.infer_type(&result).unwrap_or_else(|err| {
        panic!(
            "expected match As(name, nested multi-field Ctor(...)) to typecheck, got {err:?}; expr={result:?}"
        )
    });
    assert!(
        ctx.is_def_eq(&result_ty, &option_prod_nat_bool_ty()),
        "expected match As(name, nested multi-field Ctor(...)) to keep Option (Prod Nat Bool) type, got {result_ty:?}; expr={result:?}"
    );
}

#[test]
fn test_match_as_nested_multifield_ctor_inner_rejects_non_nat_numeric_bool_field() {
    use clean_parser::{Span, SurfaceExpr, SurfaceMatchArm, SurfacePattern};
    let env = option_prod_nat_bool_axiom_env("opt");
    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "opt".to_string());
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
                        "some".to_string(),
                        vec![SurfacePattern::Ctor(
                            "mk".to_string(),
                            vec![
                                SurfacePattern::Var("x".to_string()),
                                SurfacePattern::NumeralAdd(
                                    Box::new(SurfacePattern::Var("k".to_string())),
                                    2,
                                ),
                            ],
                        )],
                    )),
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "whole".to_string()),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: SurfaceExpr::Ident(Span::dummy(), "opt".to_string()),
            },
        ],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        matches!(result, Err(ElabError::NotImplemented(ref msg)) if msg.contains("only supported for Nat scrutinees") && msg.contains("Bool")),
        "expected alias rewrite to fail closed on numeric Bool field patterns, got {result:?}"
    );
}

#[test]
fn test_match_as_or_inner_supported_when_branches_supported() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = nat_axiom_env();
    let scrutinee = SurfaceExpr::Ident(Span::dummy(), "n".to_string());
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(scrutinee),
        vec![SurfaceMatchArm {
            span: Span::dummy(),
            pattern: SurfacePattern::As(
                "whole".to_string(),
                Box::new(SurfacePattern::Or(
                    Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
                    Box::new(SurfacePattern::NumeralAdd(
                        Box::new(SurfacePattern::Var("k".to_string())),
                        1,
                    )),
                )),
            ),
            body: SurfaceExpr::Ident(Span::dummy(), "whole".to_string()),
        }],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "expected match As(name, Or(...)) to elaborate when each branch is supported, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_as_pattern_lit_inner_supported() {
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
                    patterns: vec![SurfacePattern::As(
                        "whole".to_string(),
                        Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
                    )],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "whole".to_string())),
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
        "do-match as-pattern with literal inner should elaborate, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_as_pattern_numeral_add_inner_supported() {
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
                    patterns: vec![SurfacePattern::As(
                        "whole".to_string(),
                        Box::new(SurfacePattern::NumeralAdd(
                            Box::new(SurfacePattern::Var("k".to_string())),
                            1,
                        )),
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
        "do-match as-pattern with numeral-add inner should elaborate, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_as_pattern_ctor_inner_supported() {
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
                    patterns: vec![SurfacePattern::As(
                        "whole".to_string(),
                        Box::new(SurfacePattern::Ctor(
                            "Nat.succ".to_string(),
                            vec![SurfacePattern::Var("k".to_string())],
                        )),
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
        "do-match as-pattern with constructor inner should elaborate, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_as_pattern_nested_multifield_ctor_inner_with_bare_names_supported() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};
    let env = option_prod_nat_bool_axiom_env("opt");
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "opt".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::As(
                        "whole".to_string(),
                        Box::new(SurfacePattern::Ctor(
                            "some".to_string(),
                            vec![SurfacePattern::Ctor(
                                "mk".to_string(),
                                vec![
                                    SurfacePattern::Var("x".to_string()),
                                    SurfacePattern::Ctor("true".to_string(), vec![]),
                                ],
                            )],
                        )),
                    )],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "whole".to_string())),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "opt".to_string())),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elaborate(&surface)
        .unwrap_or_else(|err| panic!("do-match as-pattern with nested multi-field constructor inner should elaborate, got {err:?}"));
    let _ = ctx.infer_type(&result).unwrap_or_else(|err| {
        panic!(
            "do-match as-pattern with nested multi-field constructor inner should typecheck, got {err:?}; expr={result:?}"
        )
    });
}

#[test]
fn test_elab_do_match_as_pattern_nested_multifield_ctor_inner_rejects_non_nat_numeric_bool_field() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};
    let env = option_prod_nat_bool_axiom_env("opt");
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "opt".to_string())],
            vec![
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::As(
                        "whole".to_string(),
                        Box::new(SurfacePattern::Ctor(
                            "some".to_string(),
                            vec![SurfacePattern::Ctor(
                                "mk".to_string(),
                                vec![
                                    SurfacePattern::Var("x".to_string()),
                                    SurfacePattern::NumeralAdd(
                                        Box::new(SurfacePattern::Var("k".to_string())),
                                        2,
                                    ),
                                ],
                            )],
                        )),
                    )],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "whole".to_string())),
                    )],
                },
                DoMatchArm {
                    span: Span::dummy(),
                    patterns: vec![SurfacePattern::Wildcard],
                    body: vec![DoElem::Expr(
                        Span::dummy(),
                        Box::new(SurfaceExpr::Ident(Span::dummy(), "opt".to_string())),
                    )],
                },
            ],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        matches!(result, Err(ElabError::NotImplemented(ref msg)) if msg.contains("only supported for Nat scrutinees") && msg.contains("Bool")),
        "expected do-match alias rewrite to fail closed on numeric Bool field patterns, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_as_pattern_or_inner_supported() {
    use clean_parser::{DoElem, DoMatchArm, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();

    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Match(
            Span::dummy(),
            vec![SurfaceExpr::Ident(Span::dummy(), "n".to_string())],
            vec![DoMatchArm {
                span: Span::dummy(),
                patterns: vec![SurfacePattern::As(
                    "whole".to_string(),
                    Box::new(SurfacePattern::Or(
                        Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
                        Box::new(SurfacePattern::NumeralAdd(
                            Box::new(SurfacePattern::Var("k".to_string())),
                            1,
                        )),
                    )),
                )],
                body: vec![DoElem::Expr(
                    Span::dummy(),
                    Box::new(SurfaceExpr::Ident(Span::dummy(), "whole".to_string())),
                )],
            }],
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "do-match as-pattern with Or inner should elaborate when each branch is supported, got {result:?}"
    );
}
