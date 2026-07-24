// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused do-if-let pattern regressions for #796.

use super::*;
use clean_parser::SurfaceLit;

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
fn test_do_if_let_ctor_pattern_binds_field_in_then_branch() {
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::IfLet(
            Span::dummy(),
            SurfacePattern::Ctor(
                "Nat.succ".to_string(),
                vec![SurfacePattern::Var("k".to_string())],
            ),
            Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(Span::dummy(), "k".to_string())),
            )],
            Some(vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
            )]),
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "constructor-pattern do-if-let should bind the field in the then branch, got {result:?}"
    );
}

#[test]
fn test_do_if_let_ctor_pattern_without_else_uses_unit_fallback() {
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::IfLet(
            Span::dummy(),
            SurfacePattern::Ctor(
                "Nat.succ".to_string(),
                vec![SurfacePattern::Var("k".to_string())],
            ),
            Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
            vec![DoElem::Return(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(Span::dummy(), "Unit.unit".to_string())),
            )],
            None,
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    // No current_expected_type — level_eq callback resolves universe params
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "constructor-pattern do-if-let without else should use the implicit pure-unit fallback, got {result:?}"
    );
}

#[test]
fn test_do_if_let_literal_pattern_without_else_uses_unit_fallback() {
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::IfLet(
            Span::dummy(),
            SurfacePattern::Lit(SurfaceLit::Nat(0)),
            Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
            vec![DoElem::Return(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(Span::dummy(), "Unit.unit".to_string())),
            )],
            None,
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "literal-pattern do-if-let without else should use the implicit pure-unit fallback, got {result:?}"
    );
}

#[test]
fn test_do_if_let_ctor_nested_literal_pattern_elaborates() {
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::IfLet(
            Span::dummy(),
            SurfacePattern::Ctor(
                "Nat.succ".to_string(),
                vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
            ),
            Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
            )],
            Some(vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
            )]),
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "expected do-if-let nested ctor literal pattern to elaborate via do-match nested casesOn, got {result:?}"
    );
}

#[test]
fn test_do_if_let_as_ctor_nested_literal_pattern_elaborates() {
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::IfLet(
            Span::dummy(),
            SurfacePattern::As(
                "whole".to_string(),
                Box::new(SurfacePattern::Ctor(
                    "Nat.succ".to_string(),
                    vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
                )),
            ),
            Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
            )],
            Some(vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
            )]),
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "expected As-pattern do-if-let nested ctor literal pattern to elaborate via recursive if-let lowering, got {result:?}"
    );
}

#[test]
fn test_do_if_let_or_ctor_nested_literal_pattern_elaborates() {
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::IfLet(
            Span::dummy(),
            SurfacePattern::Or(
                Box::new(SurfacePattern::Ctor(
                    "Nat.succ".to_string(),
                    vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
                )),
                Box::new(SurfacePattern::Wildcard),
            ),
            Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
            )],
            Some(vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
            )]),
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "expected Or-pattern do-if-let nested ctor literal pattern to elaborate via recursive if-let lowering, got {result:?}"
    );
}

#[test]
fn test_do_if_let_as_pattern_uses_fresh_shared_scrutinee_when_base_name_taken() {
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

    let mut env = nat_axiom_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("__iflet_scrutinee"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::IfLet(
            Span::dummy(),
            SurfacePattern::As(
                "whole".to_string(),
                Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
            ),
            Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
            )],
            Some(vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
            )]),
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "As-pattern do-if-let should keep matching on the Nat scrutinee even when __iflet_scrutinee already exists, got {result:?}"
    );
}

#[test]
fn test_do_if_let_or_pattern_uses_fresh_shared_scrutinee_when_base_name_taken() {
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

    let mut env = nat_axiom_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("__iflet_scrutinee"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::IfLet(
            Span::dummy(),
            SurfacePattern::Or(
                Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
                Box::new(SurfacePattern::NumeralAdd(
                    Box::new(SurfacePattern::Wildcard),
                    1,
                )),
            ),
            Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
            )],
            Some(vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
            )]),
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "Or-pattern do-if-let should keep matching on the Nat scrutinee even when __iflet_scrutinee already exists, got {result:?}"
    );
}

#[test]
fn test_do_if_let_or_pattern_without_else_uses_unit_fallback() {
    use clean_parser::{DoElem, Span, SurfaceExpr, SurfacePattern};

    let env = nat_axiom_env();
    let surface = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::IfLet(
            Span::dummy(),
            SurfacePattern::Or(
                Box::new(SurfacePattern::Lit(SurfaceLit::Nat(0))),
                Box::new(SurfacePattern::NumeralAdd(
                    Box::new(SurfacePattern::Wildcard),
                    1,
                )),
            ),
            Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
            vec![DoElem::Return(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(Span::dummy(), "Unit.unit".to_string())),
            )],
            None,
        )],
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "Or-pattern do-if-let without else should use the implicit pure-unit fallback, got {result:?}"
    );
}
