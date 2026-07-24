// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused if-let nat-pattern regressions for #796.

use super::*;

#[test]
fn test_if_let_nat_zero_pattern_supported() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let result = elab_with_env(&env, "if let 0 := n then 1 else 0");
    assert!(
        result.is_ok(),
        "Nat.zero literal pattern should elaborate in if-let, got {result:?}"
    );
}

#[test]
fn test_if_let_numeral_add_one_pattern_supported() {
    use clean_parser::{Span, SurfaceExpr, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::NumeralAdd(Box::new(SurfacePattern::Var("k".to_string())), 1),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "k".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "`n + 1` pattern should elaborate in if-let, got {result:?}"
    );
}

#[test]
fn test_if_let_nonzero_nat_literal_pattern_supported() {
    // #796: Non-zero Nat literal patterns desugar to nested Nat.succ casesOn.
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let result = elab_with_env(&env, "if let 1 := n then 1 else 0");
    assert!(
        result.is_ok(),
        "Nat literal 1 pattern should elaborate in if-let, got {result:?}"
    );
}

#[test]
fn test_if_let_nat_literal_2_pattern_supported() {
    // #796: Nat(2) desugars to two nested Nat.succ casesOn around Nat.zero.
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let result = elab_with_env(&env, "if let 2 := n then 1 else 0");
    assert!(
        result.is_ok(),
        "Nat literal 2 pattern should elaborate in if-let, got {result:?}"
    );
}

#[test]
fn test_if_let_numeral_add_offset_two_pattern_supported() {
    use clean_parser::{Span, SurfaceExpr, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::NumeralAdd(Box::new(SurfacePattern::Var("k".to_string())), 2),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "k".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "`n + 2` pattern should elaborate in if-let, got {result:?}"
    );
}

#[test]
fn test_if_let_nat_literal_pattern_requires_nat_scrutinee() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let result = elab_with_env(&env, "if let 0 := b then 1 else 0");
    assert!(
        matches!(result, Err(ElabError::NotImplemented(ref msg)) if msg.contains("only supported for Nat scrutinees")),
        "expected fail-closed NotImplemented for if-let Nat literal on Bool, got {result:?}"
    );
}
