// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `elab` / `elab_rules` tactic-elaborator registration.
//!
//! Covers the nullary path (single string-literal keyword) and the
//! non-nullary core (keyword followed by bound term/ident antiquotations).

use super::*;
use crate::tactic::{ProofState, TacticArgPattern, TacticError};
use clean_kernel::Expr;
use clean_parser::{parse_expr, Span, SurfaceExpr, SyntaxPatternItem};

/// Build an `elab "<kw>" <vars> : tactic => <body>` surface declaration.
fn elab_tactic_decl(
    keyword: &str,
    vars: &[(&str, Option<&str>)],
    body: SurfaceExpr,
) -> SurfaceDecl {
    let mut pattern = vec![SyntaxPatternItem::Literal(keyword.to_owned())];
    for (name, category) in vars {
        pattern.push(SyntaxPatternItem::Variable {
            name: (*name).to_owned(),
            category: category.map(str::to_owned),
        });
    }
    SurfaceDecl::Elab {
        span: Span::dummy(),
        pattern,
        category: "tactic".to_owned(),
        body: Box::new(body),
    }
}

/// A body with no `throwError` so the synthesized bound-variable message fires.
fn placeholder_body() -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), "skip".to_owned())
}

/// Build an `elab "<kw>" <vars> : term => <body>` surface declaration.
fn elab_term_decl(keyword: &str, vars: &[(&str, Option<&str>)], body: SurfaceExpr) -> SurfaceDecl {
    let mut pattern = vec![SyntaxPatternItem::Literal(keyword.to_owned())];
    for (name, category) in vars {
        pattern.push(SyntaxPatternItem::Variable {
            name: (*name).to_owned(),
            category: category.map(str::to_owned),
        });
    }
    SurfaceDecl::Elab {
        span: Span::dummy(),
        pattern,
        category: "term".to_owned(),
        body: Box::new(body),
    }
}

#[test]
fn test_elab_rules_nullary_tactic_registers_nullary_pattern() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let decl = elab_tactic_decl("my_nullary", &[], placeholder_body());
    ctx.elab_decl(&decl).expect("nullary elab_rules elaborates");

    let entry = ctx
        .tactic_registry
        .get("my_nullary")
        .expect("nullary tactic should be registered");
    assert_eq!(entry.pattern, TacticArgPattern::Nullary);
}

#[test]
fn test_elab_rules_term_arg_tactic_binds_variable_and_fires() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // elab "my_term" e:term : tactic => skip
    let decl = elab_tactic_decl("my_term", &[("e", Some("term"))], placeholder_body());
    ctx.elab_decl(&decl)
        .expect("non-nullary elab_rules elaborates");

    let entry = ctx
        .tactic_registry
        .get("my_term")
        .cloned()
        .expect("term-arg tactic should be registered");

    // A single non-ident variable maps to single-term argument parsing.
    assert_eq!(entry.pattern, TacticArgPattern::TermArg);

    // Fire the handler with one elaborated argument. The handler should fail
    // (no body interpreter yet) but its message must surface the bound variable
    // name `e` and the received argument count, proving binding fired correctly.
    let mut ps = ProofState::new(Environment::new(), Expr::prop());
    let arg = Expr::const_str("Foo");
    let err = (entry.handler)(&mut ps, std::slice::from_ref(&arg))
        .expect_err("placeholder handler should report unsupported body");
    let TacticError::ElaborationFailed { detail } = err else {
        panic!("expected ElaborationFailed, got {err:?}");
    };
    assert!(
        detail.contains('e'),
        "handler message should mention bound variable `e`: {detail}"
    );
    assert!(
        detail.contains("received 1 argument"),
        "handler message should report the received argument count: {detail}"
    );
}

#[test]
fn test_elab_rules_ident_args_map_to_ident_list() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // elab "my_idents" x:ident y:ident : tactic => skip
    let decl = elab_tactic_decl(
        "my_idents",
        &[("x", Some("ident")), ("y", Some("ident"))],
        placeholder_body(),
    );
    ctx.elab_decl(&decl)
        .expect("ident-list elab_rules elaborates");

    let entry = ctx
        .tactic_registry
        .get("my_idents")
        .expect("ident-list tactic should be registered");
    assert_eq!(entry.pattern, TacticArgPattern::IdentList);
}

#[test]
fn test_elab_rules_repetition_pattern_is_deferred() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // A repetition sub-pattern is not yet supported; registration is skipped.
    let decl = SurfaceDecl::Elab {
        span: Span::dummy(),
        pattern: vec![
            SyntaxPatternItem::Literal("my_rep".to_owned()),
            SyntaxPatternItem::Repetition {
                pattern: vec![SyntaxPatternItem::Variable {
                    name: "xs".to_owned(),
                    category: Some("term".to_owned()),
                }],
                separator: Some(",".to_owned()),
                at_least_one: false,
            },
        ],
        category: "tactic".to_owned(),
        body: Box::new(placeholder_body()),
    };
    ctx.elab_decl(&decl)
        .expect("deferred pattern elaborates as skip");

    assert!(
        ctx.tactic_registry.get("my_rep").is_none(),
        "repetition patterns should be deferred, not registered"
    );
}

#[test]
fn test_elab_rules_non_tactic_category_is_skipped() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let decl = SurfaceDecl::Elab {
        span: Span::dummy(),
        pattern: vec![SyntaxPatternItem::Literal("my_term_elab".to_owned())],
        category: "term".to_owned(),
        body: Box::new(placeholder_body()),
    };
    ctx.elab_decl(&decl)
        .expect("non-tactic elab_rules elaborates as skip");

    assert!(
        ctx.tactic_registry.get("my_term_elab").is_none(),
        "term-category elaborators are deferred, not registered as tactics"
    );
}

#[test]
fn test_term_elab_identity_wrapper_elaborates_to_argument() {
    // elab "mywrap" e:term : term => e   makes `mywrap "hi"` elaborate to `"hi"`.
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let decl = elab_term_decl(
        "mywrap",
        &[("e", Some("term"))],
        SurfaceExpr::Ident(Span::dummy(), "e".to_owned()),
    );
    ctx.elab_decl(&decl).expect("term elaborator registers");

    let call = parse_expr(r#"mywrap "hi""#).expect("call parses");
    let elaborated = ctx
        .elaborate(&call)
        .expect("user term elaborator should elaborate the substituted body");
    assert_eq!(
        elaborated,
        Expr::str_lit("hi"),
        "the identity wrapper should elaborate to its kernel-checked argument"
    );
}

#[test]
fn test_term_elab_body_uses_argument_in_application() {
    // elab "boxit" e:term : term => box e   makes `boxit "hi"` elaborate to
    // `box "hi"`, kernel-checked through the normal pipeline. `box` is an
    // env-registered function constant so the test needs no prelude.
    use clean_kernel::name::Name;
    let mut env = Environment::new();
    let string_ty = Expr::const_(Name::from_string("String"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("String"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("String type registers");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("box"),
        level_params: vec![],
        type_: Expr::arrow(string_ty.clone(), string_ty),
    })
    .expect("box function registers");

    let mut ctx = ElabCtx::new(&env);
    let body = parse_expr("box e").expect("body parses");
    let decl = elab_term_decl("boxit", &[("e", Some("term"))], body);
    ctx.elab_decl(&decl).expect("term elaborator registers");

    let call = parse_expr(r#"boxit "hi""#).expect("call parses");
    let elaborated = ctx
        .elaborate(&call)
        .expect("argument should be substituted into the body application");

    let expected = Expr::app(
        Expr::const_(Name::from_string("box"), vec![]),
        Expr::str_lit("hi"),
    );
    assert_eq!(
        elaborated, expected,
        "the bound argument should appear inside the elaborated application"
    );
}

#[test]
fn test_term_elab_nullary_keyword_elaborates_body() {
    // elab "myhi" : term => "hi"   makes `myhi` elaborate to the string `"hi"`.
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let body = parse_expr(r#""hi""#).expect("body parses");
    let decl = elab_term_decl("myhi", &[], body);
    ctx.elab_decl(&decl)
        .expect("nullary term elaborator registers");

    let call = parse_expr("myhi").expect("call parses");
    let elaborated = ctx
        .elaborate(&call)
        .expect("nullary user term elaborator should elaborate its body");
    assert_eq!(elaborated, Expr::str_lit("hi"));
}

#[test]
fn test_term_elab_ill_typed_body_fails_elaboration() {
    // A body that is an unknown identifier must fail elaboration — the user term
    // elaborator never fabricates well-typedness.
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let decl = elab_term_decl(
        "mybad",
        &[("e", Some("term"))],
        SurfaceExpr::Ident(Span::dummy(), "Definitely.Not.A.Real.Constant".to_owned()),
    );
    ctx.elab_decl(&decl).expect("term elaborator registers");

    let call = parse_expr(r#"mybad "x""#).expect("call parses");
    ctx.elaborate(&call)
        .expect_err("an ill-typed body must fail through the normal pipeline");
}

#[test]
fn test_term_elab_arity_mismatch_does_not_intercept() {
    // Declared one bound var; a zero-arg use (`mywrap`) must not be silently
    // intercepted — it falls through to normal elaboration (here: unknown ident).
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let decl = elab_term_decl(
        "mywrap",
        &[("e", Some("term"))],
        SurfaceExpr::Ident(Span::dummy(), "e".to_owned()),
    );
    ctx.elab_decl(&decl).expect("term elaborator registers");

    let call = parse_expr("mywrap").expect("bare keyword parses as ident");
    ctx.elaborate(&call).expect_err(
        "a bare keyword with a non-nullary declaration should not be intercepted as the body",
    );
}
