// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{Parser, SurfaceArg, SurfaceLit};

fn expression(source: &str) -> (SurfaceExpr, SourceOrigins, OriginId) {
    let captured = Parser::parse_expr_with_origins(source).expect("parse source");
    let origins = captured.origins.expect("valid observation");
    let [OriginRoot::Expression(OriginAvailability::Located(root))] = origins.roots() else {
        panic!("expected a located expression root: {:?}", origins.roots());
    };
    let root = root.clone();
    (captured.parsed, origins, root)
}

#[test]
fn source_origins_capture_off_on_preserves_parser_output_and_refusals() {
    for source in [
        "f (g x) 7",
        "«😀.x»",
        "?_",
        "?goal",
        "fun x => x",
        "⊤",
        "[1, 2]",
    ] {
        let ordinary = Parser::parse_expr(source);
        let observed = Parser::parse_expr_with_origins(source).map(|result| result.parsed);
        assert_eq!(format!("{ordinary:?}"), format!("{observed:?}"), "{source}");
    }
    for source in [
        "def f (n : Nat) : Nat := g n",
        "def bad : := 1\ndef good := 7",
        "def «😀» := _",
    ] {
        let ordinary = Parser::parse_file(source);
        let observed = Parser::parse_file_with_origins(source).map(|result| result.parsed);
        assert_eq!(format!("{ordinary:?}"), format!("{observed:?}"), "{source}");
    }
    for source in ["(", "f +", "def bad : := 1"] {
        let ordinary = Parser::parse_expr(source);
        let observed = Parser::parse_expr_with_origins(source).map(|result| result.parsed);
        assert_eq!(format!("{ordinary:?}"), format!("{observed:?}"), "{source}");
    }
}

#[test]
fn source_origins_declaration_names_are_actual_tokens_without_universe_suffix() {
    let source = "@[simp] private def A.«😀.β».item.{u} : Nat := 7\ntheorem rfl : True := h\naxiom α : Nat\nopaque «with space» : Nat";
    let captured = Parser::parse_file_with_origins(source).expect("parse declarations");
    let origins = captured.origins.expect("valid observation");
    // A file parse records one declaration root per declaration and never an
    // expression root, so every root must be a declaration.
    let declaration_names: Vec<_> = origins
        .roots()
        .iter()
        .map(|root| match root {
            OriginRoot::Declaration { name, .. } => name,
            OriginRoot::Expression(_) => panic!("file parse recorded an expression root"),
        })
        .collect();
    let names: Vec<_> = declaration_names
        .iter()
        .map(|name| origins.text(name).expect("name slice"))
        .collect();
    assert_eq!(names, ["A.«😀.β».item", "rfl", "α", "«with space»"]);
    for name in declaration_names {
        assert_eq!(
            origins.node(name).expect("owned name").kind(),
            OriginKind::DeclarationName
        );
        assert!(origins.children(name).expect("owned name").is_empty());
    }
}

#[test]
fn source_origins_application_roles_and_full_source_ranges_preserve_legacy_spans() {
    let (expr, origins, root) = expression("f (g x) 7");
    assert_eq!(
        expr.span(),
        Span::new(0, 1),
        "legacy AST span stays unchanged"
    );
    assert_eq!(origins.node(&root).expect("root").span(), Span::new(0, 9));
    assert_eq!(origins.text(&root), Some("f (g x) 7"));
    let children = origins.children(&root).expect("children");
    assert_eq!(
        children.iter().map(|(role, _)| *role).collect::<Vec<_>>(),
        [
            OriginChildRole::ApplicationHead,
            OriginChildRole::ApplicationArgument(0),
            OriginChildRole::ApplicationArgument(1),
        ]
    );
    assert_eq!(
        children
            .iter()
            .map(|(_, id)| origins.text(id).expect("child text"))
            .collect::<Vec<_>>(),
        ["f", "(g x)", "7"]
    );
    let grouped = origins.children(&children[1].1).expect("paren child");
    assert_eq!(grouped[0].0, OriginChildRole::Parenthesized);
    assert_eq!(origins.text(&grouped[0].1), Some("g x"));
    assert!(origins.pass_through(&root, &expr).is_some());
}

#[test]
fn source_origins_unsupported_and_generated_roots_are_unavailable() {
    for source in [
        "()",
        "⊤",
        "⊥",
        "∅",
        "[1, 2]",
        "fun x => x",
        "f (x := 1)",
        "f ..",
        "f.x",
        "x + y",
    ] {
        let result = Parser::parse_expr_with_origins(source).expect("ordinary parse succeeds");
        let origins = result
            .origins
            .expect("unsupported is not an invariant error");
        assert!(
            matches!(
                origins.roots(),
                [OriginRoot::Expression(OriginAvailability::Unavailable)]
            ),
            "{source}: {:?}",
            origins.roots()
        );
        assert!(
            origins.nodes.is_empty(),
            "uncommitted child origins must not escape: {source}"
        );
    }
    let tokens = crate::lexer::Lexer::tokenize("x");
    for generated in [
        SurfaceName::generated_path("x"),
        SurfaceName::global_path("x"),
        SurfaceName::component("different", false),
    ] {
        let mut builder = OriginBuilder::new("x");
        let generated = SurfaceExpr::Ident(Span::new(0, 1), generated);
        builder.atom(&generated, &tokens[..1]);
        builder.expression_root(&generated);
        assert!(builder
            .finish()
            .expect("unsupported generated atom")
            .nodes
            .is_empty());
    }
}

#[test]
fn source_origins_pass_through_checks_hygiene_spelling_global_policy_and_spans() {
    let (expr, origins, root) = expression("x");
    let SurfaceExpr::Ident(span, name) = &expr else {
        panic!("identifier");
    };
    for changed in [
        SurfaceName::generated_path("x"),
        SurfaceName::component("x", true),
        SurfaceName::global_path("x"),
        name.clone().as_section_variable(),
        name.clone().with_header_binder_origin(true),
        name.clone()
            .with_template_scope(crate::surface::TemplateScope(99)),
    ] {
        assert_eq!(name.name(), changed.name(), "same semantic name");
        assert!(origins
            .pass_through(&root, &SurfaceExpr::Ident(*span, changed))
            .is_none());
    }
    assert!(origins
        .pass_through(&root, &SurfaceExpr::Ident(Span::new(0, 2), name.clone()))
        .is_none());
    let (app, origins, root) = expression("f 7");
    let SurfaceExpr::App(span, head, mut args) = app.clone() else {
        panic!("app");
    };
    args[0].span = Span::new(2, 4);
    assert!(origins
        .pass_through(&root, &SurfaceExpr::App(span, head, args))
        .is_none());
    let SurfaceExpr::App(span, head, _) = app else {
        panic!("app");
    };
    let changed = SurfaceExpr::App(
        span,
        head,
        vec![SurfaceArg::positional(SurfaceExpr::Lit(
            Span::new(2, 3),
            SurfaceLit::Nat(8),
        ))],
    );
    assert!(origins.pass_through(&root, &changed).is_none());
}

#[test]
fn source_origins_clone_keeps_owner_but_independent_parse_and_modified_ast_do_not() {
    let (mut expr, origins, root) = expression("f 7");
    let cloned = origins.clone();
    assert!(cloned.pass_through(&root, &expr).is_some());
    let (_, independent, independent_root) = expression("f 7");
    assert_ne!(root, independent_root);
    assert!(independent.node(&root).is_none());
    assert!(independent.children(&root).is_none());
    assert!(independent.pass_through(&root, &expr).is_none());
    if let SurfaceExpr::App(_, _, args) = &mut expr {
        args.clear();
    }
    assert!(cloned.pass_through(&root, &expr).is_none());
    assert_eq!(cloned.text(&root), Some("f 7"));
}

#[test]
fn source_origins_recovered_declaration_invalidates_only_observations() {
    let source = "def broken : := 1\ndef later := 7";
    let ordinary = Parser::parse_file(source).expect("parser recovery output");
    let observed = Parser::parse_file_with_origins(source).expect("same parser recovery output");
    assert_eq!(format!("{ordinary:?}"), format!("{:?}", observed.parsed));
    assert_eq!(
        observed
            .origins
            .expect_err("recovery must not expose observations"),
        OriginCaptureError("file contains parser recovery")
    );
}

#[test]
fn source_origins_owned_attempt_rollback_and_invariant_error_are_observation_only() {
    let mut builder = OriginBuilder::new("x");
    let parsed = Parser::parse_expr("x").expect("ordinary parse");
    let tokens = crate::lexer::Lexer::tokenize("x");
    let checkpoint = builder.checkpoint();
    builder.atom(&parsed, &tokens[..1]);
    builder.expression_root(&parsed);
    builder.rollback(checkpoint);
    assert!(builder.nodes.is_empty());
    assert!(builder.roots.is_empty());
    builder.add(Span::new(0, 2), parsed.span(), Core::Hole);
    builder.rollback(checkpoint);
    assert_eq!(
        builder
            .finish()
            .expect_err("invariant error survives rollback"),
        OriginCaptureError("invalid original-source span")
    );
    assert!(
        Parser::parse_expr("x").is_ok(),
        "the independent parse verdict is unchanged"
    );
}

#[test]
fn source_origins_small_stack_preserves_bounded_parser_and_iterative_agreement() {
    std::thread::Builder::new()
        .stack_size(1024 * 1024)
        .spawn(|| {
            let source = format!("{}x{}", "f (".repeat(24), ")".repeat(24));
            let ordinary = Parser::parse_expr(&source).expect("ordinary small-stack parse");
            let (observed, origins, root) = expression(&source);
            assert_eq!(format!("{ordinary:?}"), format!("{observed:?}"));
            assert!(origins.pass_through(&root, &observed).is_some());
        })
        .expect("spawn small-stack parser")
        .join()
        .expect("small-stack parser finishes");
}
