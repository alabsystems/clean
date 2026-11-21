// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::{parse_decl_exact, Parser, SurfaceDecl, SurfaceExpr};

fn slice<'a>(source: &'a str, expr: &SurfaceExpr) -> &'a str {
    let span = expr.span();
    source.get(span.start..span.end).expect("valid byte span")
}

fn application_head(expr: &SurfaceExpr) -> (String, usize) {
    let SurfaceExpr::App(_, head, args) = expr else {
        panic!("expected the complete application: {expr:?}");
    };
    let SurfaceExpr::Explicit(_, head) = head.as_ref() else {
        panic!("expected the original explicit head: {head:?}");
    };
    let SurfaceExpr::Ident(_, name) = head.as_ref() else {
        panic!("expected the original constant: {head:?}");
    };
    (name.name().to_string(), args.len())
}

#[test]
fn original_f1_s1a_red_goal_and_body_slices_are_complete_applications() {
    // Exact original negative-control programs, copied without changing their
    // goals or reflexivity bodies from the maintained F1/S1a source tables.
    let sources: Vec<_> = include_str!("../../tests/fixtures/application_spans/f1_s1a_red.clean")
        .lines()
        .collect();
    assert_eq!(sources.len(), 3, "all three original RED controls");
    for source in sources {
        let (_, tail) = source.split_once(" : ").expect("closed original def");
        let (goal, proof) = tail
            .split_once(" := ")
            .expect("original type/body boundary");
        let SurfaceDecl::Def {
            ty: Some(ty), val, ..
        } = parse_decl_exact(source).expect("original declaration parses")
        else {
            panic!("original explicit def required");
        };
        assert_eq!(slice(source, &ty), goal, "complete original equality goal");
        assert_eq!(slice(source, &val), proof, "complete original proof body");
        assert_eq!(application_head(&ty), ("Eq".to_owned(), 3));
        assert_eq!(application_head(&val), ("Eq.refl".to_owned(), 2));
    }
}

#[test]
fn applications_cover_written_arguments_and_physical_delimiters() {
    for (source, expected) in [
        ("@id Nat 0", "@id Nat 0"),
        ("@Eq.{u} α left right", "@Eq.{u} α left right"),
        ("f (α := Nat)", "f (α := Nat)"),
        ("f (α := Nat) (x := (g y))", "f (α := Nat) (x := (g y))"),
        ("(@id Nat) (f 0)", "(@id Nat) (f 0)"),
        ("((f x)) y", "((f x)) y"),
        ("f (x : Nat)", "f (x : Nat)"),
        ("f x.y", "f x.y"),
        ("f A.{u}.field", "f A.{u}.field"),
        ("f x[0]", "f x[0]"),
        ("f ..", "f .."),
        ("f /- inner -/ (g x) /- tail -/", "f /- inner -/ (g x)"),
        (
            r#"  f «α.β» (x := "é") /- tail -/"#,
            r#"f «α.β» (x := "é")"#,
        ),
    ] {
        let expr = Parser::parse_expr(source).expect("existing application grammar");
        assert!(matches!(expr, SurfaceExpr::App(..)), "{source}: {expr:?}");
        assert_eq!(slice(source, &expr), expected, "{source}");
    }
}

#[test]
fn named_argument_metadata_keeps_inner_expression_spans() {
    let source = "f (α := Nat) (x := (g y))";
    let SurfaceExpr::App(_, head, args) = Parser::parse_expr(source).expect("named args") else {
        panic!("application");
    };
    assert_eq!(slice(source, &head), "f");
    assert_eq!(args.len(), 2);
    assert_eq!(
        args[0]
            .name
            .as_ref()
            .expect("implicit type argument")
            .name()
            .to_string(),
        "α"
    );
    assert_eq!(
        args[1]
            .name
            .as_ref()
            .expect("named value argument")
            .name()
            .to_string(),
        "x"
    );
    assert_eq!(slice(source, &args[0].expr), "Nat");
    assert_eq!(slice(source, &args[1].expr), "(g y)");
    for arg in args {
        assert_eq!(arg.span, arg.expr.span(), "existing SurfaceArg contract");
    }
}

#[test]
fn application_spans_stop_at_operators_and_the_next_declaration() {
    let source = "f x -> g y";
    let SurfaceExpr::Arrow(_, left, right) = Parser::parse_expr(source).expect("arrow boundary")
    else {
        panic!("arrow");
    };
    assert_eq!(slice(source, &left), "f x");
    assert_eq!(slice(source, &right), "g y");

    let source = "def first : Nat := f x\ndef second : Nat := g y";
    let declarations = Parser::parse_file(source).expect("declaration boundary");
    assert_eq!(declarations.len(), 2);
    for (declaration, expected) in declarations.iter().zip(["f x", "g y"]) {
        let SurfaceDecl::Def { val, .. } = declaration else {
            panic!("definition");
        };
        assert_eq!(slice(source, val), expected);
    }
}
