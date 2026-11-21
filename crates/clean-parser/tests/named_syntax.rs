// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_parser::{parse_name, Parser, SurfaceDecl, SyntaxPatternItem};

#[test]
fn decl_options_do_not_become_parts_of_the_syntax_pattern() {
    let source = r#"syntax:51 (name := Outer.«dot.name») (priority := default+1) "probe" : term"#;
    let SurfaceDecl::Syntax {
        name,
        precedence,
        priority,
        pattern,
        ..
    } = Parser::parse_decl(source).unwrap()
    else {
        panic!("expected syntax");
    };
    assert_eq!(
        name.unwrap().name(),
        parse_name("Outer.«dot.name»").unwrap().name()
    );
    assert_eq!((precedence, priority), (Some(51), Some(1001u64.into())));
    assert!(matches!(&pattern[..], [SyntaxPatternItem::Literal(s)] if s=="probe"));
}

#[test]
fn invalid_syntax_names_are_rejected_at_the_declaration() {
    for source in [
        r#"syntax (name := ) "probe" : term"#,
        r#"syntax [myAdd] term "+" term : term"#,
        r#"syntax (name := calc) "probe" : term"#,
    ] {
        assert!(Parser::parse_decl(source).is_err(), "{source}");
    }
}

#[test]
fn named_priorities_reject_malformed_operands_and_evaluate_wide_subtraction() {
    for bad in ["missingPriority", "high +", "(low", "«high»"] {
        let text = format!(r#"syntax (name := probe) (priority := {bad}) "priorityProbe" : term"#);
        assert!(Parser::parse_decl(&text).is_err(), "{text}");
    }
    let source =
        r#"syntax (priority := 18446744073709551617000 - 18446744073709551616999) "probe" : term"#;
    let SurfaceDecl::Syntax { priority, .. } = Parser::parse_decl(source).unwrap() else {
        panic!("expected syntax");
    };
    assert_eq!(priority, Some(1u64.into()));
}
