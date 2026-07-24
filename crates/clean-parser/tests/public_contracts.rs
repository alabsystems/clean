// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Andrew Yates <andrewyates.name@gmail.com>

use clean_parser::lexer::{Lexer, TokenKind};
use clean_parser::surface::{AesopAttr, AesopBuilder, AesopIndexMode, AesopPhase, Attribute};
use clean_parser::{
    parse_expr_with_tactics, SurfaceExpr, SurfaceTactic, TacticArgPattern, TacticPatterns,
};

#[test]
fn token_kind_as_keyword_str_roundtrip() {
    assert_eq!(TokenKind::Def.as_keyword_str(), Some("def"));
    assert_eq!(TokenKind::Theorem.as_keyword_str(), Some("theorem"));
    assert_eq!(TokenKind::Ident("foo".to_string()).as_keyword_str(), None);
    assert_eq!(TokenKind::nat_lit(7).as_keyword_str(), None);
}

#[test]
fn attribute_instance_priority_contracts() {
    assert_eq!(
        Attribute::InstancePriority(42).instance_priority(),
        Some(42)
    );
    // `@[default_instance]` feeds the default-instance table; it does NOT
    // override the instance's ordinary resolution priority (B99).
    assert_eq!(
        Attribute::DefaultInstance { priority: None }.instance_priority(),
        None
    );
    assert_eq!(
        Attribute::DefaultInstance {
            priority: Some(200)
        }
        .instance_priority(),
        None
    );

    let aesop = AesopAttr {
        phase: AesopPhase::Safe,
        builder: AesopBuilder::Apply,
        builder_args: Vec::new(),
        priority: None,
        rule_sets: Vec::new(),
        index_mode: AesopIndexMode::Target,
    };
    assert_eq!(Attribute::Aesop(aesop).instance_priority(), None);
    assert_eq!(
        Attribute::Unknown("x".to_string()).instance_priority(),
        None
    );
}

#[test]
fn lexer_next_token_eof_contracts() {
    let mut lexer = Lexer::new("def");
    let tok = lexer.next_token();
    assert_eq!(tok.kind, TokenKind::Def);
    assert!(tok.span.start <= tok.span.end);

    let eof = lexer.next_token();
    assert_eq!(eof.kind, TokenKind::Eof);
    assert_eq!(eof.span.start, eof.span.end);
}

#[test]
fn public_tactic_pattern_reexport_drives_pattern_aware_parsing() {
    let mut patterns = TacticPatterns::new();
    patterns.insert("my_intro".to_string(), TacticArgPattern::IdentList);

    let expr = parse_expr_with_tactics("by my_intro x y", &patterns)
        .expect("crate-root tactic pattern types should drive parser dispatch");

    let tactics = match expr {
        SurfaceExpr::ByTactic(_, tactics) => tactics,
        other => panic!("expected by-tactic expression, got {other:?}"),
    };

    assert_eq!(tactics.len(), 1, "expected a single named tactic");
    match &tactics[0] {
        SurfaceTactic::Named { name, args, .. } => {
            assert_eq!(name, "my_intro");
            assert_eq!(
                args.len(),
                2,
                "IdentList should keep two identifier arguments"
            );
        }
        other => panic!("expected named tactic, got {other:?}"),
    }
}

#[test]
fn test_parse_conv_arg_i64_min_negate_no_overflow() {
    // Regression: `arg -9223372036854775808` puts 2^63 in a `NatLit(u64)`;
    // the old `-(n as i64)` computed `-(i64::MIN)` and panicked in debug
    // ('attempt to negate with overflow') / silently wrapped in release.
    // After the fix it must parse without panicking and clamp to i64::MIN.
    let r = clean_parser::parse_expr("by conv => arg -9223372036854775808");
    assert!(
        r.is_ok(),
        "conv arg with 2^63 magnitude must parse, got {r:?}"
    );

    // Normal in-range indices are unchanged (correct-path semantics preserved).
    assert!(clean_parser::parse_expr("by conv => arg 3").is_ok());
    assert!(clean_parser::parse_expr("by conv => arg -3").is_ok());
}

#[test]
fn test_parse_conv_enter_i64_min_negate_no_overflow() {
    // Regression: `enter [-9223372036854775808]` puts 2^63 in a `NatLit(u64)`;
    // the old `-(n as i64)` in `parse_enter_arg` computed `-(i64::MIN)` and
    // panicked in debug ('attempt to negate with overflow') / silently wrapped
    // in release. After the fix it must parse without panicking, clamping the
    // out-of-range index to i64::MIN.
    let r = clean_parser::parse_expr("by conv => enter [-9223372036854775808]");
    assert!(
        r.is_ok(),
        "conv enter with 2^63 magnitude must parse, got {r:?}"
    );

    // Normal in-range indices are unchanged (correct-path semantics preserved).
    assert!(clean_parser::parse_expr("by conv => enter [1, 2]").is_ok());
    assert!(clean_parser::parse_expr("by conv => enter [-1]").is_ok());
    assert!(clean_parser::parse_expr("by conv => enter [-2, 0]").is_ok());
}
