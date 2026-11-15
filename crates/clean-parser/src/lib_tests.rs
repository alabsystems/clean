// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn located_file_error_reports_absolute_utf8_byte_offset() {
    let source = "def café : Nat := 0\ndef bad : Nat := )\n";
    let patterns = TacticPatterns::default();
    let failure = parse_file_with_tactics_located(source, &patterns)
        .expect_err("the unmatched close delimiter must be rejected");
    assert_eq!(failure.byte_offset, source.find("def bad").unwrap());
}

#[test]
fn test_parse_identity() {
    let expr = parse_expr("fun x => x").unwrap();
    assert!(matches!(expr, SurfaceExpr::Lambda(_, _, _)));
}

#[test]
fn test_parse_def() {
    let decl = parse_decl("def id (x : Type) := x").unwrap();
    match decl {
        SurfaceDecl::Def { name, .. } => {
            assert_eq!((name).name(), SurfaceName::generated_path("id").name())
        }
        _ => panic!("expected Def"),
    }
}

/// Head identifier of a binary `App` (the operator that was lowered to).
fn binop_head(expr: &SurfaceExpr) -> &SurfaceName {
    match expr {
        SurfaceExpr::App(_, head, args) => {
            assert_eq!(args.len(), 2, "expected a binary application: {expr:?}");
            match head.as_ref() {
                SurfaceExpr::Ident(_, name) => name,
                other => panic!("expected ident head, got {other:?}"),
            }
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_parse_bitwise_operators_lower_to_h_ops() {
    assert_eq!(
        binop_head(&parse_expr("a &&& b").unwrap()),
        &SurfaceName::generated_path("HAnd.hAnd")
    );
    assert_eq!(
        binop_head(&parse_expr("a ||| b").unwrap()),
        &SurfaceName::generated_path("HOr.hOr")
    );
    assert_eq!(
        binop_head(&parse_expr("a ^^^ b").unwrap()),
        &SurfaceName::generated_path("HXor.hXor")
    );
    assert_eq!(
        binop_head(&parse_expr("a <<< b").unwrap()),
        &SurfaceName::generated_path("HShiftLeft.hShiftLeft")
    );
    assert_eq!(
        binop_head(&parse_expr("a >>> b").unwrap()),
        &SurfaceName::generated_path("HShiftRight.hShiftRight")
    );
    // Bool `&&`/`||` lower to `and`/`or`.
    assert_eq!(
        binop_head(&parse_expr("a && b").unwrap()),
        &SurfaceName::generated_path("and")
    );
    assert_eq!(
        binop_head(&parse_expr("a || b").unwrap()),
        &SurfaceName::generated_path("or")
    );
}

#[test]
fn test_parse_bitwise_precedence() {
    // `+`(65) binds tighter than `&&&`(60): `a &&& b + c` = `a &&& (b + c)`.
    let e = parse_expr("a &&& b + c").unwrap();
    assert_eq!(binop_head(&e), &SurfaceName::generated_path("HAnd.hAnd"));
    if let SurfaceExpr::App(_, _, args) = &e {
        assert_eq!(
            binop_head(&args[1].expr),
            &SurfaceName::generated_path("HAdd.hAdd")
        );
    }

    // `&&&`(60) binds tighter than `=`(50): `a = b &&& c` = `a = (b &&& c)`.
    let e = parse_expr("a = b &&& c").unwrap();
    assert_eq!(binop_head(&e), &SurfaceName::generated_path("Eq"));
    if let SurfaceExpr::App(_, _, args) = &e {
        assert_eq!(
            binop_head(&args[1].expr),
            &SurfaceName::generated_path("HAnd.hAnd")
        );
    }

    // `&&&`(60) binds tighter than `|||`(55): `a ||| b &&& c` = `a ||| (b &&& c)`.
    let e = parse_expr("a ||| b &&& c").unwrap();
    assert_eq!(binop_head(&e), &SurfaceName::generated_path("HOr.hOr"));
    if let SurfaceExpr::App(_, _, args) = &e {
        assert_eq!(
            binop_head(&args[1].expr),
            &SurfaceName::generated_path("HAnd.hAnd")
        );
    }

    // `<<<`(75) binds tighter than `+`(65): `a + b <<< c` = `a + (b <<< c)`.
    let e = parse_expr("a + b <<< c").unwrap();
    assert_eq!(binop_head(&e), &SurfaceName::generated_path("HAdd.hAdd"));
    if let SurfaceExpr::App(_, _, args) = &e {
        assert_eq!(
            binop_head(&args[1].expr),
            &SurfaceName::generated_path("HShiftLeft.hShiftLeft")
        );
    }
}

#[test]
fn test_parse_arrow_chain() {
    let expr = parse_expr("A -> B -> C").unwrap();
    // Right associative: A -> (B -> C)
    match expr {
        SurfaceExpr::Arrow(_, left, right) => {
            assert!(matches!(*left, SurfaceExpr::Ident(_, _)));
            assert!(matches!(*right, SurfaceExpr::Arrow(_, _, _)));
        }
        _ => panic!("expected Arrow"),
    }
}

#[test]
fn test_parse_projection_index() {
    let expr = parse_expr("x.1").unwrap();
    match expr {
        SurfaceExpr::Proj(_, base, Projection::Index(1)) => {
            assert!(
                matches!(*base, SurfaceExpr::Ident(_, ref name) if (name).name() == SurfaceName::generated_path("x").name())
            );
        }
        other => panic!("expected projection, got {other:?}"),
    }
}

#[test]
fn test_parse_projection_named_after_app() {
    let expr = parse_expr("(f x).field").unwrap();
    match expr {
        SurfaceExpr::Proj(_, base, Projection::Named(ref field)) => {
            assert_eq!((field).name(), SurfaceName::generated_path("field").name());
            let inner = match base.as_ref() {
                SurfaceExpr::Paren(_, inner) => inner.as_ref(),
                other => other,
            };
            assert!(
                matches!(inner, SurfaceExpr::App(_, _, _)),
                "expected application base, got {inner:?}"
            );
        }
        other => panic!("expected named projection, got {other:?}"),
    }
}

#[test]
fn test_parse_syntax_quote_preserved() {
    let expr = parse_expr("`(x)").unwrap();
    match expr {
        SurfaceExpr::SyntaxQuote(_, content) => assert!(content.contains('x')),
        other => panic!("expected syntax quote, got {other:?}"),
    }
}

// =========================================================================
// Aesop attribute parsing tests
//
// These tests verify that @[aesop] attributes produce Attribute::Aesop
// variants with correct phase, builder, and priority.
// =========================================================================

/// Test @[aesop safe] produces correct Aesop variant
#[test]
fn test_parse_aesop_safe_attribute() {
    // Test basic parsing - declaration name should be correct
    let decl = parse_decl("@[aesop safe] theorem my_thm : True := trivial").unwrap();
    match decl {
        SurfaceDecl::Theorem { name, .. } => {
            assert_eq!((name).name(), SurfaceName::generated_path("my_thm").name())
        }
        _ => panic!("expected Theorem"),
    }
}

/// Test @[aesop unsafe 30%] parses correctly
#[test]
fn test_parse_aesop_unsafe_attribute_with_priority() {
    let decl = parse_decl("@[aesop unsafe 30%] def my_def := 42").unwrap();
    match decl {
        SurfaceDecl::Def { name, .. } => {
            assert_eq!((name).name(), SurfaceName::generated_path("my_def").name())
        }
        _ => panic!("expected Def"),
    }
}

/// Test @[aesop safe apply] parses correctly
#[test]
fn test_parse_aesop_safe_apply_attribute() {
    let decl = parse_decl("@[aesop safe apply] theorem intro_rule : True := trivial").unwrap();
    match decl {
        SurfaceDecl::Theorem { name, .. } => assert_eq!(
            (name).name(),
            SurfaceName::generated_path("intro_rule").name()
        ),
        _ => panic!("expected Theorem"),
    }
}

/// Test @[aesop norm simp] parses correctly
#[test]
fn test_parse_aesop_norm_simp_attribute() {
    let decl = parse_decl("@[aesop norm simp] theorem simp_rule : True := trivial").unwrap();
    match decl {
        SurfaceDecl::Theorem { name, .. } => assert_eq!(
            (name).name(),
            SurfaceName::generated_path("simp_rule").name()
        ),
        _ => panic!("expected Theorem"),
    }
}

/// Test that grammar produces Aesop variant (not Unknown)
///
/// This test directly exercises the attribute parser to verify it returns
/// Attribute::Aesop, not Attribute::Unknown.
#[test]
fn test_aesop_attribute_produces_aesop_variant() {
    use crate::grammar::Parser;

    // Parse just the attribute part to verify correct variant
    let mut parser = Parser::new("@[aesop safe] x");
    let attrs = parser.attributes().unwrap();
    assert_eq!(attrs.len(), 1);
    match &attrs[0] {
        Attribute::Aesop(attr) => {
            assert_eq!(attr.phase, AesopPhase::Safe);
            assert_eq!(attr.builder, AesopBuilder::Apply); // default
            assert_eq!(attr.priority, None);
        }
        Attribute::Unknown(name) => {
            panic!("Expected Attribute::Aesop, got Attribute::Unknown({name})")
        }
        _ => panic!("Expected Attribute::Aesop"),
    }
}

/// Test unsafe attribute with priority parses to correct values
#[test]
fn test_aesop_unsafe_priority_values() {
    use crate::grammar::Parser;

    let mut parser = Parser::new("@[aesop unsafe 30%] x");
    let attrs = parser.attributes().unwrap();
    assert_eq!(attrs.len(), 1);
    match &attrs[0] {
        Attribute::Aesop(attr) => {
            assert_eq!(attr.phase, AesopPhase::Unsafe);
            assert_eq!(attr.builder, AesopBuilder::Apply);
            assert_eq!(attr.priority, Some(30));
        }
        _ => panic!("Expected Attribute::Aesop"),
    }
}

/// Test norm phase with simp builder
#[test]
fn test_aesop_norm_simp_values() {
    use crate::grammar::Parser;

    let mut parser = Parser::new("@[aesop norm simp] x");
    let attrs = parser.attributes().unwrap();
    assert_eq!(attrs.len(), 1);
    match &attrs[0] {
        Attribute::Aesop(attr) => {
            assert_eq!(attr.phase, AesopPhase::Norm);
            assert_eq!(attr.builder, AesopBuilder::Simp);
        }
        _ => panic!("Expected Attribute::Aesop"),
    }
}

/// Test all builder types
#[test]
fn test_aesop_all_builders() {
    use crate::grammar::Parser;

    let cases = [
        ("@[aesop safe apply] x", AesopBuilder::Apply),
        ("@[aesop safe cases] x", AesopBuilder::Cases),
        ("@[aesop safe constructors] x", AesopBuilder::Constructors),
        ("@[aesop safe destruct] x", AesopBuilder::Destruct),
        ("@[aesop safe forward] x", AesopBuilder::Forward),
        ("@[aesop norm simp] x", AesopBuilder::Simp),
        ("@[aesop safe tactic] x", AesopBuilder::Tactic),
        ("@[aesop safe unfold] x", AesopBuilder::Unfold),
    ];

    for (input, expected_builder) in cases {
        let mut parser = Parser::new(input);
        let attrs = parser.attributes().unwrap();
        match &attrs[0] {
            Attribute::Aesop(attr) => {
                assert_eq!(attr.builder, expected_builder, "Failed for input: {input}");
            }
            _ => panic!("Expected Attribute::Aesop for input: {input}"),
        }
    }
}

/// Test parsing rule set names in aesop attribute
#[test]
fn test_aesop_rule_set_single() {
    use crate::grammar::Parser;

    let mut parser = Parser::new("@[aesop safe apply, Measurable] x");
    let attrs = parser.attributes().unwrap();
    assert_eq!(attrs.len(), 1);
    match &attrs[0] {
        Attribute::Aesop(attr) => {
            assert_eq!(attr.phase, AesopPhase::Safe);
            assert_eq!(attr.builder, AesopBuilder::Apply);
            assert_eq!(attr.rule_sets, vec!["Measurable"]);
        }
        _ => panic!("Expected Attribute::Aesop"),
    }
}

/// Test parsing multiple rule sets
#[test]
fn test_aesop_rule_set_multiple() {
    use crate::grammar::Parser;

    let mut parser = Parser::new("@[aesop safe, Measurable, Continuous] x");
    let attrs = parser.attributes().unwrap();
    assert_eq!(attrs.len(), 1);
    match &attrs[0] {
        Attribute::Aesop(attr) => {
            assert_eq!(attr.phase, AesopPhase::Safe);
            assert_eq!(attr.builder, AesopBuilder::Apply); // default
            assert_eq!(attr.rule_sets, vec!["Measurable", "Continuous"]);
        }
        _ => panic!("Expected Attribute::Aesop"),
    }
}

/// Test that no rule sets results in empty vec
#[test]
fn test_aesop_no_rule_sets() {
    use crate::grammar::Parser;

    let mut parser = Parser::new("@[aesop safe apply] x");
    let attrs = parser.attributes().unwrap();
    match &attrs[0] {
        Attribute::Aesop(attr) => {
            assert!(attr.rule_sets.is_empty());
        }
        _ => panic!("Expected Attribute::Aesop"),
    }
}

/// Test unsafe with priority and rule set
#[test]
fn test_aesop_unsafe_priority_with_rule_set() {
    use crate::grammar::Parser;

    let mut parser = Parser::new("@[aesop unsafe 50% apply, GCongr] x");
    let attrs = parser.attributes().unwrap();
    match &attrs[0] {
        Attribute::Aesop(attr) => {
            assert_eq!(attr.phase, AesopPhase::Unsafe);
            assert_eq!(attr.priority, Some(50));
            assert_eq!(attr.builder, AesopBuilder::Apply);
            assert_eq!(attr.rule_sets, vec!["GCongr"]);
        }
        _ => panic!("Expected Attribute::Aesop"),
    }
}

/// Test parsing declare_aesop_rule_sets command
#[test]
fn test_parse_declare_aesop_rule_sets() {
    let decl = parse_decl("declare_aesop_rule_sets [Measurable, Continuous]").unwrap();
    match decl {
        SurfaceDecl::DeclareAesopRuleSets { names, .. } => {
            assert_eq!(
                names,
                vec![
                    SurfaceName::generated_path("Measurable"),
                    SurfaceName::generated_path("Continuous")
                ]
            );
        }
        _ => panic!("expected DeclareAesopRuleSets, got {:?}", decl),
    }
}

/// Test parsing declare_aesop_rule_sets with single name
#[test]
fn test_parse_declare_aesop_rule_sets_single() {
    let decl = parse_decl("declare_aesop_rule_sets [GCongr]").unwrap();
    match decl {
        SurfaceDecl::DeclareAesopRuleSets { names, .. } => {
            assert_eq!(names, vec![SurfaceName::generated_path("GCongr")]);
        }
        _ => panic!("expected DeclareAesopRuleSets"),
    }
}
