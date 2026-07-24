// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for syntax declaration registry, elab rule registry, and macro_rules registry.

use std::sync::Arc;

use super::*;
use crate::elab_cmd::{
    ElabRule, ElabRuleRegistry, MacroRulesArm, MacroRulesEntry, MacroRulesRegistry,
};
use clean_parser::lexer::{Token, TokenKind};
use clean_parser::{Span, SurfaceExpr, SyntaxPatternItem};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn ident_token(name: &str) -> Token {
    Token::new(
        TokenKind::Ident(name.to_owned()),
        Span::new(0, 0),
        false,
        0,
        1,
    )
}

fn lit_token(kind: TokenKind) -> Token {
    Token::new(kind, Span::new(0, 0), false, 0, 1)
}

fn ident(name: &str) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::new(0, 0), name.to_owned())
}

// ---------------------------------------------------------------------------
// SyntaxCategory
// ---------------------------------------------------------------------------

#[test]
fn test_parse_syntax_category_term() {
    assert_eq!(parse_syntax_category("term").unwrap(), SyntaxCategory::Term);
}

#[test]
fn test_parse_syntax_category_tactic() {
    assert_eq!(
        parse_syntax_category("tactic").unwrap(),
        SyntaxCategory::Tactic
    );
}

#[test]
fn test_parse_syntax_category_command() {
    assert_eq!(
        parse_syntax_category("command").unwrap(),
        SyntaxCategory::Command
    );
}

#[test]
fn test_parse_syntax_category_doelem() {
    assert_eq!(
        parse_syntax_category("doelem").unwrap(),
        SyntaxCategory::Doelem
    );
}

#[test]
fn test_parse_syntax_category_level() {
    assert_eq!(
        parse_syntax_category("level").unwrap(),
        SyntaxCategory::Level
    );
}

#[test]
fn test_parse_syntax_category_case_insensitive() {
    assert_eq!(parse_syntax_category("TERM").unwrap(), SyntaxCategory::Term);
    assert_eq!(
        parse_syntax_category("Tactic").unwrap(),
        SyntaxCategory::Tactic
    );
}

#[test]
fn test_parse_syntax_category_unknown() {
    let err = parse_syntax_category("bogus").unwrap_err();
    match err {
        SyntaxError::UnknownCategory(name) => assert_eq!(name, "bogus"),
        other => panic!("expected UnknownCategory, got {other:?}"),
    }
}

#[test]
fn test_syntax_category_as_str() {
    assert_eq!(SyntaxCategory::Term.as_str(), "term");
    assert_eq!(SyntaxCategory::Doelem.as_str(), "doElem");
}

// ---------------------------------------------------------------------------
// extract_leading_literal
// ---------------------------------------------------------------------------

#[test]
fn test_extract_leading_literal_from_literal() {
    let pat = vec![SyntaxPatternItem::Literal("if".to_owned())];
    assert_eq!(extract_leading_literal(&pat), Some("if"));
}

#[test]
fn test_extract_leading_literal_skips_variable() {
    let pat = vec![
        SyntaxPatternItem::Variable {
            name: "x".to_owned(),
            category: None,
        },
        SyntaxPatternItem::Literal("+".to_owned()),
    ];
    assert_eq!(extract_leading_literal(&pat), Some("+"));
}

#[test]
fn test_extract_leading_literal_empty() {
    assert_eq!(extract_leading_literal(&[]), None);
}

// ---------------------------------------------------------------------------
// SyntaxRegistry
// ---------------------------------------------------------------------------

#[test]
fn test_registry_new_is_empty() {
    let reg = SyntaxRegistry::new();
    assert_eq!(reg.rule_count(), 0);
    assert!(!reg.has_rules("+"));
}

#[test]
fn test_registry_register_and_lookup() {
    let mut reg = SyntaxRegistry::new();
    reg.register(SyntaxRule {
        name: "add".to_owned(),
        category: SyntaxCategory::Term,
        pattern: vec![
            SyntaxPatternItem::Variable {
                name: "a".to_owned(),
                category: Some("term".to_owned()),
            },
            SyntaxPatternItem::Literal("+".to_owned()),
            SyntaxPatternItem::Variable {
                name: "b".to_owned(),
                category: Some("term".to_owned()),
            },
        ],
        priority: 65,
    });

    assert_eq!(reg.rule_count(), 1);
    assert!(reg.has_rules("+"));
    let rules = reg.lookup("+");
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].name, "add");
}

#[test]
fn test_registry_priority_ordering() {
    let mut reg = SyntaxRegistry::new();
    reg.register(SyntaxRule {
        name: "low".to_owned(),
        category: SyntaxCategory::Term,
        pattern: vec![SyntaxPatternItem::Literal("op".to_owned())],
        priority: 10,
    });
    reg.register(SyntaxRule {
        name: "high".to_owned(),
        category: SyntaxCategory::Term,
        pattern: vec![SyntaxPatternItem::Literal("op".to_owned())],
        priority: 100,
    });

    let rules = reg.lookup("op");
    assert_eq!(rules.len(), 2);
    assert_eq!(rules[0].name, "high");
    assert_eq!(rules[1].name, "low");
}

#[test]
fn test_registry_empty_pattern_ignored() {
    let mut reg = SyntaxRegistry::new();
    reg.register(SyntaxRule {
        name: "empty".to_owned(),
        category: SyntaxCategory::Term,
        pattern: vec![],
        priority: 50,
    });
    assert_eq!(reg.rule_count(), 0);
}

#[test]
fn test_registry_all_rules() {
    let mut reg = SyntaxRegistry::new();
    reg.register(SyntaxRule {
        name: "a".to_owned(),
        category: SyntaxCategory::Term,
        pattern: vec![SyntaxPatternItem::Literal("x".to_owned())],
        priority: 10,
    });
    reg.register(SyntaxRule {
        name: "b".to_owned(),
        category: SyntaxCategory::Tactic,
        pattern: vec![SyntaxPatternItem::Literal("y".to_owned())],
        priority: 20,
    });

    let all: Vec<_> = reg.all_rules().collect();
    assert_eq!(all.len(), 2);
    // Higher priority first
    assert_eq!(all[0].name, "b");
    assert_eq!(all[1].name, "a");
}

#[test]
fn test_registry_category_rules() {
    let mut reg = SyntaxRegistry::new();
    reg.register(SyntaxRule {
        name: "t1".to_owned(),
        category: SyntaxCategory::Term,
        pattern: vec![SyntaxPatternItem::Literal("x".to_owned())],
        priority: 10,
    });
    reg.register(SyntaxRule {
        name: "c1".to_owned(),
        category: SyntaxCategory::Command,
        pattern: vec![SyntaxPatternItem::Literal("y".to_owned())],
        priority: 20,
    });

    let term_rules: Vec<_> = reg.category_rules(SyntaxCategory::Term).collect();
    assert_eq!(term_rules.len(), 1);
    assert_eq!(term_rules[0].name, "t1");
}

#[test]
fn test_registry_match_syntax_literal() {
    let mut reg = SyntaxRegistry::new();
    reg.register(SyntaxRule {
        name: "myif".to_owned(),
        category: SyntaxCategory::Term,
        pattern: vec![
            SyntaxPatternItem::Literal("if".to_owned()),
            SyntaxPatternItem::Variable {
                name: "c".to_owned(),
                category: Some("term".to_owned()),
            },
        ],
        priority: 50,
    });

    let tokens = vec![lit_token(TokenKind::If), ident_token("cond")];
    let result = reg.match_syntax(SyntaxCategory::Term, &tokens);
    assert!(result.is_some());
}

#[test]
fn test_registry_match_syntax_empty_tokens() {
    let reg = SyntaxRegistry::new();
    assert!(reg.match_syntax(SyntaxCategory::Term, &[]).is_none());
}

#[test]
fn test_registry_default() {
    let reg = SyntaxRegistry::default();
    assert_eq!(reg.rule_count(), 0);
}

// ---------------------------------------------------------------------------
// ElabRuleRegistry
// ---------------------------------------------------------------------------

#[test]
fn test_elab_registry_new_empty() {
    let reg = ElabRuleRegistry::new();
    assert_eq!(reg.rule_count(), 0);
    assert!(reg.lookup("nonexistent").is_none());
}

#[test]
fn test_elab_registry_register_and_lookup() {
    let mut reg = ElabRuleRegistry::new();
    reg.register(ElabRule {
        syntax_name: "myRule".to_owned(),
        handler: Arc::new(|_matches, _ctx| {
            Ok(clean_kernel::Expr::sort(clean_kernel::Level::zero()))
        }),
    });

    assert_eq!(reg.rule_count(), 1);
    let rules = reg.lookup("myRule").unwrap();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].syntax_name, "myRule");
}

#[test]
fn test_elab_registry_elaborate() {
    let mut reg = ElabRuleRegistry::new();
    reg.register(ElabRule {
        syntax_name: "test".to_owned(),
        handler: Arc::new(|_matches, _ctx| {
            Ok(clean_kernel::Expr::sort(clean_kernel::Level::zero()))
        }),
    });

    let env = clean_kernel::Environment::new();
    let mut ctx = crate::ElabCtx::new(&env);
    let result = reg.elaborate("test", &[], &mut ctx);
    assert!(result.is_some());
    assert!(result.unwrap().is_ok());
}

#[test]
fn test_elab_registry_no_rules_returns_none() {
    let reg = ElabRuleRegistry::new();
    let env = clean_kernel::Environment::new();
    let mut ctx = crate::ElabCtx::new(&env);
    assert!(reg.elaborate("missing", &[], &mut ctx).is_none());
}

#[test]
fn test_elab_registry_default() {
    let reg = ElabRuleRegistry::default();
    assert_eq!(reg.rule_count(), 0);
}

// ---------------------------------------------------------------------------
// MacroRulesRegistry
// ---------------------------------------------------------------------------

#[test]
fn test_macro_rules_registry_new_empty() {
    let reg = MacroRulesRegistry::new();
    assert!(reg.lookup("anything").is_none());
}

#[test]
fn test_macro_rules_registry_register_and_lookup() {
    let mut reg = MacroRulesRegistry::new();
    reg.register(MacroRulesEntry {
        name: "myMacro".to_owned(),
        arms: vec![MacroRulesArm {
            pattern: ident("_"),
            expansion: ident("expanded"),
        }],
    });

    let entry = reg.lookup("myMacro").unwrap();
    assert_eq!(entry.name, "myMacro");
    assert_eq!(entry.arms.len(), 1);
}

#[test]
fn test_macro_rules_registry_expand_stub() {
    let mut reg = MacroRulesRegistry::new();
    reg.register(MacroRulesEntry {
        name: "m".to_owned(),
        arms: vec![MacroRulesArm {
            pattern: ident("_"),
            expansion: ident("result"),
        }],
    });

    let result = reg.expand("m", &ident("input"));
    assert!(result.is_some());
    match result.unwrap() {
        SurfaceExpr::Ident(_, name) => assert_eq!(name, "result"),
        other => panic!("expected Ident, got {other:?}"),
    }
}

#[test]
fn test_macro_rules_registry_expand_unknown() {
    let reg = MacroRulesRegistry::new();
    assert!(reg.expand("unknown", &ident("x")).is_none());
}

#[test]
fn test_macro_rules_registry_replaces_on_reregister() {
    let mut reg = MacroRulesRegistry::new();
    reg.register(MacroRulesEntry {
        name: "m".to_owned(),
        arms: vec![MacroRulesArm {
            pattern: ident("_"),
            expansion: ident("old"),
        }],
    });
    reg.register(MacroRulesEntry {
        name: "m".to_owned(),
        arms: vec![MacroRulesArm {
            pattern: ident("_"),
            expansion: ident("new"),
        }],
    });

    let result = reg.expand("m", &ident("input")).unwrap();
    match result {
        SurfaceExpr::Ident(_, name) => assert_eq!(name, "new"),
        other => panic!("expected Ident, got {other:?}"),
    }
}

#[test]
fn test_macro_rules_registry_default() {
    let reg = MacroRulesRegistry::default();
    assert!(reg.lookup("x").is_none());
}

// ---------------------------------------------------------------------------
// Error display
// ---------------------------------------------------------------------------

#[test]
fn test_syntax_error_display() {
    let err = SyntaxError::UnknownCategory("foo".to_owned());
    assert_eq!(err.to_string(), "unknown syntax category: foo");

    let err = SyntaxError::EmptyPattern {
        name: "bar".to_owned(),
    };
    assert_eq!(err.to_string(), "syntax rule 'bar' has an empty pattern");
}

#[test]
fn test_elab_cmd_error_display() {
    use crate::elab_cmd::ElabCmdError;
    let err = ElabCmdError::UnknownElabRule("test".to_owned());
    assert_eq!(err.to_string(), "unknown elaboration rule: test");

    let err = ElabCmdError::NoMatchingArm {
        macro_name: "m".to_owned(),
    };
    assert_eq!(err.to_string(), "no matching macro arm for 'm'");
}
