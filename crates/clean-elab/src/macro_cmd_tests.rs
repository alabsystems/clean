// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the macro command framework.

use super::*;
use clean_parser::Span;

/// Helper: make a simple identifier expression.
fn ident(name: &str) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::new(0, 0), name.to_owned())
}

/// Helper: make a hole expression.
fn hole() -> SurfaceExpr {
    SurfaceExpr::Hole(Span::new(0, 0))
}

#[test]
fn test_builtin_check_registered() {
    let registry = MacroRegistry::new();
    assert!(registry.is_registered("check"));
    let def = registry.lookup("check").unwrap();
    assert_eq!(def.scoping, MacroScoping::Command);
    assert_eq!(def.required_arity(), 1);
}

#[test]
fn test_builtin_eval_registered() {
    let registry = MacroRegistry::new();
    assert!(registry.is_registered("eval"));
    let def = registry.lookup("eval").unwrap();
    assert_eq!(def.scoping, MacroScoping::Command);
    assert_eq!(def.required_arity(), 1);
}

#[test]
fn test_builtin_print_registered() {
    let registry = MacroRegistry::new();
    assert!(registry.is_registered("print"));
    let def = registry.lookup("print").unwrap();
    assert_eq!(def.scoping, MacroScoping::Command);
    assert_eq!(def.required_arity(), 1);
}

#[test]
fn test_register_and_expand_simple_macro() {
    let mut registry = MacroRegistry::new();
    registry.register(MacroDef {
        name: "id".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        // Template: just a hole that gets substituted
        expansion_template: hole(),
        scoping: MacroScoping::Term,
    });

    let result = expand_macro(&registry, "id", &[ident("x")]);
    assert!(result.is_ok());
    let expanded = result.unwrap();
    // The hole should be replaced by the argument
    match expanded {
        SurfaceExpr::Ident(_, name) => assert_eq!(name, "x"),
        other => panic!("expected Ident, got {other:?}"),
    }
}

#[test]
fn test_expand_ident_template_wraps_in_app() {
    let mut registry = MacroRegistry::new();
    registry.register(MacroDef {
        name: "negate".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident("Bool.not"),
        scoping: MacroScoping::Term,
    });

    let result = expand_macro(&registry, "negate", &[ident("b")]).unwrap();
    match result {
        SurfaceExpr::App(_, func, args) => {
            match func.as_ref() {
                SurfaceExpr::Ident(_, name) => assert_eq!(name, "Bool.not"),
                other => panic!("expected Ident func, got {other:?}"),
            }
            assert_eq!(args.len(), 1);
            match &args[0].expr {
                SurfaceExpr::Ident(_, name) => assert_eq!(name, "b"),
                other => panic!("expected Ident arg, got {other:?}"),
            }
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_expand_ident_no_args_returns_ident() {
    let mut registry = MacroRegistry::empty();
    registry.register(MacroDef {
        name: "unit".to_owned(),
        pattern: vec![],
        expansion_template: ident("Unit.unit"),
        scoping: MacroScoping::Term,
    });

    let result = expand_macro(&registry, "unit", &[]).unwrap();
    match result {
        SurfaceExpr::Ident(_, name) => assert_eq!(name, "Unit.unit"),
        other => panic!("expected Ident, got {other:?}"),
    }
}

#[test]
fn test_expand_unknown_macro_error() {
    let registry = MacroRegistry::new();
    let result = expand_macro(&registry, "nonexistent", &[ident("x")]);
    assert!(result.is_err());
    match result.unwrap_err() {
        MacroError::UnknownMacro(name) => assert_eq!(name, "nonexistent"),
        other => panic!("expected UnknownMacro, got {other:?}"),
    }
}

#[test]
fn test_expand_arity_mismatch_too_few() {
    let mut registry = MacroRegistry::empty();
    registry.register(MacroDef {
        name: "pair".to_owned(),
        pattern: vec![MacroPatternPart::Expr, MacroPatternPart::Expr],
        expansion_template: ident("Prod.mk"),
        scoping: MacroScoping::Term,
    });

    let result = expand_macro(&registry, "pair", &[ident("x")]);
    assert!(result.is_err());
    match result.unwrap_err() {
        MacroError::ArityMismatch {
            name,
            expected,
            actual,
        } => {
            assert_eq!(name, "pair");
            assert_eq!(expected, 2);
            assert_eq!(actual, 1);
        }
        other => panic!("expected ArityMismatch, got {other:?}"),
    }
}

#[test]
fn test_expand_hole_missing_arg() {
    let mut registry = MacroRegistry::empty();
    registry.register(MacroDef {
        name: "need_arg".to_owned(),
        pattern: vec![],
        expansion_template: hole(),
        scoping: MacroScoping::Term,
    });

    let result = expand_macro(&registry, "need_arg", &[]);
    assert!(result.is_err());
    match result.unwrap_err() {
        MacroError::MissingArgument { name, position } => {
            assert_eq!(name, "need_arg");
            assert_eq!(position, 0);
        }
        other => panic!("expected MissingArgument, got {other:?}"),
    }
}

#[test]
fn test_scoping_validation() {
    let mut registry = MacroRegistry::empty();
    registry.register(MacroDef {
        name: "cmd_macro".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident("cmd"),
        scoping: MacroScoping::Command,
    });
    registry.register(MacroDef {
        name: "term_macro".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident("term"),
        scoping: MacroScoping::Term,
    });
    registry.register(MacroDef {
        name: "tactic_macro".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident("tactic"),
        scoping: MacroScoping::Tactic,
    });

    assert_eq!(
        registry.lookup("cmd_macro").unwrap().scoping,
        MacroScoping::Command
    );
    assert_eq!(
        registry.lookup("term_macro").unwrap().scoping,
        MacroScoping::Term
    );
    assert_eq!(
        registry.lookup("tactic_macro").unwrap().scoping,
        MacroScoping::Tactic
    );
}

#[test]
fn test_empty_registry() {
    let registry = MacroRegistry::empty();
    assert_eq!(registry.count(), 0);
    assert!(!registry.is_registered("check"));
}

#[test]
fn test_registry_count() {
    let registry = MacroRegistry::new();
    // Built-in: check, eval, print
    assert_eq!(registry.count(), 3);
}

#[test]
fn test_registry_names() {
    let registry = MacroRegistry::new();
    let names: Vec<&str> = registry.names().collect();
    assert!(names.contains(&"check"));
    assert!(names.contains(&"eval"));
    assert!(names.contains(&"print"));
}

#[test]
fn test_register_replaces_existing() {
    let mut registry = MacroRegistry::empty();
    registry.register(MacroDef {
        name: "foo".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident("old"),
        scoping: MacroScoping::Term,
    });
    registry.register(MacroDef {
        name: "foo".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident("new"),
        scoping: MacroScoping::Term,
    });

    assert_eq!(registry.count(), 1);
    let def = registry.lookup("foo").unwrap();
    match &def.expansion_template {
        SurfaceExpr::Ident(_, name) => assert_eq!(name, "new"),
        other => panic!("expected Ident, got {other:?}"),
    }
}

#[test]
fn test_required_arity_with_mixed_pattern() {
    let def = MacroDef {
        name: "mixed".to_owned(),
        pattern: vec![
            MacroPatternPart::Keyword("if".to_owned()),
            MacroPatternPart::Expr,
            MacroPatternPart::Keyword("then".to_owned()),
            MacroPatternPart::Expr,
            MacroPatternPart::OptionalExpr,
        ],
        expansion_template: ident("ite"),
        scoping: MacroScoping::Term,
    };
    // Only Expr and Ident count as required, not Keyword or OptionalExpr
    assert_eq!(def.required_arity(), 2);
}

#[test]
fn test_all_macros_iterator() {
    let registry = MacroRegistry::new();
    let all: Vec<&MacroDef> = registry.all_macros().collect();
    assert_eq!(all.len(), 3);

    let names: Vec<&str> = all.iter().map(|d| d.name.as_str()).collect();
    assert!(names.contains(&"check"));
    assert!(names.contains(&"eval"));
    assert!(names.contains(&"print"));
}

#[test]
fn test_expand_multiple_args() {
    let mut registry = MacroRegistry::empty();
    registry.register(MacroDef {
        name: "pair".to_owned(),
        pattern: vec![MacroPatternPart::Expr, MacroPatternPart::Expr],
        expansion_template: ident("Prod.mk"),
        scoping: MacroScoping::Term,
    });

    let result = expand_macro(&registry, "pair", &[ident("a"), ident("b")]).unwrap();
    match result {
        SurfaceExpr::App(_, func, args) => {
            match func.as_ref() {
                SurfaceExpr::Ident(_, name) => assert_eq!(name, "Prod.mk"),
                other => panic!("expected Ident func, got {other:?}"),
            }
            assert_eq!(args.len(), 2);
            match &args[0].expr {
                SurfaceExpr::Ident(_, name) => assert_eq!(name, "a"),
                other => panic!("expected Ident first arg, got {other:?}"),
            }
            match &args[1].expr {
                SurfaceExpr::Ident(_, name) => assert_eq!(name, "b"),
                other => panic!("expected Ident second arg, got {other:?}"),
            }
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_default_creates_builtins() {
    let registry = MacroRegistry::default();
    assert!(registry.is_registered("check"));
    assert!(registry.is_registered("eval"));
    assert!(registry.is_registered("print"));
}

#[test]
fn test_macro_error_display() {
    let err = MacroError::UnknownMacro("foo".to_owned());
    assert_eq!(err.to_string(), "unknown macro: foo");

    let err = MacroError::ArityMismatch {
        name: "bar".to_owned(),
        expected: 2,
        actual: 1,
    };
    assert_eq!(err.to_string(), "macro 'bar' expects 2 argument(s), got 1");
}
