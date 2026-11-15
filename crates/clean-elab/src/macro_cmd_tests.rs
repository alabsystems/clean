// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the macro command framework.

use super::*;
use clean_parser::Span;

/// Helper: make a simple identifier expression.
fn ident(name: SurfaceName) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::new(0, 0), name)
}

/// Helper: make a hole expression.
fn hole() -> SurfaceExpr {
    SurfaceExpr::Hole(Span::new(0, 0))
}

#[test]
fn test_builtin_check_registered() {
    let registry = MacroRegistry::new();
    assert!(registry.is_registered(&SurfaceName::generated_path("check")));
    let def = registry
        .lookup(&SurfaceName::generated_path("check"))
        .unwrap();
    assert_eq!(def.scoping, MacroScoping::Command);
    assert_eq!(def.required_arity(), 1);
}

#[test]
fn test_builtin_eval_registered() {
    let registry = MacroRegistry::new();
    assert!(registry.is_registered(&SurfaceName::generated_path("eval")));
    let def = registry
        .lookup(&SurfaceName::generated_path("eval"))
        .unwrap();
    assert_eq!(def.scoping, MacroScoping::Command);
    assert_eq!(def.required_arity(), 1);
}

#[test]
fn test_builtin_print_registered() {
    let registry = MacroRegistry::new();
    assert!(registry.is_registered(&SurfaceName::generated_path("print")));
    let def = registry
        .lookup(&SurfaceName::generated_path("print"))
        .unwrap();
    assert_eq!(def.scoping, MacroScoping::Command);
    assert_eq!(def.required_arity(), 1);
}

#[test]
fn test_register_and_expand_simple_macro() {
    let mut registry = MacroRegistry::new();
    registry.register(MacroDef {
        name: SurfaceName::generated_path("id"),
        pattern: vec![MacroPatternPart::Expr],
        // Template: just a hole that gets substituted
        expansion_template: hole(),
        scoping: MacroScoping::Term,
    });

    let result = expand_macro(
        &registry,
        &SurfaceName::generated_path("id"),
        &[ident(SurfaceName::generated_path("x"))],
    );
    assert!(result.is_ok());
    let expanded = result.unwrap();
    // The hole should be replaced by the argument
    match expanded {
        SurfaceExpr::Ident(_, name) => {
            assert_eq!(name, SurfaceName::generated_path("x"))
        }
        other => panic!("expected Ident, got {other:?}"),
    }
}

#[test]
fn test_expand_ident_template_wraps_in_app() {
    let mut registry = MacroRegistry::new();
    registry.register(MacroDef {
        name: SurfaceName::generated_path("negate"),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident(SurfaceName::generated_path("Bool.not")),
        scoping: MacroScoping::Term,
    });

    let result = expand_macro(
        &registry,
        &SurfaceName::generated_path("negate"),
        &[ident(SurfaceName::generated_path("b"))],
    )
    .unwrap();
    match result {
        SurfaceExpr::App(_, func, args) => {
            match func.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name, &SurfaceName::generated_path("Bool.not"))
                }
                other => panic!("expected Ident func, got {other:?}"),
            }
            assert_eq!(args.len(), 1);
            match &args[0].expr {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name, &SurfaceName::generated_path("b"))
                }
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
        name: SurfaceName::generated_path("unit"),
        pattern: vec![],
        expansion_template: ident(SurfaceName::generated_path("Unit.unit")),
        scoping: MacroScoping::Term,
    });

    let result = expand_macro(&registry, &SurfaceName::generated_path("unit"), &[]).unwrap();
    match result {
        SurfaceExpr::Ident(_, name) => {
            assert_eq!(name, SurfaceName::generated_path("Unit.unit"))
        }
        other => panic!("expected Ident, got {other:?}"),
    }
}

#[test]
fn test_expand_unknown_macro_error() {
    let registry = MacroRegistry::new();
    let result = expand_macro(
        &registry,
        &SurfaceName::generated_path("nonexistent"),
        &[ident(SurfaceName::generated_path("x"))],
    );
    assert!(result.is_err());
    match result.unwrap_err() {
        MacroError::UnknownMacro(name) => {
            assert_eq!(name, SurfaceName::generated_path("nonexistent"))
        }
        other => panic!("expected UnknownMacro, got {other:?}"),
    }
}

#[test]
fn test_expand_arity_mismatch_too_few() {
    let mut registry = MacroRegistry::empty();
    registry.register(MacroDef {
        name: SurfaceName::generated_path("pair"),
        pattern: vec![MacroPatternPart::Expr, MacroPatternPart::Expr],
        expansion_template: ident(SurfaceName::generated_path("Prod.mk")),
        scoping: MacroScoping::Term,
    });

    let result = expand_macro(
        &registry,
        &SurfaceName::generated_path("pair"),
        &[ident(SurfaceName::generated_path("x"))],
    );
    assert!(result.is_err());
    match result.unwrap_err() {
        MacroError::ArityMismatch {
            name,
            expected,
            actual,
        } => {
            assert_eq!(name, SurfaceName::generated_path("pair"));
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
        name: SurfaceName::generated_path("need_arg"),
        pattern: vec![],
        expansion_template: hole(),
        scoping: MacroScoping::Term,
    });

    let result = expand_macro(&registry, &SurfaceName::generated_path("need_arg"), &[]);
    assert!(result.is_err());
    match result.unwrap_err() {
        MacroError::MissingArgument { name, position } => {
            assert_eq!(name, SurfaceName::generated_path("need_arg"));
            assert_eq!(position, 0);
        }
        other => panic!("expected MissingArgument, got {other:?}"),
    }
}

#[test]
fn test_scoping_validation() {
    let mut registry = MacroRegistry::empty();
    registry.register(MacroDef {
        name: SurfaceName::generated_path("cmd_macro"),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident(SurfaceName::generated_path("cmd")),
        scoping: MacroScoping::Command,
    });
    registry.register(MacroDef {
        name: SurfaceName::generated_path("term_macro"),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident(SurfaceName::generated_path("term")),
        scoping: MacroScoping::Term,
    });
    registry.register(MacroDef {
        name: SurfaceName::generated_path("tactic_macro"),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident(SurfaceName::generated_path("tactic")),
        scoping: MacroScoping::Tactic,
    });

    assert_eq!(
        registry
            .lookup(&SurfaceName::generated_path("cmd_macro"))
            .unwrap()
            .scoping,
        MacroScoping::Command
    );
    assert_eq!(
        registry
            .lookup(&SurfaceName::generated_path("term_macro"))
            .unwrap()
            .scoping,
        MacroScoping::Term
    );
    assert_eq!(
        registry
            .lookup(&SurfaceName::generated_path("tactic_macro"))
            .unwrap()
            .scoping,
        MacroScoping::Tactic
    );
}

#[test]
fn test_empty_registry() {
    let registry = MacroRegistry::empty();
    assert_eq!(registry.count(), 0);
    assert!(!registry.is_registered(&SurfaceName::generated_path("check")));
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
    let names: Vec<SurfaceName> = registry.names().cloned().collect();
    assert!(names.contains(&SurfaceName::generated_path("check")));
    assert!(names.contains(&SurfaceName::generated_path("eval")));
    assert!(names.contains(&SurfaceName::generated_path("print")));
}

#[test]
fn test_register_replaces_existing() {
    let mut registry = MacroRegistry::empty();
    registry.register(MacroDef {
        name: SurfaceName::generated_path("foo"),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident(SurfaceName::generated_path("old")),
        scoping: MacroScoping::Term,
    });
    registry.register(MacroDef {
        name: SurfaceName::generated_path("foo"),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident(SurfaceName::generated_path("new")),
        scoping: MacroScoping::Term,
    });

    assert_eq!(registry.count(), 1);
    let def = registry
        .lookup(&SurfaceName::generated_path("foo"))
        .unwrap();
    match &def.expansion_template {
        SurfaceExpr::Ident(_, name) => {
            assert_eq!(name, &SurfaceName::generated_path("new"))
        }
        other => panic!("expected Ident, got {other:?}"),
    }
}

#[test]
fn test_required_arity_with_mixed_pattern() {
    let def = MacroDef {
        name: SurfaceName::generated_path("mixed"),
        pattern: vec![
            MacroPatternPart::Keyword("if".to_owned()),
            MacroPatternPart::Expr,
            MacroPatternPart::Keyword("then".to_owned()),
            MacroPatternPart::Expr,
            MacroPatternPart::OptionalExpr,
        ],
        expansion_template: ident(SurfaceName::generated_path("ite")),
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

    let names: Vec<SurfaceName> = all.iter().map(|d| d.name.clone()).collect();
    assert!(names.contains(&SurfaceName::generated_path("check")));
    assert!(names.contains(&SurfaceName::generated_path("eval")));
    assert!(names.contains(&SurfaceName::generated_path("print")));
}

#[test]
fn test_expand_multiple_args() {
    let mut registry = MacroRegistry::empty();
    registry.register(MacroDef {
        name: SurfaceName::generated_path("pair"),
        pattern: vec![MacroPatternPart::Expr, MacroPatternPart::Expr],
        expansion_template: ident(SurfaceName::generated_path("Prod.mk")),
        scoping: MacroScoping::Term,
    });

    let result = expand_macro(
        &registry,
        &SurfaceName::generated_path("pair"),
        &[
            ident(SurfaceName::generated_path("a")),
            ident(SurfaceName::generated_path("b")),
        ],
    )
    .unwrap();
    match result {
        SurfaceExpr::App(_, func, args) => {
            match func.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name, &SurfaceName::generated_path("Prod.mk"))
                }
                other => panic!("expected Ident func, got {other:?}"),
            }
            assert_eq!(args.len(), 2);
            match &args[0].expr {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name, &SurfaceName::generated_path("a"))
                }
                other => panic!("expected Ident first arg, got {other:?}"),
            }
            match &args[1].expr {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name, &SurfaceName::generated_path("b"))
                }
                other => panic!("expected Ident second arg, got {other:?}"),
            }
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_default_creates_builtins() {
    let registry = MacroRegistry::default();
    assert!(registry.is_registered(&SurfaceName::generated_path("check")));
    assert!(registry.is_registered(&SurfaceName::generated_path("eval")));
    assert!(registry.is_registered(&SurfaceName::generated_path("print")));
}

#[test]
fn test_macro_error_display() {
    let err = MacroError::UnknownMacro(SurfaceName::generated_path("foo"));
    assert_eq!(err.to_string(), "unknown macro: foo");

    let err = MacroError::ArityMismatch {
        name: SurfaceName::generated_path("bar"),
        expected: 2,
        actual: 1,
    };
    assert_eq!(err.to_string(), "macro 'bar' expects 2 argument(s), got 1");
}
