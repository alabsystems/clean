// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// ============================================================================
// Phase A+B: Registry wiring tests
// ============================================================================

#[test]
fn test_registry_new_has_builtins() {
    let registry = TermElabRegistry::new();
    for &kind in BUILTIN_KINDS {
        assert!(
            registry.is_registered(kind),
            "builtin kind '{kind}' should be registered"
        );
    }
}

#[test]
fn test_all_surface_expr_variants_have_builtin_kinds() {
    // Verify that surface_expr_kind_name returns a kind that is registered
    // for representative SurfaceExpr variants. This ensures Phase B coverage.
    use crate::infer::surface_expr_kind_name;
    use clean_parser::Span;

    let registry = TermElabRegistry::new();

    let test_cases: Vec<(&str, SurfaceExpr)> = vec![
        ("ident", SurfaceExpr::Ident(Span::dummy(), "x".into())),
        ("hole", SurfaceExpr::Hole(Span::dummy())),
        (
            "paren",
            SurfaceExpr::Paren(Span::dummy(), Box::new(SurfaceExpr::Hole(Span::dummy()))),
        ),
        (
            "app",
            SurfaceExpr::App(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(Span::dummy(), "f".into())),
                vec![],
            ),
        ),
        (
            "universe",
            SurfaceExpr::Universe(Span::dummy(), clean_parser::UniverseExpr::Type),
        ),
        (
            "lit",
            SurfaceExpr::Lit(Span::dummy(), clean_parser::SurfaceLit::Nat(42)),
        ),
    ];

    for (expected_kind, expr) in test_cases {
        let kind = surface_expr_kind_name(&expr);
        assert_eq!(
            kind, expected_kind,
            "surface_expr_kind_name should return '{expected_kind}' for this variant"
        );
        assert!(
            registry.is_registered(kind),
            "kind '{kind}' should be registered as a builtin"
        );
    }
}

#[test]
fn test_get_user_handler_returns_none_for_builtin_only() {
    let registry = TermElabRegistry::new();
    // Builtin stubs have priority == DEFAULT_PRIORITY, which is not > DEFAULT_PRIORITY,
    // so get_user_handler should return None.
    assert!(
        registry.get_user_handler("ident").is_none(),
        "builtin-only kind should return None from get_user_handler"
    );
}

#[test]
fn test_get_user_handler_returns_handler_for_user_override() {
    let mut registry = TermElabRegistry::new();

    // Register a user handler at higher priority
    registry.register(
        "ident",
        TermElabEntry {
            syntax_kind: "ident".to_owned(),
            handler: Arc::new(|_expr, _expected_ty, _ctx| Ok(Expr::prop())),
            priority: DEFAULT_PRIORITY + 100,
        },
    );

    let handler = registry.get_user_handler("ident");
    assert!(
        handler.is_some(),
        "user-registered handler above DEFAULT_PRIORITY should be returned"
    );

    // Verify the handler works
    let env = clean_kernel::Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let expr = SurfaceExpr::Hole(clean_parser::Span::dummy());
    let result = (handler.unwrap())(&expr, None, &mut ctx);
    assert!(result.is_ok(), "user handler should succeed");
}

#[test]
fn test_registry_covers_all_builtin_kinds() {
    // BUILTIN_KINDS should have at least 30 entries (all SurfaceExpr variants)
    assert!(
        BUILTIN_KINDS.len() >= 30,
        "BUILTIN_KINDS should cover all SurfaceExpr variants, got {}",
        BUILTIN_KINDS.len()
    );
    let registry = TermElabRegistry::new();
    assert_eq!(
        registry.kind_count(),
        BUILTIN_KINDS.len(),
        "registry should have one kind per BUILTIN_KINDS entry"
    );
}

#[test]
fn test_registry_kind_count() {
    let registry = TermElabRegistry::new();
    assert_eq!(registry.kind_count(), BUILTIN_KINDS.len());
    assert_eq!(registry.handler_count(), BUILTIN_KINDS.len());
}

#[test]
fn test_registry_register_user_handler() {
    let mut registry = TermElabRegistry::new();
    let initial_kinds = registry.kind_count();

    registry.register(
        "myCustomKind",
        TermElabEntry {
            syntax_kind: "myCustomKind".to_owned(),
            handler: Arc::new(|_expr, _expected_ty, _ctx| Ok(Expr::type_())),
            priority: 2000,
        },
    );

    assert!(registry.is_registered("myCustomKind"));
    assert_eq!(registry.kind_count(), initial_kinds + 1);
}

#[test]
fn test_registry_multiple_handlers_priority_order() {
    let mut registry = TermElabRegistry::new();

    // Register low priority first
    registry.register(
        "testKind",
        TermElabEntry {
            syntax_kind: "testKind".to_owned(),
            handler: Arc::new(|_expr, _expected_ty, _ctx| {
                Err(ElabError::NotImplemented("low".into()))
            }),
            priority: 100,
        },
    );

    // Register high priority second
    registry.register(
        "testKind",
        TermElabEntry {
            syntax_kind: "testKind".to_owned(),
            handler: Arc::new(|_expr, _expected_ty, _ctx| {
                Err(ElabError::NotImplemented("high".into()))
            }),
            priority: 500,
        },
    );

    // Register medium priority third
    registry.register(
        "testKind",
        TermElabEntry {
            syntax_kind: "testKind".to_owned(),
            handler: Arc::new(|_expr, _expected_ty, _ctx| {
                Err(ElabError::NotImplemented("medium".into()))
            }),
            priority: 300,
        },
    );

    let handlers = registry.get_handlers("testKind").unwrap();
    assert_eq!(handlers.len(), 3);
    assert_eq!(handlers[0].priority, 500, "highest priority first");
    assert_eq!(handlers[1].priority, 300, "medium priority second");
    assert_eq!(handlers[2].priority, 100, "lowest priority third");
}

#[test]
fn test_registry_not_registered_for_unknown() {
    let registry = TermElabRegistry::new();
    assert!(!registry.is_registered("nonexistent"));
    assert!(registry.get_handlers("nonexistent").is_none());
}

#[test]
fn test_registry_elaborate_no_handlers_returns_none() {
    let registry = TermElabRegistry::new();
    let expr = SurfaceExpr::Hole(clean_parser::Span::dummy());
    let env = clean_kernel::Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let result = registry.elaborate("nonexistent", &expr, None, &mut ctx);
    assert!(result.is_none(), "no handlers should return None");
}

#[test]
fn test_registry_elaborate_first_success_wins() {
    let mut registry = TermElabRegistry::default();

    // High priority: succeeds
    registry.register(
        "testKind",
        TermElabEntry {
            syntax_kind: "testKind".to_owned(),
            handler: Arc::new(|_expr, _expected_ty, _ctx| Ok(Expr::type_())),
            priority: 2000,
        },
    );

    // Low priority: should not be called
    registry.register(
        "testKind",
        TermElabEntry {
            syntax_kind: "testKind".to_owned(),
            handler: Arc::new(|_expr, _expected_ty, _ctx| Ok(Expr::prop())),
            priority: 500,
        },
    );

    let expr = SurfaceExpr::Hole(clean_parser::Span::dummy());
    let env = clean_kernel::Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let result = registry.elaborate("testKind", &expr, None, &mut ctx);
    let elaborated = result
        .expect("should have handlers")
        .expect("should succeed");
    // The high-priority handler returns Type
    assert_eq!(format!("{elaborated:?}"), format!("{:?}", Expr::type_()));
}

#[test]
fn test_registry_elaborate_fallthrough_on_error() {
    let mut registry = TermElabRegistry::default();

    // High priority: fails
    registry.register(
        "testKind",
        TermElabEntry {
            syntax_kind: "testKind".to_owned(),
            handler: Arc::new(|_expr, _expected_ty, _ctx| {
                Err(ElabError::NotImplemented("skip".into()))
            }),
            priority: 2000,
        },
    );

    // Low priority: succeeds
    registry.register(
        "testKind",
        TermElabEntry {
            syntax_kind: "testKind".to_owned(),
            handler: Arc::new(|_expr, _expected_ty, _ctx| Ok(Expr::prop())),
            priority: 500,
        },
    );

    let expr = SurfaceExpr::Hole(clean_parser::Span::dummy());
    let env = clean_kernel::Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let result = registry.elaborate("testKind", &expr, None, &mut ctx);
    let elaborated = result
        .expect("should have handlers")
        .expect("should succeed");
    assert_eq!(format!("{elaborated:?}"), format!("{:?}", Expr::prop()));
}

#[test]
fn test_registry_elaborate_all_fail_returns_last_error() {
    let mut registry = TermElabRegistry::default();

    registry.register(
        "testKind",
        TermElabEntry {
            syntax_kind: "testKind".to_owned(),
            handler: Arc::new(|_expr, _expected_ty, _ctx| {
                Err(ElabError::NotImplemented("first failure".into()))
            }),
            priority: 2000,
        },
    );

    registry.register(
        "testKind",
        TermElabEntry {
            syntax_kind: "testKind".to_owned(),
            handler: Arc::new(|_expr, _expected_ty, _ctx| {
                Err(ElabError::NotImplemented("second failure".into()))
            }),
            priority: 500,
        },
    );

    let expr = SurfaceExpr::Hole(clean_parser::Span::dummy());
    let env = clean_kernel::Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let result = registry.elaborate("testKind", &expr, None, &mut ctx);
    let err = result.expect("should have handlers").unwrap_err();
    let msg = format!("{err}");
    assert!(
        msg.contains("second failure"),
        "should return last handler's error, got: {msg}"
    );
}

#[test]
fn test_registry_default_trait() {
    let registry = TermElabRegistry::default();
    assert_eq!(registry.kind_count(), BUILTIN_KINDS.len());
}

#[test]
fn test_registry_kinds_iterator() {
    let registry = TermElabRegistry::new();
    let kinds: Vec<&str> = registry.kinds().collect();
    assert_eq!(kinds.len(), BUILTIN_KINDS.len());
    for &expected in BUILTIN_KINDS {
        assert!(
            kinds.contains(&expected),
            "iterator should include '{expected}'"
        );
    }
}

#[test]
fn test_registry_user_overrides_builtin() {
    let mut registry = TermElabRegistry::new();

    // User handler at higher priority than builtin (DEFAULT_PRIORITY = 1000)
    registry.register(
        "ident",
        TermElabEntry {
            syntax_kind: "ident".to_owned(),
            handler: Arc::new(|_expr, _expected_ty, _ctx| Ok(Expr::prop())),
            priority: DEFAULT_PRIORITY + 100,
        },
    );

    let handlers = registry.get_handlers("ident").unwrap();
    assert_eq!(handlers.len(), 2, "builtin + user = 2 handlers");
    assert_eq!(
        handlers[0].priority,
        DEFAULT_PRIORITY + 100,
        "user handler should be first"
    );
    assert_eq!(
        handlers[1].priority, DEFAULT_PRIORITY,
        "builtin handler should be second"
    );

    // Elaborate should use the user handler
    let expr = SurfaceExpr::Hole(clean_parser::Span::dummy());
    let env = clean_kernel::Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let result = registry.elaborate("ident", &expr, None, &mut ctx);
    let elaborated = result
        .expect("should have handlers")
        .expect("should succeed");
    assert_eq!(format!("{elaborated:?}"), format!("{:?}", Expr::prop()));
}

#[test]
fn test_entry_debug_format() {
    let entry = TermElabEntry {
        syntax_kind: "myKind".to_owned(),
        handler: Arc::new(|_expr, _expected_ty, _ctx| Ok(Expr::type_())),
        priority: 500,
    };
    let debug = format!("{entry:?}");
    assert!(debug.contains("myKind"));
    assert!(debug.contains("500"));
}

#[test]
fn test_entry_clone() {
    let entry = TermElabEntry {
        syntax_kind: "myKind".to_owned(),
        handler: Arc::new(|_expr, _expected_ty, _ctx| Ok(Expr::type_())),
        priority: 500,
    };
    let cloned = entry.clone();
    assert_eq!(cloned.syntax_kind, "myKind");
    assert_eq!(cloned.priority, 500);
}

#[test]
fn test_registry_elaborate_with_expected_type() {
    let mut registry = TermElabRegistry::default();

    // Handler that uses the expected type
    registry.register(
        "typedKind",
        TermElabEntry {
            syntax_kind: "typedKind".to_owned(),
            handler: Arc::new(|_expr, expected_ty, _ctx| {
                if expected_ty.is_some() {
                    Ok(Expr::type_())
                } else {
                    Err(ElabError::CannotInfer)
                }
            }),
            priority: 1000,
        },
    );

    let expr = SurfaceExpr::Hole(clean_parser::Span::dummy());
    let env = clean_kernel::Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // With expected type: should succeed
    let ty = Expr::type_();
    let result = registry.elaborate("typedKind", &expr, Some(&ty), &mut ctx);
    assert!(
        result.expect("should have handlers").is_ok(),
        "should succeed with expected type"
    );

    // Without expected type: should fail
    let result = registry.elaborate("typedKind", &expr, None, &mut ctx);
    assert!(
        result.expect("should have handlers").is_err(),
        "should fail without expected type"
    );
}
