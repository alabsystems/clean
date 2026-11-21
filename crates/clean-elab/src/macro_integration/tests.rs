// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use clean_parser::{parse_decl, parse_expr, DoElem, SurfaceDecl, SurfaceExpr};

#[test]
fn ordinary_and_synthetic_holes_survive_macro_expansion_with_their_spans() {
    for source in ["_", "?_", "?goal"] {
        let original = parse_expr(source).expect("hole source");
        let expanded = expand_surface_macros(&mut MacroCtx::new(), &original).expect("expansion");
        assert_eq!(expanded.span(), original.span());
        match (&original, &expanded) {
            (SurfaceExpr::Hole(_), SurfaceExpr::Hole(_)) => assert_eq!(source, "_"),
            (SurfaceExpr::NamedHole(_, before), SurfaceExpr::NamedHole(_, after)) => {
                assert!(before.same_syntax(after));
                assert_eq!(after.name().is_anon(), source == "?_");
            }
            _ => panic!("{source} changed from {original:?} to {expanded:?}"),
        }
    }
}

#[test]
fn application_ellipsis_and_quoted_named_argument_survive_actual_macro_roundtrip() {
    for (source, expected) in [("f ..", true), ("f («..» := x)", false)] {
        let expression = parse_expr(source).unwrap();
        let SurfaceExpr::App(_, _, before) = &expression else {
            panic!("expected application");
        };
        let Some(SurfaceExpr::App(_, _, after)) =
            syntax_to_surface(&surface_to_syntax(&expression))
        else {
            panic!("actual macro argument transport failed");
        };
        assert_eq!(before.len(), 1);
        assert_eq!(after.len(), 1);
        assert_eq!(before[0].is_ellipsis(), expected);
        assert_eq!(after[0].is_ellipsis(), expected);
        assert!(before[0]
            .name
            .as_ref()
            .unwrap()
            .same_syntax(after[0].name.as_ref().unwrap()));
        if !expected {
            assert!(after[0]
                .name
                .as_ref()
                .unwrap()
                .same_syntax(&SurfaceName::component("..", true)));
        }
    }
}

#[test]
fn structural_source_names_survive_macro_roundtrips_without_keyword_reinterpretation() {
    for spelling in ["«A.B»", "A.B", "«7»", "«λ 星»", "«Type»", "«Prop»"] {
        let expected = clean_parser::parse_name(spelling).unwrap();
        let span = Span::new(17, 31);
        let expr = SurfaceExpr::Ident(span, expected.clone());
        let syntax = surface_to_syntax(&expr);
        assert!(syntax.as_ident().unwrap().same_syntax(&expected));
        let Some(SurfaceExpr::Ident(actual_span, actual_name)) = syntax_to_surface(&syntax) else {
            panic!("{spelling} was not retained as an identifier");
        };
        assert_eq!(actual_span, span);
        assert!(actual_name.same_syntax(&expected));
    }
    for (spelling, universe) in [("Type", UniverseExpr::Type), ("Prop", UniverseExpr::Prop)] {
        let syntax = Syntax::ident(&SurfaceName::component(spelling, false));
        let Some(SurfaceExpr::Universe(_, actual)) = syntax_to_surface(&syntax) else {
            panic!("unescaped universe keyword must remain syntax");
        };
        assert!(matches!(
            (actual, universe),
            (UniverseExpr::Type, UniverseExpr::Type) | (UniverseExpr::Prop, UniverseExpr::Prop)
        ));
    }
    for universe in ["Prop", "Type", "Type 2", "Sort 0"] {
        let original = parse_expr(&format!("({universe} → {universe})")).unwrap();
        let expanded = expand_surface_macros(&mut MacroCtx::new(), &original).unwrap();
        let SurfaceExpr::Paren(_, before) = &original else {
            panic!("parenthesized source");
        };
        let SurfaceExpr::Paren(_, after) = &expanded else {
            panic!("parenthesized expansion");
        };
        let SurfaceExpr::Arrow(_, before_domain, before_codomain) = before.as_ref() else {
            panic!("source arrow");
        };
        let SurfaceExpr::Arrow(_, after_domain, after_codomain) = after.as_ref() else {
            panic!("expanded arrow");
        };
        for (before, after) in [
            (before_domain.as_ref(), after_domain.as_ref()),
            (before_codomain.as_ref(), after_codomain.as_ref()),
        ] {
            assert!(matches!(before, SurfaceExpr::Universe(..)));
            assert_eq!(before.span(), after.span());
            assert_eq!(format!("{before:?}"), format!("{after:?}"));
        }
    }
}

#[test]
fn typed_macro_scope_activation_distinguishes_escaped_component_and_qualification() {
    let escaped = SurfaceName::component("A.B", true);
    let qualified = SurfaceName::generated_path("A.B");
    let mut ctx = MacroCtx::new();
    let expansion = SurfaceExpr::Ident(Span::dummy(), SurfaceName::component("value", false));
    ctx.register_scoped_notation(
        &escaped,
        NotationKind::Notation,
        None,
        &[NotationItem::Literal("alias".into())],
        &expansion,
    )
    .unwrap();
    ctx.set_current_namespace(&qualified);
    let alias = SurfaceName::component("alias", false);
    assert!(ctx.lookup_simple_notation(&alias).is_none());
    ctx.set_current_namespace(&escaped.append(&SurfaceName::component("Child", false)));
    assert!(ctx.lookup_simple_notation(&alias).is_some());
    ctx.set_current_namespace(&qualified);
    ctx.activate_scoped_namespace(&escaped);
    assert!(ctx.lookup_simple_notation(&alias).is_some());
}

#[test]
fn binder_level_and_projection_roundtrips_preserve_typed_numeric_components() {
    let name = SurfaceName::component("A.B", true)
        .append(&SurfaceName::from_name(clean_kernel::Name::anon().num(7)));
    let binder = SurfaceBinder {
        span: Span::dummy(),
        name: name.clone(),
        ty: None,
        default: None,
        info: SurfaceBinderInfo::Explicit,
    };
    let expression = SurfaceExpr::Lambda(
        Span::dummy(),
        vec![binder],
        Box::new(SurfaceExpr::Ident(Span::dummy(), name.clone())),
    );
    let Some(SurfaceExpr::Lambda(_, binders, body)) =
        syntax_to_surface(&surface_to_syntax(&expression))
    else {
        panic!("lambda did not roundtrip");
    };
    assert!(binders[0].name.same_syntax(&name));
    let SurfaceExpr::Ident(_, body_name) = body.as_ref() else {
        panic!("binder reference lost");
    };
    assert!(body_name.same_syntax(&name));
    let Some(LevelExpr::Param(level_name)) =
        syntax_to_level(&level_to_syntax(&LevelExpr::Param(name.clone())))
    else {
        panic!("level did not roundtrip");
    };
    assert!(level_name.same_syntax(&name));
    let projection = SurfaceExpr::Proj(
        Span::dummy(),
        Box::new(expression),
        Projection::Named(name.clone()),
    );
    let Some(SurfaceExpr::Proj(_, _, Projection::Named(field_name))) =
        syntax_to_surface(&surface_to_syntax(&projection))
    else {
        panic!("projection did not roundtrip");
    };
    assert!(field_name.same_syntax(&name));
}

#[test]
fn test_macro_ctx_creation() {
    let ctx = MacroCtx::new();
    assert!(!ctx.registry().is_empty());
}

#[test]
fn test_surface_to_syntax_ident() {
    let expr = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("foo"));
    let syntax = surface_to_syntax(&expr);
    assert!(syntax.is_ident());
    assert_eq!(syntax.as_ident(), Some(&SurfaceName::generated_path("foo")));
}

#[test]
fn test_surface_to_syntax_lit_nat() {
    let expr = SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42));
    let syntax = surface_to_syntax(&expr);
    assert!(syntax.is_node());
    assert_eq!(syntax.kind(), Some(&SyntaxKind::num()));
}

#[test]
fn test_surface_to_syntax_app() {
    let func = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("f"));
    let arg = SurfaceArg::positional(SurfaceExpr::Ident(
        Span::dummy(),
        SurfaceName::generated_path("x"),
    ));
    let expr = SurfaceExpr::App(Span::dummy(), Box::new(func), vec![arg]);

    let syntax = surface_to_syntax(&expr);
    assert!(syntax.is_node());
    assert_eq!(syntax.kind(), Some(&SyntaxKind::app_kind()));
}

#[test]
fn test_surface_to_syntax_if() {
    let cond = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("cond"));
    let then_br = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("then"));
    let else_br = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("else"));
    let expr = SurfaceExpr::If(
        Span::dummy(),
        Box::new(cond),
        Box::new(then_br),
        Box::new(else_br),
    );

    let syntax = surface_to_syntax(&expr);
    assert!(syntax.is_node());
    assert_eq!(syntax.kind(), Some(&SyntaxKind::if_then_else()));
}

#[test]
fn test_syntax_to_surface_ident() {
    let syntax = Syntax::generated_ident("bar");
    let surface = syntax_to_surface(&syntax).unwrap();
    match surface {
        SurfaceExpr::Ident(_, name) => {
            assert_eq!(name.name(), SurfaceName::generated_path("bar").name())
        }
        _ => panic!("expected ident"),
    }
}

#[test]
fn test_syntax_to_surface_num() {
    let syntax = Syntax::mk_num(123);
    let surface = syntax_to_surface(&syntax).unwrap();
    match surface {
        SurfaceExpr::Lit(_, SurfaceLit::Nat(n)) => assert_eq!(n, 123),
        _ => panic!("expected nat literal"),
    }
}

#[test]
fn test_syntax_to_surface_app() {
    let syntax = Syntax::mk_app(
        Syntax::generated_ident("f"),
        vec![Syntax::generated_ident("x"), Syntax::generated_ident("y")],
    );
    let surface = syntax_to_surface(&syntax).unwrap();
    match surface {
        SurfaceExpr::App(_, func, args) => {
            match func.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("f").name())
                }
                _ => panic!("expected ident"),
            }
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected app"),
    }
}

#[test]
fn test_roundtrip_simple() {
    let original = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("test"));
    let syntax = surface_to_syntax(&original);
    let recovered = syntax_to_surface(&syntax).unwrap();

    match recovered {
        SurfaceExpr::Ident(_, name) => {
            assert_eq!(name.name(), SurfaceName::generated_path("test").name())
        }
        _ => panic!("roundtrip failed"),
    }
}

#[test]
fn test_roundtrip_app() {
    let func = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("add"));
    let arg1 = SurfaceArg::positional(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)));
    let arg2 = SurfaceArg::positional(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(2)));
    let original = SurfaceExpr::App(Span::dummy(), Box::new(func), vec![arg1, arg2]);

    let syntax = surface_to_syntax(&original);
    let recovered = syntax_to_surface(&syntax).unwrap();

    match recovered {
        SurfaceExpr::App(_, func, args) => {
            match func.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("add").name())
                }
                _ => panic!("expected ident"),
            }
            assert_eq!(args.len(), 2);
        }
        _ => panic!("roundtrip failed"),
    }
}

#[test]
fn test_if_expansion() {
    let mut ctx = MacroCtx::new();

    // Create if-then-else syntax
    let syntax = Syntax::node(
        SyntaxKind::if_then_else(),
        vec![
            Syntax::generated_ident("condition"),
            Syntax::generated_ident("thenBranch"),
            Syntax::generated_ident("elseBranch"),
        ],
    );

    // Expand
    let expanded = ctx.expand(syntax).unwrap();

    // Should expand to ite application
    assert!(expanded.is_node());
    assert_eq!(expanded.kind(), Some(&SyntaxKind::app_kind()));

    // First child should be "ite"
    assert_eq!(
        expanded.child(0).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("ite"))
    );
}

#[test]
fn test_macro_stats() {
    let mut ctx = MacroCtx::new();

    let syntax = Syntax::node(
        SyntaxKind::if_then_else(),
        vec![
            Syntax::generated_ident("c"),
            Syntax::generated_ident("t"),
            Syntax::generated_ident("e"),
        ],
    );

    let _ = ctx.expand(syntax).unwrap();

    let stats = ctx.last_stats().unwrap();
    assert!(stats.expansions > 0);
}

#[test]
fn test_register_macro_rules_from_decl() {
    let decl = parse_decl("macro_rules | `(myMacro $x) => `(id $x)").unwrap();
    let arms = match decl {
        SurfaceDecl::MacroRules { arms, .. } => arms,
        other => panic!("unexpected decl {other:?}"),
    };

    let mut ctx = MacroCtx::new();
    ctx.register_macro_rules(None, &arms).unwrap();

    let expr = parse_expr("myMacro foo").unwrap();
    let syntax = surface_to_syntax(&expr);
    assert!(!ctx
        .registry()
        .get_by_kind(&SyntaxKind::app_kind())
        .is_empty());

    let direct = ctx
        .registry()
        .try_expand(&syntax)
        .expect("macro should apply");
    assert_eq!(direct.kind(), Some(&SyntaxKind::app_kind()));

    let expanded = ctx.expand(syntax).unwrap();
    let stats = ctx.last_stats().unwrap();
    assert!(stats.expansions > 0);

    assert_eq!(expanded.kind(), Some(&SyntaxKind::app_kind()));
    assert_eq!(
        expanded.child(0).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("id"))
    );
}

#[test]
fn test_register_syntax_category() {
    let mut ctx = MacroCtx::new();

    // Built-in categories should exist
    assert!(ctx.has_syntax_category("term"));
    assert!(ctx.has_syntax_category("tactic"));

    // Custom category should not exist yet
    assert!(!ctx.has_syntax_category("mycat"));

    // Register custom category
    ctx.register_syntax_category("mycat");
    assert!(ctx.has_syntax_category("mycat"));
}

#[test]
fn typed_syntax_category_ingress_does_not_reparse_dotted_or_numeric_components() {
    let mut ctx = MacroCtx::new();
    let escaped = SurfaceName::component("a.b", true);
    ctx.register_typed_syntax_category(&escaped).unwrap();
    assert!(ctx.has_syntax_category("a.b"));
    assert!(ctx
        .register_typed_syntax_category(&SurfaceName::generated_path("a.b"))
        .is_err());
    assert!(ctx
        .register_typed_syntax_category(&SurfaceName::from_name(clean_kernel::Name::anon().num(1)))
        .is_err());
    assert!(ctx
        .register_typed_syntax_category(
            &SurfaceName::component("a.b", true).with_relative_constructor()
        )
        .is_err());

    let pattern = [SyntaxPatternItem::Literal("unique_category_keyword".into())];
    ctx.register_syntax(None, None, &pattern, "a.b").unwrap();
    let def = ctx
        .registry
        .get_by_kind(&pattern_kind_from_items(&pattern))
        .first()
        .expect("registered syntax");
    assert_eq!(
        def.replacement.category.name(),
        &clean_kernel::Name::anon().str("a.b")
    );
    assert_ne!(
        def.replacement.category.name(),
        SurfaceName::generated_path("a.b").name()
    );
}

#[test]
fn test_register_syntax_declaration() {
    let mut ctx = MacroCtx::new();

    // Register a simple syntax declaration: syntax "mykey" x:term : term
    let pattern = vec![
        SyntaxPatternItem::Literal("mykey".to_string()),
        SyntaxPatternItem::Variable {
            name: SurfaceName::generated_path("x"),
            category: Some("term".to_string()),
        },
    ];

    ctx.register_syntax(
        Some(&SurfaceName::generated_path("mykey_syntax")),
        Some(&50u64.into()),
        &pattern,
        "term",
    )
    .unwrap();

    // Check that the macro was registered
    assert!(
        ctx.registry().get_by_name("mykey_syntax").is_some(),
        "mykey_syntax should be registered"
    );
}

#[test]
fn test_register_notation_infixl() {
    let mut ctx = MacroCtx::new();

    // Register: infixl:65 " +++ " => myAdd
    let pattern = vec![
        NotationItem::Variable(SurfaceName::generated_path("a")),
        NotationItem::Literal(" +++ ".to_string()),
        NotationItem::Variable(SurfaceName::generated_path("b")),
    ];
    let expansion = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("myAdd"));

    ctx.register_notation(NotationKind::Infixl, Some(65), &pattern, &expansion)
        .unwrap();

    // Check macro was registered
    let registered_names = ctx.registry().macro_names();
    assert!(registered_names
        .iter()
        .any(|n| n.contains("infixl") && n.contains("+++")));
}

#[test]
fn test_register_notation_prefix() {
    let mut ctx = MacroCtx::new();

    // Register: prefix:max "!!!" => myNot
    let pattern = vec![
        NotationItem::Literal("!!!".to_string()),
        NotationItem::Variable(SurfaceName::generated_path("x")),
    ];
    let expansion = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("myNot"));

    ctx.register_notation(NotationKind::Prefix, Some(1024), &pattern, &expansion)
        .unwrap();

    // Check macro was registered
    let registered_names = ctx.registry().macro_names();
    assert!(registered_names
        .iter()
        .any(|n| n.contains("prefix") && n.contains("!!!")));
}

#[test]
fn test_nullary_notation_capture_requires_same_lexical_variable() {
    let mut ctx = MacroCtx::new();
    ctx.set_active_variable_bindings([(SurfaceName::generated_path("x"), 41)]);
    let pattern = vec![NotationItem::Literal("A".to_string())];
    let expansion = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("x"));
    ctx.register_notation(NotationKind::Notation, None, &pattern, &expansion)
        .expect("nullary notation should register");

    assert!(
        matches!(
            ctx.lookup_simple_notation(&SurfaceName::generated_path("A")),
            Some(SimpleNotationLookup::Active(SurfaceExpr::Ident(_, name))) if name.name() == SurfaceName::generated_path("x").name()
        ),
        "alias is active while its captured section variable is active"
    );
    let mut dependencies = HashSet::from([SurfaceName::generated_path("A")]);
    ctx.close_over_simple_notation_dependencies(&mut dependencies);
    assert!(
        dependencies.contains(&SurfaceName::generated_path("x")),
        "section-binder use analysis must see identifiers introduced by the alias"
    );

    ctx.set_active_variable_bindings(std::iter::empty());
    assert!(
        matches!(
            ctx.lookup_simple_notation(&SurfaceName::generated_path("A")),
            Some(SimpleNotationLookup::Expired)
        ),
        "expired alias must remain registered as an unavailable hygienic capture"
    );

    ctx.set_active_variable_bindings([(SurfaceName::generated_path("x"), 99)]);
    assert!(
        matches!(
            ctx.lookup_simple_notation(&SurfaceName::generated_path("A")),
            Some(SimpleNotationLookup::Expired)
        ),
        "same spelling in a later scope must not reactivate the captured alias"
    );

    ctx.set_active_variable_bindings([
        (SurfaceName::generated_path("x"), 41),
        (SurfaceName::generated_path("x"), 99),
    ]);
    assert!(
        matches!(
            ctx.lookup_simple_notation(&SurfaceName::generated_path("A")),
            Some(SimpleNotationLookup::Active(SurfaceExpr::Ident(_, name))) if name.name() == SurfaceName::generated_path("x").name()
        ),
        "an inner shadow must not retire the still-live captured outer binding"
    );
}

#[test]
fn test_scoped_notation_gated_by_current_namespace_and_activation() {
    let mut ctx = MacroCtx::new();
    let pattern = vec![NotationItem::Literal("two".to_string())];
    let expansion = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("Two.mk"));

    ctx.register_scoped_notation(
        &SurfaceName::generated_path("Foo"),
        NotationKind::Notation,
        None,
        &pattern,
        &expansion,
    )
    .expect("scoped nullary notation should lower");

    // Inert at root: not in the base registry, alias not visible.
    assert!(
        ctx.lookup_simple_notation(&SurfaceName::generated_path("two"))
            .is_none(),
        "scoped notation must be INERT at root without activation"
    );

    // Active while the declaring namespace is current …
    ctx.set_current_namespace(&SurfaceName::generated_path("Foo"));
    assert!(
        ctx.lookup_simple_notation(&SurfaceName::generated_path("two"))
            .is_some(),
        "scoped notation must be active inside its declaring namespace"
    );
    // … or an ancestor of the current namespace.
    ctx.set_current_namespace(&SurfaceName::generated_path("Foo.Bar"));
    assert!(
        ctx.lookup_simple_notation(&SurfaceName::generated_path("two"))
            .is_some(),
        "scoped notation must be active in child namespaces"
    );
    // A non-dot-boundary prefix must NOT activate (Foo vs Foobar).
    ctx.set_current_namespace(&SurfaceName::generated_path("Foobar"));
    assert!(
        ctx.lookup_simple_notation(&SurfaceName::generated_path("two"))
            .is_none(),
        "`Foobar` must not activate `Foo`'s scoped notation"
    );

    // `open` activation is frame-bounded.
    ctx.set_current_namespace(&SurfaceName::generated_path(""));
    ctx.push_scoped_activation_frame();
    ctx.activate_scoped_namespace(&SurfaceName::generated_path("Foo"));
    assert!(
        ctx.lookup_simple_notation(&SurfaceName::generated_path("two"))
            .is_some(),
        "activation must make the scoped notation visible"
    );
    ctx.pop_scoped_activation_frame();
    assert!(
        ctx.lookup_simple_notation(&SurfaceName::generated_path("two"))
            .is_none(),
        "popping the frame must deactivate the scoped notation"
    );
}

#[test]
fn test_scoped_infix_joins_effective_registry_only_when_active() {
    let mut ctx = MacroCtx::new();
    let pattern = vec![
        NotationItem::Variable(SurfaceName::generated_path("a")),
        NotationItem::Literal(" +++ ".to_string()),
        NotationItem::Variable(SurfaceName::generated_path("b")),
    ];
    let expansion = SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("myAdd"));

    ctx.register_scoped_notation(
        &SurfaceName::generated_path("Foo"),
        NotationKind::Infixl,
        Some(65),
        &pattern,
        &expansion,
    )
    .expect("scoped infixl should lower");

    // The BASE registry never holds the scoped def.
    assert!(
        !ctx.registry()
            .macro_names()
            .iter()
            .any(|n| n.contains("infixl") && n.contains("+++")),
        "scoped notation must stay out of the base registry"
    );

    // Inactive: no effective registry is materialized.
    assert!(
        ctx.effective_registry.is_none(),
        "no effective registry without an active scoped notation"
    );

    // Active: the effective registry holds the scoped def.
    ctx.set_current_namespace(&SurfaceName::generated_path("Foo"));
    let effective = ctx
        .effective_registry
        .as_ref()
        .expect("activation must materialize the effective registry");
    assert!(
        effective
            .macro_names()
            .iter()
            .any(|n| n.contains("infixl") && n.contains("+++")),
        "active scoped notation must be in the effective registry"
    );

    // Deactivate: the effective registry is dropped again.
    ctx.set_current_namespace(&SurfaceName::generated_path(""));
    assert!(
        ctx.effective_registry.is_none(),
        "deactivation must drop the effective registry"
    );
}

#[test]
fn test_register_macro_declaration() {
    let mut ctx = MacroCtx::new();

    // Register: macro "unless" cond:term "then" body:term : term => `(if !$cond then $body else ())
    let pattern = vec![
        SyntaxPatternItem::Literal("unless".to_string()),
        SyntaxPatternItem::Variable {
            name: SurfaceName::generated_path("cond"),
            category: Some("term".to_string()),
        },
        SyntaxPatternItem::Literal("then".to_string()),
        SyntaxPatternItem::Variable {
            name: SurfaceName::generated_path("body"),
            category: Some("term".to_string()),
        },
    ];
    let expansion = SurfaceExpr::Ident(
        Span::dummy(),
        SurfaceName::generated_path("expanded_unless"),
    );

    ctx.register_macro(&pattern, "term", &expansion).unwrap();

    // Check macro was registered
    let registered_names = ctx.registry().macro_names();
    assert!(registered_names.iter().any(|n| n.contains("unless")));
}

#[test]
fn test_syntax_pattern_to_syntax_simple() {
    let pattern = vec![
        SyntaxPatternItem::Literal("if".to_string()),
        SyntaxPatternItem::Variable {
            name: SurfaceName::generated_path("cond"),
            category: Some("term".to_string()),
        },
        SyntaxPatternItem::Literal("then".to_string()),
        SyntaxPatternItem::Variable {
            name: SurfaceName::generated_path("body"),
            category: None,
        },
    ];

    let syntax = syntax_pattern_to_syntax(&pattern);
    assert!(syntax.is_node());
    assert_eq!(syntax.kind(), Some(&SyntaxKind::app("seq")));
    assert_eq!(syntax.children().len(), 4);
}

#[test]
fn test_notation_pattern_to_syntax() {
    let items = vec![
        NotationItem::Variable(SurfaceName::generated_path("a")),
        NotationItem::Literal("+".to_string()),
        NotationItem::Variable(SurfaceName::generated_path("b")),
    ];

    let (syntax, kind, vars) = notation_pattern_to_syntax(NotationKind::Infixl, &items);

    assert!(syntax.is_node());
    assert_eq!(kind, SyntaxKind::app("+"));
    assert_eq!(
        vars,
        vec![
            SurfaceName::generated_path("a"),
            SurfaceName::generated_path("b")
        ]
    );
}

#[test]
fn test_pattern_to_name() {
    let pattern = vec![
        SyntaxPatternItem::Literal("unless".to_string()),
        SyntaxPatternItem::Variable {
            name: SurfaceName::generated_path("cond"),
            category: None,
        },
    ];

    let name = pattern_to_name(&pattern);
    assert_eq!(name, "unless_cond");
}

#[test]
fn test_notation_to_name() {
    let items = vec![
        NotationItem::Variable(SurfaceName::generated_path("a")),
        NotationItem::Literal(" + ".to_string()),
        NotationItem::Variable(SurfaceName::generated_path("b")),
    ];

    let name = notation_to_name(NotationKind::Infixl, &items);
    assert!(name.starts_with("infixl_"));
    assert!(name.contains('+'));
}

// ====================================================================
// Roundtrip tests for all SurfaceExpr variants (#1271)
// ====================================================================

#[test]
fn test_roundtrip_universe_inst() {
    // Foo.{u, v} — explicit universe level arguments
    let expr = SurfaceExpr::UniverseInst(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("Foo"),
        )),
        vec![
            LevelExpr::Param(SurfaceName::generated_path("u")),
            LevelExpr::Param(SurfaceName::generated_path("v")),
        ],
    );
    let syntax = surface_to_syntax(&expr);
    assert_eq!(syntax.kind(), Some(&SyntaxKind::app("universeInst")));
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::UniverseInst(_, inner, levels) => {
            match inner.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("Foo").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            assert_eq!(levels.len(), 2);
            assert!(
                matches!(&levels[0], LevelExpr::Param(p) if p.name() == SurfaceName::generated_path("u").name())
            );
            assert!(
                matches!(&levels[1], LevelExpr::Param(p) if p.name() == SurfaceName::generated_path("v").name())
            );
        }
        other => panic!("expected UniverseInst, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_universe_inst_succ_level() {
    // Foo.{u+1} — universe with successor level
    let expr = SurfaceExpr::UniverseInst(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("Bar"),
        )),
        vec![LevelExpr::Succ(Box::new(LevelExpr::Param(
            SurfaceName::generated_path("u"),
        )))],
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::UniverseInst(_, inner, levels) => {
            match inner.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("Bar").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            assert_eq!(levels.len(), 1);
            match &levels[0] {
                LevelExpr::Succ(inner) => {
                    assert!(
                        matches!(inner.as_ref(), LevelExpr::Param(p) if p.name() == SurfaceName::generated_path("u").name())
                    );
                }
                other => panic!("expected Succ, got {other:?}"),
            }
        }
        other => panic!("expected UniverseInst, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_pattern_match_lambda() {
    // fun | x => x — pattern match lambda
    let binder = SurfaceBinder {
        span: Span::dummy(),
        name: SurfaceName::generated_path("x"),
        ty: None,
        default: None,
        info: SurfaceBinderInfo::Explicit,
    };
    let expr = SurfaceExpr::PatternMatchLambda(
        Span::dummy(),
        vec![binder],
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("x"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    assert_eq!(syntax.kind(), Some(&SyntaxKind::app("patternMatchLambda")));
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::PatternMatchLambda(_, binders, body) => {
            assert_eq!(binders.len(), 1);
            assert_eq!(
                binders[0].name.name(),
                SurfaceName::generated_path("x").name()
            );
            match body.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("x").name())
                }
                other => panic!("expected Ident body, got {other:?}"),
            }
        }
        other => panic!("expected PatternMatchLambda, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_lambda() {
    // fun (x : Nat) => x
    let binder = SurfaceBinder {
        span: Span::dummy(),
        name: SurfaceName::generated_path("x"),
        ty: Some(Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("Nat"),
        ))),
        default: None,
        info: SurfaceBinderInfo::Explicit,
    };
    let expr = SurfaceExpr::Lambda(
        Span::dummy(),
        vec![binder],
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("x"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Lambda(_, binders, body) => {
            assert_eq!(binders.len(), 1);
            assert_eq!(
                binders[0].name.name(),
                SurfaceName::generated_path("x").name()
            );
            match binders[0].ty.as_deref() {
                Some(SurfaceExpr::Ident(_, ty_name)) => {
                    assert_eq!(
                        ty_name.name(),
                        SurfaceName::generated_path("Nat").name(),
                        "binder type should be Nat"
                    );
                }
                other => panic!("expected Some(Ident(\"Nat\")) binder type, got {other:?}"),
            }
            match body.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("x").name())
                }
                other => panic!("expected Ident body, got {other:?}"),
            }
        }
        other => panic!("expected Lambda, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_pi() {
    // forall (x : A), B
    let binder = SurfaceBinder {
        span: Span::dummy(),
        name: SurfaceName::generated_path("x"),
        ty: Some(Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("A"),
        ))),
        default: None,
        info: SurfaceBinderInfo::Explicit,
    };
    let expr = SurfaceExpr::Pi(
        Span::dummy(),
        vec![binder],
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("B"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Pi(_, binders, body) => {
            assert_eq!(binders.len(), 1);
            assert_eq!(
                binders[0].name.name(),
                SurfaceName::generated_path("x").name()
            );
            match body.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("B").name())
                }
                other => panic!("expected Ident body, got {other:?}"),
            }
        }
        other => panic!("expected Pi, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_arrow() {
    // A → B
    let expr = SurfaceExpr::Arrow(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("A"),
        )),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("B"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Arrow(_, from, to) => {
            match from.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("A").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            match to.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("B").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
        }
        other => panic!("expected Arrow, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_let() {
    // let x := 42 in x
    let binder = SurfaceBinder {
        span: Span::dummy(),
        name: SurfaceName::generated_path("x"),
        ty: None,
        default: None,
        info: SurfaceBinderInfo::Explicit,
    };
    let expr = SurfaceExpr::Let(
        Span::dummy(),
        binder,
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42))),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("x"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Let(_, b, val, body) => {
            assert_eq!(b.name.name(), SurfaceName::generated_path("x").name());
            match val.as_ref() {
                SurfaceExpr::Lit(_, SurfaceLit::Nat(n)) => assert_eq!(*n, 42),
                other => panic!("expected Nat lit, got {other:?}"),
            }
            match body.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("x").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_let_rec() {
    // let rec f := body in result
    let binder = SurfaceBinder {
        span: Span::dummy(),
        name: SurfaceName::generated_path("f"),
        ty: None,
        default: None,
        info: SurfaceBinderInfo::Explicit,
    };
    let expr = SurfaceExpr::LetRec(
        Span::dummy(),
        binder,
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("body"),
        )),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("result"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::LetRec(_, b, val, body) => {
            assert_eq!(b.name.name(), SurfaceName::generated_path("f").name());
            match val.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("body").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            match body.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("result").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
        }
        other => panic!("expected LetRec, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_ascription() {
    // (e : T)
    let expr = SurfaceExpr::Ascription(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("e"),
        )),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("T"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Ascription(_, e, t) => {
            match e.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("e").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            match t.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("T").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
        }
        other => panic!("expected Ascription, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_explicit() {
    // @f
    let expr = SurfaceExpr::Explicit(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("f"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Explicit(_, inner) => match inner.as_ref() {
            SurfaceExpr::Ident(_, name) => {
                assert_eq!(name.name(), SurfaceName::generated_path("f").name())
            }
            other => panic!("expected Ident, got {other:?}"),
        },
        other => panic!("expected Explicit, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_named_arg() {
    // (name := expr)
    let expr = SurfaceExpr::NamedArg(
        Span::dummy(),
        SurfaceName::generated_path("name"),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("val"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::NamedArg(_, name, val) => {
            assert_eq!(name.name(), SurfaceName::generated_path("name").name());
            match val.as_ref() {
                SurfaceExpr::Ident(_, v) => {
                    assert_eq!(v.name(), SurfaceName::generated_path("val").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
        }
        other => panic!("expected NamedArg, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_out_param() {
    // outParam T
    let expr = SurfaceExpr::OutParam(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("T"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::OutParam(_, inner) => match inner.as_ref() {
            SurfaceExpr::Ident(_, name) => {
                assert_eq!(name.name(), SurfaceName::generated_path("T").name())
            }
            other => panic!("expected Ident, got {other:?}"),
        },
        other => panic!("expected OutParam, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_semi_out_param() {
    // semiOutParam T
    let expr = SurfaceExpr::SemiOutParam(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("T"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::SemiOutParam(_, inner) => match inner.as_ref() {
            SurfaceExpr::Ident(_, name) => {
                assert_eq!(name.name(), SurfaceName::generated_path("T").name())
            }
            other => panic!("expected Ident, got {other:?}"),
        },
        other => panic!("expected SemiOutParam, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_if_then_else() {
    // if c then t else e
    let expr = SurfaceExpr::If(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("c"),
        )),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("t"),
        )),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("e"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::If(_, cond, then_br, else_br) => {
            match cond.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("c").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            match then_br.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("t").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            match else_br.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("e").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
        }
        other => panic!("expected If, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_if_let() {
    // if let pat := scrutinee then t else e
    let expr = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::Var(SurfaceName::generated_path("x")),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("scrutinee"),
        )),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("t"),
        )),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("e"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::IfLet(_, pat, scrut, then_br, else_br) => {
            assert!(
                matches!(pat, SurfacePattern::Var(ref n) if n.name() == SurfaceName::generated_path("x").name())
            );
            match scrut.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("scrutinee").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            match then_br.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("t").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            match else_br.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("e").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
        }
        other => panic!("expected IfLet, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_if_decidable() {
    // if h : p then t else e
    let expr = SurfaceExpr::IfDecidable(
        Span::dummy(),
        SurfaceName::generated_path("h"),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("p"),
        )),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("t"),
        )),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("e"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::IfDecidable(_, witness, prop, then_br, else_br) => {
            assert_eq!(witness.name(), SurfaceName::generated_path("h").name());
            match prop.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("p").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            match then_br.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("t").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            match else_br.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("e").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
        }
        other => panic!("expected IfDecidable, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_match() {
    // match x with | y => y
    let arm = SurfaceMatchArm {
        span: Span::dummy(),
        pattern: SurfacePattern::Var(SurfaceName::generated_path("y")),
        body: SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("y")),
    };
    let expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("x"),
        )),
        vec![arm],
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Match(_, _, scrutinee, arms) => {
            match scrutinee.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("x").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            assert_eq!(arms.len(), 1);
            assert!(
                matches!(&arms[0].pattern, SurfacePattern::Var(ref n) if n.name() == SurfaceName::generated_path("y").name())
            );
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_proj_named() {
    // e.field
    let expr = SurfaceExpr::Proj(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("e"),
        )),
        Projection::Named(SurfaceName::generated_path("field")),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Proj(_, inner, proj) => {
            match inner.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("e").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            assert!(
                matches!(proj, Projection::Named(ref n) if n.name() == SurfaceName::generated_path("field").name())
            );
        }
        other => panic!("expected Proj, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_proj_index() {
    // e.0
    let expr = SurfaceExpr::Proj(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("e"),
        )),
        Projection::Index(0),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Proj(_, inner, proj) => {
            match inner.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("e").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            assert!(matches!(proj, Projection::Index(0)));
        }
        other => panic!("expected Proj, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_paren() {
    // (x)
    let expr = SurfaceExpr::Paren(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("x"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Paren(_, inner) => match inner.as_ref() {
            SurfaceExpr::Ident(_, name) => {
                assert_eq!(name.name(), SurfaceName::generated_path("x").name())
            }
            other => panic!("expected Ident, got {other:?}"),
        },
        other => panic!("expected Paren, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_hole() {
    let expr = SurfaceExpr::Hole(Span::dummy());
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    assert!(matches!(recovered, SurfaceExpr::Hole(_)));
}

#[test]
fn test_roundtrip_universe_prop() {
    let expr = SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Prop);
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    assert!(matches!(
        recovered,
        SurfaceExpr::Universe(_, UniverseExpr::Prop)
    ));
}

#[test]
fn test_roundtrip_universe_type() {
    let expr = SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Type);
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    assert!(matches!(
        recovered,
        SurfaceExpr::Universe(_, UniverseExpr::Type)
    ));
}

#[test]
fn test_roundtrip_universe_sort() {
    let expr = SurfaceExpr::Universe(
        Span::dummy(),
        UniverseExpr::Sort(Box::new(LevelExpr::Param(SurfaceName::generated_path("u")))),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Universe(_, UniverseExpr::Sort(level)) => {
            assert!(
                matches!(level.as_ref(), LevelExpr::Param(p) if p.name() == SurfaceName::generated_path("u").name())
            );
        }
        other => panic!("expected Universe(Sort), got {other:?}"),
    }
}

#[test]
fn test_roundtrip_let_pattern() {
    // let q($pat) := scrutinee | fallback in body
    let expr = SurfaceExpr::LetPattern(
        Span::dummy(),
        SurfacePattern::Var(SurfaceName::generated_path("x")),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("scrutinee"),
        )),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("fallback"),
        )),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("body"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::LetPattern(_, pat, scrut, fallback, body) => {
            assert!(
                matches!(pat, SurfacePattern::Var(ref n) if n.name() == SurfaceName::generated_path("x").name())
            );
            match scrut.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("scrutinee").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            match fallback.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("fallback").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            match body.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("body").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
        }
        other => panic!("expected LetPattern, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_qq_quotation() {
    // q(expr)
    let expr = SurfaceExpr::QQuotation {
        span: Span::dummy(),
        kind: QQuotationKind::Value,
        inner: Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("x"),
        )),
        type_annot: None,
    };
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::QQuotation {
            kind,
            inner,
            type_annot,
            ..
        } => {
            assert!(matches!(kind, QQuotationKind::Value));
            match inner.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("x").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            assert!(
                type_annot.is_none(),
                "QQuotation Value should have no type annotation"
            );
        }
        other => panic!("expected QQuotation, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_qq_quotation_type() {
    // Q(α)
    let expr = SurfaceExpr::QQuotation {
        span: Span::dummy(),
        kind: QQuotationKind::Type,
        inner: Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("alpha"),
        )),
        type_annot: Some(Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("Nat"),
        ))),
    };
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::QQuotation {
            kind,
            inner,
            type_annot,
            ..
        } => {
            assert!(matches!(kind, QQuotationKind::Type));
            match inner.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("alpha").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
            match type_annot.as_deref() {
                Some(SurfaceExpr::Ident(_, name)) => {
                    assert_eq!(
                        name.name(),
                        SurfaceName::generated_path("Nat").name(),
                        "type annotation should be Nat"
                    );
                }
                other => panic!("expected Some(Ident(\"Nat\")) type annot, got {other:?}"),
            }
        }
        other => panic!("expected QQuotation, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_q_antiquot_simple() {
    // $x
    let expr = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Simple(SurfaceName::generated_path("x")),
    };
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::QAntiquot { content, .. } => {
            assert!(
                matches!(content, QAntiquotContent::Simple(ref n) if n.name() == SurfaceName::generated_path("x").name())
            );
        }
        other => panic!("expected QAntiquot, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_q_antiquot_expr() {
    // $(e)
    let expr = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Expr(Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("e"),
        ))),
    };
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::QAntiquot { content, .. } => match content {
            QAntiquotContent::Expr(inner) => match inner.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("e").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            },
            other => panic!("expected Expr antiquot, got {other:?}"),
        },
        other => panic!("expected QAntiquot, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_q_antiquot_typed() {
    // $(x : τ)
    let expr = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Typed {
            name: SurfaceName::generated_path("x"),
            ty: Box::new(SurfaceExpr::Ident(
                Span::dummy(),
                SurfaceName::generated_path("Nat"),
            )),
        },
    };
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::QAntiquot { content, .. } => match content {
            QAntiquotContent::Typed { name, ty } => {
                assert_eq!(name.name(), SurfaceName::generated_path("x").name());
                match ty.as_ref() {
                    SurfaceExpr::Ident(_, n) => {
                        assert_eq!(n.name(), SurfaceName::generated_path("Nat").name())
                    }
                    other => panic!("expected Ident, got {other:?}"),
                }
            }
            other => panic!("expected Typed antiquot, got {other:?}"),
        },
        other => panic!("expected QAntiquot, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_q_antiquot_splice() {
    // $[xs]* with separator ","
    let expr = SurfaceExpr::QAntiquot {
        span: Span::dummy(),
        content: QAntiquotContent::Splice {
            name: SurfaceName::generated_path("xs"),
            separator: Some(",".to_string()),
            at_least_one: false,
        },
    };
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::QAntiquot { content, .. } => match content {
            QAntiquotContent::Splice {
                name,
                separator,
                at_least_one,
            } => {
                assert_eq!(name.name(), SurfaceName::generated_path("xs").name());
                assert_eq!(separator, Some(",".to_string()));
                assert!(!at_least_one);
            }
            other => panic!("expected Splice antiquot, got {other:?}"),
        },
        other => panic!("expected QAntiquot, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_struct_lit() {
    // { x := val, y := val2 }
    let expr = SurfaceExpr::StructLit {
        span: Span::dummy(),
        struct_type: None,
        base: None,
        fields: vec![
            SurfaceFieldAssign {
                span: Span::dummy(),
                name: SurfaceName::generated_path("x"),
                val: SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("val1")),
            },
            SurfaceFieldAssign {
                span: Span::dummy(),
                name: SurfaceName::generated_path("y"),
                val: SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("val2")),
            },
        ],
    };
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::StructLit {
            struct_type,
            base,
            fields,
            ..
        } => {
            assert!(
                struct_type.is_none(),
                "anonymous struct literal should have no struct_type"
            );
            assert!(
                base.is_none(),
                "struct literal with no spread should have no base"
            );
            assert_eq!(fields.len(), 2);
            assert_eq!(
                fields[0].name.name(),
                SurfaceName::generated_path("x").name()
            );
            assert_eq!(
                fields[1].name.name(),
                SurfaceName::generated_path("y").name()
            );
            match &fields[0].val {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("val1").name())
                }
                other => panic!("expected Ident, got {other:?}"),
            }
        }
        other => panic!("expected StructLit, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_struct_lit_with_base() {
    // { s with x := val }
    let expr = SurfaceExpr::StructLit {
        span: Span::dummy(),
        struct_type: Some(Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("MyStruct"),
        ))),
        base: Some(Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("s"),
        ))),
        fields: vec![SurfaceFieldAssign {
            span: Span::dummy(),
            name: SurfaceName::generated_path("x"),
            val: SurfaceExpr::Ident(Span::dummy(), SurfaceName::generated_path("val")),
        }],
    };
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::StructLit {
            struct_type,
            base,
            fields,
            ..
        } => {
            match struct_type.as_deref() {
                Some(SurfaceExpr::Ident(_, name)) => {
                    assert_eq!(
                        name.name(),
                        SurfaceName::generated_path("MyStruct").name(),
                        "struct_type should be MyStruct"
                    );
                }
                other => {
                    panic!("expected Some(Ident(\"MyStruct\")) struct_type, got {other:?}")
                }
            }
            match base.as_deref() {
                Some(SurfaceExpr::Ident(_, name)) => {
                    assert_eq!(
                        name.name(),
                        SurfaceName::generated_path("s").name(),
                        "base should be s"
                    );
                }
                other => panic!("expected Some(Ident(\"s\")) base, got {other:?}"),
            }
            assert_eq!(fields.len(), 1);
            assert_eq!(
                fields[0].name.name(),
                SurfaceName::generated_path("x").name()
            );
        }
        other => panic!("expected StructLit, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_implicit_binder() {
    // fun {x : A} => x — implicit binder roundtrip
    let binder = SurfaceBinder {
        span: Span::dummy(),
        name: SurfaceName::generated_path("x"),
        ty: Some(Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("A"),
        ))),
        default: None,
        info: SurfaceBinderInfo::Implicit,
    };
    let expr = SurfaceExpr::Lambda(
        Span::dummy(),
        vec![binder],
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("x"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 1);
            assert_eq!(
                binders[0].name.name(),
                SurfaceName::generated_path("x").name()
            );
            assert!(matches!(binders[0].info, SurfaceBinderInfo::Implicit));
        }
        other => panic!("expected Lambda, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_instance_binder() {
    // fun [inst : A] => x — instance binder roundtrip
    let binder = SurfaceBinder {
        span: Span::dummy(),
        name: SurfaceName::generated_path("inst"),
        ty: Some(Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("A"),
        ))),
        default: None,
        info: SurfaceBinderInfo::Instance,
    };
    let expr = SurfaceExpr::Lambda(
        Span::dummy(),
        vec![binder],
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("x"),
        )),
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 1);
            assert_eq!(
                binders[0].name.name(),
                SurfaceName::generated_path("inst").name()
            );
            assert!(matches!(binders[0].info, SurfaceBinderInfo::Instance));
        }
        other => panic!("expected Lambda, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_level_max() {
    // Level: max u v
    let level = LevelExpr::Max(
        Box::new(LevelExpr::Param(SurfaceName::generated_path("u"))),
        Box::new(LevelExpr::Param(SurfaceName::generated_path("v"))),
    );
    let syntax = level_to_syntax(&level);
    let recovered = syntax_to_level(&syntax).unwrap();
    match recovered {
        LevelExpr::Max(a, b) => {
            assert!(
                matches!(a.as_ref(), LevelExpr::Param(p) if p.name() == SurfaceName::generated_path("u").name())
            );
            assert!(
                matches!(b.as_ref(), LevelExpr::Param(p) if p.name() == SurfaceName::generated_path("v").name())
            );
        }
        other => panic!("expected Max, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_level_imax() {
    // Level: imax u v
    let level = LevelExpr::IMax(
        Box::new(LevelExpr::Param(SurfaceName::generated_path("u"))),
        Box::new(LevelExpr::Lit(0)),
    );
    let syntax = level_to_syntax(&level);
    let recovered = syntax_to_level(&syntax).unwrap();
    match recovered {
        LevelExpr::IMax(a, b) => {
            assert!(
                matches!(a.as_ref(), LevelExpr::Param(p) if p.name() == SurfaceName::generated_path("u").name())
            );
            assert!(matches!(b.as_ref(), LevelExpr::Lit(0)));
        }
        other => panic!("expected IMax, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_level_lit() {
    let level = LevelExpr::Lit(3);
    let syntax = level_to_syntax(&level);
    let recovered = syntax_to_level(&syntax).unwrap();
    assert!(matches!(recovered, LevelExpr::Lit(3)));
}

#[test]
fn test_roundtrip_level_antiquot() {
    let level = LevelExpr::Antiquot(SurfaceName::generated_path("u"));
    let syntax = level_to_syntax(&level);
    let recovered = syntax_to_level(&syntax).unwrap();
    assert!(
        matches!(recovered, LevelExpr::Antiquot(ref s) if s.name() == SurfaceName::generated_path("u").name())
    );
}

// Self-audit: missing roundtrip tests found in audit of 5c2c97479

#[test]
fn test_roundtrip_lit_nat() {
    let expr = SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42));
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Lit(_, SurfaceLit::Nat(n)) => assert_eq!(n, 42),
        other => panic!("expected Lit(Nat), got {other:?}"),
    }
}

#[test]
fn test_roundtrip_lit_string() {
    let expr = SurfaceExpr::Lit(Span::dummy(), SurfaceLit::String("hello".to_string()));
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Lit(_, SurfaceLit::String(s)) => assert_eq!(s, "hello"),
        other => panic!("expected Lit(String), got {other:?}"),
    }
}

#[test]
fn test_roundtrip_pattern_string_lit() {
    // Regression test: syntax_to_pattern was missing "str" handler,
    // causing string literal patterns to be misinterpreted as
    // Ctor("str", [Var(s)]) instead of Lit(String(s))
    let pattern = SurfacePattern::Lit(SurfaceLit::String("world".to_string()));
    let syntax = surface_pattern_to_syntax(&pattern);
    let recovered = syntax_to_pattern(&syntax).unwrap();
    match recovered {
        SurfacePattern::Lit(SurfaceLit::String(s)) => assert_eq!(s, "world"),
        other => panic!("expected Lit(String) pattern, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_pattern_nat_lit() {
    let pattern = SurfacePattern::Lit(SurfaceLit::Nat(99));
    let syntax = surface_pattern_to_syntax(&pattern);
    let recovered = syntax_to_pattern(&syntax).unwrap();
    match recovered {
        SurfacePattern::Lit(SurfaceLit::Nat(n)) => assert_eq!(n, 99),
        other => panic!("expected Lit(Nat) pattern, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_pattern_wildcard() {
    let pattern = SurfacePattern::Wildcard;
    let syntax = surface_pattern_to_syntax(&pattern);
    let recovered = syntax_to_pattern(&syntax).unwrap();
    assert!(matches!(recovered, SurfacePattern::Wildcard));
}

#[test]
fn test_roundtrip_pattern_ctor() {
    let pattern = SurfacePattern::Ctor(
        SurfaceName::generated_path("Some"),
        vec![SurfacePattern::Var(SurfaceName::generated_path("x"))],
    );
    let syntax = surface_pattern_to_syntax(&pattern);
    let recovered = syntax_to_pattern(&syntax).unwrap();
    match recovered {
        SurfacePattern::Ctor(name, args) => {
            assert_eq!(name.name(), SurfaceName::generated_path("Some").name());
            assert_eq!(args.len(), 1);
            assert!(
                matches!(&args[0], SurfacePattern::Var(n) if n.name() == SurfaceName::generated_path("x").name())
            );
        }
        other => panic!("expected Ctor pattern, got {other:?}"),
    }
}

// ====================================================================
// Round-trip tests for from_syntax gaps fixed in #2211
// ====================================================================

#[test]
fn test_roundtrip_pattern_as() {
    // As-pattern: x@pat — previously corrupted to Ctor("asPattern", ...)
    let pattern = SurfacePattern::As(
        SurfaceName::generated_path("x"),
        Box::new(SurfacePattern::Ctor(
            SurfaceName::generated_path("Some"),
            vec![SurfacePattern::Var(SurfaceName::generated_path("y"))],
        )),
    );
    let syntax = surface_pattern_to_syntax(&pattern);
    let recovered = syntax_to_pattern(&syntax).unwrap();
    match recovered {
        SurfacePattern::As(name, inner) => {
            assert_eq!(name.name(), SurfaceName::generated_path("x").name());
            match inner.as_ref() {
                SurfacePattern::Ctor(ctor_name, args) => {
                    assert_eq!(ctor_name.name(), SurfaceName::generated_path("Some").name());
                    assert_eq!(args.len(), 1);
                    assert!(
                        matches!(&args[0], SurfacePattern::Var(n) if n.name() == SurfaceName::generated_path("y").name())
                    );
                }
                other => panic!("expected Ctor inner pattern, got {other:?}"),
            }
        }
        other => panic!("expected As pattern, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_pattern_or() {
    // Or-pattern: pat1 | pat2 — previously corrupted to Ctor("orPattern", ...)
    let pattern = SurfacePattern::Or(
        Box::new(SurfacePattern::Ctor(
            SurfaceName::generated_path("None"),
            vec![],
        )),
        Box::new(SurfacePattern::Ctor(
            SurfaceName::generated_path("Some"),
            vec![SurfacePattern::Wildcard],
        )),
    );
    let syntax = surface_pattern_to_syntax(&pattern);
    let recovered = syntax_to_pattern(&syntax).unwrap();
    match recovered {
        SurfacePattern::Or(left, right) => {
            match left.as_ref() {
                SurfacePattern::Ctor(name, args) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("None").name());
                    assert!(args.is_empty());
                }
                other => panic!("expected Ctor(None) left, got {other:?}"),
            }
            match right.as_ref() {
                SurfacePattern::Ctor(name, args) => {
                    assert_eq!(name.name(), SurfaceName::generated_path("Some").name());
                    assert_eq!(args.len(), 1);
                    assert!(matches!(&args[0], SurfacePattern::Wildcard));
                }
                other => panic!("expected Ctor(Some) right, got {other:?}"),
            }
        }
        other => panic!("expected Or pattern, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_do_repeat() {
    // do repeat body — DoElem::Repeat previously had no from_syntax handler
    let expr = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::Repeat(
            Span::dummy(),
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(
                    Span::dummy(),
                    SurfaceName::generated_path("action"),
                )),
            )],
        )],
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::Repeat(_, body) => {
                    assert_eq!(body.len(), 1);
                    match &body[0] {
                        DoElem::Expr(_, inner) => match inner.as_ref() {
                            SurfaceExpr::Ident(_, name) => assert_eq!(
                                name.name(),
                                SurfaceName::generated_path("action").name()
                            ),
                            other => panic!("expected Ident, got {other:?}"),
                        },
                        other => panic!("expected Expr elem, got {other:?}"),
                    }
                }
                other => panic!("expected Repeat elem, got {other:?}"),
            }
        }
        other => panic!("expected Do, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_do_while() {
    // do while cond body — DoElem::While previously had no from_syntax handler
    let expr = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::While(
            Span::dummy(),
            Box::new(SurfaceExpr::Ident(
                Span::dummy(),
                SurfaceName::generated_path("cond"),
            )),
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(
                    Span::dummy(),
                    SurfaceName::generated_path("body"),
                )),
            )],
        )],
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::While(_, cond, body) => {
                    match cond.as_ref() {
                        SurfaceExpr::Ident(_, name) => {
                            assert_eq!(name.name(), SurfaceName::generated_path("cond").name())
                        }
                        other => panic!("expected Ident cond, got {other:?}"),
                    }
                    assert_eq!(body.len(), 1);
                }
                other => panic!("expected While elem, got {other:?}"),
            }
        }
        other => panic!("expected Do, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_do_dbg_trace() {
    // do dbg_trace msg — DoElem::DbgTrace previously had no from_syntax handler
    let expr = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::DbgTrace(
            Span::dummy(),
            Box::new(SurfaceExpr::Lit(
                Span::dummy(),
                SurfaceLit::String("debug".to_string()),
            )),
        )],
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::DbgTrace(_, msg) => match msg.as_ref() {
                    SurfaceExpr::Lit(_, SurfaceLit::String(s)) => assert_eq!(s, "debug"),
                    other => panic!("expected String lit, got {other:?}"),
                },
                other => panic!("expected DbgTrace elem, got {other:?}"),
            }
        }
        other => panic!("expected Do, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_do_bind_return() {
    // do x <- action; return x — exercises renamed doBind + doReturn kind names
    let expr = SurfaceExpr::Do(
        Span::dummy(),
        vec![
            DoElem::Bind(
                Span::dummy(),
                SurfaceBinder::new("x".to_string(), None, SurfaceBinderInfo::Explicit),
                Box::new(SurfaceExpr::Ident(
                    Span::dummy(),
                    SurfaceName::generated_path("getLine"),
                )),
            ),
            DoElem::Return(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(
                    Span::dummy(),
                    SurfaceName::generated_path("x"),
                )),
            ),
        ],
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::Bind(_, binder, action) => {
                    assert_eq!(binder.name.name(), SurfaceName::generated_path("x").name());
                    match action.as_ref() {
                        SurfaceExpr::Ident(_, name) => {
                            assert_eq!(name.name(), SurfaceName::generated_path("getLine").name())
                        }
                        other => panic!("expected Ident, got {other:?}"),
                    }
                }
                other => panic!("expected Bind, got {other:?}"),
            }
            match &elems[1] {
                DoElem::Return(_, expr) => match expr.as_ref() {
                    SurfaceExpr::Ident(_, name) => {
                        assert_eq!(name.name(), SurfaceName::generated_path("x").name())
                    }
                    other => panic!("expected Ident, got {other:?}"),
                },
                other => panic!("expected Return, got {other:?}"),
            }
        }
        other => panic!("expected Do, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_do_let_expr() {
    // do let y := 42; y — exercises renamed doLet + doElem kind names
    let expr = SurfaceExpr::Do(
        Span::dummy(),
        vec![
            DoElem::Let(
                Span::dummy(),
                SurfaceBinder::new("y".to_string(), None, SurfaceBinderInfo::Explicit),
                Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(42))),
            ),
            DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(
                    Span::dummy(),
                    SurfaceName::generated_path("y"),
                )),
            ),
        ],
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2);
            match &elems[0] {
                DoElem::Let(_, binder, val) => {
                    assert_eq!(binder.name.name(), SurfaceName::generated_path("y").name());
                    match val.as_ref() {
                        SurfaceExpr::Lit(_, SurfaceLit::Nat(n)) => assert_eq!(*n, 42),
                        other => panic!("expected Nat lit, got {other:?}"),
                    }
                }
                other => panic!("expected Let, got {other:?}"),
            }
            match &elems[1] {
                DoElem::Expr(_, inner) => match inner.as_ref() {
                    SurfaceExpr::Ident(_, name) => {
                        assert_eq!(name.name(), SurfaceName::generated_path("y").name())
                    }
                    other => panic!("expected Ident, got {other:?}"),
                },
                other => panic!("expected Expr, got {other:?}"),
            }
        }
        other => panic!("expected Do, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_do_try_finally() {
    // do try action catch e => handler finally cleanup
    // exercises doTry + doFinally round-trip (doFinally was missing doSeq wrapper)
    use clean_parser::DoCatchClause;
    let expr = SurfaceExpr::Do(
        Span::dummy(),
        vec![DoElem::TryCatch(
            Span::dummy(),
            // try body
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(
                    Span::dummy(),
                    SurfaceName::generated_path("action"),
                )),
            )],
            // catch clauses
            vec![DoCatchClause {
                span: Span::dummy(),
                binder: SurfaceName::generated_path("e"),
                exc_type: None,
                body: vec![DoElem::Expr(
                    Span::dummy(),
                    Box::new(SurfaceExpr::Ident(
                        Span::dummy(),
                        SurfaceName::generated_path("handler"),
                    )),
                )],
            }],
            // finally body
            Some(vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(
                    Span::dummy(),
                    SurfaceName::generated_path("cleanup"),
                )),
            )]),
        )],
    );
    let syntax = surface_to_syntax(&expr);
    let recovered = syntax_to_surface(&syntax).unwrap();
    match recovered {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::TryCatch(_, try_body, catches, finally_body) => {
                    // Try body
                    assert_eq!(try_body.len(), 1);
                    match &try_body[0] {
                        DoElem::Expr(_, inner) => match inner.as_ref() {
                            SurfaceExpr::Ident(_, name) => assert_eq!(
                                name.name(),
                                SurfaceName::generated_path("action").name()
                            ),
                            other => panic!("expected Ident, got {other:?}"),
                        },
                        other => panic!("expected Expr in try body, got {other:?}"),
                    }
                    // Catch clauses
                    assert_eq!(catches.len(), 1);
                    assert_eq!(
                        catches[0].binder.name(),
                        SurfaceName::generated_path("e").name()
                    );
                    assert_eq!(catches[0].body.len(), 1);
                    // Finally body
                    let fin = finally_body.as_ref().expect("expected finally body");
                    assert_eq!(fin.len(), 1);
                    match &fin[0] {
                        DoElem::Expr(_, inner) => match inner.as_ref() {
                            SurfaceExpr::Ident(_, name) => assert_eq!(
                                name.name(),
                                SurfaceName::generated_path("cleanup").name()
                            ),
                            other => panic!("expected Ident in finally, got {other:?}"),
                        },
                        other => panic!("expected Expr in finally, got {other:?}"),
                    }
                }
                other => panic!("expected TryCatch, got {other:?}"),
            }
        }
        other => panic!("expected Do, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_by_tactic_preserves_variant() {
    // byTactic is serialized as an empty opaque node — tactic children are lost,
    // but the variant type is preserved as ByTactic(_, vec![]).
    let syntax = Syntax::node(SyntaxKind::app("byTactic"), vec![]);
    let result = syntax_to_surface(&syntax);
    assert!(
        matches!(result, Some(SurfaceExpr::ByTactic(_, ref tactics)) if tactics.is_empty()),
        "byTactic should return ByTactic with empty tactics, got {result:?}"
    );
}

#[test]
fn test_roundtrip_calc_block_preserves_variant() {
    // calcBlock is serialized as an empty opaque node — calc steps are lost,
    // but the variant type is preserved as CalcBlock(_, vec![]).
    let syntax = Syntax::node(SyntaxKind::app("calcBlock"), vec![]);
    let result = syntax_to_surface(&syntax);
    assert!(
        matches!(result, Some(SurfaceExpr::CalcBlock(_, ref steps)) if steps.is_empty()),
        "calcBlock should return CalcBlock with empty steps, got {result:?}"
    );
}

// ---- macro_rules expansion: pure-template instantiation (metaprog phase 4) ----

/// Helper: register the arms of a parsed `macro_rules` decl into a fresh ctx.
fn register_macro_rules_src(src: &str) -> MacroCtx {
    let decl = parse_decl(src).expect("macro_rules should parse");
    let arms = match decl {
        SurfaceDecl::MacroRules { arms, .. } => arms,
        other => panic!("expected macro_rules decl, got {other:?}"),
    };
    let mut ctx = MacroCtx::new();
    ctx.register_macro_rules(None, &arms)
        .expect("macro_rules should register");
    ctx
}

#[test]
fn test_macro_rules_binop_template_instantiates_both_operands() {
    // `macro_rules | `(twice $x) => `($x + $x)` applied to `twice foo` must expand to
    // the faithful desugaring `HAdd.hAdd foo foo` (i.e. `foo + foo`), with the
    // antiquotation `$x` substituted in BOTH operand positions — not the previous
    // truncated `foo`.
    let mut ctx = register_macro_rules_src("macro_rules | `(twice $x) => `($x + $x)");
    let syntax = surface_to_syntax(&parse_expr("twice foo").unwrap());

    let expanded = ctx.expand(syntax).expect("twice macro should expand");
    assert_eq!(expanded.kind(), Some(&SyntaxKind::app_kind()));
    let children = expanded.children();
    assert_eq!(children.len(), 3, "expected `(app HAdd.hAdd foo foo)`");
    assert_eq!(
        children[0].as_ident(),
        Some(&SurfaceName::generated_path("HAdd.hAdd"))
    );
    assert_eq!(
        children[1].as_ident(),
        Some(&SurfaceName::generated_path("foo"))
    );
    assert_eq!(
        children[2].as_ident(),
        Some(&SurfaceName::generated_path("foo"))
    );

    // And it converts back to a surface application identical to writing `foo + foo`.
    let back = syntax_to_surface(&expanded).expect("should convert back to surface");
    let reference = surface_to_syntax(&parse_expr("foo + foo").unwrap());
    assert_eq!(
        surface_to_syntax(&back).pretty(),
        reference.pretty(),
        "expansion of `twice foo` must match the direct parse of `foo + foo`"
    );
}

#[test]
fn test_macro_rules_function_template_instantiates_arg() {
    // `macro_rules | `(myMacro $x) => `(id $x)` applied to `myMacro foo` => `id foo`.
    let mut ctx = register_macro_rules_src("macro_rules | `(myMacro $x) => `(id $x)");
    let syntax = surface_to_syntax(&parse_expr("myMacro foo").unwrap());

    let expanded = ctx.expand(syntax).expect("myMacro should expand");
    assert_eq!(expanded.kind(), Some(&SyntaxKind::app_kind()));
    assert_eq!(
        expanded.child(0).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("id"))
    );
    assert_eq!(
        expanded.child(1).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("foo"))
    );
}

#[test]
fn test_macro_rules_multi_arm_selects_matching_arm() {
    // Two arms with distinct heads: the input head selects the right arm and the
    // matching arm's template is instantiated.
    let mut ctx =
        register_macro_rules_src("macro_rules | `(pickA $x $y) => `($x) | `(pickB $x $y) => `($y)");

    // `pickA a b` selects the first arm => `$x` => `a`.
    let a = ctx
        .expand(surface_to_syntax(&parse_expr("pickA a b").unwrap()))
        .expect("pickA should expand");
    assert_eq!(a.as_ident(), Some(&SurfaceName::generated_path("a")));

    // `pickB a b` selects the second arm => `$y` => `b`.
    let b = ctx
        .expand(surface_to_syntax(&parse_expr("pickB a b").unwrap()))
        .expect("pickB should expand");
    assert_eq!(b.as_ident(), Some(&SurfaceName::generated_path("b")));
}

#[test]
fn test_macro_rules_mkfreshid_distinct_per_expansion() {
    // The per-expansion gensym fix, end-to-end through registration + expansion.
    // A computed body that binds a fresh id with `mkFreshId` and returns a
    // quotation using it:
    //   macro_rules | `(dup) => do let f <- mkFreshId; return `(fun $f => $f)
    // Expanding `dup` TWICE must yield two DISTINCT fresh binder ids (before the
    // fix the id was frozen at registration and collided on every expansion).
    // Body uses an application `g $f $f` (the quotation-body grammar's `fun`
    // binder does not yet accept an antiquotation binder; the fresh-id mechanism
    // is the same either way — two markers sharing the one fresh `f`). The arm
    // takes an argument `$y` so the matched input forms an application node (the
    // expander matches on node kinds; a nullary head would not).
    let decl = parse_decl("macro_rules | `(dup $y) => do let f <- mkFreshId; return `(g $f $f $y)");
    let arms = match decl {
        Ok(SurfaceDecl::MacroRules { arms, .. }) => arms,
        // If the parser cannot represent this arm yet, fall back to the
        // clean-macro unit coverage (test_fresh_marker_distinct_id_per_expansion)
        // which proves the same mechanism at the layer the fix lives in.
        other => panic!("expected macro_rules decl to parse, got {other:?}"),
    };
    let mut ctx = MacroCtx::new();
    ctx.register_macro_rules(None, &arms)
        .expect("mkFreshId computed body should register (no longer defers)");

    let input = surface_to_syntax(&parse_expr("dup foo").unwrap());
    let first = ctx.expand(input.clone()).expect("first dup expansion");
    let second = ctx.expand(input).expect("second dup expansion");

    // Collect the fresh binder/use idents from each `fun` expansion. The two
    // markers share the prefix `f`, so within one expansion they coincide.
    let id_of = |s: &Syntax| -> SurfaceName {
        // Find the first ident leaf that carries the fresh prefix `x` (the gensym
        // seed used for the marker) — robust to the surrounding `fun` shape.
        fn first_fresh(s: &Syntax) -> Option<SurfaceName> {
            if let Some(name) = s.as_ident() {
                if name.component_syntax().len() > 1
                    && name.to_string().starts_with("x._macro_fresh.")
                {
                    return Some(name.clone());
                }
            }
            for c in s.children() {
                if let Some(found) = first_fresh(c) {
                    return Some(found);
                }
            }
            None
        }
        first_fresh(s).expect("expansion should contain a gensym'd fresh id")
    };

    let f1 = id_of(&first);
    let f2 = id_of(&second);
    assert_ne!(
        f1, f2,
        "mkFreshId must yield DISTINCT ids on two expansions (got {f1} twice)"
    );
}

#[test]
fn test_macro_rules_static_template_unchanged_alongside_fresh() {
    // NEGATIVE/robustness: a macro that does NOT use gensym still expands
    // identically every time (no behavior change from the hygienic re-eval path).
    let mut ctx = register_macro_rules_src("macro_rules | `(myMacro $x) => `(id $x)");
    let input = surface_to_syntax(&parse_expr("myMacro foo").unwrap());
    let r1 = ctx.expand(input.clone()).expect("expand once");
    let r2 = ctx.expand(input).expect("expand twice");
    assert_eq!(
        r1.pretty(),
        r2.pretty(),
        "non-gensym macro must be unaffected by the fresh-name path"
    );
    assert_eq!(
        r1.child(0).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("id"))
    );
    assert_eq!(
        r1.child(1).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("foo"))
    );
}

#[test]
fn test_macro_rules_nonmatching_input_is_left_unexpanded() {
    // An input whose head does not match any arm is left as-is (no spurious match).
    let mut ctx = register_macro_rules_src("macro_rules | `(only $x) => `($x)");
    let input = surface_to_syntax(&parse_expr("other foo").unwrap());

    let direct = ctx.registry().try_expand(&input);
    assert!(
        direct.is_none(),
        "non-matching head must not match any arm, got {direct:?}"
    );
    // Full expansion returns the input unchanged (recursing into children).
    let expanded = ctx
        .expand(input.clone())
        .expect("expansion should not fail");
    assert_eq!(
        expanded.child(0).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("other"))
    );
}

#[test]
fn test_macro_rules_computed_body_unsupported_defers_honestly() {
    // HONEST DEFER (now: the *unsupported* slice). A computed/monadic `do`-body
    // that uses a monadic bind (`y <- pure $x`) is OUTSIDE the faithfully-
    // evaluable subset (`computed_body`). We must not fabricate a template
    // expansion for it: registration DEFERS with a typed error rather than
    // mis-lowering the whole `do`-block as a pure quotation.
    let decl = parse_decl("macro_rules | `(computed $x) => do let y <- pure $x; return y");
    // Whether the parser accepts this exact shape is not the point; if it does
    // register, the computed arm must NOT yield a faked pure-template expansion of
    // a plain `computed foo` call. (As of this writing the parser rejects the
    // `$`-after-`pure` shape, so the branch below is conservative.)
    if let Ok(SurfaceDecl::MacroRules { arms, .. }) = decl {
        let mut ctx = MacroCtx::new();
        match ctx.register_macro_rules(None, &arms) {
            // Honest defer: a typed registration error, never a silent success.
            Err(MacroRegistrationError::ComputedBodyUnsupported(_)) => {}
            Err(_) => {} // any other honest conversion error is also acceptable.
            Ok(()) => {
                let input = surface_to_syntax(&parse_expr("computed foo").unwrap());
                let expanded = ctx
                    .expand(input.clone())
                    .expect("expansion should not panic");
                // If it did register, it must not be the fabricated `$x` template.
                assert_ne!(
                    expanded.pretty(),
                    Syntax::generated_ident("foo").pretty(),
                    "computed macro body must not be faked as a pure `$x` template"
                );
            }
        }
    }
}

#[test]
fn test_macro_rules_computed_return_quotation_matches_direct_parse() {
    // SUPPORTED: a computed `do`-body whose value is `return `(…)`` evaluates to
    // exactly that quotation. `macro_rules | `(computed $x) => do return `(id $x)`
    // must expand `computed foo` byte-identically to the direct template
    // `macro_rules | `(computed $x) => `(id $x)` applied to `computed foo`.
    let mut computed =
        register_macro_rules_src("macro_rules | `(computed $x) => do return `(id $x)");
    let mut direct = register_macro_rules_src("macro_rules | `(computed $x) => `(id $x)");

    let input = surface_to_syntax(&parse_expr("computed foo").unwrap());
    let computed_out = computed
        .expand(input.clone())
        .expect("computed body should expand");
    let direct_out = direct.expand(input).expect("direct template should expand");

    assert_eq!(
        computed_out.pretty(),
        direct_out.pretty(),
        "computed `do return `(id $x)`` must match the direct template `(id $x)`"
    );
    // And the concrete shape is `(app id foo)`.
    assert_eq!(computed_out.kind(), Some(&SyntaxKind::app_kind()));
    assert_eq!(
        computed_out.child(0).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("id"))
    );
    assert_eq!(
        computed_out.child(1).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("foo"))
    );
}

#[test]
fn test_macro_rules_computed_trailing_expr_quotation_matches_direct_parse() {
    // SUPPORTED: a computed body whose trailing statement is a bare quotation
    // (no `return`) is also a quotation value. `do `(id $x)` == `(id $x)`.
    let mut computed = register_macro_rules_src("macro_rules | `(computed $x) => do `(id $x)");
    let mut direct = register_macro_rules_src("macro_rules | `(computed $x) => `(id $x)");

    let input = surface_to_syntax(&parse_expr("computed foo").unwrap());
    let computed_out = computed.expand(input.clone()).expect("should expand");
    let direct_out = direct.expand(input).expect("should expand");
    assert_eq!(computed_out.pretty(), direct_out.pretty());
}

#[test]
fn test_macro_rules_computed_let_splice_matches_direct_parse() {
    // SUPPORTED: a pure `let inner := `(id $x)` binding spliced into a later
    // quotation `$inner`. The arm
    //   `(wrap $x) => do let inner := `(id $x); return `(f $inner)`
    // is equivalent to the direct quotation `(f (id $x))`, so expanding
    // `wrap foo` must match the direct template applied to `wrap foo`.
    let mut computed = register_macro_rules_src(
        "macro_rules | `(wrap $x) => do let inner := `(id $x); return `(f $inner)",
    );
    let mut direct = register_macro_rules_src("macro_rules | `(wrap $x) => `(f (id $x))");

    let input = surface_to_syntax(&parse_expr("wrap foo").unwrap());
    let computed_out = computed
        .expand(input.clone())
        .expect("computed let/splice should expand");
    let direct_out = direct.expand(input).expect("direct template should expand");
    assert_eq!(
        computed_out.pretty(),
        direct_out.pretty(),
        "let-bound quotation must splice to match `(f (id $x))`"
    );
}

#[test]
fn test_macro_rules_computed_if_literal_selects_quotation_branch() {
    // SUPPORTED: a metaprogram-time `if <literal-bool>` selects a quotation
    // branch. With a literal `true` condition the THEN quotation is taken, so
    //   `(pick $x) => do if true then return `(a $x) else return `(b $x)`
    // expands `pick foo` to `(a foo)`.
    let mut computed = register_macro_rules_src(
        "macro_rules | `(pick $x) => do if true then return `(a $x) else return `(b $x)",
    );
    let input = surface_to_syntax(&parse_expr("pick foo").unwrap());
    let out = computed.expand(input).expect("computed if should expand");
    assert_eq!(out.kind(), Some(&SyntaxKind::app_kind()));
    assert_eq!(
        out.child(0).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("a"))
    );
    assert_eq!(
        out.child(1).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("foo"))
    );
}

#[test]
fn test_macro_rules_pure_template_still_works_unchanged() {
    // REGRESSION GUARD: a pure-template arm (no `do`-block) keeps the existing
    // fast path and is unaffected by the computed-body evaluator.
    let mut ctx = register_macro_rules_src("macro_rules | `(twice $x) => `($x + $x)");
    let expanded = ctx
        .expand(surface_to_syntax(&parse_expr("twice foo").unwrap()))
        .expect("pure template should expand");
    assert_eq!(expanded.kind(), Some(&SyntaxKind::app_kind()));
    let children = expanded.children();
    assert_eq!(children.len(), 3, "expected `(app HAdd.hAdd foo foo)`");
    assert_eq!(
        children[0].as_ident(),
        Some(&SurfaceName::generated_path("HAdd.hAdd"))
    );
    assert_eq!(
        children[1].as_ident(),
        Some(&SurfaceName::generated_path("foo"))
    );
    assert_eq!(
        children[2].as_ident(),
        Some(&SurfaceName::generated_path("foo"))
    );
}

#[test]
fn test_macro_rules_computed_unknown_antiquot_defers_honestly() {
    // HONEST DEFER: a `$name` that is neither a pattern variable nor a `let`
    // binding cannot be faithfully resolved, so registration DEFERS with a typed
    // error rather than fabricating an expansion.
    let decl =
        parse_decl("macro_rules | `(bad $x) => do return `(f $unbound)").expect("should parse");
    let SurfaceDecl::MacroRules { arms, .. } = decl else {
        panic!("expected macro_rules decl");
    };
    let mut ctx = MacroCtx::new();
    let result = ctx.register_macro_rules(None, &arms);
    assert!(
        matches!(
            result,
            Err(MacroRegistrationError::ComputedBodyUnsupported(_))
        ),
        "unknown `$name` in computed body must defer honestly, got {result:?}"
    );
}

#[test]
fn test_macro_rules_computed_monadic_bind_quotation_matches_direct_parse() {
    // SUPPORTED (new slice): a *monadic* bind `let inner <- `(id $x)` of a syntax
    // quotation. In `MacroM` a quotation has type `MacroM Syntax`, so binding its
    // result with `<-` yields the same `Syntax` the pure `let inner := `(id $x)`
    // form makes available. The arm
    //   `(wrap $x) => do let inner <- `(id $x); return `(f $inner)`
    // is therefore equivalent to the direct quotation `(f (id $x))`, and must
    // expand `wrap foo` byte-identically to the direct template applied to it —
    // and identically to the pure-`let` form of the same body.
    let mut computed = register_macro_rules_src(
        "macro_rules | `(wrap $x) => do let inner <- `(id $x); return `(f $inner)",
    );
    let mut direct = register_macro_rules_src("macro_rules | `(wrap $x) => `(f (id $x))");
    let mut pure_let = register_macro_rules_src(
        "macro_rules | `(wrap $x) => do let inner := `(id $x); return `(f $inner)",
    );

    let input = surface_to_syntax(&parse_expr("wrap foo").unwrap());
    let computed_out = computed
        .expand(input.clone())
        .expect("monadic-bind quotation should expand");
    let direct_out = direct
        .expand(input.clone())
        .expect("direct template should expand");
    let pure_let_out = pure_let.expand(input).expect("pure-let form should expand");
    assert_eq!(
        computed_out.pretty(),
        direct_out.pretty(),
        "monadic `let inner <- `(id $x)` must splice to match `(f (id $x))`"
    );
    assert_eq!(
        computed_out.pretty(),
        pure_let_out.pretty(),
        "monadic `<-` bind of a quotation must be byte-identical to the `:=` form"
    );
}

#[test]
fn test_macro_rules_computed_chained_monadic_binds_match_direct_parse() {
    // SUPPORTED (new slice): several monadic-bind quotation statements in sequence,
    // each referring to the previous binding. The arm
    //   `(seq $x) => do let a <- `(inner $x); let b <- `(mid $a); return `(outer $b)`
    // resolves `$a` to `(inner $x)` and `$b` to `(mid (inner $x))`, so it is
    // equivalent to the direct quotation `(outer (mid (inner $x)))`.
    let mut computed = register_macro_rules_src(
        "macro_rules | `(seq $x) => do let a <- `(inner $x); let b <- `(mid $a); return `(outer $b)",
    );
    let mut direct =
        register_macro_rules_src("macro_rules | `(seq $x) => `(outer (mid (inner $x)))");

    let input = surface_to_syntax(&parse_expr("seq foo").unwrap());
    let computed_out = computed
        .expand(input.clone())
        .expect("chained monadic binds should expand");
    let direct_out = direct.expand(input).expect("direct template should expand");
    assert_eq!(
        computed_out.pretty(),
        direct_out.pretty(),
        "chained `<-` quotation binds must match `(outer (mid (inner $x)))`"
    );
}

#[test]
fn test_macro_rules_computed_monadic_bind_nonquotation_action_defers_honestly() {
    // HONEST DEFER: a monadic bind whose action is a *real* `MacroM` action rather
    // than a syntax quotation (`let y <- expandFn foo`) is outside the faithfully-
    // evaluable subset — it needs the full `MacroM` monad. We must NOT fabricate a
    // value for `y`; registration DEFERS with a typed error. The parser rejects an
    // antiquotation argument outside a quotation, so the bind action is built as a
    // plain application AST directly.
    let pattern = SurfaceExpr::SyntaxQuote(Span::dummy(), "(bad $x)".to_string());
    let action = SurfaceExpr::App(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("expandFn"),
        )),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("foo"),
        ))],
    );
    let bind = DoElem::Bind(
        Span::dummy(),
        SurfaceBinder::new("y", None, SurfaceBinderInfo::Explicit),
        Box::new(action),
    );
    let ret = DoElem::Return(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            SurfaceName::generated_path("y"),
        )),
    );
    let expansion = SurfaceExpr::Do(Span::dummy(), vec![bind, ret]);
    let arm = MacroArm {
        span: Span::dummy(),
        pattern: Box::new(pattern),
        expansion: Box::new(expansion),
    };

    let mut ctx = MacroCtx::new();
    let result = ctx.register_macro_rules(None, std::slice::from_ref(&arm));
    assert!(
        matches!(
            result,
            Err(MacroRegistrationError::ComputedBodyUnsupported(_))
        ),
        "monadic bind of a non-quotation action must defer honestly, got {result:?}"
    );
}

// ---- throwError from a computed macro body (MacroM effect) ----------------

#[test]
fn test_macro_rules_computed_do_throw_error_surfaces_message() {
    // SUPPORTED (new slice): a computed `do`-body whose action is `throwError "msg"`
    // is a real `MacroM` effect — the macro FAILS to expand with the user's custom
    // message. Faithful to Lean: a real diagnostic, NOT a fabricated expansion.
    let decl = parse_decl(r#"macro_rules | `(boom $x) => do throwError "bad input""#)
        .expect("macro_rules with a throwError do-body should parse");
    let SurfaceDecl::MacroRules { arms, .. } = decl else {
        panic!("expected macro_rules decl");
    };
    let mut ctx = MacroCtx::new();
    match ctx.register_macro_rules(None, &arms) {
        Err(MacroRegistrationError::MacroThrowError(message)) => {
            assert_eq!(
                message, "bad input",
                "throwError must surface its literal message verbatim"
            );
        }
        other => panic!("expected a MacroThrowError carrying the message, got {other:?}"),
    }
}

#[test]
fn test_macro_rules_bare_throw_error_surfaces_message() {
    // SUPPORTED (new slice): a *bare* (non-`do`) `throwError "msg"` RHS is itself a
    // `MacroM` action that unconditionally raises the user's error. It must surface
    // the message rather than be mis-lowered as a `throwError`-named syntax template.
    let decl = parse_decl(r#"macro_rules | `(boom $x) => throwError "no good""#)
        .expect("macro_rules with a bare throwError RHS should parse");
    let SurfaceDecl::MacroRules { arms, .. } = decl else {
        panic!("expected macro_rules decl");
    };
    let mut ctx = MacroCtx::new();
    match ctx.register_macro_rules(None, &arms) {
        Err(MacroRegistrationError::MacroThrowError(message)) => {
            assert_eq!(message, "no good");
        }
        other => panic!("expected a MacroThrowError carrying the message, got {other:?}"),
    }
}

#[test]
fn test_macro_rules_computed_if_true_throw_error_branch_fires() {
    // SUPPORTED (new slice): a metaprogram-time `if <literal-true>` selects the THEN
    // branch; when that branch is `throwError "msg"`, the macro fails with that
    // message. The `else` quotation is NOT taken (the literal decides statically).
    let decl = parse_decl(
        r#"macro_rules | `(pick $x) => do if true then throwError "rejected" else return `(a $x)"#,
    )
    .expect("computed if with a throwError branch should parse");
    let SurfaceDecl::MacroRules { arms, .. } = decl else {
        panic!("expected macro_rules decl");
    };
    let mut ctx = MacroCtx::new();
    match ctx.register_macro_rules(None, &arms) {
        Err(MacroRegistrationError::MacroThrowError(message)) => {
            assert_eq!(message, "rejected");
        }
        other => panic!("expected the throwError branch to fire, got {other:?}"),
    }
}

#[test]
fn test_macro_rules_computed_if_false_skips_throw_error_branch() {
    // SUPPORTED (new slice): the dual of the above — a literal-`false` condition
    // takes the ELSE quotation, so the THEN `throwError` does NOT fire and the arm
    // registers and expands normally. Confirms throwError is genuinely conditional,
    // not unconditionally fired whenever it appears.
    let mut ctx = register_macro_rules_src(
        r#"macro_rules | `(pick $x) => do if false then throwError "rejected" else return `(a $x)"#,
    );
    let out = ctx
        .expand(surface_to_syntax(&parse_expr("pick foo").unwrap()))
        .expect("the else quotation branch should expand");
    assert_eq!(out.kind(), Some(&SyntaxKind::app_kind()));
    assert_eq!(
        out.child(0).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("a"))
    );
    assert_eq!(
        out.child(1).unwrap().as_ident(),
        Some(&SurfaceName::generated_path("foo"))
    );
}

#[test]
fn test_macro_rules_computed_throw_error_constant_interpolation_renders() {
    // SUPPORTED (new slice): a `throwError s!"…"` whose holes are all constant
    // (here a string literal) renders fully and fires, reusing the same B89
    // interpolation machinery as the metaprog tactic/term path.
    let decl = parse_decl(r#"macro_rules | `(boom $x) => do throwError s!"saw {"lit"} here""#);
    // Parser support for this exact interpolation-in-throwError shape is not the
    // point; if it parses, the rendered message must be the concatenated text.
    if let Ok(SurfaceDecl::MacroRules { arms, .. }) = decl {
        let mut ctx = MacroCtx::new();
        match ctx.register_macro_rules(None, &arms) {
            Err(MacroRegistrationError::MacroThrowError(message)) => {
                assert_eq!(message, "saw lit here");
            }
            // If the parser shapes it differently, a defer is also acceptable —
            // what is forbidden is a fabricated successful expansion.
            Err(_) => {}
            Ok(()) => panic!("a throwError body must never register as a plain template"),
        }
    }
}

#[test]
fn test_macro_rules_computed_throw_error_pattern_var_interpolation_defers() {
    // HONEST DEFER: `throwError s!"got {x}"` where `x` is a *pattern* variable — the
    // message text depends on the runtime-matched syntax, which is not available at
    // registration time. We must NOT fabricate the message (B72): defer honestly,
    // and NEVER silently drop the throwError into a successful expansion.
    let decl = parse_decl(r#"macro_rules | `(boom $x) => do throwError s!"got {x}""#);
    if let Ok(SurfaceDecl::MacroRules { arms, .. }) = decl {
        let mut ctx = MacroCtx::new();
        let result = ctx.register_macro_rules(None, &arms);
        assert!(
            matches!(
                result,
                Err(MacroRegistrationError::ComputedBodyUnsupported(_))
                    | Err(MacroRegistrationError::MacroThrowError(_))
            ),
            "a throwError whose message depends on matched syntax must defer or carry \
             a faithful message, never a fabricated expansion, got {result:?}"
        );
    }
}

// ===========================================================================
// `(cat| …)` quotation category heads (tactic-position macro routing)
// ===========================================================================

#[test]
fn test_quotation_category_recognizes_category_heads() {
    use super::registration::quotation_category;
    assert_eq!(quotation_category("(tactic| rfl)"), SyntaxKind::tactic());
    assert_eq!(
        quotation_category("(command| #check x)"),
        SyntaxKind::command()
    );
    assert_eq!(quotation_category("(conv| lhs)"), SyntaxKind::app("conv"));
    assert_eq!(quotation_category("(term| x + y)"), SyntaxKind::term());
}

#[test]
fn test_quotation_category_head_ignores_ordinary_parens() {
    use super::registration::{quotation_category, quotation_category_head};
    // `|`/`||` inside ordinary parenthesized terms must never be read as a
    // category head — that would silently re-categorize a term template.
    assert_eq!(quotation_category("(a || b)"), SyntaxKind::term());
    assert_eq!(quotation_category("(p | q)"), SyntaxKind::term());
    assert!(quotation_category_head("($x + $x)").is_none());
    // The legacy delimiter forms keep their meaning.
    assert_eq!(quotation_category("[intro h]"), SyntaxKind::tactic());
    assert_eq!(quotation_category("{ #eval x }"), SyntaxKind::command());
}

#[test]
fn test_surface_quote_tactic_head_lowers_body_with_tactic_category() {
    use super::registration::surface_expr_to_syntax_quote;
    let expr = SurfaceExpr::SyntaxQuote(Span::dummy(), "(tactic| exact hP)".to_string());
    let quote = surface_expr_to_syntax_quote(&expr).expect("tactic-headed quotation should lower");
    assert_eq!(quote.category, SyntaxKind::tactic());
    // The body is the parsed application `exact hP`, not a raw/truncated token.
    assert_eq!(quote.syntax.kind(), Some(&SyntaxKind::app_kind()));
}

#[test]
fn test_surface_quote_tactic_head_unparseable_body_errors_loudly() {
    use super::registration::surface_expr_to_syntax_quote;
    // An explicitly tactic-categorized quotation whose body the quotation
    // grammar cannot parse must be a LOUD registration error, never a silent
    // fall-back to a term template that could never fire.
    let expr = SurfaceExpr::SyntaxQuote(Span::dummy(), "(tactic| =>)".to_string());
    let result = surface_expr_to_syntax_quote(&expr);
    assert!(
        matches!(result, Err(MacroRegistrationError::QuotationParse(_))),
        "unparseable `(tactic| …)` body must error loudly, got {result:?}"
    );
}

/// A structure-instance pattern must survive the surface → syntax → surface
/// round trip intact.
///
/// A form the macro pass cannot reproduce comes back as a bare identifier named
/// after its node kind — that is how `open X in e` became the identifier
/// `openIn` (closed class 42) — so this is pinned rather than assumed.
#[test]
fn test_roundtrip_pattern_struct_instance_with_ellipsis() {
    let pattern = SurfacePattern::StructInst {
        fields: vec![(
            SurfaceName::generated_path("a"),
            SurfacePattern::Var(SurfaceName::generated_path("x")),
        )],
        ellipsis: true,
        ty: None,
    };
    let syntax = surface_pattern_to_syntax(&pattern);
    let recovered = syntax_to_pattern(&syntax).expect("struct-instance pattern round-trips");
    match recovered {
        SurfacePattern::StructInst {
            fields,
            ellipsis,
            ty,
        } => {
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0.name(), SurfaceName::generated_path("a").name());
            assert!(ellipsis, "the `..` flag must survive the round trip");
            assert!(ty.is_none());
        }
        other => panic!("expected StructInst pattern, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_pattern_struct_instance_without_ellipsis() {
    let pattern = SurfacePattern::StructInst {
        fields: vec![(SurfaceName::generated_path("a"), SurfacePattern::Wildcard)],
        ellipsis: false,
        ty: None,
    };
    let syntax = surface_pattern_to_syntax(&pattern);
    let recovered = syntax_to_pattern(&syntax).expect("struct-instance pattern round-trips");
    match recovered {
        SurfacePattern::StructInst {
            fields, ellipsis, ..
        } => {
            assert_eq!(fields.len(), 1);
            assert!(
                !ellipsis,
                "a literal with no `..` must not gain one in the round trip"
            );
        }
        other => panic!("expected StructInst pattern, got {other:?}"),
    }
}

#[test]
fn term_have_origin_and_typed_binder_survive_actual_macro_roundtrip() {
    let source = parse_expr("have «n.x» : Nat := 7; «n.x»").expect("typed have parses");
    let Some(SurfaceExpr::Have(_, binder, value, body)) =
        syntax_to_surface(&surface_to_syntax(&source))
    else {
        panic!("actual macro transport erased term-have origin");
    };
    assert_eq!(binder.info, SurfaceBinderInfo::Explicit);
    assert!(binder.ty.is_some());
    assert!(matches!(*value, SurfaceExpr::Lit(_, SurfaceLit::Nat(7))));
    let SurfaceExpr::Ident(_, name) = *body else {
        panic!("have body reference must survive");
    };
    assert!(binder.name.same_syntax(&name));
    assert!(binder
        .name
        .same_syntax(&SurfaceName::component("n.x", true)));
}

#[test]
fn do_have_origin_and_typed_binder_survive_actual_macro_roundtrip() {
    let source = parse_expr("do have n : Nat := 7; return n").expect("typed do-have parses");
    let Some(SurfaceExpr::Do(_, elems)) = syntax_to_surface(&surface_to_syntax(&source)) else {
        panic!("actual macro transport erased do");
    };
    let DoElem::Have(_, binder, value) = &elems[0] else {
        panic!("actual macro transport erased do-have origin");
    };
    assert_eq!(elems.len(), 2);
    assert_eq!(binder.info, SurfaceBinderInfo::Explicit);
    assert!(binder.ty.is_some());
    assert!(matches!(
        value.as_ref(),
        SurfaceExpr::Lit(_, SurfaceLit::Nat(7))
    ));
    assert!(matches!(&elems[1], DoElem::Return(_, _)));
}
