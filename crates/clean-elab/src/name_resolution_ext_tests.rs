// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended name resolution.

use crate::name_resolution_ext::{
    NameResolutionExt, NameResolutionExtConfig, ResolutionCandidate, ResolutionResult,
    ResolutionSource,
};
use crate::namespace::NamespaceState;
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};

/// Helper: add an axiom constant with `Type` as its type.
fn add_const(env: &mut Environment, name: &str) {
    let n = Name::from_string(name);
    let decl = Declaration::Axiom {
        name: n,
        level_params: vec![],
        type_: Expr::type_(),
    };
    env.add_decl_structural(decl)
        .expect("add_const should succeed");
}

/// Helper: add an axiom constant with a specific type expression.
fn add_const_typed(env: &mut Environment, name: &str, type_: Expr) {
    let n = Name::from_string(name);
    let decl = Declaration::Axiom {
        name: n,
        level_params: vec![],
        type_,
    };
    env.add_decl_structural(decl)
        .expect("add_const_typed should succeed");
}

/// Helper: assert that resolution yields a unique match with the given name.
fn assert_resolved(result: &ResolutionResult, expected_name: &str) {
    match result {
        ResolutionResult::Resolved(c) => {
            assert_eq!(c.name.to_string(), expected_name, "resolved name mismatch");
        }
        ResolutionResult::Ambiguous(cs) => {
            panic!(
                "expected resolved '{expected_name}', got ambiguous: {:?}",
                cs.iter().map(|c| c.name.to_string()).collect::<Vec<_>>()
            );
        }
        ResolutionResult::Unresolved => {
            panic!("expected resolved '{expected_name}', got unresolved");
        }
    }
}

// =========================================================================
// Qualified name resolution
// =========================================================================

#[test]
fn test_qualified_two_level() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let result = resolver.resolve(&Name::from_string("Nat.add"), &state, &env);
    assert_resolved(&result, "Nat.add");
}

#[test]
fn test_qualified_three_level() {
    let mut env = Environment::new();
    add_const(&mut env, "Foo.Bar.baz");

    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let result = resolver.resolve(&Name::from_string("Foo.Bar.baz"), &state, &env);
    assert_resolved(&result, "Foo.Bar.baz");
}

#[test]
fn test_qualified_nonexistent() {
    let env = Environment::new();
    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let result = resolver.resolve(&Name::from_string("Foo.nonexistent"), &state, &env);
    assert!(matches!(result, ResolutionResult::Unresolved));
}

// =========================================================================
// Open namespace resolution
// =========================================================================

#[test]
fn test_open_namespace_resolve_unqualified() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let mut resolver = NameResolutionExt::new();
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let result = resolver.resolve(&Name::from_string("add"), &state, &env);
    assert_resolved(&result, "Nat.add");
}

#[test]
fn test_open_namespace_does_not_resolve_nonexistent() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let mut resolver = NameResolutionExt::new();
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let result = resolver.resolve(&Name::from_string("nonexistent"), &state, &env);
    assert!(matches!(result, ResolutionResult::Unresolved));
}

#[test]
fn test_multiple_open_namespaces() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Int.neg");

    let mut resolver = NameResolutionExt::new();
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));
    state.open_namespace(Name::from_string("Int"));

    let result1 = resolver.resolve(&Name::from_string("add"), &state, &env);
    assert_resolved(&result1, "Nat.add");

    let result2 = resolver.resolve(&Name::from_string("neg"), &state, &env);
    assert_resolved(&result2, "Int.neg");
}

// =========================================================================
// Alias resolution
// =========================================================================

#[test]
fn test_alias_basic() {
    let mut env = Environment::new();
    add_const(&mut env, "MyModule.helper");

    let mut resolver = NameResolutionExt::new();
    resolver.register_alias("h", Name::from_string("MyModule.helper"));
    let state = NamespaceState::new();

    let result = resolver.resolve(&Name::from_string("h"), &state, &env);
    assert_resolved(&result, "MyModule.helper");
    if let ResolutionResult::Resolved(c) = &result {
        assert!(matches!(c.source, ResolutionSource::Alias(_)));
    }
}

#[test]
fn test_alias_overridden_by_open() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "OldModule.add");

    let mut resolver = NameResolutionExt::new();
    resolver.register_alias("add", Name::from_string("OldModule.add"));
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    // Open namespace has higher priority than alias
    let result = resolver.resolve(&Name::from_string("add"), &state, &env);
    assert_resolved(&result, "Nat.add");
}

#[test]
fn test_alias_to_nonexistent_constant() {
    let env = Environment::new();
    let mut resolver = NameResolutionExt::new();
    resolver.register_alias("missing", Name::from_string("Gone.missing"));
    let state = NamespaceState::new();

    // Alias target doesn't exist in env — should not resolve
    let result = resolver.resolve(&Name::from_string("missing"), &state, &env);
    assert!(matches!(result, ResolutionResult::Unresolved));
}

// =========================================================================
// Overload resolution (type-directed disambiguation)
// =========================================================================

#[test]
fn test_overload_disambiguate_by_type() {
    let mut env = Environment::new();
    // Two "add" functions with different types
    add_const_typed(&mut env, "Nat.add", Expr::type_());
    add_const_typed(&mut env, "Int.add", Expr::prop());

    let resolver = NameResolutionExt::new();
    let candidates = vec![
        ResolutionCandidate {
            name: Name::from_string("Nat.add"),
            source: ResolutionSource::OpenNamespace(Name::from_string("Nat")),
        },
        ResolutionCandidate {
            name: Name::from_string("Int.add"),
            source: ResolutionSource::OpenNamespace(Name::from_string("Int")),
        },
    ];

    // Wave 96 — Gap 14 CLOSED. `type_compatible` now refines the
    // `Sort` payload so `Prop` (Sort 0) and `Type` (Sort 1) are
    // distinct, pruning `Nat.add : Type` when the expected type is
    // `Prop`.
    let result = resolver.disambiguate_by_type(&candidates, &Expr::prop(), &env);
    match &result {
        ResolutionResult::Resolved(c) if c.name.to_string() == "Int.add" => {}
        _ => panic!("disambiguate_by_type must resolve to Int.add: {result:?}"),
    }
}

#[test]
fn test_overload_disambiguate_by_type_prunes_const_head_mismatch() {
    // Wave 96 — Gap 14 negative test. The refined `type_compatible`
    // also distinguishes constants by head name. Given two candidates
    // typed `Nat` and `Int` respectively and an expected type of
    // `Int`, the filter must drop the `Nat`-typed candidate and
    // resolve uniquely to the `Int`-typed one — proving the new path
    // is conservative (it doesn't accidentally accept the wrong head).
    let mut env = Environment::new();
    add_const_typed(
        &mut env,
        "Foo.zero",
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    add_const_typed(
        &mut env,
        "Bar.zero",
        Expr::const_(Name::from_string("Int"), vec![]),
    );

    let resolver = NameResolutionExt::new();
    let candidates = vec![
        ResolutionCandidate {
            name: Name::from_string("Foo.zero"),
            source: ResolutionSource::OpenNamespace(Name::from_string("Foo")),
        },
        ResolutionCandidate {
            name: Name::from_string("Bar.zero"),
            source: ResolutionSource::OpenNamespace(Name::from_string("Bar")),
        },
    ];

    let expected = Expr::const_(Name::from_string("Int"), vec![]);
    let result = resolver.disambiguate_by_type(&candidates, &expected, &env);
    match &result {
        ResolutionResult::Resolved(c) if c.name.to_string() == "Bar.zero" => {}
        _ => panic!("disambiguate_by_type must resolve uniquely to Bar.zero: {result:?}"),
    }

    // And vice-versa: expecting `Nat` resolves to `Foo.zero`.
    let expected_nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let result_nat = resolver.disambiguate_by_type(&candidates, &expected_nat, &env);
    match &result_nat {
        ResolutionResult::Resolved(c) if c.name.to_string() == "Foo.zero" => {}
        _ => panic!("disambiguate_by_type must resolve uniquely to Foo.zero: {result_nat:?}"),
    }
}

#[test]
fn test_overload_disambiguate_no_match() {
    let mut env = Environment::new();
    add_const_typed(&mut env, "Nat.add", Expr::type_());
    add_const_typed(&mut env, "Int.add", Expr::type_());

    let resolver = NameResolutionExt::new();
    let candidates = vec![
        ResolutionCandidate {
            name: Name::from_string("Nat.add"),
            source: ResolutionSource::Global,
        },
        ResolutionCandidate {
            name: Name::from_string("Int.add"),
            source: ResolutionSource::Global,
        },
    ];

    // Both match Prop — still ambiguous (since neither is Prop)
    let result = resolver.disambiguate_by_type(&candidates, &Expr::prop(), &env);
    // No candidates match Prop, so returns original ambiguous
    assert!(matches!(result, ResolutionResult::Ambiguous(_)));
}

#[test]
fn test_overload_disambiguate_both_match() {
    let mut env = Environment::new();
    add_const_typed(&mut env, "A.f", Expr::type_());
    add_const_typed(&mut env, "B.f", Expr::type_());

    let resolver = NameResolutionExt::new();
    let candidates = vec![
        ResolutionCandidate {
            name: Name::from_string("A.f"),
            source: ResolutionSource::Global,
        },
        ResolutionCandidate {
            name: Name::from_string("B.f"),
            source: ResolutionSource::Global,
        },
    ];

    // Both have Type — still ambiguous
    let result = resolver.disambiguate_by_type(&candidates, &Expr::type_(), &env);
    assert!(matches!(result, ResolutionResult::Ambiguous(_)));
}

// =========================================================================
// Protected name resolution
// =========================================================================

#[test]
fn test_protected_name_skipped_in_open() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.internal");
    add_const(&mut env, "Nat.add");

    let mut resolver = NameResolutionExt::new();
    resolver.mark_protected(Name::from_string("Nat.internal"));

    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    // Protected name should not resolve via open
    let result = resolver.resolve(&Name::from_string("internal"), &state, &env);
    assert!(matches!(result, ResolutionResult::Unresolved));

    // Non-protected name still works
    let result2 = resolver.resolve(&Name::from_string("add"), &state, &env);
    assert_resolved(&result2, "Nat.add");
}

#[test]
fn test_protected_name_accessible_qualified() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.internal");

    let mut resolver = NameResolutionExt::new();
    resolver.mark_protected(Name::from_string("Nat.internal"));
    let state = NamespaceState::new();

    // Fully qualified access still works
    let result = resolver.resolve(&Name::from_string("Nat.internal"), &state, &env);
    assert_resolved(&result, "Nat.internal");
}

#[test]
fn test_is_protected_query() {
    let mut resolver = NameResolutionExt::new();
    let name = Name::from_string("Foo.secret");
    assert!(!resolver.is_protected(&name));
    resolver.mark_protected(name.clone());
    assert!(resolver.is_protected(&name));
}

// =========================================================================
// Auto-open namespaces
// =========================================================================

#[test]
fn test_auto_open_resolves() {
    let mut env = Environment::new();
    add_const(&mut env, "List.map");
    add_const(&mut env, "List.filter");

    let mut resolver = NameResolutionExt::new();
    resolver.register_auto_open(Name::from_string("List"), Name::from_string("List"));

    let state = NamespaceState::new();
    let result = resolver.resolve(&Name::from_string("map"), &state, &env);
    assert_resolved(&result, "List.map");

    if let ResolutionResult::Resolved(c) = &result {
        assert!(matches!(c.source, ResolutionSource::AutoOpen(_)));
    }
}

#[test]
fn test_auto_open_lower_priority_than_open() {
    let mut env = Environment::new();
    add_const(&mut env, "List.map");
    add_const(&mut env, "Array.map");

    let mut resolver = NameResolutionExt::new();
    resolver.register_auto_open(Name::from_string("Array"), Name::from_string("Array"));

    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("List"));

    // Open namespace wins over auto-open
    let result = resolver.resolve(&Name::from_string("map"), &state, &env);
    assert_resolved(&result, "List.map");
}

#[test]
fn test_auto_open_disabled_by_config() {
    let mut env = Environment::new();
    add_const(&mut env, "List.map");

    let config = NameResolutionExtConfig {
        auto_open: false,
        ..Default::default()
    };
    let mut resolver = NameResolutionExt::with_config(config);
    resolver.register_auto_open(Name::from_string("List"), Name::from_string("List"));

    let state = NamespaceState::new();
    let result = resolver.resolve(&Name::from_string("map"), &state, &env);
    assert!(matches!(result, ResolutionResult::Unresolved));
}

// =========================================================================
// Priority ordering
// =========================================================================

#[test]
fn test_local_beats_open() {
    let mut env = Environment::new();
    add_const(&mut env, "x");
    add_const(&mut env, "Nat.x");

    let mut resolver = NameResolutionExt::new();
    resolver.register_local(Name::from_string("x"));

    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let result = resolver.resolve(&Name::from_string("x"), &state, &env);
    assert_resolved(&result, "x");
    if let ResolutionResult::Resolved(c) = &result {
        assert_eq!(c.source, ResolutionSource::Local);
    }
}

#[test]
fn test_local_beats_alias() {
    let mut env = Environment::new();
    add_const(&mut env, "myvar");
    add_const(&mut env, "Other.myvar");

    let mut resolver = NameResolutionExt::new();
    resolver.register_local(Name::from_string("myvar"));
    resolver.register_alias("myvar", Name::from_string("Other.myvar"));

    let state = NamespaceState::new();
    let result = resolver.resolve(&Name::from_string("myvar"), &state, &env);
    assert_resolved(&result, "myvar");
    if let ResolutionResult::Resolved(c) = &result {
        assert_eq!(c.source, ResolutionSource::Local);
    }
}

#[test]
fn test_open_beats_alias() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.f");
    add_const(&mut env, "Other.f");

    let mut resolver = NameResolutionExt::new();
    resolver.register_alias("f", Name::from_string("Other.f"));

    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let result = resolver.resolve(&Name::from_string("f"), &state, &env);
    assert_resolved(&result, "Nat.f");
}

#[test]
fn test_alias_beats_global() {
    let mut env = Environment::new();
    add_const(&mut env, "g");
    add_const(&mut env, "Better.g");

    let mut resolver = NameResolutionExt::new();
    resolver.register_alias("g", Name::from_string("Better.g"));

    let state = NamespaceState::new();
    let result = resolver.resolve(&Name::from_string("g"), &state, &env);
    assert_resolved(&result, "Better.g");
    if let ResolutionResult::Resolved(c) = &result {
        assert!(matches!(c.source, ResolutionSource::Alias(_)));
    }
}

#[test]
fn test_current_namespace_beats_open() {
    let mut env = Environment::new();
    add_const(&mut env, "MyNs.foo");
    add_const(&mut env, "Other.foo");

    let mut resolver = NameResolutionExt::new();
    let mut state = NamespaceState::new();
    state.enter_namespace(Name::from_string("MyNs"));
    state.open_namespace(Name::from_string("Other"));

    let result = resolver.resolve(&Name::from_string("foo"), &state, &env);
    assert_resolved(&result, "MyNs.foo");
}

// =========================================================================
// Ambiguity detection and reporting
// =========================================================================

#[test]
fn test_ambiguity_two_opens() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.zero");
    add_const(&mut env, "Int.zero");

    let mut resolver = NameResolutionExt::new();
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));
    state.open_namespace(Name::from_string("Int"));

    let result = resolver.resolve(&Name::from_string("zero"), &state, &env);
    match &result {
        ResolutionResult::Ambiguous(cs) => {
            assert!(cs.len() >= 2, "expected at least 2 candidates");
            let names: Vec<String> = cs.iter().map(|c| c.name.to_string()).collect();
            assert!(names.contains(&"Nat.zero".to_string()));
            assert!(names.contains(&"Int.zero".to_string()));
        }
        other => panic!("expected ambiguous, got {other:?}"),
    }
}

#[test]
fn test_format_ambiguity_message() {
    let candidates = vec![
        ResolutionCandidate {
            name: Name::from_string("A.f"),
            source: ResolutionSource::Global,
        },
        ResolutionCandidate {
            name: Name::from_string("B.f"),
            source: ResolutionSource::Global,
        },
    ];
    let msg = NameResolutionExt::format_ambiguity(&candidates);
    assert!(msg.contains("A.f"));
    assert!(msg.contains("B.f"));
    assert!(msg.contains("ambiguous"));
}

#[test]
fn test_format_ambiguity_empty() {
    let msg = NameResolutionExt::format_ambiguity(&[]);
    assert_eq!(msg, "no candidates");
}

#[test]
fn test_candidate_names_extraction() {
    let candidates = vec![
        ResolutionCandidate {
            name: Name::from_string("X.a"),
            source: ResolutionSource::Global,
        },
        ResolutionCandidate {
            name: Name::from_string("Y.b"),
            source: ResolutionSource::Global,
        },
    ];
    let names = NameResolutionExt::candidate_names(&candidates);
    assert_eq!(names.len(), 2);
    assert_eq!(names[0].to_string(), "X.a");
    assert_eq!(names[1].to_string(), "Y.b");
}

// =========================================================================
// Cache behavior
// =========================================================================

#[test]
fn test_cache_populates_on_resolve() {
    let mut env = Environment::new();
    add_const(&mut env, "Foo.bar");

    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    assert_eq!(resolver.cache_size(), 0);
    let _ = resolver.resolve(&Name::from_string("Foo.bar"), &state, &env);
    assert_eq!(resolver.cache_size(), 1);
}

#[test]
fn test_cache_returns_same_result() {
    let mut env = Environment::new();
    add_const(&mut env, "Foo.bar");

    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let r1 = resolver.resolve(&Name::from_string("Foo.bar"), &state, &env);
    let r2 = resolver.resolve(&Name::from_string("Foo.bar"), &state, &env);
    assert_eq!(r1, r2);
    // Still only one entry
    assert_eq!(resolver.cache_size(), 1);
}

#[test]
fn test_cache_invalidated_on_mutation() {
    let mut env = Environment::new();
    add_const(&mut env, "Foo.bar");

    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let _ = resolver.resolve(&Name::from_string("Foo.bar"), &state, &env);
    assert_eq!(resolver.cache_size(), 1);

    resolver.register_alias("x", Name::from_string("Foo.bar"));
    assert_eq!(
        resolver.cache_size(),
        0,
        "cache should be cleared on alias registration"
    );
}

#[test]
fn test_cache_invalidated_on_protected_mark() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let mut resolver = NameResolutionExt::new();
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let _ = resolver.resolve(&Name::from_string("add"), &state, &env);
    assert!(resolver.cache_size() > 0);

    resolver.mark_protected(Name::from_string("Nat.add"));
    assert_eq!(resolver.cache_size(), 0);
}

#[test]
fn test_cache_disabled_by_config() {
    let mut env = Environment::new();
    add_const(&mut env, "Foo.bar");

    let config = NameResolutionExtConfig {
        enable_cache: false,
        ..Default::default()
    };
    let mut resolver = NameResolutionExt::with_config(config);
    let state = NamespaceState::new();

    let _ = resolver.resolve(&Name::from_string("Foo.bar"), &state, &env);
    assert_eq!(
        resolver.cache_size(),
        0,
        "cache should stay empty when disabled"
    );
}

// =========================================================================
// Edge cases
// =========================================================================

#[test]
fn test_anon_name_resolves_to_unresolved() {
    let env = Environment::new();
    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let result = resolver.resolve(&Name::anon(), &state, &env);
    assert!(matches!(result, ResolutionResult::Unresolved));
}

#[test]
fn test_empty_namespace_no_panic() {
    let env = Environment::new();
    let mut resolver = NameResolutionExt::new();
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Empty"));

    let result = resolver.resolve(&Name::from_string("anything"), &state, &env);
    assert!(matches!(result, ResolutionResult::Unresolved));
}

#[test]
fn test_shadowing_local_over_global() {
    let mut env = Environment::new();
    add_const(&mut env, "shadow");

    let mut resolver = NameResolutionExt::new();
    resolver.register_local(Name::from_string("shadow"));
    let state = NamespaceState::new();

    let result = resolver.resolve(&Name::from_string("shadow"), &state, &env);
    assert_resolved(&result, "shadow");
    if let ResolutionResult::Resolved(c) = &result {
        assert_eq!(c.source, ResolutionSource::Local);
    }
}

#[test]
fn test_unregister_local_falls_through() {
    let mut env = Environment::new();
    add_const(&mut env, "x");

    let mut resolver = NameResolutionExt::new();
    resolver.register_local(Name::from_string("x"));
    let state = NamespaceState::new();

    let r1 = resolver.resolve(&Name::from_string("x"), &state, &env);
    if let ResolutionResult::Resolved(c) = &r1 {
        assert_eq!(c.source, ResolutionSource::Local);
    }

    resolver.unregister_local(&Name::from_string("x"));
    let r2 = resolver.resolve(&Name::from_string("x"), &state, &env);
    // Now falls through to global
    assert_resolved(&r2, "x");
    if let ResolutionResult::Resolved(c) = &r2 {
        assert_eq!(c.source, ResolutionSource::Global);
    }
}

#[test]
fn test_circular_alias_does_not_infinite_loop() {
    // Alias "a" -> "b" and "b" -> "a" — neither exists in env.
    // Should resolve to Unresolved without hanging.
    let env = Environment::new();
    let mut resolver = NameResolutionExt::new();
    resolver.register_alias("a", Name::from_string("b"));
    resolver.register_alias("b", Name::from_string("a"));
    let state = NamespaceState::new();

    let r1 = resolver.resolve(&Name::from_string("a"), &state, &env);
    assert!(matches!(r1, ResolutionResult::Unresolved));

    let r2 = resolver.resolve(&Name::from_string("b"), &state, &env);
    assert!(matches!(r2, ResolutionResult::Unresolved));
}

#[test]
fn test_default_config_values() {
    let config = NameResolutionExtConfig::default();
    assert!(config.enable_cache);
    assert!(config.auto_open);
    assert_eq!(config.max_ambiguity_candidates, 10);
}

#[test]
fn test_with_config_preserves_settings() {
    let config = NameResolutionExtConfig {
        enable_cache: false,
        auto_open: false,
        max_ambiguity_candidates: 3,
    };
    let resolver = NameResolutionExt::with_config(config);
    assert!(!resolver.config().enable_cache);
    assert!(!resolver.config().auto_open);
    assert_eq!(resolver.config().max_ambiguity_candidates, 3);
}

#[test]
fn test_resolve_uncached_bypasses_cache() {
    let mut env = Environment::new();
    add_const(&mut env, "Foo.bar");

    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let name = Name::from_string("Foo.bar");
    let result = resolver.resolve_uncached(&name, "Foo.bar", &state, &env);
    assert_resolved(&result, "Foo.bar");
    assert_eq!(
        resolver.cache_size(),
        0,
        "resolve_uncached should not populate cache"
    );

    // Now use resolve() to populate cache
    let _ = resolver.resolve(&name, &state, &env);
    assert_eq!(resolver.cache_size(), 1);
}

#[test]
fn test_multiple_auto_open_ambiguity() {
    let mut env = Environment::new();
    add_const(&mut env, "List.size");
    add_const(&mut env, "Array.size");

    let mut resolver = NameResolutionExt::new();
    resolver.register_auto_open(Name::from_string("List"), Name::from_string("List"));
    resolver.register_auto_open(Name::from_string("Array"), Name::from_string("Array"));

    let state = NamespaceState::new();
    let result = resolver.resolve(&Name::from_string("size"), &state, &env);
    assert!(
        matches!(result, ResolutionResult::Ambiguous(_)),
        "two auto-open namespaces with same name should be ambiguous"
    );
}
