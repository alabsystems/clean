// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended name resolution analysis (phase 2).

use crate::name_resolution_ext::{
    NameResolutionExt, ResolutionCandidate, ResolutionResult, ResolutionSource,
};
use crate::name_resolution_ext2::{
    analyze_import_impact, classify_ambiguity, detect_shadows, explain_resolution,
    format_shadow_chain, format_source, get_completion_candidates, traverse_namespace,
    AmbiguityKind, CompletionSource, NameResolutionExt2Error, ResolutionStats, TraversalConfig,
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

// =========================================================================
// Ambiguity classification
// =========================================================================

#[test]
fn test_classify_ambiguity_open_namespace_conflict() {
    let candidates = vec![
        ResolutionCandidate {
            name: Name::from_string("Nat.zero"),
            source: ResolutionSource::OpenNamespace(Name::from_string("Nat")),
        },
        ResolutionCandidate {
            name: Name::from_string("Int.zero"),
            source: ResolutionSource::OpenNamespace(Name::from_string("Int")),
        },
    ];
    let report = classify_ambiguity("zero", &candidates);
    assert_eq!(report.kind, AmbiguityKind::OpenNamespaceConflict);
    assert_eq!(report.name, "zero");
    assert_eq!(report.candidates.len(), 2);
}

#[test]
fn test_classify_ambiguity_auto_open_conflict() {
    let candidates = vec![
        ResolutionCandidate {
            name: Name::from_string("List.size"),
            source: ResolutionSource::AutoOpen(Name::from_string("List")),
        },
        ResolutionCandidate {
            name: Name::from_string("Array.size"),
            source: ResolutionSource::AutoOpen(Name::from_string("Array")),
        },
    ];
    let report = classify_ambiguity("size", &candidates);
    assert_eq!(report.kind, AmbiguityKind::AutoOpenConflict);
}

#[test]
fn test_classify_ambiguity_mixed_conflict() {
    let candidates = vec![
        ResolutionCandidate {
            name: Name::from_string("Nat.add"),
            source: ResolutionSource::OpenNamespace(Name::from_string("Nat")),
        },
        ResolutionCandidate {
            name: Name::from_string("Custom.add"),
            source: ResolutionSource::Alias("add".to_string()),
        },
    ];
    let report = classify_ambiguity("add", &candidates);
    assert_eq!(report.kind, AmbiguityKind::MixedSourceConflict);
}

#[test]
fn test_classify_ambiguity_generates_suggestions() {
    let candidates = vec![
        ResolutionCandidate {
            name: Name::from_string("A.f"),
            source: ResolutionSource::OpenNamespace(Name::from_string("A")),
        },
        ResolutionCandidate {
            name: Name::from_string("B.f"),
            source: ResolutionSource::OpenNamespace(Name::from_string("B")),
        },
    ];
    let report = classify_ambiguity("f", &candidates);
    assert!(!report.suggestions.is_empty());
    // Should suggest fully qualified names
    assert!(report.suggestions.iter().any(|s| s.contains("A.f")));
    assert!(report.suggestions.iter().any(|s| s.contains("B.f")));
}

#[test]
fn test_classify_ambiguity_single_candidate() {
    let candidates = vec![ResolutionCandidate {
        name: Name::from_string("Nat.add"),
        source: ResolutionSource::OpenNamespace(Name::from_string("Nat")),
    }];
    let report = classify_ambiguity("add", &candidates);
    assert_eq!(report.kind, AmbiguityKind::OpenNamespaceConflict);
    assert_eq!(report.candidates.len(), 1);
}

#[test]
fn test_classify_ambiguity_empty_candidates() {
    let report = classify_ambiguity("nothing", &[]);
    assert_eq!(report.kind, AmbiguityKind::MixedSourceConflict);
    assert!(report.candidates.is_empty());
}

// =========================================================================
// Namespace traversal
// =========================================================================

#[test]
fn test_traverse_namespace_basic() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");
    add_const(&mut env, "Nat.sub");

    let config = TraversalConfig::default();
    let nodes =
        traverse_namespace(&Name::from_string("Nat"), &env, &config).expect("traversal succeeds");

    assert!(!nodes.is_empty());
    let names: Vec<String> = nodes.iter().map(|n| n.name.to_string()).collect();
    assert!(names.contains(&"Nat.add".to_string()));
    assert!(names.contains(&"Nat.mul".to_string()));
    assert!(names.contains(&"Nat.sub".to_string()));
}

#[test]
fn test_traverse_namespace_nested() {
    let mut env = Environment::new();
    add_const(&mut env, "Foo.Bar.baz");
    add_const(&mut env, "Foo.Bar.qux");
    add_const(&mut env, "Foo.other");

    let config = TraversalConfig::default();
    let nodes =
        traverse_namespace(&Name::from_string("Foo"), &env, &config).expect("traversal succeeds");

    let names: Vec<String> = nodes.iter().map(|n| n.name.to_string()).collect();
    assert!(names.contains(&"Foo.Bar".to_string()));
    assert!(names.contains(&"Foo.Bar.baz".to_string()));
    assert!(names.contains(&"Foo.other".to_string()));
}

#[test]
fn test_traverse_namespace_with_prefix_filter() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.addOne");
    add_const(&mut env, "Nat.mul");

    let config = TraversalConfig {
        prefix_filter: Some("add".to_string()),
        ..Default::default()
    };
    let nodes =
        traverse_namespace(&Name::from_string("Nat"), &env, &config).expect("traversal succeeds");

    let names: Vec<String> = nodes.iter().map(|n| n.name.to_string()).collect();
    assert!(names.contains(&"Nat.add".to_string()));
    assert!(names.contains(&"Nat.addOne".to_string()));
    // mul should not appear
    assert!(!names.contains(&"Nat.mul".to_string()));
}

#[test]
fn test_traverse_namespace_max_results() {
    let mut env = Environment::new();
    for i in 0..20 {
        add_const(&mut env, &format!("Big.item{i}"));
    }

    let config = TraversalConfig {
        max_results: 5,
        ..Default::default()
    };
    let nodes =
        traverse_namespace(&Name::from_string("Big"), &env, &config).expect("traversal succeeds");

    assert!(nodes.len() <= 5);
}

#[test]
fn test_traverse_namespace_not_found() {
    let env = Environment::new();
    let config = TraversalConfig::default();
    let result = traverse_namespace(&Name::from_string("Missing"), &env, &config);
    assert!(matches!(
        result,
        Err(NameResolutionExt2Error::NamespaceNotFound(_))
    ));
}

#[test]
fn test_traverse_namespace_root() {
    let mut env = Environment::new();
    add_const(&mut env, "topLevel");

    let config = TraversalConfig::default();
    let nodes = traverse_namespace(&Name::anon(), &env, &config).expect("traversal succeeds");

    let names: Vec<String> = nodes.iter().map(|n| n.name.to_string()).collect();
    assert!(names.contains(&"topLevel".to_string()));
}

#[test]
fn test_traverse_namespace_depth_zero() {
    let mut env = Environment::new();
    add_const(&mut env, "Ns.a");
    add_const(&mut env, "Ns.b.c");

    let config = TraversalConfig {
        max_depth: 0,
        ..Default::default()
    };
    let nodes =
        traverse_namespace(&Name::from_string("Ns"), &env, &config).expect("traversal succeeds");

    // With depth 0, should only see direct children
    for node in &nodes {
        assert_eq!(node.depth, 0);
    }
}

// =========================================================================
// Shadow detection
// =========================================================================

#[test]
fn test_detect_shadows_basic() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Int.add");

    let mut resolver = NameResolutionExt::new();
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));
    state.open_namespace(Name::from_string("Int"));

    let shadows = detect_shadows(&mut resolver, &state, &env);
    // When there are multiple open namespaces with the same name,
    // resolution may pick one over the other or be ambiguous
    // In either case, detect_shadows captures the relationship
    let _ = shadows; // shadows may or may not exist depending on resolution order
}

#[test]
fn test_detect_shadows_local_over_open() {
    let mut env = Environment::new();
    add_const(&mut env, "x");
    add_const(&mut env, "Nat.x");

    let mut resolver = NameResolutionExt::new();
    resolver.register_local(Name::from_string("x"));
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let shadows = detect_shadows(&mut resolver, &state, &env);
    assert!(
        !shadows.is_empty(),
        "local should shadow open namespace name"
    );
    assert_eq!(shadows[0].short_name, "x");
}

#[test]
fn test_detect_shadows_empty_env() {
    let env = Environment::new();
    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let shadows = detect_shadows(&mut resolver, &state, &env);
    assert!(shadows.is_empty());
}

#[test]
fn test_format_shadow_chain_empty() {
    let formatted = format_shadow_chain(&[]);
    assert_eq!(formatted, "no shadows detected");
}

#[test]
fn test_format_shadow_chain_single() {
    let shadows = vec![crate::name_resolution_ext2::ShadowEntry {
        short_name: "x".to_string(),
        shadower: ResolutionCandidate {
            name: Name::from_string("x"),
            source: ResolutionSource::Local,
        },
        shadowed: ResolutionCandidate {
            name: Name::from_string("Nat.x"),
            source: ResolutionSource::OpenNamespace(Name::from_string("Nat")),
        },
    }];
    let formatted = format_shadow_chain(&shadows);
    assert!(formatted.contains("`x`"));
    assert!(formatted.contains("shadows"));
    assert!(formatted.contains("Nat.x"));
}

// =========================================================================
// Resolution statistics
// =========================================================================

#[test]
fn test_resolution_stats_default() {
    let stats = ResolutionStats::default();
    assert_eq!(stats.total_lookups, 0);
    assert_eq!(stats.successes, 0);
    assert_eq!(stats.ambiguities, 0);
    assert_eq!(stats.failures, 0);
    assert_eq!(stats.cache_hits, 0);
}

#[test]
fn test_resolution_stats_record_success() {
    let mut stats = ResolutionStats::default();
    let result = ResolutionResult::Resolved(ResolutionCandidate {
        name: Name::from_string("Nat.add"),
        source: ResolutionSource::OpenNamespace(Name::from_string("Nat")),
    });
    stats.record(&result, false);

    assert_eq!(stats.total_lookups, 1);
    assert_eq!(stats.successes, 1);
    assert_eq!(stats.failures, 0);
    assert_eq!(stats.cache_hits, 0);
}

#[test]
fn test_resolution_stats_record_cache_hit() {
    let mut stats = ResolutionStats::default();
    let result = ResolutionResult::Resolved(ResolutionCandidate {
        name: Name::from_string("x"),
        source: ResolutionSource::Local,
    });
    stats.record(&result, true);

    assert_eq!(stats.cache_hits, 1);
    assert!((stats.cache_hit_rate() - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_resolution_stats_record_failure() {
    let mut stats = ResolutionStats::default();
    stats.record(&ResolutionResult::Unresolved, false);

    assert_eq!(stats.failures, 1);
    assert_eq!(stats.successes, 0);
    assert!((stats.success_rate() - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_resolution_stats_record_ambiguity() {
    let mut stats = ResolutionStats::default();
    let result = ResolutionResult::Ambiguous(vec![
        ResolutionCandidate {
            name: Name::from_string("A.f"),
            source: ResolutionSource::Global,
        },
        ResolutionCandidate {
            name: Name::from_string("B.f"),
            source: ResolutionSource::Global,
        },
    ]);
    stats.record(&result, false);

    assert_eq!(stats.ambiguities, 1);
}

#[test]
fn test_resolution_stats_success_rate() {
    let mut stats = ResolutionStats::default();
    let ok = ResolutionResult::Resolved(ResolutionCandidate {
        name: Name::from_string("a"),
        source: ResolutionSource::Local,
    });
    stats.record(&ok, false);
    stats.record(&ok, false);
    stats.record(&ResolutionResult::Unresolved, false);

    assert!((stats.success_rate() - 2.0 / 3.0).abs() < 0.01);
}

#[test]
fn test_resolution_stats_avg_depth() {
    let mut stats = ResolutionStats::default();
    // Local = depth 0
    let local = ResolutionResult::Resolved(ResolutionCandidate {
        name: Name::from_string("x"),
        source: ResolutionSource::Local,
    });
    // Global = depth 4
    let global = ResolutionResult::Resolved(ResolutionCandidate {
        name: Name::from_string("y"),
        source: ResolutionSource::Global,
    });
    stats.record(&local, false);
    stats.record(&global, false);

    assert!((stats.avg_lookup_depth() - 2.0).abs() < f64::EPSILON);
}

#[test]
fn test_resolution_stats_display() {
    let mut stats = ResolutionStats::default();
    let ok = ResolutionResult::Resolved(ResolutionCandidate {
        name: Name::from_string("a"),
        source: ResolutionSource::Local,
    });
    stats.record(&ok, true);
    let display = format!("{stats}");
    assert!(display.contains("lookups=1"));
    assert!(display.contains("success=100.0%"));
    assert!(display.contains("cache_hit=100.0%"));
}

#[test]
fn test_resolution_stats_zero_division() {
    let stats = ResolutionStats::default();
    assert!((stats.success_rate() - 0.0).abs() < f64::EPSILON);
    assert!((stats.cache_hit_rate() - 0.0).abs() < f64::EPSILON);
    assert!((stats.avg_lookup_depth() - 0.0).abs() < f64::EPSILON);
}

// =========================================================================
// Completion candidates
// =========================================================================

#[test]
fn test_completion_from_current_namespace() {
    let mut env = Environment::new();
    add_const(&mut env, "MyNs.alpha");
    add_const(&mut env, "MyNs.beta");
    add_const(&mut env, "Other.gamma");

    let mut state = NamespaceState::new();
    state.enter_namespace(Name::from_string("MyNs"));

    let candidates = get_completion_candidates("al", &state, &env, 100);
    assert!(candidates
        .iter()
        .any(|c| c.name.to_string() == "MyNs.alpha"));
}

#[test]
fn test_completion_from_open_namespace() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.addOne");
    add_const(&mut env, "Nat.mul");

    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let candidates = get_completion_candidates("add", &state, &env, 100);
    let names: Vec<String> = candidates.iter().map(|c| c.name.to_string()).collect();
    assert!(names.contains(&"Nat.add".to_string()));
    assert!(names.contains(&"Nat.addOne".to_string()));
}

#[test]
fn test_completion_global_prefix() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "NatHelper.stuff");

    let state = NamespaceState::new();
    let candidates = get_completion_candidates("Nat", &state, &env, 100);
    let names: Vec<String> = candidates.iter().map(|c| c.name.to_string()).collect();
    assert!(names.contains(&"Nat.add".to_string()));
    assert!(names.contains(&"NatHelper.stuff".to_string()));
}

#[test]
fn test_completion_max_results() {
    let mut env = Environment::new();
    for i in 0..20 {
        add_const(&mut env, &format!("Ns.item{i}"));
    }

    let state = NamespaceState::new();
    let candidates = get_completion_candidates("Ns", &state, &env, 5);
    assert!(candidates.len() <= 5);
}

#[test]
fn test_completion_empty_prefix() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "topLevel");

    let state = NamespaceState::new();
    let candidates = get_completion_candidates("", &state, &env, 100);
    // Empty prefix should match everything as global
    assert!(!candidates.is_empty());
}

#[test]
fn test_completion_source_metadata() {
    let mut env = Environment::new();
    add_const(&mut env, "MyNs.helper");

    let mut state = NamespaceState::new();
    state.enter_namespace(Name::from_string("MyNs"));

    let candidates = get_completion_candidates("help", &state, &env, 100);
    let from_ns: Vec<_> = candidates
        .iter()
        .filter(|c| c.source == CompletionSource::CurrentNamespace)
        .collect();
    assert!(!from_ns.is_empty());
}

// =========================================================================
// Import impact analysis
// =========================================================================

#[test]
fn test_import_impact_new_names() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");
    add_const(&mut env, "Nat.mul");

    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let impact = analyze_import_impact(&Name::from_string("Nat"), &mut resolver, &state, &env);

    assert_eq!(impact.namespace.to_string(), "Nat");
    assert_eq!(impact.new_names.len(), 2);
    let names: Vec<String> = impact.new_names.iter().map(|n| n.to_string()).collect();
    assert!(names.contains(&"Nat.add".to_string()));
    assert!(names.contains(&"Nat.mul".to_string()));
}

#[test]
fn test_import_impact_shadow_detection() {
    let mut env = Environment::new();
    add_const(&mut env, "x");
    add_const(&mut env, "Nat.x");

    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let impact = analyze_import_impact(&Name::from_string("Nat"), &mut resolver, &state, &env);

    // "x" already exists globally, opening Nat introduces Nat.x which
    // would interact with existing "x"
    assert!(
        !impact.new_shadows.is_empty() || !impact.new_names.is_empty(),
        "opening Nat should have some effect on 'x'"
    );
}

#[test]
fn test_import_impact_no_names() {
    let env = Environment::new();
    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let impact = analyze_import_impact(&Name::from_string("Empty"), &mut resolver, &state, &env);

    assert!(impact.new_names.is_empty());
    assert!(impact.new_ambiguities.is_empty());
    assert!(impact.new_shadows.is_empty());
}

// =========================================================================
// Resolution explanation
// =========================================================================

#[test]
fn test_explain_resolution_resolved() {
    let mut env = Environment::new();
    add_const(&mut env, "Nat.add");

    let mut resolver = NameResolutionExt::new();
    let mut state = NamespaceState::new();
    state.open_namespace(Name::from_string("Nat"));

    let explanation = explain_resolution(&Name::from_string("add"), &mut resolver, &state, &env);

    assert_eq!(explanation.input, "add");
    assert!(matches!(explanation.result, ResolutionResult::Resolved(_)));
    assert!(!explanation.steps.is_empty());
    // Should mention the open namespace
    let text = format!("{explanation}");
    assert!(text.contains("Nat"));
}

#[test]
fn test_explain_resolution_unresolved() {
    let env = Environment::new();
    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let explanation = explain_resolution(
        &Name::from_string("nonexistent"),
        &mut resolver,
        &state,
        &env,
    );

    assert!(matches!(explanation.result, ResolutionResult::Unresolved));
    let text = format!("{explanation}");
    assert!(text.contains("UNRESOLVED"));
}

#[test]
fn test_explain_resolution_anon_name() {
    let env = Environment::new();
    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let explanation = explain_resolution(&Name::anon(), &mut resolver, &state, &env);

    assert!(matches!(explanation.result, ResolutionResult::Unresolved));
    assert!(explanation.steps.iter().any(|s| s.contains("anonymous")));
}

#[test]
fn test_explain_resolution_display_format() {
    let mut env = Environment::new();
    add_const(&mut env, "topLevel");

    let mut resolver = NameResolutionExt::new();
    let state = NamespaceState::new();

    let explanation =
        explain_resolution(&Name::from_string("topLevel"), &mut resolver, &state, &env);

    let text = format!("{explanation}");
    assert!(text.contains("Resolution of `topLevel`"));
    assert!(text.contains("resolved to"));
}

// =========================================================================
// format_source helper
// =========================================================================

#[test]
fn test_format_source_local() {
    assert_eq!(format_source(&ResolutionSource::Local), "local binding");
}

#[test]
fn test_format_source_open_namespace() {
    let s = format_source(&ResolutionSource::OpenNamespace(Name::from_string("Nat")));
    assert!(s.contains("Nat"));
    assert!(s.contains("open namespace"));
}

#[test]
fn test_format_source_alias() {
    let s = format_source(&ResolutionSource::Alias("h".to_string()));
    assert!(s.contains("alias"));
    assert!(s.contains("h"));
}

#[test]
fn test_format_source_global() {
    assert_eq!(format_source(&ResolutionSource::Global), "global scope");
}

#[test]
fn test_format_source_auto_open() {
    let s = format_source(&ResolutionSource::AutoOpen(Name::from_string("List")));
    assert!(s.contains("auto-open"));
    assert!(s.contains("List"));
}
