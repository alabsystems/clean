// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended attribute macro analysis.

use std::time::Duration;

use clean_kernel::Name;
use clean_parser::Attribute;

use crate::attr_macro::{
    expand_attributes, AttrMacroRegistry, AttrMacroResult, ExpansionResult, InlineKind,
    ReducibilityLevel,
};
use crate::attr_macro_ext::*;

// ============================================================================
// Scope analysis
// ============================================================================

#[test]
fn test_classify_scope_builtin_is_global() {
    let registry = AttrMacroRegistry::with_builtins();
    assert_eq!(classify_scope("simp", &registry), MacroScope::Global);
    assert_eq!(classify_scope("inline", &registry), MacroScope::Global);
    assert_eq!(classify_scope("reducible", &registry), MacroScope::Global);
}

#[test]
fn test_classify_scope_unknown_is_module() {
    let registry = AttrMacroRegistry::with_builtins();
    assert_eq!(
        classify_scope("my_custom_attr", &registry),
        MacroScope::Module
    );
}

#[test]
fn test_classify_scope_empty_registry() {
    let registry = AttrMacroRegistry::new();
    assert_eq!(classify_scope("simp", &registry), MacroScope::Module);
}

// ============================================================================
// Dependency graph — construction
// ============================================================================

#[test]
fn test_dep_graph_new_empty() {
    let graph = MacroDependencyGraph::new();
    assert!(!graph.has_dependencies("anything"));
    assert!(graph.macros_with_dependencies().is_empty());
}

#[test]
fn test_dep_graph_default_empty() {
    let graph = MacroDependencyGraph::default();
    assert!(graph.macros_with_dependencies().is_empty());
}

#[test]
fn test_dep_graph_add_dependency() {
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("simp_ext", "simp");
    assert!(graph.has_dependencies("simp_ext"));
    assert!(!graph.has_dependencies("simp"));
    let deps = graph.dependencies_of("simp_ext");
    assert!(deps.contains("simp"));
    assert_eq!(deps.len(), 1);
}

#[test]
fn test_dep_graph_multiple_dependencies() {
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("combined", "simp");
    graph.add_dependency("combined", "ext");
    graph.add_dependency("combined", "inline");
    let deps = graph.dependencies_of("combined");
    assert_eq!(deps.len(), 3);
    assert!(deps.contains("simp"));
    assert!(deps.contains("ext"));
    assert!(deps.contains("inline"));
}

#[test]
fn test_dep_graph_dependencies_of_unknown() {
    let graph = MacroDependencyGraph::new();
    assert!(graph.dependencies_of("nonexistent").is_empty());
}

#[test]
fn test_dep_graph_macros_with_dependencies() {
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("a", "b");
    graph.add_dependency("c", "d");
    let mut macros = graph.macros_with_dependencies();
    macros.sort();
    assert_eq!(macros, vec!["a", "c"]);
}

// ============================================================================
// Dependency graph — topological ordering
// ============================================================================

#[test]
fn test_topological_order_no_deps() {
    let graph = MacroDependencyGraph::new();
    let order = graph.topological_order(&["a", "b", "c"]).unwrap();
    assert_eq!(order.len(), 3);
}

#[test]
fn test_topological_order_linear_chain() {
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("c", "b");
    graph.add_dependency("b", "a");
    let order = graph.topological_order(&["a", "b", "c"]).unwrap();
    // a must come before b, b before c
    let pos_a = order.iter().position(|x| x == "a").unwrap();
    let pos_b = order.iter().position(|x| x == "b").unwrap();
    let pos_c = order.iter().position(|x| x == "c").unwrap();
    assert!(pos_a < pos_b);
    assert!(pos_b < pos_c);
}

#[test]
fn test_topological_order_diamond() {
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("d", "b");
    graph.add_dependency("d", "c");
    graph.add_dependency("b", "a");
    graph.add_dependency("c", "a");
    let order = graph.topological_order(&["a", "b", "c", "d"]).unwrap();
    let pos_a = order.iter().position(|x| x == "a").unwrap();
    let pos_b = order.iter().position(|x| x == "b").unwrap();
    let pos_c = order.iter().position(|x| x == "c").unwrap();
    let pos_d = order.iter().position(|x| x == "d").unwrap();
    assert!(pos_a < pos_b);
    assert!(pos_a < pos_c);
    assert!(pos_b < pos_d);
    assert!(pos_c < pos_d);
}

#[test]
fn test_topological_order_cycle_detected() {
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("a", "b");
    graph.add_dependency("b", "a");
    let result = graph.topological_order(&["a", "b"]);
    assert!(result.is_err());
    let err = result.unwrap_err();
    match err {
        AttrMacroExtError::CircularDependency { cycle } => {
            assert!(!cycle.is_empty());
        }
        other => panic!("expected CircularDependency, got {other:?}"),
    }
}

#[test]
fn test_topological_order_three_node_cycle() {
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("a", "b");
    graph.add_dependency("b", "c");
    graph.add_dependency("c", "a");
    let result = graph.topological_order(&["a", "b", "c"]);
    assert!(result.is_err());
}

#[test]
fn test_topological_order_partial_subset() {
    // Only order a subset that doesn't include the dependency target
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("b", "a");
    // Only order ["b"] — "a" is outside the set, so b has no in-set deps
    let order = graph.topological_order(&["b"]).unwrap();
    assert_eq!(order, vec!["b"]);
}

#[test]
fn test_topological_order_empty() {
    let graph = MacroDependencyGraph::new();
    let order = graph.topological_order(&[]).unwrap();
    assert!(order.is_empty());
}

// ============================================================================
// Dependency graph — validation
// ============================================================================

#[test]
fn test_validate_dependencies_all_registered() {
    let registry = AttrMacroRegistry::with_builtins();
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("my_macro", "simp");
    graph.add_dependency("my_macro", "ext");
    let errors = graph.validate_dependencies(&registry);
    assert!(errors.is_empty());
}

#[test]
fn test_validate_dependencies_missing() {
    let registry = AttrMacroRegistry::new();
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("my_macro", "nonexistent");
    let errors = graph.validate_dependencies(&registry);
    assert_eq!(errors.len(), 1);
    match &errors[0] {
        AttrMacroExtError::MissingDependency {
            macro_name,
            dependency,
        } => {
            assert_eq!(macro_name, "my_macro");
            assert_eq!(dependency, "nonexistent");
        }
        other => panic!("expected MissingDependency, got {other:?}"),
    }
}

// ============================================================================
// Conflict detection
// ============================================================================

#[test]
fn test_conflict_registry_new_empty() {
    let reg = ConflictRegistry::new();
    assert!(reg.is_empty());
    assert_eq!(reg.len(), 0);
}

#[test]
fn test_conflict_registry_with_defaults() {
    let reg = ConflictRegistry::with_defaults();
    assert!(!reg.is_empty());
    // At least inline/noinline, specialize/nospecialize, reducible variants
    assert!(reg.len() >= 9);
}

#[test]
fn test_conflict_detection_no_conflict() {
    let reg = ConflictRegistry::with_defaults();
    let errors = reg.detect_conflicts("my_decl", &["simp", "ext"]);
    assert!(errors.is_empty());
}

#[test]
fn test_conflict_detection_inline_noinline() {
    let reg = ConflictRegistry::with_defaults();
    let errors = reg.detect_conflicts("my_fn", &["inline", "noinline"]);
    assert_eq!(errors.len(), 1);
    match &errors[0] {
        AttrMacroExtError::ConflictingAttributes { decl, a, b } => {
            assert_eq!(decl, "my_fn");
            assert_eq!(a, "inline");
            assert_eq!(b, "noinline");
        }
        other => panic!("expected ConflictingAttributes, got {other:?}"),
    }
}

#[test]
fn test_conflict_detection_reducible_irreducible() {
    let reg = ConflictRegistry::with_defaults();
    let errors = reg.detect_conflicts("my_def", &["reducible", "irreducible"]);
    assert_eq!(errors.len(), 1);
}

#[test]
fn test_conflict_detection_specialize_nospecialize() {
    let reg = ConflictRegistry::with_defaults();
    let errors = reg.detect_conflicts("my_fn", &["specialize", "nospecialize"]);
    assert_eq!(errors.len(), 1);
}

#[test]
fn test_conflict_detection_multiple_conflicts() {
    let reg = ConflictRegistry::with_defaults();
    let errors = reg.detect_conflicts("bad_decl", &["inline", "noinline", "always_inline"]);
    // inline-noinline, inline-always_inline, noinline-always_inline
    assert_eq!(errors.len(), 3);
}

#[test]
fn test_conflict_custom_rule() {
    let mut reg = ConflictRegistry::new();
    reg.add_conflict("foo", "bar");
    let errors = reg.detect_conflicts("test", &["foo", "bar"]);
    assert_eq!(errors.len(), 1);
}

#[test]
fn test_conflict_detection_empty_attrs() {
    let reg = ConflictRegistry::with_defaults();
    let errors = reg.detect_conflicts("my_decl", &[]);
    assert!(errors.is_empty());
}

#[test]
fn test_conflict_detection_single_attr() {
    let reg = ConflictRegistry::with_defaults();
    let errors = reg.detect_conflicts("my_decl", &["inline"]);
    assert!(errors.is_empty());
}

// ============================================================================
// Statistics collection
// ============================================================================

#[test]
fn test_stats_collector_new_empty() {
    let collector = StatsCollector::new();
    assert_eq!(collector.macro_count(), 0);
    assert_eq!(collector.total_successes(), 0);
    assert_eq!(collector.total_failures(), 0);
}

#[test]
fn test_stats_collector_record_success() {
    let mut collector = StatsCollector::new();
    collector.record_success("simp", Duration::from_micros(10));
    collector.record_success("simp", Duration::from_micros(20));
    let stats = collector.get("simp").unwrap();
    assert_eq!(stats.success_count, 2);
    assert_eq!(stats.failure_count, 0);
    assert_eq!(stats.total_duration, Duration::from_micros(30));
}

#[test]
fn test_stats_collector_record_failure() {
    let mut collector = StatsCollector::new();
    collector.record_failure("bad_macro");
    collector.record_failure("bad_macro");
    collector.record_failure("bad_macro");
    let stats = collector.get("bad_macro").unwrap();
    assert_eq!(stats.success_count, 0);
    assert_eq!(stats.failure_count, 3);
}

#[test]
fn test_stats_collector_mixed() {
    let mut collector = StatsCollector::new();
    collector.record_success("a", Duration::from_micros(5));
    collector.record_failure("a");
    collector.record_success("b", Duration::from_micros(10));
    assert_eq!(collector.macro_count(), 2);
    assert_eq!(collector.total_successes(), 2);
    assert_eq!(collector.total_failures(), 1);
}

#[test]
fn test_stats_collector_get_unknown() {
    let collector = StatsCollector::new();
    assert!(collector.get("nonexistent").is_none());
}

#[test]
fn test_stats_collector_iter() {
    let mut collector = StatsCollector::new();
    collector.record_success("a", Duration::from_micros(1));
    collector.record_success("b", Duration::from_micros(2));
    let entries: Vec<_> = collector.iter().collect();
    assert_eq!(entries.len(), 2);
}

// ============================================================================
// MacroStats
// ============================================================================

#[test]
fn test_macro_stats_default() {
    let stats = MacroStats::default();
    assert_eq!(stats.total_count(), 0);
    assert_eq!(stats.failure_rate(), 0.0);
    assert_eq!(stats.avg_duration(), Duration::ZERO);
}

#[test]
fn test_macro_stats_failure_rate() {
    let stats = MacroStats {
        success_count: 7,
        failure_count: 3,
        total_duration: Duration::ZERO,
    };
    assert_eq!(stats.total_count(), 10);
    let rate = stats.failure_rate();
    assert!((rate - 0.3).abs() < f64::EPSILON);
}

#[test]
fn test_macro_stats_avg_duration() {
    let stats = MacroStats {
        success_count: 4,
        failure_count: 0,
        total_duration: Duration::from_micros(100),
    };
    assert_eq!(stats.avg_duration(), Duration::from_micros(25));
}

#[test]
fn test_macro_stats_all_failures() {
    let stats = MacroStats {
        success_count: 0,
        failure_count: 5,
        total_duration: Duration::ZERO,
    };
    assert_eq!(stats.failure_rate(), 1.0);
    assert_eq!(stats.avg_duration(), Duration::ZERO);
}

// ============================================================================
// Effect classification
// ============================================================================

#[test]
fn test_classify_effect_lemma_registration() {
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterSimpLemma { priority: None }),
        EffectKind::LemmaRegistration
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterExtLemma),
        EffectKind::LemmaRegistration
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterCongrLemma),
        EffectKind::LemmaRegistration
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterReflLemma),
        EffectKind::LemmaRegistration
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterSymmLemma),
        EffectKind::LemmaRegistration
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterCsimpLemma),
        EffectKind::LemmaRegistration
    );
}

#[test]
fn test_classify_effect_compiler_hint() {
    assert_eq!(
        classify_effect(&AttrMacroResult::SetReducibility(
            ReducibilityLevel::Reducible
        )),
        EffectKind::CompilerHint
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::SetInline(InlineKind::Inline)),
        EffectKind::CompilerHint
    );
}

#[test]
fn test_classify_effect_ffi() {
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterExtern {
            extern_name: "foo".to_owned()
        }),
        EffectKind::FfiBinding
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterExport {
            export_name: "bar".to_owned()
        }),
        EffectKind::FfiBinding
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterImplementedBy {
            impl_name: "baz".to_owned()
        }),
        EffectKind::FfiBinding
    );
}

#[test]
fn test_classify_effect_metadata() {
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterDeprecated { message: None }),
        EffectKind::MetadataAnnotation
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterCoercion),
        EffectKind::MetadataAnnotation
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterClass),
        EffectKind::MetadataAnnotation
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterInstance { priority: 100 }),
        EffectKind::MetadataAnnotation
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterInit),
        EffectKind::MetadataAnnotation
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterDefaultInstance),
        EffectKind::MetadataAnnotation
    );
    assert_eq!(
        classify_effect(&AttrMacroResult::RegisterMatchPattern),
        EffectKind::MetadataAnnotation
    );
}

#[test]
fn test_classify_effect_custom() {
    assert_eq!(
        classify_effect(&AttrMacroResult::Custom("tag".to_owned())),
        EffectKind::Custom
    );
}

// ============================================================================
// Expansion analysis
// ============================================================================

#[test]
fn test_analyze_expansion_empty() {
    let result = ExpansionResult {
        effects: vec![],
        errors: vec![],
        unhandled: vec![],
    };
    let analysis = analyze_expansion(&result);
    assert_eq!(analysis.effect_count, 0);
    assert_eq!(analysis.error_count, 0);
    assert_eq!(analysis.unhandled_count, 0);
    assert!(analysis.effect_kinds.is_empty());
}

#[test]
fn test_analyze_expansion_mixed() {
    let result = ExpansionResult {
        effects: vec![
            AttrMacroResult::RegisterSimpLemma { priority: None },
            AttrMacroResult::SetInline(InlineKind::Inline),
        ],
        errors: vec![("bad".to_owned(), crate::ElabError::CannotInfer)],
        unhandled: vec!["custom1".to_owned(), "custom2".to_owned()],
    };
    let analysis = analyze_expansion(&result);
    assert_eq!(analysis.effect_count, 2);
    assert_eq!(analysis.error_count, 1);
    assert_eq!(analysis.unhandled_count, 2);
    assert_eq!(analysis.effect_kinds.len(), 2);
    assert_eq!(analysis.effect_kinds[0], EffectKind::LemmaRegistration);
    assert_eq!(analysis.effect_kinds[1], EffectKind::CompilerHint);
}

#[test]
fn test_analyze_expansion_from_registry() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_lemma");
    let attrs = vec![
        Attribute::Simp { priority: None },
        Attribute::Ext,
        Attribute::Inline,
    ];
    let result = expand_attributes(&name, &attrs, &registry);
    let analysis = analyze_expansion(&result);
    assert_eq!(analysis.effect_count, 3);
    assert_eq!(analysis.error_count, 0);
}

// ============================================================================
// Batch expansion
// ============================================================================

#[test]
fn test_batch_expand_empty() {
    let registry = AttrMacroRegistry::with_builtins();
    let conflicts = ConflictRegistry::with_defaults();
    let mut stats = StatsCollector::new();
    let result = batch_expand(&[], &registry, &conflicts, &mut stats);
    assert!(result.results.is_empty());
    assert!(result.conflict_errors.is_empty());
}

#[test]
fn test_batch_expand_single_decl() {
    let registry = AttrMacroRegistry::with_builtins();
    let conflicts = ConflictRegistry::with_defaults();
    let mut stats = StatsCollector::new();
    let decls = vec![(
        Name::from_string("my_lemma"),
        vec![Attribute::Simp { priority: None }],
    )];
    let result = batch_expand(&decls, &registry, &conflicts, &mut stats);
    assert_eq!(result.results.len(), 1);
    assert!(result.conflict_errors.is_empty());
    assert_eq!(result.results[0].1.effects.len(), 1);
}

#[test]
fn test_batch_expand_multiple_decls() {
    let registry = AttrMacroRegistry::with_builtins();
    let conflicts = ConflictRegistry::with_defaults();
    let mut stats = StatsCollector::new();
    let decls = vec![
        (
            Name::from_string("lemma1"),
            vec![Attribute::Simp { priority: None }],
        ),
        (Name::from_string("lemma2"), vec![Attribute::Ext]),
        (Name::from_string("def1"), vec![Attribute::Inline]),
    ];
    let result = batch_expand(&decls, &registry, &conflicts, &mut stats);
    assert_eq!(result.results.len(), 3);
    assert!(result.conflict_errors.is_empty());
}

#[test]
fn test_batch_expand_detects_conflicts() {
    let registry = AttrMacroRegistry::with_builtins();
    let conflicts = ConflictRegistry::with_defaults();
    let mut stats = StatsCollector::new();
    let decls = vec![(
        Name::from_string("bad_fn"),
        vec![Attribute::Inline, Attribute::Noinline],
    )];
    let result = batch_expand(&decls, &registry, &conflicts, &mut stats);
    assert!(!result.conflict_errors.is_empty());
    // Expansion still proceeds despite conflict detection
    assert_eq!(result.results.len(), 1);
}

#[test]
fn test_batch_expand_updates_stats() {
    let registry = AttrMacroRegistry::with_builtins();
    let conflicts = ConflictRegistry::with_defaults();
    let mut stats = StatsCollector::new();
    let decls = vec![
        (
            Name::from_string("a"),
            vec![Attribute::Simp { priority: None }],
        ),
        (Name::from_string("b"), vec![Attribute::Ext]),
    ];
    batch_expand(&decls, &registry, &conflicts, &mut stats);
    assert!(stats.total_successes() > 0);
}

// ============================================================================
// Validation
// ============================================================================

#[test]
fn test_validate_macros_clean() {
    let registry = AttrMacroRegistry::with_builtins();
    let graph = MacroDependencyGraph::new();
    let result = validate_macros(&registry, &graph);
    assert!(result.is_ok());
    assert!(result.macros_checked > 0);
}

#[test]
fn test_validate_macros_with_valid_deps() {
    let registry = AttrMacroRegistry::with_builtins();
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("simp", "ext"); // Both registered
    let result = validate_macros(&registry, &graph);
    assert!(result.is_ok());
}

#[test]
fn test_validate_macros_missing_dep() {
    let registry = AttrMacroRegistry::new(); // Empty registry
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("my_macro", "nonexistent");
    let result = validate_macros(&registry, &graph);
    assert!(!result.is_ok());
    // Both MissingDependency (nonexistent) and MissingHandler (my_macro)
    assert!(!result.errors.is_empty());
}

#[test]
fn test_validate_macros_circular_dep() {
    let registry = AttrMacroRegistry::with_builtins();
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("simp", "ext");
    graph.add_dependency("ext", "simp");
    let result = validate_macros(&registry, &graph);
    assert!(!result.is_ok());
}

#[test]
fn test_validate_macros_missing_handler() {
    let registry = AttrMacroRegistry::new();
    let mut graph = MacroDependencyGraph::new();
    graph.add_dependency("unregistered_macro", "also_unregistered");
    let result = validate_macros(&registry, &graph);
    assert!(!result.is_ok());
    let has_missing_handler = result.errors.iter().any(
        |e| matches!(e, AttrMacroExtError::MissingHandler { name } if name == "unregistered_macro"),
    );
    assert!(has_missing_handler);
}

// ============================================================================
// Error types
// ============================================================================

#[test]
fn test_error_display_conflicting() {
    let err = AttrMacroExtError::ConflictingAttributes {
        decl: "my_fn".to_owned(),
        a: "inline".to_owned(),
        b: "noinline".to_owned(),
    };
    let msg = format!("{err}");
    assert!(msg.contains("inline"));
    assert!(msg.contains("noinline"));
    assert!(msg.contains("my_fn"));
}

#[test]
fn test_error_display_circular() {
    let err = AttrMacroExtError::CircularDependency {
        cycle: "a -> b -> a".to_owned(),
    };
    let msg = format!("{err}");
    assert!(msg.contains("circular"));
    assert!(msg.contains("a -> b -> a"));
}

#[test]
fn test_error_display_missing_dep() {
    let err = AttrMacroExtError::MissingDependency {
        macro_name: "my_macro".to_owned(),
        dependency: "gone".to_owned(),
    };
    let msg = format!("{err}");
    assert!(msg.contains("my_macro"));
    assert!(msg.contains("gone"));
}

#[test]
fn test_error_display_missing_handler() {
    let err = AttrMacroExtError::MissingHandler {
        name: "orphan".to_owned(),
    };
    let msg = format!("{err}");
    assert!(msg.contains("orphan"));
    assert!(msg.contains("no handler"));
}

#[test]
fn test_error_from_elab_error() {
    let elab_err = crate::ElabError::CannotInfer;
    let ext_err: AttrMacroExtError = elab_err.into();
    let msg = format!("{ext_err}");
    assert!(msg.contains("elaboration error"));
}

// ============================================================================
// Integration: scope + conflict + batch
// ============================================================================

#[test]
fn test_integration_full_pipeline() {
    let registry = AttrMacroRegistry::with_builtins();
    let conflicts = ConflictRegistry::with_defaults();
    let mut stats = StatsCollector::new();

    let decls = vec![
        (
            Name::from_string("simp_lemma"),
            vec![Attribute::Simp { priority: None }, Attribute::Ext],
        ),
        (
            Name::from_string("fast_fn"),
            vec![Attribute::Inline, Attribute::Reducible],
        ),
    ];

    // Check scopes
    assert_eq!(classify_scope("simp", &registry), MacroScope::Global);
    assert_eq!(classify_scope("ext", &registry), MacroScope::Global);

    // Batch expand
    let result = batch_expand(&decls, &registry, &conflicts, &mut stats);
    assert_eq!(result.results.len(), 2);
    assert!(result.conflict_errors.is_empty());

    // Analyze each
    for (_name, expansion) in &result.results {
        let analysis = analyze_expansion(expansion);
        assert!(analysis.effect_count > 0);
        assert_eq!(analysis.error_count, 0);
    }

    // Stats were collected
    assert!(stats.total_successes() > 0);
}
