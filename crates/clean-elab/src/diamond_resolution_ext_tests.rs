// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended diamond resolution: path enumeration, coherence, strategies,
//! statistics, visualization, cycle detection, and caching.

use crate::diamond_resolution::{DiamondDetector, InstanceEntry};
use crate::diamond_resolution_ext::{
    DiamondExtError, DiamondResolverExt, DiamondStats, ResolutionCache, ResolutionStrategy,
    ResolvedDiamond,
};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mk_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_instance(name: &str, class: &str, expr: Expr) -> InstanceEntry {
    InstanceEntry {
        name: name.to_owned(),
        class: class.to_owned(),
        type_args: vec![],
        instance_expr: expr,
    }
}

/// Standard Monad diamond: Monad -> {Applicative, Alternative} -> Functor.
fn monad_ext() -> DiamondResolverExt {
    let mut ext = DiamondResolverExt::new();
    ext.register_superclass("Monad", "Applicative");
    ext.register_superclass("Monad", "Alternative");
    ext.register_superclass("Applicative", "Functor");
    ext.register_superclass("Alternative", "Functor");
    ext
}

/// Register a Functor instance on the monad diamond.
fn monad_ext_with_instance() -> DiamondResolverExt {
    let mut ext = monad_ext();
    ext.register_instance(mk_instance(
        "instFunctor",
        "Functor",
        mk_const("functor_impl"),
    ));
    ext
}

// ===========================================================================
// Path enumeration
// ===========================================================================

#[test]
fn test_enumerate_paths_diamond() {
    let ext = monad_ext();
    let paths = ext.enumerate_paths("Monad", "Functor");
    assert_eq!(paths.len(), 2);
    for p in &paths {
        assert_eq!(p.first().map(String::as_str), Some("Monad"));
        assert_eq!(p.last().map(String::as_str), Some("Functor"));
    }
}

#[test]
fn test_enumerate_paths_no_path() {
    let ext = monad_ext();
    let paths = ext.enumerate_paths("Functor", "Monad");
    assert!(paths.is_empty(), "no reverse path in directed graph");
}

#[test]
fn test_enumerate_paths_same_node() {
    let ext = monad_ext();
    let paths = ext.enumerate_paths("Monad", "Monad");
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0], vec!["Monad"]);
}

#[test]
fn test_path_count_diamond() {
    let ext = monad_ext();
    assert_eq!(ext.path_count("Monad", "Functor"), 2);
}

#[test]
fn test_path_count_linear() {
    let mut ext = DiamondResolverExt::new();
    ext.register_superclass("A", "B");
    ext.register_superclass("B", "C");
    assert_eq!(ext.path_count("A", "C"), 1);
}

#[test]
fn test_path_count_no_path() {
    let ext = monad_ext();
    assert_eq!(ext.path_count("Functor", "Monad"), 0);
}

// ===========================================================================
// Coherence checking
// ===========================================================================

#[test]
fn test_check_all_coherence_no_errors() {
    let mut ext = monad_ext();
    ext.register_instance(mk_instance("inst1", "Functor", mk_const("same")));
    let errors = ext.check_all_coherence("Monad");
    assert!(errors.is_empty(), "same instance is coherent");
}

#[test]
fn test_check_all_coherence_with_incoherence() {
    let mut ext = monad_ext();
    ext.register_instance(mk_instance("inst1", "Functor", mk_const("a")));
    ext.register_instance(mk_instance("inst2", "Functor", mk_const("b")));
    let errors = ext.check_all_coherence("Monad");
    assert_eq!(errors.len(), 1);
}

#[test]
fn test_check_coherence_for_specific_ancestor() {
    let mut ext = monad_ext();
    ext.register_instance(mk_instance("inst", "Functor", mk_const("f")));
    ext.check_coherence_for("Monad", "Functor")
        .expect("should be coherent");
}

#[test]
fn test_check_coherence_for_missing_ancestor() {
    let ext = monad_ext();
    let err = ext
        .check_coherence_for("Monad", "NonExistent")
        .expect_err("should fail for missing ancestor");
    assert!(matches!(err, DiamondExtError::Base(_)));
}

// ===========================================================================
// Resolution strategies
// ===========================================================================

#[test]
fn test_resolve_prefer_shortest() {
    let mut ext = monad_ext_with_instance();
    let results = ext
        .resolve_with_strategy("Monad", ResolutionStrategy::PreferShortest)
        .expect("should resolve");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].class_name, "Functor");
    assert_eq!(results[0].strategy_used, ResolutionStrategy::PreferShortest);
}

#[test]
fn test_resolve_prefer_explicit() {
    let mut ext = monad_ext();
    ext.register_explicit_instance(mk_instance(
        "explicitF",
        "Functor",
        mk_const("explicit_impl"),
    ));
    let results = ext
        .resolve_with_strategy("Monad", ResolutionStrategy::PreferExplicit)
        .expect("should resolve");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].strategy_used, ResolutionStrategy::PreferExplicit);
}

#[test]
fn test_resolve_prefer_local() {
    let mut ext = monad_ext_with_instance();
    let results = ext
        .resolve_with_strategy("Monad", ResolutionStrategy::PreferLocal)
        .expect("should resolve");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].strategy_used, ResolutionStrategy::PreferLocal);
}

#[test]
fn test_resolve_no_instances_empty_result() {
    let mut ext = monad_ext();
    let results = ext
        .resolve_with_strategy("Monad", ResolutionStrategy::PreferShortest)
        .expect("should succeed with empty results");
    assert!(results.is_empty(), "no instances means no resolutions");
}

#[test]
fn test_resolve_no_diamonds_empty_result() {
    let mut ext = DiamondResolverExt::new();
    ext.register_superclass("A", "B");
    ext.register_superclass("B", "C");
    ext.register_instance(mk_instance("inst", "C", mk_const("c")));
    let results = ext
        .resolve_with_strategy("A", ResolutionStrategy::PreferShortest)
        .expect("linear hierarchy");
    assert!(results.is_empty());
}

// ===========================================================================
// Batch resolution (resolve_all)
// ===========================================================================

#[test]
fn test_resolve_all_success() {
    let mut ext = monad_ext_with_instance();
    let (resolved, errors) = ext.resolve_all("Monad", ResolutionStrategy::PreferShortest);
    assert_eq!(resolved.len(), 1);
    assert!(errors.is_empty());
}

#[test]
fn test_resolve_all_multiple_diamonds() {
    let mut ext = DiamondResolverExt::new();
    ext.register_superclass("A", "B");
    ext.register_superclass("A", "C");
    ext.register_superclass("B", "D");
    ext.register_superclass("C", "D");
    ext.register_superclass("B", "E");
    ext.register_superclass("C", "E");
    ext.register_instance(mk_instance("instD", "D", mk_const("d")));
    ext.register_instance(mk_instance("instE", "E", mk_const("e")));

    let (resolved, errors) = ext.resolve_all("A", ResolutionStrategy::PreferShortest);
    assert_eq!(resolved.len(), 2);
    assert!(errors.is_empty());
}

// ===========================================================================
// Cycle detection
// ===========================================================================

#[test]
fn test_no_cycles_in_dag() {
    let ext = monad_ext();
    assert!(!ext.has_cycles());
    assert!(ext.detect_cycles().is_empty());
}

#[test]
fn test_detect_self_loop() {
    let mut ext = DiamondResolverExt::new();
    ext.register_superclass("A", "A");
    assert!(ext.has_cycles());
    let cycles = ext.detect_cycles();
    assert!(!cycles.is_empty());
}

#[test]
fn test_detect_two_node_cycle() {
    let mut ext = DiamondResolverExt::new();
    ext.register_superclass("A", "B");
    ext.register_superclass("B", "A");
    assert!(ext.has_cycles());
}

#[test]
fn test_detect_three_node_cycle() {
    let mut ext = DiamondResolverExt::new();
    ext.register_superclass("A", "B");
    ext.register_superclass("B", "C");
    ext.register_superclass("C", "A");
    assert!(ext.has_cycles());
}

#[test]
fn test_no_cycles_empty_graph() {
    let ext = DiamondResolverExt::new();
    assert!(!ext.has_cycles());
    assert!(ext.detect_cycles().is_empty());
}

// ===========================================================================
// Diamond statistics
// ===========================================================================

#[test]
fn test_stats_no_diamonds() {
    let mut ext = DiamondResolverExt::new();
    ext.register_superclass("A", "B");
    let stats = ext.compute_stats("A");
    assert_eq!(stats.diamond_count, 0);
    assert_eq!(stats.total_paths, 0);
}

#[test]
fn test_stats_simple_diamond() {
    let ext = monad_ext_with_instance();
    let stats = ext.compute_stats("Monad");
    assert_eq!(stats.diamond_count, 1);
    assert!(
        stats.max_depth >= 3,
        "Monad->Applicative->Functor = 3 nodes"
    );
    assert!(stats.max_branching_factor >= 2);
}

#[test]
fn test_stats_display() {
    let stats = DiamondStats {
        diamond_count: 2,
        max_depth: 5,
        max_branching_factor: 3,
        branching_distribution: HashMap::new(),
        total_paths: 7,
    };
    let display = format!("{stats}");
    assert!(display.contains("diamonds=2"));
    assert!(display.contains("max_depth=5"));
    assert!(display.contains("max_branching=3"));
    assert!(display.contains("total_paths=7"));
}

use std::collections::HashMap;

#[test]
fn test_stats_default() {
    let stats = DiamondStats::default();
    assert_eq!(stats.diamond_count, 0);
    assert_eq!(stats.max_depth, 0);
    assert_eq!(stats.max_branching_factor, 0);
    assert!(stats.branching_distribution.is_empty());
    assert_eq!(stats.total_paths, 0);
}

// ===========================================================================
// Resolution cache
// ===========================================================================

#[test]
fn test_cache_empty_initially() {
    let cache = ResolutionCache::new();
    assert!(cache.is_empty());
    assert_eq!(cache.len(), 0);
}

#[test]
fn test_cache_insert_and_get() {
    let mut cache = ResolutionCache::new();
    let resolved = ResolvedDiamond {
        class_name: "Functor".to_owned(),
        chosen_path_index: 0,
        strategy_used: ResolutionStrategy::PreferShortest,
        instance_expr: mk_const("f"),
    };
    cache.insert("Monad", "Functor", resolved.clone(), 1);
    assert_eq!(cache.len(), 1);

    let cached = cache.get("Monad", "Functor", 1).expect("no error");
    assert_eq!(cached, Some(&resolved));
}

#[test]
fn test_cache_miss() {
    let mut cache = ResolutionCache::new();
    let resolved = ResolvedDiamond {
        class_name: "Functor".to_owned(),
        chosen_path_index: 0,
        strategy_used: ResolutionStrategy::PreferShortest,
        instance_expr: mk_const("f"),
    };
    cache.insert("Monad", "Functor", resolved, 1);

    let cached = cache.get("Monad", "Other", 1).expect("no error");
    assert!(cached.is_none());
}

#[test]
fn test_cache_invalidation_on_fingerprint_mismatch() {
    let mut cache = ResolutionCache::new();
    let resolved = ResolvedDiamond {
        class_name: "Functor".to_owned(),
        chosen_path_index: 0,
        strategy_used: ResolutionStrategy::PreferShortest,
        instance_expr: mk_const("f"),
    };
    cache.insert("Monad", "Functor", resolved, 1);

    let err = cache
        .get("Monad", "Functor", 2)
        .expect_err("fingerprint mismatch");
    assert!(matches!(err, DiamondExtError::CacheInvalidated));
}

#[test]
fn test_cache_invalidate_clears_entries() {
    let mut cache = ResolutionCache::new();
    let resolved = ResolvedDiamond {
        class_name: "Functor".to_owned(),
        chosen_path_index: 0,
        strategy_used: ResolutionStrategy::PreferShortest,
        instance_expr: mk_const("f"),
    };
    cache.insert("Monad", "Functor", resolved, 1);
    assert_eq!(cache.len(), 1);
    cache.invalidate();
    assert!(cache.is_empty());
}

#[test]
fn test_cache_empty_allows_any_fingerprint() {
    let cache = ResolutionCache::new();
    // Empty cache should return None, not an error, regardless of fingerprint.
    let result = cache.get("X", "Y", 999).expect("empty cache no error");
    assert!(result.is_none());
}

// ===========================================================================
// Cache integration with resolver
// ===========================================================================

#[test]
fn test_resolver_cache_populated_after_resolve() {
    let mut ext = monad_ext_with_instance();
    assert!(ext.cache.is_empty());

    ext.resolve_with_strategy("Monad", ResolutionStrategy::PreferShortest)
        .expect("should resolve");
    assert!(!ext.cache.is_empty());
}

#[test]
fn test_resolver_cache_invalidated_on_new_instance() {
    let mut ext = monad_ext_with_instance();
    ext.resolve_with_strategy("Monad", ResolutionStrategy::PreferShortest)
        .expect("resolve");
    assert!(!ext.cache.is_empty());

    ext.register_instance(mk_instance("inst2", "Functor", mk_const("other")));
    assert!(ext.cache.is_empty(), "cache cleared after new instance");
}

#[test]
fn test_resolver_cache_invalidated_on_new_superclass() {
    let mut ext = monad_ext_with_instance();
    ext.resolve_with_strategy("Monad", ResolutionStrategy::PreferShortest)
        .expect("resolve");
    assert!(!ext.cache.is_empty());

    ext.register_superclass("Functor", "Semigroup");
    assert!(ext.cache.is_empty(), "cache cleared after hierarchy change");
}

// ===========================================================================
// DOT visualization
// ===========================================================================

#[test]
fn test_dot_output_basic() {
    let ext = monad_ext();
    let dot = ext.to_dot();
    assert!(dot.starts_with("digraph diamond_hierarchy {"));
    assert!(dot.contains("\"Monad\""));
    assert!(dot.contains("\"Functor\""));
    assert!(dot.contains("\"Monad\" -> \"Applicative\""));
    assert!(dot.ends_with("}\n"));
}

#[test]
fn test_dot_diamond_highlighting() {
    let ext = monad_ext();
    let dot = ext.to_dot();
    // Functor is a diamond class, should be highlighted.
    assert!(dot.contains("lightyellow"));
}

#[test]
fn test_diamond_subgraph_dot() {
    let ext = monad_ext();
    let dot = ext.diamond_subgraph_dot("Monad", "Functor");
    assert!(dot.starts_with("digraph diamond_subgraph {"));
    assert!(dot.contains("\"Monad\""));
    assert!(dot.contains("\"Functor\""));
    assert!(dot.contains("lightblue")); // target
    assert!(dot.contains("lightyellow")); // ancestor
}

#[test]
fn test_diamond_subgraph_dot_no_path() {
    let ext = monad_ext();
    let dot = ext.diamond_subgraph_dot("Functor", "Monad");
    // No nodes or edges since there is no path.
    assert!(dot.starts_with("digraph diamond_subgraph {"));
    assert!(!dot.contains("\"Monad\""));
}

#[test]
fn test_dot_empty_graph() {
    let ext = DiamondResolverExt::new();
    let dot = ext.to_dot();
    assert!(dot.starts_with("digraph diamond_hierarchy {"));
    assert!(dot.ends_with("}\n"));
}

// ===========================================================================
// From detector
// ===========================================================================

#[test]
fn test_from_detector() {
    let mut det = DiamondDetector::new();
    det.register_superclass("A", "B");
    det.register_superclass("A", "C");
    det.register_superclass("B", "D");
    det.register_superclass("C", "D");

    let ext = DiamondResolverExt::from_detector(det);
    assert_eq!(ext.path_count("A", "D"), 2);
}

// ===========================================================================
// Instance fingerprint tracking
// ===========================================================================

#[test]
fn test_fingerprint_increments_on_register() {
    let mut ext = DiamondResolverExt::new();
    ext.register_superclass("A", "B");
    let fp0 = ext.instance_fingerprint();

    ext.register_instance(mk_instance("inst1", "B", mk_const("b1")));
    let fp1 = ext.instance_fingerprint();
    assert!(fp1 > fp0);

    ext.register_instance(mk_instance("inst2", "B", mk_const("b2")));
    let fp2 = ext.instance_fingerprint();
    assert!(fp2 > fp1);
}

#[test]
fn test_fingerprint_increments_on_explicit_register() {
    let mut ext = DiamondResolverExt::new();
    ext.register_superclass("A", "B");
    let fp0 = ext.instance_fingerprint();

    ext.register_explicit_instance(mk_instance("explicit", "B", mk_const("b")));
    assert!(ext.instance_fingerprint() > fp0);
}

// ===========================================================================
// Edge cases
// ===========================================================================

#[test]
fn test_resolve_empty_resolver() {
    let mut ext = DiamondResolverExt::new();
    let results = ext
        .resolve_with_strategy("Nothing", ResolutionStrategy::PreferShortest)
        .expect("empty resolver should succeed with no results");
    assert!(results.is_empty());
}

#[test]
fn test_deep_diamond_stats() {
    // A -> B -> C -> F, A -> D -> E -> F
    let mut ext = DiamondResolverExt::new();
    ext.register_superclass("A", "B");
    ext.register_superclass("B", "C");
    ext.register_superclass("C", "F");
    ext.register_superclass("A", "D");
    ext.register_superclass("D", "E");
    ext.register_superclass("E", "F");
    ext.register_instance(mk_instance("instF", "F", mk_const("f")));

    let stats = ext.compute_stats("A");
    assert_eq!(stats.diamond_count, 1);
    assert_eq!(stats.max_depth, 4); // A -> B -> C -> F or A -> D -> E -> F
}

#[test]
fn test_prefer_explicit_falls_back_when_none_explicit() {
    let mut ext = monad_ext_with_instance();
    // No explicit instances registered, should fall back to first path.
    let results = ext
        .resolve_with_strategy("Monad", ResolutionStrategy::PreferExplicit)
        .expect("should fall back");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].chosen_path_index, 0);
}
