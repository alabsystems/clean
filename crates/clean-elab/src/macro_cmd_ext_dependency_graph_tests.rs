// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

// =============================================================================
// Dependency graph tests
// =============================================================================

#[test]
fn test_dep_graph_empty_registry() {
    let reg = MacroRegistry::empty();
    let graph = MacroDependencyGraph::build(&reg);
    assert!(graph.edges.is_empty());
    assert!(graph.reverse_edges.is_empty());
}

#[test]
fn test_dep_graph_independent_macros() {
    let reg = MacroRegistry::new(); // check, eval, print — all independent
    let graph = MacroDependencyGraph::build(&reg);

    assert_eq!(graph.edges.len(), 3);
    // All builtins should have zero dependencies on each other
    for deps in graph.edges.values() {
        assert!(deps.is_empty());
    }
}

#[test]
fn test_dep_graph_with_delegation() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("base"),
        ident(clean_parser::SurfaceName::generated_path("impl")),
        MacroScoping::Term,
    ));
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("wrapper"),
        ident(clean_parser::SurfaceName::generated_path("base")),
        MacroScoping::Term,
    ));

    let graph = MacroDependencyGraph::build(&reg);

    let wrapper_deps = graph.dependencies_of(&clean_parser::SurfaceName::generated_path("wrapper"));
    assert!(
        wrapper_deps.contains(&clean_parser::SurfaceName::generated_path("base")),
        "wrapper should depend on base"
    );

    let base_deps = graph.dependencies_of(&clean_parser::SurfaceName::generated_path("base"));
    assert!(base_deps.is_empty(), "base should have no deps");

    let base_dependents = graph.dependents_of(&clean_parser::SurfaceName::generated_path("base"));
    assert!(base_dependents.contains(&clean_parser::SurfaceName::generated_path("wrapper")));
}

#[test]
fn test_dep_graph_leaves_and_roots() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("base"),
        ident(clean_parser::SurfaceName::generated_path("impl")),
        MacroScoping::Term,
    ));
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("wrapper"),
        ident(clean_parser::SurfaceName::generated_path("base")),
        MacroScoping::Term,
    ));

    let graph = MacroDependencyGraph::build(&reg);

    let leaves = graph.leaves();
    assert!(
        leaves.contains(&clean_parser::SurfaceName::generated_path("base")),
        "base should be a leaf (no deps)"
    );

    let roots = graph.roots();
    assert!(
        roots.contains(&clean_parser::SurfaceName::generated_path("wrapper")),
        "wrapper should be a root (no dependents)"
    );
}

#[test]
fn test_dep_graph_no_cycle_in_independent() {
    let reg = MacroRegistry::new();
    let graph = MacroDependencyGraph::build(&reg);
    assert!(graph.detect_cycle().is_none());
}

#[test]
fn test_dep_graph_no_cycle_in_chain() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("a"),
        ident(clean_parser::SurfaceName::generated_path("b")),
        MacroScoping::Term,
    ));
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("b"),
        ident(clean_parser::SurfaceName::generated_path("c")),
        MacroScoping::Term,
    ));
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("c"),
        ident(clean_parser::SurfaceName::generated_path("end")),
        MacroScoping::Term,
    ));

    let graph = MacroDependencyGraph::build(&reg);
    assert!(graph.detect_cycle().is_none());
}

#[test]
fn test_dep_graph_detects_cycle() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("x"),
        ident(clean_parser::SurfaceName::generated_path("y")),
        MacroScoping::Term,
    ));
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("y"),
        ident(clean_parser::SurfaceName::generated_path("x")),
        MacroScoping::Term,
    ));

    let graph = MacroDependencyGraph::build(&reg);
    let cycle = graph.detect_cycle();
    assert!(cycle.is_some(), "should detect x <-> y cycle");
    let cycle = cycle.unwrap();
    assert!(cycle.contains(&clean_parser::SurfaceName::generated_path("x")));
    assert!(cycle.contains(&clean_parser::SurfaceName::generated_path("y")));
}

#[test]
fn test_dep_graph_topological_order_independent() {
    let reg = MacroRegistry::new();
    let graph = MacroDependencyGraph::build(&reg);
    let order = graph.topological_order();
    assert!(order.is_some());
    let order = order.unwrap();
    assert_eq!(order.len(), 3);
}

#[test]
fn test_dep_graph_topological_order_cycle_returns_none() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("x"),
        ident(clean_parser::SurfaceName::generated_path("y")),
        MacroScoping::Term,
    ));
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("y"),
        ident(clean_parser::SurfaceName::generated_path("x")),
        MacroScoping::Term,
    ));

    let graph = MacroDependencyGraph::build(&reg);
    assert!(graph.topological_order().is_none());
}

#[test]
fn test_dep_graph_dependencies_of_unknown() {
    let reg = MacroRegistry::new();
    let graph = MacroDependencyGraph::build(&reg);
    let deps = graph.dependencies_of(&clean_parser::SurfaceName::generated_path("nonexistent"));
    assert!(deps.is_empty());
}
