// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for diamond detection and coherence checking.

use crate::diamond_resolution::{
    Diamond, DiamondDetector, DiamondError, DiamondPath, InstanceEntry,
};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

/// Helper: create a simple const expression for testing.
fn mk_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Helper: create an instance entry.
fn mk_instance(name: &str, class: &str, expr: Expr) -> InstanceEntry {
    InstanceEntry {
        name: name.to_owned(),
        class: class.to_owned(),
        type_args: vec![],
        instance_expr: expr,
    }
}

/// Helper: build a detector with the standard Monad diamond hierarchy.
fn monad_diamond_detector() -> DiamondDetector {
    let mut det = DiamondDetector::new();
    det.register_superclass("Monad", "Applicative");
    det.register_superclass("Monad", "Alternative");
    det.register_superclass("Applicative", "Functor");
    det.register_superclass("Alternative", "Functor");
    det
}

// ---------------------------------------------------------------------------
// Superclass registration
// ---------------------------------------------------------------------------

#[test]
fn test_register_superclass_basic() {
    let mut det = DiamondDetector::new();
    det.register_superclass("Monad", "Applicative");

    let supers = det.superclasses("Monad");
    assert_eq!(supers, vec!["Applicative"]);
}

#[test]
fn test_register_superclass_dedup() {
    let mut det = DiamondDetector::new();
    det.register_superclass("Monad", "Applicative");
    det.register_superclass("Monad", "Applicative"); // duplicate

    let supers = det.superclasses("Monad");
    assert_eq!(supers.len(), 1, "duplicates should be ignored");
}

#[test]
fn test_superclasses_unknown_class() {
    let det = DiamondDetector::new();
    let supers = det.superclasses("NonExistent");
    assert!(supers.is_empty());
}

// ---------------------------------------------------------------------------
// All ancestors (transitive closure)
// ---------------------------------------------------------------------------

#[test]
fn test_all_ancestors_linear() {
    let mut det = DiamondDetector::new();
    det.register_superclass("Monad", "Applicative");
    det.register_superclass("Applicative", "Functor");

    let ancestors = det.all_ancestors("Monad");
    assert!(ancestors.contains("Applicative"));
    assert!(ancestors.contains("Functor"));
    assert!(!ancestors.contains("Monad"), "self not in ancestors");
    assert_eq!(ancestors.len(), 2);
}

#[test]
fn test_all_ancestors_diamond() {
    let det = monad_diamond_detector();

    let ancestors = det.all_ancestors("Monad");
    assert!(ancestors.contains("Applicative"));
    assert!(ancestors.contains("Alternative"));
    assert!(ancestors.contains("Functor"));
    assert_eq!(ancestors.len(), 3);
}

#[test]
fn test_all_ancestors_empty() {
    let mut det = DiamondDetector::new();
    det.register_superclass("Monad", "Applicative");

    // Applicative is a leaf: registered via register_superclass but has no parents.
    let ancestors = det.all_ancestors("Applicative");
    assert!(ancestors.is_empty(), "leaf class has no ancestors");
}

#[test]
fn test_all_ancestors_unknown_class() {
    let det = DiamondDetector::new();
    let ancestors = det.all_ancestors("Unknown");
    assert!(ancestors.is_empty());
}

// ---------------------------------------------------------------------------
// Path finding
// ---------------------------------------------------------------------------

#[test]
fn test_find_all_paths_direct() {
    let mut det = DiamondDetector::new();
    det.register_superclass("A", "B");

    let paths = det.find_all_paths("A", "B");
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0], vec!["A", "B"]);
}

#[test]
fn test_find_all_paths_two_paths() {
    let det = monad_diamond_detector();

    let paths = det.find_all_paths("Monad", "Functor");
    assert_eq!(paths.len(), 2);

    // Both paths should start with Monad and end with Functor.
    for path in &paths {
        assert_eq!(path.first().map(String::as_str), Some("Monad"));
        assert_eq!(path.last().map(String::as_str), Some("Functor"));
    }
}

#[test]
fn test_find_all_paths_no_path() {
    let mut det = DiamondDetector::new();
    det.register_superclass("A", "B");

    let paths = det.find_all_paths("B", "A");
    assert!(paths.is_empty(), "no reverse path in directed graph");
}

#[test]
fn test_find_all_paths_same_node() {
    let mut det = DiamondDetector::new();
    det.register_superclass("A", "B");

    let paths = det.find_all_paths("A", "A");
    assert_eq!(paths.len(), 1, "trivial path from A to A");
    assert_eq!(paths[0], vec!["A"]);
}

// ---------------------------------------------------------------------------
// Diamond detection -- no diamonds
// ---------------------------------------------------------------------------

#[test]
fn test_no_diamonds_linear() {
    let mut det = DiamondDetector::new();
    det.register_superclass("Monad", "Applicative");
    det.register_superclass("Applicative", "Functor");

    let diamonds = det.detect_diamonds("Monad");
    assert!(diamonds.is_empty(), "linear hierarchy has no diamonds");
}

#[test]
fn test_no_diamonds_empty() {
    let det = DiamondDetector::new();
    let diamonds = det.detect_diamonds("Anything");
    assert!(diamonds.is_empty());
}

// ---------------------------------------------------------------------------
// Diamond detection -- simple diamond
// ---------------------------------------------------------------------------

#[test]
fn test_detect_simple_diamond() {
    let mut det = monad_diamond_detector();

    // Register a Functor instance so diamond paths get populated.
    det.register_instance(mk_instance("instFunctor", "Functor", mk_const("myFunctor")));

    let diamonds = det.detect_diamonds("Monad");
    assert_eq!(diamonds.len(), 1);
    assert_eq!(diamonds[0].class_name, "Functor");
    assert_eq!(diamonds[0].instance_paths.len(), 2);
    assert!(!diamonds[0].resolved);
}

#[test]
fn test_detect_diamond_no_instances_means_no_paths() {
    // Diamond exists in the hierarchy but no instances registered for the
    // ancestor class -- build_diamond_paths returns empty in that case.
    let det = monad_diamond_detector();

    let diamonds = det.detect_diamonds("Monad");
    // The diamond at Functor is detected but has 0 instance_paths because
    // no instances were registered.
    assert_eq!(diamonds.len(), 1);
    assert_eq!(diamonds[0].class_name, "Functor");
    assert!(diamonds[0].instance_paths.is_empty());
}

// ---------------------------------------------------------------------------
// Diamond coherence -- success
// ---------------------------------------------------------------------------

#[test]
fn test_coherence_same_instance() {
    let mut det = monad_diamond_detector();
    let expr = mk_const("sharedFunctor");
    det.register_instance(mk_instance("instA", "Functor", expr.clone()));

    let diamonds = det.detect_diamonds("Monad");
    assert_eq!(diamonds.len(), 1);

    det.check_diamond_coherence(&diamonds[0])
        .expect("same instance should be coherent");
}

#[test]
fn test_coherence_single_path() {
    let mut det = DiamondDetector::new();
    det.register_superclass("A", "B");
    det.register_instance(mk_instance("inst", "B", mk_const("onlyOne")));

    // A->B is a single path, not a diamond. Test coherence on a manually
    // constructed single-path Diamond to validate the edge case.
    let diamond = Diamond {
        class_name: "B".to_owned(),
        instance_paths: vec![DiamondPath {
            through: vec!["A".to_owned(), "B".to_owned()],
            instance_expr: mk_const("onlyOne"),
        }],
        resolved: false,
    };

    det.check_diamond_coherence(&diamond)
        .expect("single path is trivially coherent");
}

// ---------------------------------------------------------------------------
// Diamond coherence -- failure
// ---------------------------------------------------------------------------

#[test]
fn test_coherence_different_instances() {
    let mut det = monad_diamond_detector();
    det.register_instance(mk_instance("instA", "Functor", mk_const("functorA")));
    det.register_instance(mk_instance("instB", "Functor", mk_const("functorB")));

    let diamonds = det.detect_diamonds("Monad");
    assert_eq!(diamonds.len(), 1);

    // The two paths should get different instances (index 0 and index 1).
    let err = det
        .check_diamond_coherence(&diamonds[0])
        .expect_err("different instances should be incoherent");
    assert!(matches!(err, DiamondError::IncoherentInstances { .. }));
}

#[test]
fn test_coherence_unknown_class_error() {
    let det = DiamondDetector::new();
    let diamond = Diamond {
        class_name: "NonExistent".to_owned(),
        instance_paths: vec![],
        resolved: false,
    };

    let err = det
        .check_diamond_coherence(&diamond)
        .expect_err("unknown class should error");
    assert!(matches!(err, DiamondError::UnknownClass(_)));
}

// ---------------------------------------------------------------------------
// Diamond resolution with unifier
// ---------------------------------------------------------------------------

#[test]
fn test_resolve_diamond_success() {
    let mut det = monad_diamond_detector();
    let expr = mk_const("shared");
    det.register_instance(mk_instance("inst", "Functor", expr));

    let mut diamonds = det.detect_diamonds("Monad");
    assert_eq!(diamonds.len(), 1);

    let always_eq = |_a: &Expr, _b: &Expr| true;
    det.resolve_diamond(&mut diamonds[0], &always_eq)
        .expect("unifier says equal");
    assert!(diamonds[0].resolved);
}

#[test]
fn test_resolve_diamond_failure() {
    let mut det = monad_diamond_detector();
    det.register_instance(mk_instance("instA", "Functor", mk_const("a")));
    det.register_instance(mk_instance("instB", "Functor", mk_const("b")));

    let mut diamonds = det.detect_diamonds("Monad");
    assert_eq!(diamonds.len(), 1);

    let never_eq = |_a: &Expr, _b: &Expr| false;
    let err = det
        .resolve_diamond(&mut diamonds[0], &never_eq)
        .expect_err("unifier rejects");
    assert!(matches!(err, DiamondError::IncoherentInstances { .. }));
    assert!(!diamonds[0].resolved);
}

#[test]
fn test_resolve_diamond_trivial_single_path() {
    let mut det = DiamondDetector::new();
    det.register_superclass("X", "Y");
    det.register_instance(mk_instance("inst", "X", mk_const("only")));

    let mut diamond = Diamond {
        class_name: "X".to_owned(),
        instance_paths: vec![DiamondPath {
            through: vec!["X".to_owned()],
            instance_expr: mk_const("only"),
        }],
        resolved: false,
    };

    let never_eq = |_a: &Expr, _b: &Expr| false;
    det.resolve_diamond(&mut diamond, &never_eq)
        .expect("single path is trivially resolved");
    assert!(diamond.resolved);
}

// ---------------------------------------------------------------------------
// Multiple diamonds
// ---------------------------------------------------------------------------

#[test]
fn test_multiple_diamonds() {
    // A -> B, A -> C, B -> D, C -> D, B -> E, C -> E
    let mut det = DiamondDetector::new();
    det.register_superclass("A", "B");
    det.register_superclass("A", "C");
    det.register_superclass("B", "D");
    det.register_superclass("C", "D");
    det.register_superclass("B", "E");
    det.register_superclass("C", "E");

    // Register instances for both diamond classes.
    det.register_instance(mk_instance("instD", "D", mk_const("d_impl")));
    det.register_instance(mk_instance("instE", "E", mk_const("e_impl")));

    let diamonds = det.detect_diamonds("A");
    assert_eq!(diamonds.len(), 2, "should detect diamonds at D and E");

    let names: Vec<&str> = diamonds.iter().map(|d| d.class_name.as_str()).collect();
    assert!(names.contains(&"D"));
    assert!(names.contains(&"E"));
}

// ---------------------------------------------------------------------------
// Deep hierarchy
// ---------------------------------------------------------------------------

#[test]
fn test_deep_hierarchy_diamond() {
    // A -> B -> C -> F, A -> D -> E -> F
    let mut det = DiamondDetector::new();
    det.register_superclass("A", "B");
    det.register_superclass("B", "C");
    det.register_superclass("C", "F");
    det.register_superclass("A", "D");
    det.register_superclass("D", "E");
    det.register_superclass("E", "F");

    det.register_instance(mk_instance("instF", "F", mk_const("f_impl")));

    let diamonds = det.detect_diamonds("A");
    assert_eq!(diamonds.len(), 1);
    assert_eq!(diamonds[0].class_name, "F");
    // Each instance_path.through stores the full path [A, ..., F].
    // A->B->C->F has 4 nodes, A->D->E->F has 4 nodes.
    assert_eq!(diamonds[0].instance_paths.len(), 2);
    for path in &diamonds[0].instance_paths {
        assert_eq!(
            path.through.len(),
            4,
            "full path should have 4 nodes: start, 2 intermediates, end"
        );
    }
}

// ---------------------------------------------------------------------------
// Instance registration
// ---------------------------------------------------------------------------

#[test]
fn test_register_and_detect_with_instances() {
    let mut det = monad_diamond_detector();

    det.register_instance(mk_instance(
        "instFunctorViaApplicative",
        "Functor",
        mk_const("functor_impl"),
    ));
    det.register_instance(mk_instance(
        "instFunctorViaAlternative",
        "Functor",
        mk_const("functor_impl"),
    ));

    let diamonds = det.detect_diamonds("Monad");
    assert_eq!(diamonds.len(), 1);

    // Path 0 gets instance[0] (functor_impl), path 1 gets instance[1] (functor_impl).
    // Both are structurally equal.
    det.check_diamond_coherence(&diamonds[0])
        .expect("same expression should be coherent");
}

// ---------------------------------------------------------------------------
// Edge case: self-loop
// ---------------------------------------------------------------------------

#[test]
fn test_self_loop_no_crash() {
    let mut det = DiamondDetector::new();
    det.register_superclass("A", "A"); // self-loop

    // Should not infinite-loop; DFS visited set prevents revisiting.
    let ancestors = det.all_ancestors("A");
    assert!(
        ancestors.contains("A"),
        "self-loop means A is its own ancestor"
    );

    let diamonds = det.detect_diamonds("A");
    // No diamond because there is only one path (A -> A), and no instances.
    assert!(diamonds.is_empty());
}
