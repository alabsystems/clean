// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended mutual inductive elaboration (`mutual_inductive_ext`).

use clean_kernel::{BinderInfo, Expr, Level, Name};

use crate::error::ElabError;
use crate::mutual_inductive_ext::{
    check_constructor_targets, check_mutual_positivity, check_parameter_consistency,
    elaborate_mutual_inductive_ext, generate_below, generate_brec, generate_induction_principles,
    generate_recursors, identify_mutual_groups, unify_universe_levels, MutualCtorEntry,
    MutualDepGraph, MutualIndExtBlock, MutualIndExtError, MutualIndExtStats, MutualTypeEntry,
};

// =============================================================================
// Test helpers
// =============================================================================

fn type_0() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

fn prop() -> Expr {
    Expr::sort(Level::zero())
}

fn arrow(domain: Expr, codomain: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, domain, codomain)
}

fn simple_type(name: &str) -> MutualTypeEntry {
    MutualTypeEntry {
        name: Name::from_string(name),
        type_expr: type_0(),
        params: Vec::new(),
        constructors: Vec::new(),
    }
}

fn simple_ctor(name: &str, type_expr: Expr) -> MutualCtorEntry {
    MutualCtorEntry {
        name: Name::from_string(name),
        type_expr,
        fields: Vec::new(),
    }
}

fn make_block(types: Vec<MutualTypeEntry>) -> MutualIndExtBlock {
    MutualIndExtBlock {
        types,
        universe_params: vec![Name::from_string("u")],
    }
}

/// Build the classic Tree/Forest mutual block.
fn tree_forest_block() -> MutualIndExtBlock {
    let tree_const = Expr::const_(Name::from_string("Tree"), vec![]);
    let forest_const = Expr::const_(Name::from_string("Forest"), vec![]);

    let mut tree = simple_type("Tree");
    tree.constructors.push(MutualCtorEntry {
        name: Name::from_string("Tree.node"),
        type_expr: arrow(forest_const.clone(), tree_const.clone()),
        fields: vec![(Name::from_string("children"), forest_const.clone())],
    });

    let mut forest = simple_type("Forest");
    forest
        .constructors
        .push(simple_ctor("Forest.nil", forest_const.clone()));
    forest.constructors.push(MutualCtorEntry {
        name: Name::from_string("Forest.cons"),
        type_expr: arrow(
            tree_const.clone(),
            arrow(forest_const.clone(), forest_const.clone()),
        ),
        fields: vec![
            (Name::from_string("head"), tree_const),
            (Name::from_string("tail"), forest_const),
        ],
    });

    make_block(vec![tree, forest])
}

// =============================================================================
// Grouping tests
// =============================================================================

#[test]
fn test_identify_mutual_groups_independent() {
    let a = simple_type("A");
    let b = simple_type("B");
    let groups = identify_mutual_groups(&[a, b]);
    // No cross-references: each type is its own group.
    assert_eq!(groups.len(), 2);
}

#[test]
fn test_identify_mutual_groups_mutual_pair() {
    let block = tree_forest_block();
    let groups = identify_mutual_groups(&block.types);
    // Tree and Forest reference each other: one group.
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].len(), 2);
}

#[test]
fn test_identify_mutual_groups_single_type() {
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let mut nat = simple_type("Nat");
    nat.constructors
        .push(simple_ctor("Nat.zero", nat_const.clone()));
    nat.constructors
        .push(simple_ctor("Nat.succ", arrow(nat_const.clone(), nat_const)));
    let groups = identify_mutual_groups(&[nat]);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0], vec![0]);
}

#[test]
fn test_identify_mutual_groups_three_way() {
    let a_const = Expr::const_(Name::from_string("A"), vec![]);
    let b_const = Expr::const_(Name::from_string("B"), vec![]);
    let c_const = Expr::const_(Name::from_string("C"), vec![]);

    let mut a = simple_type("A");
    a.constructors
        .push(simple_ctor("A.mk", arrow(b_const.clone(), a_const.clone())));
    let mut b = simple_type("B");
    b.constructors
        .push(simple_ctor("B.mk", arrow(c_const.clone(), b_const.clone())));
    let mut c = simple_type("C");
    c.constructors
        .push(simple_ctor("C.mk", arrow(a_const, c_const)));

    let groups = identify_mutual_groups(&[a, b, c]);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].len(), 3);
}

#[test]
fn test_identify_mutual_groups_empty() {
    let groups: Vec<Vec<usize>> = identify_mutual_groups(&[]);
    assert!(groups.is_empty());
}

// =============================================================================
// Universe unification tests
// =============================================================================

#[test]
fn test_unify_universe_empty() {
    let block = make_block(Vec::new());
    let level = unify_universe_levels(&block).expect("empty should succeed");
    assert_eq!(level, Level::zero());
}

#[test]
fn test_unify_universe_single_type() {
    let block = make_block(vec![simple_type("Nat")]);
    let level = unify_universe_levels(&block).expect("single should succeed");
    assert_eq!(level, Level::succ(Level::zero()));
}

#[test]
fn test_unify_universe_two_same_level() {
    let block = tree_forest_block();
    let level = unify_universe_levels(&block).expect("same level should unify");
    // Both are type_0() = Sort(succ(0)), max is succ(0).
    assert_eq!(
        level,
        Level::max(Level::succ(Level::zero()), Level::succ(Level::zero()))
    );
}

#[test]
fn test_unify_universe_prop_and_type() {
    let mut a = simple_type("A");
    a.type_expr = prop();
    let b = simple_type("B");
    let block = make_block(vec![a, b]);
    let level = unify_universe_levels(&block).expect("prop+type should unify");
    assert_eq!(level, Level::max(Level::zero(), Level::succ(Level::zero())));
}

// =============================================================================
// Parameter consistency tests
// =============================================================================

#[test]
fn test_param_consistency_empty() {
    let block = make_block(Vec::new());
    let n = check_parameter_consistency(&block).expect("empty should pass");
    assert_eq!(n, 0);
}

#[test]
fn test_param_consistency_matching() {
    let mut a = simple_type("A");
    a.params = vec![(Name::from_string("X"), type_0())];
    let mut b = simple_type("B");
    b.params = vec![(Name::from_string("X"), type_0())];
    let block = make_block(vec![a, b]);
    let n = check_parameter_consistency(&block).expect("matching params should pass");
    assert_eq!(n, 1);
}

#[test]
fn test_param_consistency_mismatch() {
    let mut a = simple_type("A");
    a.params = vec![(Name::from_string("X"), type_0())];
    let b = simple_type("B"); // no params
    let block = make_block(vec![a, b]);
    let result = check_parameter_consistency(&block);
    assert!(result.is_err());
}

#[test]
fn test_param_consistency_no_params() {
    let block = tree_forest_block();
    let n = check_parameter_consistency(&block).expect("no params should pass");
    assert_eq!(n, 0);
}

// =============================================================================
// Constructor target tests
// =============================================================================

#[test]
fn test_ctor_targets_valid() {
    let block = tree_forest_block();
    check_constructor_targets(&block).expect("tree/forest targets should be valid");
}

#[test]
fn test_ctor_targets_no_ctors() {
    let block = make_block(vec![simple_type("Empty")]);
    check_constructor_targets(&block).expect("no ctors should pass");
}

#[test]
fn test_ctor_targets_unknown_reference() {
    let unknown_const = Expr::const_(Name::from_string("Unknown"), vec![]);
    let mut a = simple_type("A");
    a.constructors.push(simple_ctor("A.mk", unknown_const));
    let block = make_block(vec![a]);
    let result = check_constructor_targets(&block);
    assert!(result.is_err());
}

// =============================================================================
// Positivity checking tests
// =============================================================================

#[test]
fn test_mutual_positivity_passes() {
    let block = tree_forest_block();
    // tree/forest mutual occurrence is strictly-positive —
    // `Tree.node : Forest → Tree` puts Forest in the
    // strictly-positive position. Wave 107 refines
    // `has_negative_occurrence` to use a real strict-positivity walk
    // (mirroring the kernel `check_strictly_positive_impl` path)
    // instead of the previous "mention anywhere in any Pi domain"
    // over-approximation. The tree/forest classical pair is now
    // accepted as the Lean 4 reference accepts it.
    check_mutual_positivity(&block).expect("tree/forest mutual pair must be strictly positive");
}

#[test]
fn test_mutual_positivity_rejects_inner_arrow_in_one_arm() {
    // Negative for Wave 107: ensure that even though we relaxed the
    // "mentions in any Pi domain" rule, an actual inner-arrow
    // violation in any constructor of any arm is still rejected with
    // a `MutualPositivityViolation`.
    let tree = Name::from_string("Tree");
    let forest = Name::from_string("Forest");
    let tree_const = Expr::const_(tree.clone(), vec![]);
    let forest_const = Expr::const_(forest.clone(), vec![]);
    let bool_const = Expr::const_str("Bool");

    let mut tree_ty = simple_type("Tree");
    tree_ty.constructors.push(MutualCtorEntry {
        name: Name::from_string("Tree.bad"),
        type_expr: arrow(arrow(forest_const.clone(), bool_const), tree_const.clone()),
        fields: Vec::new(),
    });
    let mut forest_ty = simple_type("Forest");
    forest_ty
        .constructors
        .push(simple_ctor("Forest.nil", forest_const));
    let _ = (forest, tree);

    let block = make_block(vec![tree_ty, forest_ty]);
    let err = check_mutual_positivity(&block).expect_err(
        "Tree.bad : (Forest -> Bool) -> Tree must be rejected (Forest under inner arrow)",
    );
    let detail = format!("{err:?}");
    assert!(
        detail.contains("Forest") || detail.contains("MutualPositivityViolation"),
        "the violation must identify the cross-reference as the offender: got {detail}"
    );
}

#[test]
fn test_mutual_positivity_negative_fails() {
    let bad_const = Expr::const_(Name::from_string("Bad"), vec![]);
    let bool_const = Expr::const_str("Bool");
    let mut bad = simple_type("Bad");
    bad.constructors.push(MutualCtorEntry {
        name: Name::from_string("Bad.mk"),
        type_expr: arrow(arrow(bad_const.clone(), bool_const), bad_const),
        fields: Vec::new(),
    });
    let block = make_block(vec![bad]);
    let result = check_mutual_positivity(&block);
    assert!(result.is_err());
}

#[test]
fn test_mutual_positivity_cross_negative() {
    let a_const = Expr::const_(Name::from_string("A"), vec![]);
    let b_const = Expr::const_(Name::from_string("B"), vec![]);
    let bool_const = Expr::const_str("Bool");

    let mut a = simple_type("A");
    // A.mk : (B -> Bool) -> A -- B appears negatively
    a.constructors.push(MutualCtorEntry {
        name: Name::from_string("A.mk"),
        type_expr: arrow(arrow(b_const.clone(), bool_const), a_const),
        fields: Vec::new(),
    });
    let mut b = simple_type("B");
    b.constructors.push(simple_ctor("B.mk", b_const));
    let block = make_block(vec![a, b]);
    let result = check_mutual_positivity(&block);
    assert!(result.is_err());
}

#[test]
fn test_mutual_positivity_no_ctors() {
    let block = make_block(vec![simple_type("Empty")]);
    check_mutual_positivity(&block).expect("no ctors should pass");
}

// =============================================================================
// Dependency graph tests
// =============================================================================

#[test]
fn test_dep_graph_tree_forest() {
    let block = tree_forest_block();
    let graph = MutualDepGraph::build(&block);
    let tree = Name::from_string("Tree");
    let forest = Name::from_string("Forest");
    assert!(graph.depends_on(&tree, &forest));
    assert!(graph.depends_on(&forest, &tree));
    assert_eq!(graph.edge_count(), 2);
}

#[test]
fn test_dep_graph_independent() {
    let block = make_block(vec![simple_type("A"), simple_type("B")]);
    let graph = MutualDepGraph::build(&block);
    assert_eq!(graph.edge_count(), 0);
}

#[test]
fn test_dep_graph_one_direction() {
    let b_const = Expr::const_(Name::from_string("B"), vec![]);
    let a_const = Expr::const_(Name::from_string("A"), vec![]);
    let mut a = simple_type("A");
    a.constructors
        .push(simple_ctor("A.mk", arrow(b_const, a_const)));
    let b = simple_type("B");
    let block = make_block(vec![a, b]);
    let graph = MutualDepGraph::build(&block);
    let a_name = Name::from_string("A");
    let b_name = Name::from_string("B");
    assert!(graph.depends_on(&a_name, &b_name));
    assert!(!graph.depends_on(&b_name, &a_name));
}

#[test]
fn test_dep_graph_deps_of() {
    let block = tree_forest_block();
    let graph = MutualDepGraph::build(&block);
    let tree = Name::from_string("Tree");
    let forest = Name::from_string("Forest");
    let deps = graph.deps_of(&tree).expect("Tree should have deps");
    assert!(deps.contains(&forest));
}

#[test]
fn test_dep_graph_topo_sort_independent() {
    let block = make_block(vec![simple_type("A"), simple_type("B")]);
    let graph = MutualDepGraph::build(&block);
    let sorted = graph
        .topological_sort()
        .expect("should succeed for independent types");
    assert_eq!(sorted.len(), 2);
}

#[test]
fn test_dep_graph_topo_sort_cycle() {
    // Mutual deps form a cycle in the topo sort sense.
    let block = tree_forest_block();
    let graph = MutualDepGraph::build(&block);
    // Tree <-> Forest is a cycle, so topo sort should fail.
    let result = graph.topological_sort();
    assert!(result.is_err());
}

// =============================================================================
// Recursor generation tests
// =============================================================================

#[test]
fn test_generate_recursors_tree_forest() {
    let block = tree_forest_block();
    let recs = generate_recursors(&block);
    assert_eq!(recs.len(), 2);
    assert_eq!(recs[0].name, Name::from_string("Tree.rec"));
    assert_eq!(recs[1].name, Name::from_string("Forest.rec"));
    assert_eq!(recs[0].num_motives, 2);
    assert_eq!(recs[0].num_minors, 3); // 1 + 2 ctors
    assert_eq!(recs[1].num_motives, 2);
    assert_eq!(recs[1].num_minors, 3);
}

#[test]
fn test_generate_recursors_single_type() {
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let mut nat = simple_type("Nat");
    nat.constructors
        .push(simple_ctor("Nat.zero", nat_const.clone()));
    nat.constructors
        .push(simple_ctor("Nat.succ", arrow(nat_const.clone(), nat_const)));
    let block = make_block(vec![nat]);
    let recs = generate_recursors(&block);
    assert_eq!(recs.len(), 1);
    assert_eq!(recs[0].name, Name::from_string("Nat.rec"));
    assert_eq!(recs[0].num_motives, 1);
    assert_eq!(recs[0].num_minors, 2);
}

#[test]
fn test_generate_recursors_no_ctors() {
    let block = make_block(vec![simple_type("Empty")]);
    let recs = generate_recursors(&block);
    assert_eq!(recs.len(), 1);
    assert_eq!(recs[0].num_minors, 0);
}

// =============================================================================
// Induction principle tests
// =============================================================================

#[test]
fn test_generate_induction_tree_forest() {
    let block = tree_forest_block();
    let inds = generate_induction_principles(&block);
    assert_eq!(inds.len(), 2);
    assert_eq!(inds[0].name, Name::from_string("Tree.ind"));
    assert_eq!(inds[1].name, Name::from_string("Forest.ind"));
    assert_eq!(inds[0].target_type, Name::from_string("Tree"));
    assert_eq!(inds[1].target_type, Name::from_string("Forest"));
}

#[test]
fn test_generate_induction_single() {
    let block = make_block(vec![simple_type("Unit")]);
    let inds = generate_induction_principles(&block);
    assert_eq!(inds.len(), 1);
    assert_eq!(inds[0].name, Name::from_string("Unit.ind"));
}

// =============================================================================
// Below / BRec generation tests
// =============================================================================

#[test]
fn test_generate_below_tree_forest() {
    let block = tree_forest_block();
    let below = generate_below(&block);
    assert_eq!(below.len(), 2);
    assert_eq!(below[0].name, Name::from_string("Tree.below"));
    assert_eq!(below[1].name, Name::from_string("Forest.below"));
}

#[test]
fn test_generate_brec_tree_forest() {
    let block = tree_forest_block();
    let brecs = generate_brec(&block);
    assert_eq!(brecs.len(), 2);
    assert_eq!(brecs[0].name, Name::from_string("Tree.brecOn"));
    assert_eq!(brecs[1].name, Name::from_string("Forest.brecOn"));
}

#[test]
fn test_generate_below_with_params() {
    let mut a = simple_type("A");
    a.params = vec![(Name::from_string("X"), type_0())];
    let block = make_block(vec![a]);
    let below = generate_below(&block);
    assert_eq!(below.len(), 1);
    assert_eq!(below[0].name, Name::from_string("A.below"));
}

#[test]
fn test_generate_brec_with_params() {
    let mut a = simple_type("A");
    a.params = vec![
        (Name::from_string("X"), type_0()),
        (Name::from_string("Y"), type_0()),
    ];
    let block = make_block(vec![a]);
    let brecs = generate_brec(&block);
    assert_eq!(brecs.len(), 1);
    assert_eq!(brecs[0].name, Name::from_string("A.brecOn"));
}

// =============================================================================
// Statistics tests
// =============================================================================

#[test]
fn test_stats_default() {
    let stats = MutualIndExtStats::default();
    assert_eq!(stats.mutual_blocks_processed, 0);
    assert_eq!(stats.types_in_block, 0);
    assert_eq!(stats.constructors_checked, 0);
    assert_eq!(stats.recursors_generated, 0);
}

#[test]
fn test_stats_tree_forest() {
    let block = tree_forest_block();
    let result = elaborate_mutual_inductive_ext(&block)
        .expect("Wave 107: tree/forest must elaborate (strictly positive)");
    assert_eq!(result.stats.mutual_blocks_processed, 1);
    assert_eq!(result.stats.types_in_block, 2);
    assert_eq!(result.stats.constructors_checked, 3);
    assert_eq!(result.stats.recursors_generated, 2);
    assert_eq!(result.stats.induction_principles_generated, 2);
    assert_eq!(result.stats.below_specs_generated, 2);
    assert_eq!(result.stats.brec_specs_generated, 2);
    assert_eq!(result.stats.dependency_edges, 2);
}

// =============================================================================
// Full pipeline tests
// =============================================================================

#[test]
fn test_elaborate_tree_forest() {
    let block = tree_forest_block();
    let result = elaborate_mutual_inductive_ext(&block)
        .expect("Wave 107: tree/forest must elaborate (strictly positive)");
    assert_eq!(result.num_params, 0);
    assert_eq!(result.recursors.len(), 2);
    assert_eq!(result.induction_principles.len(), 2);
    assert_eq!(result.below_specs.len(), 2);
    assert_eq!(result.brec_specs.len(), 2);
}

#[test]
fn test_elaborate_single_type() {
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let mut nat = simple_type("Nat");
    nat.constructors
        .push(simple_ctor("Nat.zero", nat_const.clone()));
    nat.constructors
        .push(simple_ctor("Nat.succ", arrow(nat_const.clone(), nat_const)));
    let block = make_block(vec![nat]);
    let result = elaborate_mutual_inductive_ext(&block)
        .expect("Wave 107: Nat.succ : Nat -> Nat is strictly positive and must elaborate");
    assert_eq!(result.recursors.len(), 1);
    assert_eq!(result.induction_principles.len(), 1);
}

#[test]
fn test_elaborate_empty_block_fails() {
    let block = make_block(Vec::new());
    let result = elaborate_mutual_inductive_ext(&block);
    assert!(result.is_err());
}

#[test]
fn test_elaborate_param_mismatch_fails() {
    let mut a = simple_type("A");
    a.params = vec![(Name::from_string("X"), type_0())];
    let b = simple_type("B");
    let block = make_block(vec![a, b]);
    let result = elaborate_mutual_inductive_ext(&block);
    assert!(result.is_err());
}

#[test]
fn test_elaborate_negative_fails() {
    let bad_const = Expr::const_(Name::from_string("Bad"), vec![]);
    let bool_const = Expr::const_str("Bool");
    let mut bad = simple_type("Bad");
    bad.constructors.push(MutualCtorEntry {
        name: Name::from_string("Bad.mk"),
        type_expr: arrow(arrow(bad_const.clone(), bool_const), bad_const),
        fields: Vec::new(),
    });
    let block = make_block(vec![bad]);
    let result = elaborate_mutual_inductive_ext(&block);
    assert!(result.is_err());
}

#[test]
fn test_elaborate_three_way_mutual() {
    let a_const = Expr::const_(Name::from_string("A"), vec![]);
    let b_const = Expr::const_(Name::from_string("B"), vec![]);
    let c_const = Expr::const_(Name::from_string("C"), vec![]);

    let mut a = simple_type("A");
    a.constructors
        .push(simple_ctor("A.mk", arrow(b_const.clone(), a_const.clone())));
    let mut b = simple_type("B");
    b.constructors
        .push(simple_ctor("B.mk", arrow(c_const.clone(), b_const.clone())));
    let mut c = simple_type("C");
    c.constructors
        .push(simple_ctor("C.mk", arrow(a_const, c_const)));

    let block = make_block(vec![a, b, c]);
    let result = elaborate_mutual_inductive_ext(&block)
        .expect("Wave 107: three-way A->B->C->A mutual inductive is strictly positive");
    assert_eq!(result.recursors.len(), 3);
    assert_eq!(result.induction_principles.len(), 3);
    assert_eq!(result.stats.types_in_block, 3);
}

// =============================================================================
// Error type tests
// =============================================================================

#[test]
fn test_error_param_mismatch_display() {
    let err = MutualIndExtError::ParameterMismatch {
        type_name: Name::from_string("B"),
        expected: 2,
        actual: 0,
    };
    let msg = err.to_string();
    assert!(msg.contains("B"));
    assert!(msg.contains("2"));
    assert!(msg.contains("0"));
}

#[test]
fn test_error_positivity_display() {
    let err = MutualIndExtError::MutualPositivityViolation {
        type_name: Name::from_string("A"),
        ctor: Name::from_string("A.mk"),
        offender: Name::from_string("B"),
    };
    let msg = err.to_string();
    assert!(msg.contains("A.mk"));
    assert!(msg.contains("B"));
}

#[test]
fn test_error_cycle_display() {
    let err = MutualIndExtError::DependencyCycle {
        cycle: "A -> B -> A".to_string(),
    };
    let msg = err.to_string();
    assert!(msg.contains("A -> B -> A"));
}

#[test]
fn test_error_converts_to_elab_error() {
    let ext_err = MutualIndExtError::UniverseUnificationFailed {
        detail: "test failure".to_string(),
    };
    let elab_err: ElabError = ext_err.into();
    let msg = elab_err.to_string();
    assert!(msg.contains("test failure"));
}

// =============================================================================
// Clone/Debug/PartialEq trait tests
// =============================================================================

#[test]
fn test_mutual_type_entry_clone() {
    let entry = simple_type("X");
    let cloned = entry.clone();
    assert_eq!(entry.name, cloned.name);
}

#[test]
fn test_mutual_ctor_entry_clone() {
    let entry = simple_ctor("X.mk", type_0());
    let cloned = entry.clone();
    assert_eq!(entry.name, cloned.name);
}

#[test]
fn test_dep_graph_clone() {
    let block = tree_forest_block();
    let graph = MutualDepGraph::build(&block);
    let cloned = graph.clone();
    assert_eq!(graph.edge_count(), cloned.edge_count());
}

#[test]
fn test_recursor_spec_clone() {
    let block = tree_forest_block();
    let recs = generate_recursors(&block);
    let cloned = recs[0].clone();
    assert_eq!(recs[0].name, cloned.name);
}

#[test]
fn test_induction_spec_clone() {
    let block = tree_forest_block();
    let inds = generate_induction_principles(&block);
    let cloned = inds[0].clone();
    assert_eq!(inds[0].name, cloned.name);
}

#[test]
fn test_below_spec_clone() {
    let block = tree_forest_block();
    let below = generate_below(&block);
    let cloned = below[0].clone();
    assert_eq!(below[0].name, cloned.name);
}

#[test]
fn test_brec_spec_clone() {
    let block = tree_forest_block();
    let brecs = generate_brec(&block);
    let cloned = brecs[0].clone();
    assert_eq!(brecs[0].name, cloned.name);
}

#[test]
fn test_stats_equality() {
    let a = MutualIndExtStats::default();
    let b = MutualIndExtStats::default();
    assert_eq!(a, b);
}
