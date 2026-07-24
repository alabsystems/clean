// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended structure inheritance analysis (phase 2).

use crate::structure_cmd::{elaborate_structure, StructDef, StructField};
use crate::structure_inherit::FieldInfo;
use crate::structure_inherit_ext2::{
    has_diamonds, linearize, tree_depth, AnalyzerConfig, DiamondResolution, InheritAnalysisError,
    InheritAnalyzer,
};
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn type_expr() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

fn nat_type(env: &mut Environment) -> Expr {
    if env.get_inductive(&Name::from_string("Nat")).is_none() {
        env.init_nat().ok();
    }
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn simple_field(name: &str, type_: Expr) -> StructField {
    StructField {
        name: Name::from_string(name),
        type_,
        default_value: None,
        binder_info: BinderInfo::Default,
        auto_param: false,
    }
}

fn simple_struct(name: &str, fields: Vec<StructField>) -> StructDef {
    StructDef {
        name: Name::from_string(name),
        universe_params: vec![],
        params: vec![],
        fields,
        parents: vec![],
        is_class: false,
    }
}

fn mk_own_field(name: &str, type_expr: Expr) -> FieldInfo {
    FieldInfo {
        name: Name::from_string(name),
        type_expr,
        default_value: None,
        is_inherited: false,
        source_struct: None,
    }
}

fn register_struct(env: &mut Environment, name: &str, fields: Vec<StructField>) {
    elaborate_structure(&simple_struct(name, fields), env)
        .unwrap_or_else(|e| panic!("failed to elaborate {name}: {e}"));
}

fn register_struct_with_parents(
    env: &mut Environment,
    name: &str,
    fields: Vec<StructField>,
    parents: Vec<String>,
) {
    let def = StructDef {
        name: Name::from_string(name),
        universe_params: vec![],
        params: vec![],
        fields,
        parents: parents.iter().map(|p| Name::from_string(p)).collect(),
        is_class: false,
    };
    elaborate_structure(&def, env).unwrap_or_else(|e| panic!("failed to elaborate {name}: {e}"));
}

// ===========================================================================
// Inheritance tree construction
// ===========================================================================

#[test]
fn test_build_tree_single_struct() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Solo", vec![simple_field("x", nat)]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let tree = analyzer
        .build_tree(&Name::from_string("Solo"))
        .expect("build_tree");
    assert_eq!(tree.total_nodes, 1);
    assert_eq!(tree.max_depth, 0);
    assert_eq!(tree.max_breadth, 1);
}

#[test]
fn test_build_tree_linear_chain() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("a", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "B",
        vec![simple_field("b", nat.clone())],
        vec!["A".into()],
    );
    register_struct_with_parents(
        &mut env,
        "C",
        vec![simple_field("c", nat)],
        vec!["B".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let tree = analyzer
        .build_tree(&Name::from_string("C"))
        .expect("build_tree");
    assert!(tree.total_nodes >= 3, "should have at least C, B, A");
    assert!(tree.max_depth >= 2, "depth should be at least 2");
}

#[test]
fn test_build_tree_wide_hierarchy() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "P1", vec![simple_field("p1", nat.clone())]);
    register_struct(&mut env, "P2", vec![simple_field("p2", nat.clone())]);
    register_struct(&mut env, "P3", vec![simple_field("p3", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Wide",
        vec![simple_field("w", nat)],
        vec!["P1".into(), "P2".into(), "P3".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let tree = analyzer
        .build_tree(&Name::from_string("Wide"))
        .expect("build_tree");
    assert!(tree.total_nodes >= 4);
    assert!(tree.max_breadth >= 1);
}

#[test]
fn test_build_tree_nonexistent_struct() {
    let env = Environment::new();
    let analyzer = InheritAnalyzer::with_defaults(&env);
    let tree = analyzer.build_tree(&Name::from_string("Ghost"));
    // Should succeed with a single node (no parents found)
    assert!(tree.is_ok());
    assert_eq!(tree.unwrap().total_nodes, 1);
}

#[test]
fn test_build_tree_depth_limit() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "D0", vec![simple_field("f0", nat.clone())]);
    for i in 1..=5 {
        register_struct_with_parents(
            &mut env,
            &format!("D{i}"),
            vec![simple_field(&format!("f{i}"), nat.clone())],
            vec![format!("D{}", i - 1)],
        );
    }

    let config = AnalyzerConfig { max_depth: 3 };
    let analyzer = InheritAnalyzer::new(&env, config);
    let result = analyzer.build_tree(&Name::from_string("D5"));
    assert!(
        matches!(result, Err(InheritAnalysisError::DepthLimitExceeded { .. })),
        "should fail when depth limit is exceeded"
    );
}

// ===========================================================================
// Field resolution
// ===========================================================================

#[test]
fn test_resolve_fields_own_only() {
    let env = Environment::new();
    let analyzer = InheritAnalyzer::with_defaults(&env);
    let own = vec![
        mk_own_field("x", type_expr()),
        mk_own_field("y", type_expr()),
    ];
    let result = analyzer
        .resolve_fields(&Name::from_string("S"), &own)
        .expect("resolve");
    assert_eq!(result.len(), 2);
    assert!(result.iter().all(|f| !f.is_override));
}

#[test]
fn test_resolve_fields_with_inheritance() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let own = vec![mk_own_field("y", nat)];
    let _parents = [Name::from_string("Base")];
    // Need to register child to have it in env, but we test resolve_fields independently
    let result = analyzer.resolve_fields(&Name::from_string("Child"), &own);
    // Should succeed even without Child in env (it resolves parents from env)
    assert!(result.is_ok());
}

#[test]
fn test_resolve_fields_override_detection() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Child",
        vec![simple_field("x", nat.clone())],
        vec!["Base".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let own = vec![mk_own_field("x", nat)];
    let result = analyzer
        .resolve_fields(&Name::from_string("Child"), &own)
        .expect("resolve");
    let own_x = result
        .iter()
        .find(|f| f.name == Name::from_string("x") && f.is_override);
    assert!(own_x.is_some(), "own field x should be marked as override");
}

#[test]
fn test_resolve_fields_chain_tracking() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Mid",
        vec![simple_field("m", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Leaf",
        vec![simple_field("l", nat)],
        vec!["Mid".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let result = analyzer
        .resolve_fields(&Name::from_string("Leaf"), &[])
        .expect("resolve");
    // Fields should have chain info
    for field in &result {
        assert!(!field.chain.is_empty(), "chain should not be empty");
    }
}

// ===========================================================================
// Override analysis
// ===========================================================================

#[test]
fn test_analyze_overrides_none() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let own = vec![mk_own_field("y", nat)]; // different field name
    let parents = vec![Name::from_string("Base")];
    let overrides = analyzer
        .analyze_overrides(&Name::from_string("Child"), &own, &parents)
        .expect("analyze");
    assert!(overrides.is_empty(), "no overrides expected");
}

#[test]
fn test_analyze_overrides_compatible() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let own = vec![mk_own_field("x", nat)]; // same type
    let parents = vec![Name::from_string("Base")];
    let overrides = analyzer
        .analyze_overrides(&Name::from_string("Child"), &own, &parents)
        .expect("analyze");
    assert_eq!(overrides.len(), 1);
    assert!(
        overrides[0].is_compatible,
        "same-type override should be compatible"
    );
}

#[test]
fn test_analyze_overrides_incompatible() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat)]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let own = vec![mk_own_field("x", type_expr())]; // different type
    let parents = vec![Name::from_string("Base")];
    let overrides = analyzer
        .analyze_overrides(&Name::from_string("Child"), &own, &parents)
        .expect("analyze");
    assert_eq!(overrides.len(), 1);
    assert!(
        !overrides[0].is_compatible,
        "different-type override should be incompatible"
    );
}

#[test]
fn test_analyze_overrides_multiple_parents() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("x", nat.clone())]);
    register_struct(&mut env, "B", vec![simple_field("y", nat.clone())]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let own = vec![mk_own_field("x", nat.clone()), mk_own_field("y", nat)];
    let parents = vec![Name::from_string("A"), Name::from_string("B")];
    let overrides = analyzer
        .analyze_overrides(&Name::from_string("Child"), &own, &parents)
        .expect("analyze");
    assert_eq!(
        overrides.len(),
        2,
        "should detect overrides from both parents"
    );
}

#[test]
fn test_analyze_overrides_unknown_parent() {
    let env = Environment::new();
    let analyzer = InheritAnalyzer::with_defaults(&env);
    let own = vec![mk_own_field("x", type_expr())];
    let parents = vec![Name::from_string("NonExistent")];
    let overrides = analyzer
        .analyze_overrides(&Name::from_string("Child"), &own, &parents)
        .expect("analyze");
    assert!(
        overrides.is_empty(),
        "unknown parent should yield no overrides"
    );
}

// ===========================================================================
// Diamond detection
// ===========================================================================

#[test]
fn test_detect_diamonds_none() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("a", nat.clone())]);
    register_struct(&mut env, "B", vec![simple_field("b", nat)]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let diamonds = analyzer.detect_diamonds(&[Name::from_string("A"), Name::from_string("B")]);
    assert!(
        diamonds.is_empty(),
        "independent parents should have no diamonds"
    );
}

#[test]
fn test_detect_diamonds_basic() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat)],
        vec!["Root".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let parents = vec![Name::from_string("Left"), Name::from_string("Right")];
    let diamonds = analyzer.detect_diamonds(&parents);
    assert!(!diamonds.is_empty(), "should detect diamond through Root");
}

#[test]
fn test_detect_diamonds_resolution_deduplicate() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat)],
        vec!["Root".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let diamonds =
        analyzer.detect_diamonds(&[Name::from_string("Left"), Name::from_string("Right")]);
    let root_diamond = diamonds
        .iter()
        .find(|d| d.ancestor == Name::from_string("Root"));
    assert!(root_diamond.is_some());
    assert_eq!(
        root_diamond.unwrap().resolution,
        DiamondResolution::Deduplicate
    );
}

#[test]
fn test_detect_diamonds_single_parent() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Only", vec![simple_field("o", nat)]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let diamonds = analyzer.detect_diamonds(&[Name::from_string("Only")]);
    assert!(diamonds.is_empty(), "single parent cannot form diamond");
}

#[test]
fn test_detect_diamonds_shared_fields_recorded() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(
        &mut env,
        "Root",
        vec![
            simple_field("r", nat.clone()),
            simple_field("s", nat.clone()),
        ],
    );
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat)],
        vec!["Root".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let diamonds =
        analyzer.detect_diamonds(&[Name::from_string("Left"), Name::from_string("Right")]);
    let root_diamond = diamonds
        .iter()
        .find(|d| d.ancestor == Name::from_string("Root"));
    assert!(root_diamond.is_some());
    assert!(!root_diamond.unwrap().shared_fields.is_empty());
}

// ===========================================================================
// C3 linearization
// ===========================================================================

#[test]
fn test_c3_single_struct() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Solo", vec![simple_field("x", nat)]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let lin = analyzer
        .c3_linearize(&Name::from_string("Solo"))
        .expect("linearize");
    assert_eq!(lin, vec![Name::from_string("Solo")]);
}

#[test]
fn test_c3_linear_chain() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("a", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "B",
        vec![simple_field("b", nat.clone())],
        vec!["A".into()],
    );
    register_struct_with_parents(
        &mut env,
        "C",
        vec![simple_field("c", nat)],
        vec!["B".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let lin = analyzer
        .c3_linearize(&Name::from_string("C"))
        .expect("linearize");
    // C should come first, then B, then A
    assert_eq!(lin[0], Name::from_string("C"));
    let b_pos = lin.iter().position(|n| *n == Name::from_string("B"));
    let a_pos = lin.iter().position(|n| *n == Name::from_string("A"));
    assert!(b_pos.is_some() && a_pos.is_some());
    assert!(b_pos.unwrap() < a_pos.unwrap(), "B should come before A");
}

#[test]
fn test_c3_preserves_parent_order() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "X", vec![simple_field("x", nat.clone())]);
    register_struct(&mut env, "Y", vec![simple_field("y", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Z",
        vec![simple_field("z", nat)],
        vec!["X".into(), "Y".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let lin = analyzer
        .c3_linearize(&Name::from_string("Z"))
        .expect("linearize");
    assert_eq!(lin[0], Name::from_string("Z"));
    let x_pos = lin.iter().position(|n| *n == Name::from_string("X"));
    let y_pos = lin.iter().position(|n| *n == Name::from_string("Y"));
    assert!(x_pos.is_some() && y_pos.is_some());
    assert!(
        x_pos.unwrap() < y_pos.unwrap(),
        "X should come before Y (parent order)"
    );
}

#[test]
fn test_c3_no_duplicates() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Diamond",
        vec![simple_field("d", nat)],
        vec!["Left".into(), "Right".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let lin = analyzer
        .c3_linearize(&Name::from_string("Diamond"))
        .expect("linearize");
    let mut seen = HashSet::new();
    for name in &lin {
        assert!(
            seen.insert(name.clone()),
            "duplicate in linearization: {name}"
        );
    }
}

#[test]
fn test_c3_nonexistent_struct() {
    let env = Environment::new();
    let analyzer = InheritAnalyzer::with_defaults(&env);
    let lin = analyzer
        .c3_linearize(&Name::from_string("Missing"))
        .expect("linearize");
    assert_eq!(lin, vec![Name::from_string("Missing")]);
}

// ===========================================================================
// Statistics
// ===========================================================================

#[test]
fn test_stats_empty() {
    let mut env = Environment::new();
    let _nat = nat_type(&mut env);
    register_struct(&mut env, "Empty", vec![]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let stats = analyzer
        .compute_stats(&Name::from_string("Empty"), &[], &[])
        .expect("stats");
    assert_eq!(stats.own_fields, 0);
    assert_eq!(stats.override_count, 0);
    assert_eq!(stats.diamond_count, 0);
}

#[test]
fn test_stats_own_fields_only() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "S", vec![simple_field("x", nat.clone())]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let own = vec![mk_own_field("a", nat.clone()), mk_own_field("b", nat)];
    let stats = analyzer
        .compute_stats(&Name::from_string("S"), &own, &[])
        .expect("stats");
    assert_eq!(stats.own_fields, 2);
    assert_eq!(stats.total_structures, 1);
}

#[test]
fn test_stats_with_inheritance() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Child",
        vec![simple_field("y", nat.clone())],
        vec!["Base".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let own = vec![mk_own_field("y", nat)];
    let parents = vec![Name::from_string("Base")];
    let stats = analyzer
        .compute_stats(&Name::from_string("Child"), &own, &parents)
        .expect("stats");
    assert!(stats.total_structures >= 2);
    assert!(stats.inherited_fields >= 1);
}

#[test]
fn test_stats_with_diamonds() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat.clone())],
        vec!["Root".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let parents = vec![Name::from_string("Left"), Name::from_string("Right")];
    let stats = analyzer
        .compute_stats(&Name::from_string("D"), &[], &parents)
        .expect("stats");
    assert!(stats.diamond_count >= 1);
}

#[test]
fn test_stats_override_count() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(
        &mut env,
        "Base",
        vec![
            simple_field("x", nat.clone()),
            simple_field("y", nat.clone()),
        ],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let own = vec![mk_own_field("x", nat.clone()), mk_own_field("y", nat)];
    let parents = vec![Name::from_string("Base")];
    let stats = analyzer
        .compute_stats(&Name::from_string("Child"), &own, &parents)
        .expect("stats");
    assert_eq!(stats.override_count, 2);
}

// ===========================================================================
// DOT visualization
// ===========================================================================

#[test]
fn test_dot_single_node() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Solo", vec![simple_field("x", nat)]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let dot = analyzer.to_dot(&Name::from_string("Solo")).expect("to_dot");
    assert!(dot.contains("digraph inheritance"));
    assert!(dot.contains("Solo"));
    assert!(dot.contains("rankdir=BT"));
}

#[test]
fn test_dot_with_edges() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Parent", vec![simple_field("p", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Child",
        vec![simple_field("c", nat)],
        vec!["Parent".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let dot = analyzer
        .to_dot(&Name::from_string("Child"))
        .expect("to_dot");
    assert!(dot.contains("->"), "should have edges");
    assert!(dot.contains("Parent"));
    assert!(dot.contains("Child"));
}

#[test]
fn test_dot_contains_fields() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Struct", vec![simple_field("field_a", nat)]);

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let dot = analyzer
        .to_dot(&Name::from_string("Struct"))
        .expect("to_dot");
    assert!(
        dot.contains("field_a"),
        "DOT output should contain field names"
    );
}

// ===========================================================================
// Convenience functions
// ===========================================================================

#[test]
fn test_has_diamonds_false() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("a", nat.clone())]);
    register_struct(&mut env, "B", vec![simple_field("b", nat)]);

    assert!(!has_diamonds(
        &[Name::from_string("A"), Name::from_string("B")],
        &env
    ));
}

#[test]
fn test_has_diamonds_true() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat)],
        vec!["Root".into()],
    );

    assert!(has_diamonds(
        &[Name::from_string("Left"), Name::from_string("Right")],
        &env
    ));
}

#[test]
fn test_linearize_simple() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("a", nat)]);

    let lin = linearize(&Name::from_string("A"), &env).expect("linearize");
    assert_eq!(lin, vec![Name::from_string("A")]);
}

#[test]
fn test_tree_depth_no_parents() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Flat", vec![simple_field("f", nat)]);

    let depth = tree_depth(&Name::from_string("Flat"), &env).expect("depth");
    assert_eq!(depth, 0);
}

#[test]
fn test_tree_depth_chain() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("a", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "B",
        vec![simple_field("b", nat.clone())],
        vec!["A".into()],
    );
    register_struct_with_parents(
        &mut env,
        "C",
        vec![simple_field("c", nat)],
        vec!["B".into()],
    );

    let depth = tree_depth(&Name::from_string("C"), &env).expect("depth");
    assert!(depth >= 2, "chain A->B->C should have depth >= 2");
}

// ===========================================================================
// Edge cases and error paths
// ===========================================================================

#[test]
fn test_analyzer_config_default() {
    let config = AnalyzerConfig::default();
    assert_eq!(config.max_depth, 64);
}

#[test]
fn test_empty_parents_list() {
    let env = Environment::new();
    let analyzer = InheritAnalyzer::with_defaults(&env);
    let diamonds = analyzer.detect_diamonds(&[]);
    assert!(diamonds.is_empty());
}

#[test]
fn test_resolve_fields_empty_own() {
    let env = Environment::new();
    let analyzer = InheritAnalyzer::with_defaults(&env);
    let result = analyzer
        .resolve_fields(&Name::from_string("Empty"), &[])
        .expect("resolve");
    assert!(result.is_empty());
}

// Extra import needed for the no-duplicates test
use std::collections::HashSet;

// ===========================================================================
// Additional coverage
// ===========================================================================

#[test]
fn test_build_tree_diamond_node_count() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Diamond",
        vec![simple_field("d", nat)],
        vec!["Left".into(), "Right".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let tree = analyzer
        .build_tree(&Name::from_string("Diamond"))
        .expect("build_tree");
    // Diamond, Left, Right, Root = 4 nodes (Root only counted once)
    assert!(tree.total_nodes >= 4);
}

#[test]
fn test_c3_diamond_linearization() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Dia",
        vec![simple_field("d", nat)],
        vec!["Left".into(), "Right".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let lin = analyzer
        .c3_linearize(&Name::from_string("Dia"))
        .expect("linearize");
    // Dia should be first
    assert_eq!(lin[0], Name::from_string("Dia"));
    // Root should be last (common ancestor)
    let root_pos = lin.iter().position(|n| *n == Name::from_string("Root"));
    let left_pos = lin.iter().position(|n| *n == Name::from_string("Left"));
    let right_pos = lin.iter().position(|n| *n == Name::from_string("Right"));
    assert!(root_pos.is_some());
    assert!(
        left_pos.is_some() && left_pos.unwrap() < root_pos.unwrap(),
        "Left before Root"
    );
    assert!(
        right_pos.is_some() && right_pos.unwrap() < root_pos.unwrap(),
        "Right before Root"
    );
}

#[test]
fn test_dot_diamond_graph() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Dia",
        vec![simple_field("d", nat)],
        vec!["Left".into(), "Right".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let dot = analyzer.to_dot(&Name::from_string("Dia")).expect("to_dot");
    assert!(dot.contains("Root"));
    assert!(dot.contains("Left"));
    assert!(dot.contains("Right"));
    assert!(dot.contains("Dia"));
    // Diamond should produce multiple edges
    let edge_count = dot.matches("->").count();
    assert!(
        edge_count >= 3,
        "diamond graph should have at least 3 edges"
    );
}

#[test]
fn test_stats_depth_chain() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "L0", vec![simple_field("f0", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "L1",
        vec![simple_field("f1", nat.clone())],
        vec!["L0".into()],
    );
    register_struct_with_parents(
        &mut env,
        "L2",
        vec![simple_field("f2", nat.clone())],
        vec!["L1".into()],
    );
    register_struct_with_parents(
        &mut env,
        "L3",
        vec![simple_field("f3", nat)],
        vec!["L2".into()],
    );

    let analyzer = InheritAnalyzer::with_defaults(&env);
    let stats = analyzer
        .compute_stats(&Name::from_string("L3"), &[], &[Name::from_string("L2")])
        .expect("stats");
    assert!(
        stats.max_depth >= 3,
        "chain L0->L1->L2->L3 should have depth >= 3"
    );
}

#[test]
fn test_linearize_chain() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("a", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "B",
        vec![simple_field("b", nat)],
        vec!["A".into()],
    );

    let lin = linearize(&Name::from_string("B"), &env).expect("linearize");
    assert_eq!(lin[0], Name::from_string("B"));
    assert!(lin.contains(&Name::from_string("A")));
}

#[test]
fn test_has_diamonds_empty_parents() {
    let env = Environment::new();
    assert!(!has_diamonds(&[], &env));
}

#[test]
fn test_tree_depth_nonexistent() {
    let env = Environment::new();
    let depth = tree_depth(&Name::from_string("Ghost"), &env).expect("depth");
    assert_eq!(depth, 0);
}
