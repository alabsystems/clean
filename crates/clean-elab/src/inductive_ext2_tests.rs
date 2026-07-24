// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended inductive type analysis (`inductive_ext2`).

use clean_kernel::{BinderInfo, Expr, Level, Name};

use crate::inductive_ext::{ConstructorSpec, InductiveSpec, MutualInductiveSpec};
use crate::inductive_ext2::{
    analyze_inductive, analyze_mutual_inductive, analyze_universe_constraints,
    classify_all_constructors, classify_constructor, compute_size_metrics,
    detect_mutual_recursion_scheme, detect_recursion_scheme, predict_eliminator_shape,
    predict_pattern_match_info, summarize_positivity, EliminatorShape, IndexPattern,
    InductiveAnalysisError, ParameterPositivity, RecursionScheme,
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

fn simple_spec(name: &str, type_: Expr) -> InductiveSpec {
    InductiveSpec {
        name: Name::from_string(name),
        params: Vec::new(),
        indices: Vec::new(),
        type_,
        ctors: Vec::new(),
        is_recursive: false,
        is_nested: false,
    }
}

fn nullary_ctor(name: &str, type_: Expr) -> ConstructorSpec {
    ConstructorSpec {
        name: Name::from_string(name),
        fields: Vec::new(),
        type_,
    }
}

fn unary_ctor(
    name: &str,
    field_name: &str,
    field_ty: Expr,
    is_recursive: bool,
    type_: Expr,
) -> ConstructorSpec {
    ConstructorSpec {
        name: Name::from_string(name),
        fields: vec![(Name::from_string(field_name), field_ty, is_recursive)],
        type_,
    }
}

// =============================================================================
// Constructor classification tests
// =============================================================================

#[test]
fn test_classify_nullary_constructor() {
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let ctor = nullary_ctor("Nat.zero", nat_const);
    let cls = classify_constructor(&ctor, &nat);
    assert_eq!(cls.arity, 0);
    assert_eq!(cls.recursive_field_count, 0);
    assert_eq!(cls.higher_order_recursive_count, 0);
    assert!(cls.recursive_field_indices.is_empty());
}

#[test]
fn test_classify_unary_recursive_constructor() {
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let ctor = unary_ctor(
        "Nat.succ",
        "pred",
        nat_const.clone(),
        true,
        arrow(nat_const.clone(), nat_const),
    );
    let cls = classify_constructor(&ctor, &nat);
    assert_eq!(cls.arity, 1);
    assert_eq!(cls.recursive_field_count, 1);
    assert_eq!(cls.recursive_field_indices, vec![0]);
}

#[test]
fn test_classify_binary_recursive_constructor() {
    let tree = Name::from_string("Tree");
    let tree_const = Expr::const_(tree.clone(), vec![]);
    let nat_const = Expr::const_str("Nat");
    let ctor = ConstructorSpec {
        name: Name::from_string("Tree.node"),
        fields: vec![
            (Name::from_string("val"), nat_const, false),
            (Name::from_string("left"), tree_const.clone(), true),
            (Name::from_string("right"), tree_const.clone(), true),
        ],
        type_: arrow(
            Expr::const_str("Nat"),
            arrow(tree_const.clone(), arrow(tree_const.clone(), tree_const)),
        ),
    };
    let cls = classify_constructor(&ctor, &tree);
    assert_eq!(cls.arity, 3);
    assert_eq!(cls.recursive_field_count, 2);
    assert_eq!(cls.recursive_field_indices, vec![1, 2]);
}

#[test]
fn test_classify_all_constructors_nat() {
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let mut spec = simple_spec("Nat", type_0());
    spec.is_recursive = true;
    spec.ctors.push(nullary_ctor("Nat.zero", nat_const.clone()));
    spec.ctors.push(unary_ctor(
        "Nat.succ",
        "pred",
        nat_const.clone(),
        true,
        arrow(nat_const.clone(), nat_const),
    ));

    let classifications = classify_all_constructors(&spec);
    assert_eq!(classifications.len(), 2);
    assert_eq!(classifications[0].arity, 0);
    assert_eq!(classifications[1].arity, 1);
    assert_eq!(classifications[1].recursive_field_count, 1);
}

#[test]
fn test_classify_constructor_name_preserved() {
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let ctor = nullary_ctor("Nat.zero", nat_const);
    let cls = classify_constructor(&ctor, &nat);
    assert_eq!(cls.name, Name::from_string("Nat.zero"));
}

#[test]
fn test_classify_no_index_pattern() {
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let ctor = nullary_ctor("Nat.zero", nat_const);
    let cls = classify_constructor(&ctor, &nat);
    assert_eq!(cls.index_pattern, IndexPattern::None);
}

// =============================================================================
// Recursion scheme detection tests
// =============================================================================

#[test]
fn test_scheme_non_recursive_empty() {
    let spec = simple_spec("Empty", type_0());
    assert_eq!(
        detect_recursion_scheme(&spec),
        RecursionScheme::NonRecursive
    );
}

#[test]
fn test_scheme_non_recursive_bool() {
    let mut spec = simple_spec("Bool", type_0());
    spec.ctors
        .push(nullary_ctor("Bool.true", Expr::const_str("Bool")));
    spec.ctors
        .push(nullary_ctor("Bool.false", Expr::const_str("Bool")));
    assert_eq!(
        detect_recursion_scheme(&spec),
        RecursionScheme::NonRecursive
    );
}

#[test]
fn test_scheme_nat_like() {
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let mut spec = simple_spec("Nat", type_0());
    spec.is_recursive = true;
    spec.ctors.push(nullary_ctor("Nat.zero", nat_const.clone()));
    spec.ctors.push(unary_ctor(
        "Nat.succ",
        "pred",
        nat_const.clone(),
        true,
        arrow(nat_const.clone(), nat_const),
    ));
    assert_eq!(detect_recursion_scheme(&spec), RecursionScheme::NatLike);
}

#[test]
fn test_scheme_list_like() {
    let list = Name::from_string("List");
    let list_const = Expr::const_(list.clone(), vec![]);
    let a_const = Expr::const_str("A");
    let mut spec = simple_spec("List", type_0());
    spec.is_recursive = true;
    spec.ctors
        .push(nullary_ctor("List.nil", list_const.clone()));
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("List.cons"),
        fields: vec![
            (Name::from_string("head"), a_const, false),
            (Name::from_string("tail"), list_const.clone(), true),
        ],
        type_: arrow(Expr::const_str("A"), arrow(list_const.clone(), list_const)),
    });
    assert_eq!(detect_recursion_scheme(&spec), RecursionScheme::ListLike);
}

#[test]
fn test_scheme_tree_like() {
    let tree = Name::from_string("Tree");
    let tree_const = Expr::const_(tree.clone(), vec![]);
    let mut spec = simple_spec("Tree", type_0());
    spec.is_recursive = true;
    spec.ctors
        .push(nullary_ctor("Tree.leaf", tree_const.clone()));
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Tree.node"),
        fields: vec![
            (Name::from_string("left"), tree_const.clone(), true),
            (Name::from_string("right"), tree_const.clone(), true),
        ],
        type_: arrow(tree_const.clone(), arrow(tree_const.clone(), tree_const)),
    });
    assert_eq!(detect_recursion_scheme(&spec), RecursionScheme::TreeLike);
}

#[test]
fn test_scheme_nested() {
    let mut spec = simple_spec("Rose", type_0());
    spec.is_recursive = true;
    spec.is_nested = true;
    assert_eq!(detect_recursion_scheme(&spec), RecursionScheme::Nested);
}

#[test]
fn test_scheme_general_recursive() {
    // Multiple base cases + one recursive step doesn't match any specific pattern
    let g = Name::from_string("G");
    let g_const = Expr::const_(g.clone(), vec![]);
    let mut spec = simple_spec("G", type_0());
    spec.is_recursive = true;
    spec.ctors.push(nullary_ctor("G.base1", g_const.clone()));
    spec.ctors.push(nullary_ctor("G.base2", g_const.clone()));
    spec.ctors.push(unary_ctor(
        "G.step",
        "prev",
        g_const.clone(),
        true,
        arrow(g_const.clone(), g_const),
    ));
    assert_eq!(
        detect_recursion_scheme(&spec),
        RecursionScheme::GeneralRecursive
    );
}

// =============================================================================
// Mutual recursion scheme detection
// =============================================================================

#[test]
fn test_mutual_scheme_single() {
    let spec = MutualInductiveSpec {
        inductives: vec![simple_spec("Unit", type_0())],
        universe_params: Vec::new(),
    };
    let schemes = detect_mutual_recursion_scheme(&spec);
    assert_eq!(schemes.len(), 1);
    assert_eq!(schemes[0].1, RecursionScheme::NonRecursive);
}

#[test]
fn test_mutual_scheme_multiple_types() {
    let spec = MutualInductiveSpec {
        inductives: vec![simple_spec("A", type_0()), simple_spec("B", type_0())],
        universe_params: Vec::new(),
    };
    let schemes = detect_mutual_recursion_scheme(&spec);
    assert_eq!(schemes.len(), 2);
    assert_eq!(schemes[0].1, RecursionScheme::Mutual);
    assert_eq!(schemes[1].1, RecursionScheme::Mutual);
}

// =============================================================================
// Universe constraint analysis tests
// =============================================================================

#[test]
fn test_universe_prop_type() {
    let spec = simple_spec("True", prop());
    let summary = analyze_universe_constraints(&spec);
    assert!(summary.is_prop);
    assert!(!summary.has_type_valued_fields);
    assert!(summary.is_small_eliminator);
}

#[test]
fn test_universe_type_type() {
    let mut spec = simple_spec("Wrap", type_0());
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Wrap.mk"),
        fields: vec![(Name::from_string("val"), type_0(), false)],
        type_: arrow(type_0(), Expr::const_str("Wrap")),
    });
    let summary = analyze_universe_constraints(&spec);
    assert!(!summary.is_prop);
    assert!(summary.has_type_valued_fields);
    assert!(!summary.is_small_eliminator);
}

#[test]
fn test_universe_prop_with_no_ctors_is_small() {
    let spec = simple_spec("EmptyProp", prop());
    let summary = analyze_universe_constraints(&spec);
    assert!(summary.is_small_eliminator);
}

#[test]
fn test_universe_prop_with_one_ctor_no_type_fields() {
    let mut spec = simple_spec("True", prop());
    spec.ctors.push(nullary_ctor("True.intro", prop()));
    let summary = analyze_universe_constraints(&spec);
    assert!(summary.is_small_eliminator);
}

#[test]
fn test_universe_param_count() {
    let u_level = Level::param(Name::from_string("u"));
    let type_u = Expr::sort(Level::succ(u_level));
    let mut spec = simple_spec("Parametric", type_0());
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Parametric.mk"),
        fields: vec![(Name::from_string("val"), type_u, false)],
        type_: Expr::const_str("Parametric"),
    });
    let summary = analyze_universe_constraints(&spec);
    assert!(summary.universe_param_count >= 1);
}

// =============================================================================
// Eliminator shape prediction tests
// =============================================================================

#[test]
fn test_eliminator_empty_type() {
    let spec = simple_spec("Empty", type_0());
    let shape = predict_eliminator_shape(&spec);
    assert_eq!(shape.motive_count, 1);
    assert_eq!(shape.minor_premise_count, 0);
    assert_eq!(shape.target_count, 1);
    assert!(shape.is_large_eliminator);
}

#[test]
fn test_eliminator_bool() {
    let mut spec = simple_spec("Bool", type_0());
    spec.ctors
        .push(nullary_ctor("Bool.true", Expr::const_str("Bool")));
    spec.ctors
        .push(nullary_ctor("Bool.false", Expr::const_str("Bool")));
    let shape = predict_eliminator_shape(&spec);
    assert_eq!(shape.minor_premise_count, 2);
    assert!(shape.is_large_eliminator);
}

#[test]
fn test_eliminator_prop_small() {
    let mut spec = simple_spec("True", prop());
    spec.ctors
        .push(nullary_ctor("True.intro", Expr::const_str("True")));
    let shape = predict_eliminator_shape(&spec);
    assert!(
        shape.is_large_eliminator,
        "Prop with 1 ctor is large eliminator"
    );
}

#[test]
fn test_eliminator_prop_multiple_ctors() {
    let mut spec = simple_spec("Or", prop());
    spec.ctors
        .push(nullary_ctor("Or.inl", Expr::const_str("Or")));
    spec.ctors
        .push(nullary_ctor("Or.inr", Expr::const_str("Or")));
    let shape = predict_eliminator_shape(&spec);
    assert!(
        !shape.is_large_eliminator,
        "Prop with 2+ ctors is small eliminator"
    );
}

#[test]
fn test_eliminator_total_binder_count() {
    let mut spec = simple_spec("Vec", type_0());
    spec.params = vec![(Name::from_string("A"), type_0())];
    spec.indices = vec![(Name::from_string("n"), Expr::const_str("Nat"))];
    spec.ctors
        .push(nullary_ctor("Vec.nil", Expr::const_str("Vec")));
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Vec.cons"),
        fields: vec![(Name::from_string("head"), Expr::const_str("A"), false)],
        type_: Expr::const_str("Vec"),
    });
    let shape = predict_eliminator_shape(&spec);
    // 1 param + 1 motive + 2 minor + 1 index + 1 target = 6
    assert_eq!(shape.total_binder_count, 6);
}

// =============================================================================
// Size metrics tests
// =============================================================================

#[test]
fn test_size_empty() {
    let spec = simple_spec("Empty", type_0());
    let m = compute_size_metrics(&spec);
    assert_eq!(m.constructor_count, 0);
    assert_eq!(m.total_field_count, 0);
    assert_eq!(m.max_constructor_arity, 0);
    assert_eq!(m.max_field_depth, 0);
}

#[test]
fn test_size_nat() {
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let mut spec = simple_spec("Nat", type_0());
    spec.is_recursive = true;
    spec.ctors.push(nullary_ctor("Nat.zero", nat_const.clone()));
    spec.ctors.push(unary_ctor(
        "Nat.succ",
        "pred",
        nat_const.clone(),
        true,
        arrow(nat_const.clone(), nat_const),
    ));
    let m = compute_size_metrics(&spec);
    assert_eq!(m.constructor_count, 2);
    assert_eq!(m.total_field_count, 1);
    assert_eq!(m.max_constructor_arity, 1);
    assert_eq!(m.total_recursive_fields, 1);
}

#[test]
fn test_size_with_params_and_indices() {
    let mut spec = simple_spec("Vec", type_0());
    spec.params = vec![(Name::from_string("A"), type_0())];
    spec.indices = vec![(Name::from_string("n"), Expr::const_str("Nat"))];
    let m = compute_size_metrics(&spec);
    assert_eq!(m.param_count, 1);
    assert_eq!(m.index_count, 1);
}

#[test]
fn test_size_field_depth() {
    // Field type: (A -> B -> C) has depth 2
    let deep_field = arrow(
        Expr::const_str("A"),
        arrow(Expr::const_str("B"), Expr::const_str("C")),
    );
    let mut spec = simple_spec("Deep", type_0());
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Deep.mk"),
        fields: vec![(Name::from_string("f"), deep_field, false)],
        type_: Expr::const_str("Deep"),
    });
    let m = compute_size_metrics(&spec);
    assert_eq!(m.max_field_depth, 2);
}

// =============================================================================
// Positivity summary tests
// =============================================================================

#[test]
fn test_positivity_non_recursive_unused() {
    let spec = simple_spec("Unit", type_0());
    let summary = summarize_positivity(&spec);
    assert!(summary.passes);
    assert_eq!(summary.self_positivity, ParameterPositivity::Unused);
}

#[test]
fn test_positivity_recursive_passes() {
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let mut spec = simple_spec("Nat", type_0());
    spec.is_recursive = true;
    spec.ctors.push(nullary_ctor("Nat.zero", nat_const.clone()));
    spec.ctors.push(unary_ctor(
        "Nat.succ",
        "pred",
        nat_const.clone(),
        true,
        arrow(nat_const.clone(), nat_const),
    ));
    let summary = summarize_positivity(&spec);
    assert!(summary.passes);
    assert_eq!(
        summary.self_positivity,
        ParameterPositivity::StrictlyPositive
    );
}

#[test]
fn test_positivity_negative_self_reference() {
    let bad = Name::from_string("Bad");
    let bad_const = Expr::const_(bad.clone(), vec![]);
    let bool_const = Expr::const_str("Bool");
    let neg_ty = arrow(bad_const.clone(), bool_const);

    let mut spec = simple_spec("Bad", type_0());
    spec.is_recursive = true;
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Bad.mk"),
        fields: vec![(Name::from_string("f"), neg_ty.clone(), false)],
        type_: arrow(neg_ty, bad_const),
    });
    let summary = summarize_positivity(&spec);
    assert!(!summary.passes);
    assert!(matches!(
        summary.self_positivity,
        ParameterPositivity::Negative(_)
    ));
}

#[test]
fn test_positivity_param_analysis() {
    let a_name = Name::from_string("A");
    let a_const = Expr::const_(a_name.clone(), vec![]);
    let mut spec = simple_spec("Box", type_0());
    spec.params = vec![(a_name.clone(), type_0())];
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Box.mk"),
        fields: vec![(Name::from_string("val"), a_const, false)],
        type_: Expr::const_str("Box"),
    });
    let summary = summarize_positivity(&spec);
    assert!(summary.passes);
    assert_eq!(summary.param_positivity.len(), 1);
    assert_eq!(
        summary.param_positivity[0].1,
        ParameterPositivity::StrictlyPositive
    );
}

#[test]
fn test_positivity_unused_param() {
    let mut spec = simple_spec("Phantom", type_0());
    spec.params = vec![(Name::from_string("A"), type_0())];
    spec.ctors
        .push(nullary_ctor("Phantom.mk", Expr::const_str("Phantom")));
    let summary = summarize_positivity(&spec);
    assert!(summary.passes);
    assert_eq!(summary.param_positivity[0].1, ParameterPositivity::Unused);
}

// =============================================================================
// Pattern match info tests
// =============================================================================

#[test]
fn test_pattern_match_empty() {
    let spec = simple_spec("Empty", type_0());
    let info = predict_pattern_match_info(&spec);
    assert_eq!(info.case_count, 0);
    assert!(info.is_empty);
    assert!(!info.is_irrefutable);
    assert!(!info.needs_default);
}

#[test]
fn test_pattern_match_unit() {
    let mut spec = simple_spec("Unit", type_0());
    spec.ctors
        .push(nullary_ctor("Unit.unit", Expr::const_str("Unit")));
    let info = predict_pattern_match_info(&spec);
    assert_eq!(info.case_count, 1);
    assert!(!info.is_empty);
    assert!(info.is_irrefutable);
    assert!(!info.needs_default);
}

#[test]
fn test_pattern_match_bool() {
    let mut spec = simple_spec("Bool", type_0());
    spec.ctors
        .push(nullary_ctor("Bool.true", Expr::const_str("Bool")));
    spec.ctors
        .push(nullary_ctor("Bool.false", Expr::const_str("Bool")));
    let info = predict_pattern_match_info(&spec);
    assert_eq!(info.case_count, 2);
    assert!(!info.is_empty);
    assert!(!info.is_irrefutable);
    assert_eq!(info.constructor_names.len(), 2);
    assert_eq!(info.constructor_names[0], Name::from_string("Bool.true"));
    assert_eq!(info.constructor_names[1], Name::from_string("Bool.false"));
}

// =============================================================================
// Composite analysis tests
// =============================================================================

#[test]
fn test_full_analysis_nat() {
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let mut spec = simple_spec("Nat", type_0());
    spec.is_recursive = true;
    spec.ctors.push(nullary_ctor("Nat.zero", nat_const.clone()));
    spec.ctors.push(unary_ctor(
        "Nat.succ",
        "pred",
        nat_const.clone(),
        true,
        arrow(nat_const.clone(), nat_const),
    ));

    let report = analyze_inductive(&spec);
    assert_eq!(report.name, Name::from_string("Nat"));
    assert_eq!(report.constructor_classifications.len(), 2);
    assert_eq!(report.recursion_scheme, RecursionScheme::NatLike);
    assert!(!report.universe_constraints.is_prop);
    assert!(report.eliminator_shape.is_large_eliminator);
    assert_eq!(report.size_metrics.constructor_count, 2);
    assert!(report.positivity_summary.passes);
    assert_eq!(report.pattern_match_info.case_count, 2);
}

#[test]
fn test_full_analysis_empty() {
    let spec = simple_spec("Empty", type_0());
    let report = analyze_inductive(&spec);
    assert_eq!(report.recursion_scheme, RecursionScheme::NonRecursive);
    assert_eq!(report.size_metrics.constructor_count, 0);
    assert!(report.pattern_match_info.is_empty);
}

// =============================================================================
// Mutual analysis tests
// =============================================================================

#[test]
fn test_analyze_mutual_single() {
    let spec = MutualInductiveSpec {
        inductives: vec![simple_spec("Unit", type_0())],
        universe_params: Vec::new(),
    };
    let reports = analyze_mutual_inductive(&spec).expect("should succeed");
    assert_eq!(reports.len(), 1);
}

#[test]
fn test_analyze_mutual_multiple() {
    let spec = MutualInductiveSpec {
        inductives: vec![simple_spec("A", type_0()), simple_spec("B", type_0())],
        universe_params: Vec::new(),
    };
    let reports = analyze_mutual_inductive(&spec).expect("should succeed");
    assert_eq!(reports.len(), 2);
}

#[test]
fn test_analyze_mutual_empty_block_error() {
    let spec = MutualInductiveSpec {
        inductives: Vec::new(),
        universe_params: Vec::new(),
    };
    let err = analyze_mutual_inductive(&spec).unwrap_err();
    assert_eq!(err, InductiveAnalysisError::EmptyMutualBlock);
}

// =============================================================================
// Error type tests
// =============================================================================

#[test]
fn test_error_no_constructors_display() {
    let err = InductiveAnalysisError::NoConstructors {
        name: Name::from_string("Empty"),
    };
    let msg = err.to_string();
    assert!(msg.contains("Empty"));
    assert!(msg.contains("no constructors"));
}

#[test]
fn test_error_unclassifiable_field_display() {
    let err = InductiveAnalysisError::UnclassifiableField {
        ctor: Name::from_string("Foo.mk"),
        field: Name::from_string("x"),
    };
    let msg = err.to_string();
    assert!(msg.contains("Foo.mk"));
    assert!(msg.contains("x"));
}

#[test]
fn test_error_empty_mutual_display() {
    let err = InductiveAnalysisError::EmptyMutualBlock;
    let msg = err.to_string();
    assert!(msg.contains("empty"));
}

#[test]
fn test_error_eq() {
    let e1 = InductiveAnalysisError::EmptyMutualBlock;
    let e2 = InductiveAnalysisError::EmptyMutualBlock;
    assert_eq!(e1, e2);
}

// =============================================================================
// RecursionScheme enum tests
// =============================================================================

#[test]
fn test_recursion_scheme_eq() {
    assert_eq!(RecursionScheme::NatLike, RecursionScheme::NatLike);
    assert_ne!(RecursionScheme::NatLike, RecursionScheme::ListLike);
    assert_ne!(RecursionScheme::TreeLike, RecursionScheme::HigherOrder);
}

#[test]
fn test_recursion_scheme_clone() {
    let scheme = RecursionScheme::Mutual;
    let cloned = scheme.clone();
    assert_eq!(scheme, cloned);
}

// =============================================================================
// IndexPattern tests
// =============================================================================

#[test]
fn test_index_pattern_eq() {
    assert_eq!(IndexPattern::None, IndexPattern::None);
    assert_ne!(IndexPattern::None, IndexPattern::Mixed);
    assert_ne!(
        IndexPattern::AllVariables,
        IndexPattern::HasConstructorIndices
    );
}

// =============================================================================
// EliminatorShape tests
// =============================================================================

#[test]
fn test_eliminator_shape_clone() {
    let shape = EliminatorShape {
        motive_count: 1,
        minor_premise_count: 2,
        target_count: 1,
        is_large_eliminator: true,
        total_binder_count: 5,
    };
    let cloned = shape.clone();
    assert_eq!(shape, cloned);
}
