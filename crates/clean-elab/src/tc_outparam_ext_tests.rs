// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended type class outParam analysis.

use super::*;
use crate::instances::{InstanceTable, DEFAULT_PRIORITY};
use clean_kernel::expr::{Expr, FVarId};
use clean_kernel::name::Name;

// -- Helpers --

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

/// HAdd with 3 params: alpha, beta, gamma(outParam=2).
/// Instances: HAdd Nat Nat Nat, HAdd Int Int Int.
fn make_hadd_table() -> InstanceTable {
    let mut t = InstanceTable::new();
    t.register_class_full(n("HAdd"), 3, vec![2], vec![]);
    let hadd_type = |a: &str| Expr::app(Expr::app(Expr::app(c("HAdd"), c(a)), c(a)), c(a));
    t.add_instance(
        n("instHAddNat"),
        n("HAdd"),
        c("instHAddNat"),
        hadd_type("Nat"),
        DEFAULT_PRIORITY,
    );
    t.add_instance(
        n("instHAddInt"),
        n("HAdd"),
        c("instHAddInt"),
        hadd_type("Int"),
        DEFAULT_PRIORITY,
    );
    t
}

/// Add with 1 param, no outParams.
fn make_add_table() -> InstanceTable {
    let mut t = InstanceTable::new();
    t.register_class(n("Add"), 1, vec![]);
    t.add_instance(
        n("instAddNat"),
        n("Add"),
        c("instAddNat"),
        Expr::app(c("Add"), c("Nat")),
        DEFAULT_PRIORITY,
    );
    t
}

/// OfNat with 2 params: alpha(semiOut=0), n.
fn make_semi_table() -> InstanceTable {
    let mut t = InstanceTable::new();
    t.register_class_full(n("OfNat"), 2, vec![], vec![0]);
    t.add_instance(
        n("instOfNatNatZero"),
        n("OfNat"),
        c("instOfNatNatZero"),
        Expr::app(Expr::app(c("OfNat"), c("Nat")), c("zero")),
        DEFAULT_PRIORITY,
    );
    t
}

/// HMul with conflicting outParam values.
fn make_conflicting_table() -> InstanceTable {
    let mut t = InstanceTable::new();
    t.register_class_full(n("HMul"), 3, vec![2], vec![]);
    let mk = |out: &str| Expr::app(Expr::app(Expr::app(c("HMul"), c("Nat")), c("Nat")), c(out));
    t.add_instance(
        n("inst1"),
        n("HMul"),
        c("inst1"),
        mk("Nat"),
        DEFAULT_PRIORITY,
    );
    t.add_instance(
        n("inst2"),
        n("HMul"),
        c("inst2"),
        mk("Int"),
        DEFAULT_PRIORITY,
    );
    t
}

/// Empty table.
fn make_empty_table() -> InstanceTable {
    InstanceTable::new()
}

/// Table with multiple classes.
fn make_multi_class_table() -> InstanceTable {
    let mut t = InstanceTable::new();

    // HAdd: 3 params, out=2
    t.register_class_full(n("HAdd"), 3, vec![2], vec![]);
    let hadd_nat = Expr::app(
        Expr::app(Expr::app(c("HAdd"), c("Nat")), c("Nat")),
        c("Nat"),
    );
    t.add_instance(
        n("instHAddNat"),
        n("HAdd"),
        c("instHAddNat"),
        hadd_nat,
        DEFAULT_PRIORITY,
    );

    // Add: 1 param, no out
    t.register_class(n("Add"), 1, vec![]);
    t.add_instance(
        n("instAddNat"),
        n("Add"),
        c("instAddNat"),
        Expr::app(c("Add"), c("Nat")),
        DEFAULT_PRIORITY,
    );

    // OfNat: 2 params, semi=0
    t.register_class_full(n("OfNat"), 2, vec![], vec![0]);
    t.add_instance(
        n("instOfNatNat"),
        n("OfNat"),
        c("instOfNatNat"),
        Expr::app(Expr::app(c("OfNat"), c("Nat")), c("zero")),
        DEFAULT_PRIORITY,
    );

    t
}

// =============================================================================
// Inference tests
// =============================================================================

#[test]
fn test_infer_param_roles_hadd_annotated() {
    let t = make_hadd_table();
    let profile = infer_param_roles(&n("HAdd"), &t).expect("class registered");
    assert_eq!(profile.num_params, 3);
    assert_eq!(profile.params.len(), 3);
    assert_eq!(profile.params[2].role, ParamRole::Output);
    assert!(profile.params[2].reason.contains("outParam"));
}

#[test]
fn test_infer_param_roles_hadd_inputs() {
    let t = make_hadd_table();
    let profile = infer_param_roles(&n("HAdd"), &t).expect("class registered");
    assert_eq!(profile.params[0].role, ParamRole::Input);
    assert_eq!(profile.params[1].role, ParamRole::Input);
}

#[test]
fn test_infer_param_roles_add_single_instance() {
    let t = make_add_table();
    let profile = infer_param_roles(&n("Add"), &t).expect("class registered");
    assert_eq!(profile.params.len(), 1);
    // Only one instance so heuristic says all agree -> output.
    assert_eq!(profile.params[0].role, ParamRole::Output);
    assert!(profile.params[0].reason.contains("inferred output"));
}

#[test]
fn test_infer_param_roles_semi_outparam() {
    let t = make_semi_table();
    let profile = infer_param_roles(&n("OfNat"), &t).expect("class registered");
    assert_eq!(profile.params[0].role, ParamRole::SemiOutput);
    assert!(profile.params[0].reason.contains("semiOutParam"));
}

#[test]
fn test_infer_param_roles_unregistered_class() {
    let t = make_empty_table();
    assert!(infer_param_roles(&n("Unknown"), &t).is_none());
}

#[test]
fn test_infer_param_roles_no_instances() {
    let mut t = InstanceTable::new();
    t.register_class(n("Empty"), 2, vec![]);
    let profile = infer_param_roles(&n("Empty"), &t).expect("class registered");
    assert_eq!(profile.params.len(), 2);
    assert_eq!(profile.params[0].role, ParamRole::Input);
    assert!(profile.params[0].reason.contains("no instances"));
}

#[test]
fn test_infer_param_roles_class_name_matches() {
    let t = make_hadd_table();
    let profile = infer_param_roles(&n("HAdd"), &t).expect("class registered");
    assert_eq!(profile.class_name, n("HAdd"));
}

#[test]
fn test_infer_param_roles_num_params_correct() {
    let t = make_hadd_table();
    let profile = infer_param_roles(&n("HAdd"), &t).expect("class registered");
    assert_eq!(profile.num_params, 3);
}

// =============================================================================
// Hierarchy tests
// =============================================================================

#[test]
fn test_analyze_hierarchy_shared_outparams() {
    let mut t = InstanceTable::new();
    t.register_class_full(n("Parent"), 3, vec![1, 2], vec![]);
    t.register_class_full(n("Child"), 3, vec![2], vec![]);

    let rel = analyze_hierarchy_outparams(&n("Parent"), &n("Child"), &t).expect("both registered");
    assert_eq!(rel.shared_out_indices, vec![2]);
    assert_eq!(rel.parent_only_out, vec![1]);
    assert!(rel.child_only_out.is_empty());
}

#[test]
fn test_analyze_hierarchy_no_overlap() {
    let mut t = InstanceTable::new();
    t.register_class_full(n("A"), 3, vec![0], vec![]);
    t.register_class_full(n("B"), 3, vec![2], vec![]);

    let rel = analyze_hierarchy_outparams(&n("A"), &n("B"), &t).expect("both registered");
    assert!(rel.shared_out_indices.is_empty());
    assert_eq!(rel.parent_only_out, vec![0]);
    assert_eq!(rel.child_only_out, vec![2]);
}

#[test]
fn test_analyze_hierarchy_different_sizes() {
    let mut t = InstanceTable::new();
    t.register_class_full(n("Big"), 5, vec![0, 3, 4], vec![]);
    t.register_class_full(n("Small"), 2, vec![0], vec![]);

    let rel = analyze_hierarchy_outparams(&n("Big"), &n("Small"), &t).expect("both registered");
    assert_eq!(rel.shared_out_indices, vec![0]);
    assert!(rel.parent_only_out.is_empty());
    assert!(rel.child_only_out.is_empty());
}

#[test]
fn test_analyze_hierarchy_unregistered_parent() {
    let mut t = InstanceTable::new();
    t.register_class(n("Child"), 2, vec![]);
    assert!(analyze_hierarchy_outparams(&n("Unknown"), &n("Child"), &t).is_none());
}

#[test]
fn test_analyze_hierarchy_unregistered_child() {
    let mut t = InstanceTable::new();
    t.register_class(n("Parent"), 2, vec![]);
    assert!(analyze_hierarchy_outparams(&n("Parent"), &n("Unknown"), &t).is_none());
}

#[test]
fn test_analyze_hierarchy_names_correct() {
    let mut t = InstanceTable::new();
    t.register_class_full(n("X"), 2, vec![1], vec![]);
    t.register_class_full(n("Y"), 2, vec![1], vec![]);

    let rel = analyze_hierarchy_outparams(&n("X"), &n("Y"), &t).expect("both registered");
    assert_eq!(rel.parent, n("X"));
    assert_eq!(rel.child, n("Y"));
}

#[test]
fn test_analyze_hierarchy_no_outparams_either_side() {
    let mut t = InstanceTable::new();
    t.register_class(n("A"), 2, vec![]);
    t.register_class(n("B"), 2, vec![]);

    let rel = analyze_hierarchy_outparams(&n("A"), &n("B"), &t).expect("both registered");
    assert!(rel.shared_out_indices.is_empty());
    assert!(rel.parent_only_out.is_empty());
    assert!(rel.child_only_out.is_empty());
}

#[test]
fn test_analyze_hierarchy_all_shared() {
    let mut t = InstanceTable::new();
    t.register_class_full(n("P"), 3, vec![0, 1, 2], vec![]);
    t.register_class_full(n("C"), 3, vec![0, 1, 2], vec![]);

    let rel = analyze_hierarchy_outparams(&n("P"), &n("C"), &t).expect("both registered");
    assert_eq!(rel.shared_out_indices, vec![0, 1, 2]);
    assert!(rel.parent_only_out.is_empty());
    assert!(rel.child_only_out.is_empty());
}

// =============================================================================
// Validation tests
// =============================================================================

#[test]
fn test_validate_hadd_valid() {
    let t = make_hadd_table();
    assert_eq!(
        validate_outparam_uniqueness(&n("HAdd"), &t),
        ValidationResult::Valid
    );
}

#[test]
fn test_validate_conflicting_hmul() {
    let t = make_conflicting_table();
    match validate_outparam_uniqueness(&n("HMul"), &t) {
        ValidationResult::Conflict {
            conflicting_indices,
            conflicting_instances,
        } => {
            assert!(conflicting_indices.contains(&2));
            assert!(!conflicting_instances.is_empty());
        }
        other => panic!("Expected Conflict, got {other:?}"),
    }
}

#[test]
fn test_validate_no_outparams() {
    let t = make_add_table();
    assert_eq!(
        validate_outparam_uniqueness(&n("Add"), &t),
        ValidationResult::Valid
    );
}

#[test]
fn test_validate_not_registered() {
    let t = make_empty_table();
    assert_eq!(
        validate_outparam_uniqueness(&n("Missing"), &t),
        ValidationResult::NotRegistered,
    );
}

#[test]
fn test_validate_single_instance() {
    let mut t = InstanceTable::new();
    t.register_class_full(n("Solo"), 2, vec![1], vec![]);
    t.add_instance(
        n("soloinst"),
        n("Solo"),
        c("soloinst"),
        Expr::app(Expr::app(c("Solo"), c("Nat")), c("Nat")),
        DEFAULT_PRIORITY,
    );
    assert_eq!(
        validate_outparam_uniqueness(&n("Solo"), &t),
        ValidationResult::Valid
    );
}

#[test]
fn test_validate_multiple_agreeing() {
    let mut t = InstanceTable::new();
    t.register_class_full(n("Agree"), 2, vec![1], vec![]);
    let mk = || Expr::app(Expr::app(c("Agree"), c("Nat")), c("Nat"));
    t.add_instance(n("a1"), n("Agree"), c("a1"), mk(), DEFAULT_PRIORITY);
    t.add_instance(n("a2"), n("Agree"), c("a2"), mk(), 50);
    assert_eq!(
        validate_outparam_uniqueness(&n("Agree"), &t),
        ValidationResult::Valid
    );
}

// =============================================================================
// Diagnostic tests
// =============================================================================

#[test]
fn test_diagnose_params_hadd() {
    let t = make_hadd_table();
    let diags = diagnose_params(&n("HAdd"), &t);
    assert_eq!(diags.len(), 3);
    assert_eq!(diags[0].role, ParamRole::Input);
    assert_eq!(diags[2].role, ParamRole::Output);
}

#[test]
fn test_diagnose_params_unregistered() {
    let t = make_empty_table();
    assert!(diagnose_params(&n("Unknown"), &t).is_empty());
}

#[test]
fn test_diagnose_params_explanations_non_empty() {
    let t = make_hadd_table();
    let diags = diagnose_params(&n("HAdd"), &t);
    for d in &diags {
        assert!(!d.explanation.is_empty());
        assert!(d.explanation.contains("HAdd"));
    }
}

#[test]
fn test_diagnose_params_indices_sequential() {
    let t = make_hadd_table();
    let diags = diagnose_params(&n("HAdd"), &t);
    for (i, d) in diags.iter().enumerate() {
        assert_eq!(d.index, i);
    }
}

#[test]
fn test_diagnose_params_semi_outparam_label() {
    let t = make_semi_table();
    let diags = diagnose_params(&n("OfNat"), &t);
    assert_eq!(diags[0].role, ParamRole::SemiOutput);
    assert!(diags[0].explanation.contains("SEMI-OUTPUT"));
}

#[test]
fn test_format_diagnostic_report_hadd() {
    let t = make_hadd_table();
    let report = format_diagnostic_report(&n("HAdd"), &t);
    assert!(report.contains("OutParam diagnostic"));
    assert!(report.contains("HAdd"));
    assert!(report.contains("OUTPUT"));
    assert!(report.contains("INPUT"));
    assert!(report.contains("Validation: OK"));
}

#[test]
fn test_format_diagnostic_report_conflicting() {
    let t = make_conflicting_table();
    let report = format_diagnostic_report(&n("HMul"), &t);
    assert!(report.contains("CONFLICT"));
}

#[test]
fn test_format_diagnostic_report_unregistered() {
    let t = make_empty_table();
    let report = format_diagnostic_report(&n("X"), &t);
    assert!(report.contains("not registered"));
}

// =============================================================================
// Statistics tests
// =============================================================================

#[test]
fn test_compute_stats_multi_class() {
    let t = make_multi_class_table();
    let stats = compute_stats(&t);
    assert_eq!(stats.total_classes, 3);
    assert_eq!(stats.classes_with_outparams, 1); // HAdd
    assert_eq!(stats.classes_with_semi_outparams, 1); // OfNat
    assert_eq!(stats.total_outparam_positions, 1);
    assert_eq!(stats.total_semi_outparam_positions, 1);
    assert_eq!(stats.conflicting_classes, 0);
}

#[test]
fn test_compute_stats_empty() {
    let t = make_empty_table();
    let stats = compute_stats(&t);
    assert_eq!(stats.total_classes, 0);
    assert_eq!(stats.classes_with_outparams, 0);
    assert_eq!(stats.valid_classes, 0);
}

#[test]
fn test_compute_stats_with_conflict() {
    let t = make_conflicting_table();
    let stats = compute_stats(&t);
    assert_eq!(stats.total_classes, 1);
    assert_eq!(stats.conflicting_classes, 1);
    assert_eq!(stats.valid_classes, 0);
}

#[test]
fn test_compute_stats_valid_counts() {
    let t = make_multi_class_table();
    let stats = compute_stats(&t);
    assert_eq!(stats.valid_classes, 3);
}

#[test]
fn test_format_stats_output() {
    let stats = OutParamStats {
        total_classes: 5,
        classes_with_outparams: 3,
        classes_with_semi_outparams: 1,
        total_outparam_positions: 4,
        total_semi_outparam_positions: 1,
        valid_classes: 4,
        conflicting_classes: 1,
    };
    let s = format_stats(&stats);
    assert!(s.contains("5 total"));
    assert!(s.contains("3 with outParams"));
    assert!(s.contains("4 valid"));
    assert!(s.contains("1 conflicting"));
}

#[test]
fn test_format_stats_zeros() {
    let stats = OutParamStats::default();
    let s = format_stats(&stats);
    assert!(s.contains("0 total"));
    assert!(s.contains("0 valid"));
}

// =============================================================================
// Helper function tests
// =============================================================================

#[test]
fn test_has_any_out_params_hadd() {
    let t = make_hadd_table();
    assert!(has_any_out_params(&n("HAdd"), &t));
}

#[test]
fn test_has_any_out_params_add_none() {
    let t = make_add_table();
    assert!(!has_any_out_params(&n("Add"), &t));
}

#[test]
fn test_has_any_out_params_semi() {
    let t = make_semi_table();
    assert!(has_any_out_params(&n("OfNat"), &t));
}

#[test]
fn test_has_any_out_params_unregistered() {
    let t = make_empty_table();
    assert!(!has_any_out_params(&n("X"), &t));
}

#[test]
fn test_classes_with_outparams_multi() {
    let t = make_multi_class_table();
    let names = classes_with_outparams(&t);
    assert_eq!(names.len(), 1);
    assert_eq!(names[0], n("HAdd"));
}

#[test]
fn test_classes_with_semi_outparams_multi() {
    let t = make_multi_class_table();
    let names = classes_with_semi_outparams(&t);
    assert_eq!(names.len(), 1);
    assert_eq!(names[0], n("OfNat"));
}

#[test]
fn test_classes_with_outparams_empty() {
    let t = make_empty_table();
    assert!(classes_with_outparams(&t).is_empty());
}

#[test]
fn test_count_input_params_hadd() {
    let t = make_hadd_table();
    // HAdd has 3 params, 1 outParam -> 2 inputs.
    assert_eq!(count_input_params(&n("HAdd"), &t), 2);
}

#[test]
fn test_count_input_params_add() {
    let t = make_add_table();
    // Add has 1 param, 0 outParams -> 1 input.
    assert_eq!(count_input_params(&n("Add"), &t), 1);
}

#[test]
fn test_count_input_params_semi_excluded() {
    let t = make_semi_table();
    // OfNat has 2 params, 1 semiOutParam -> 1 input.
    assert_eq!(count_input_params(&n("OfNat"), &t), 1);
}

#[test]
fn test_count_input_params_unregistered() {
    let t = make_empty_table();
    assert_eq!(count_input_params(&n("X"), &t), 0);
}

// =============================================================================
// expr_structural_eq tests
// =============================================================================

#[test]
fn test_expr_structural_eq_consts() {
    assert!(expr_structural_eq(&c("Nat"), &c("Nat")));
    assert!(!expr_structural_eq(&c("Nat"), &c("Int")));
}

#[test]
fn test_expr_structural_eq_app() {
    let a = Expr::app(c("F"), c("Nat"));
    let b = Expr::app(c("F"), c("Nat"));
    let d = Expr::app(c("F"), c("Int"));
    assert!(expr_structural_eq(&a, &b));
    assert!(!expr_structural_eq(&a, &d));
}

#[test]
fn test_expr_structural_eq_bvar() {
    let a = Expr::bvar(0);
    let b = Expr::bvar(0);
    let d = Expr::bvar(1);
    assert!(expr_structural_eq(&a, &b));
    assert!(!expr_structural_eq(&a, &d));
}

#[test]
fn test_expr_structural_eq_fvar() {
    let a = Expr::fvar(FVarId::new(42));
    let b = Expr::fvar(FVarId::new(42));
    let d = Expr::fvar(FVarId::new(99));
    assert!(expr_structural_eq(&a, &b));
    assert!(!expr_structural_eq(&a, &d));
}

#[test]
fn test_expr_structural_eq_different_kinds() {
    assert!(!expr_structural_eq(&c("Nat"), &Expr::bvar(0)));
}
