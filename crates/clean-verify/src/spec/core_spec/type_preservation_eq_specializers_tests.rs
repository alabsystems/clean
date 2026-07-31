// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for TypePreservation Packet A — Pi/Sort/Lam Eq specializers (#464).
//!
//! These tests confirm that the three new specializers:
//!  - are registered,
//!  - are Pi-shaped (non-trivial, non-axiom),
//!  - carry the expected `proof_status`, `axiom_deps`, and dependencies.

use std::collections::HashSet;

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::test_utils::build_spec_with_stack;

/// Each Sort/Lam specializer proves an Eq-level equality, so the statement
/// must mention both `DefEq` (the hypothesis) and `Eq KExpr` (the conclusion)
/// and it must be a universally-quantified Pi statement.
fn assert_pi_shaped_equality_statement(type_src: &str, name: &str) {
    assert!(
        type_src.starts_with("forall "),
        "{name}.type_src should be a universally-quantified Pi statement: {type_src}"
    );
    assert!(
        type_src.contains("DefEq"),
        "{name}.type_src should mention DefEq: {type_src}"
    );
    assert!(
        type_src.contains("Eq KExpr"),
        "{name}.type_src should conclude in Eq KExpr: {type_src}"
    );
}

#[test]
fn test_sort_def_eq_eq_is_derived_proved() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("sort_def_eq_eq")
        .expect("sort_def_eq_eq should be registered");

    assert!(!def.is_axiom, "sort_def_eq_eq must not be an axiom");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "sort_def_eq_eq should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "sort_def_eq_eq should be DerivedProved"
    );
    assert_eq!(
        def.axiom_deps,
        HashSet::new(),
        "sort_def_eq_eq should be axiom-free (re-pointed off church_rosser_whnf #2859)"
    );
    assert_pi_shaped_equality_statement(&def.type_src, "sort_def_eq_eq");
    assert!(
        def.type_src.contains("KExpr.sort"),
        "sort_def_eq_eq should mention KExpr.sort: {}",
        def.type_src
    );
    assert!(
        def.value_src.is_some(),
        "sort_def_eq_eq should carry a proof term (value_src)"
    );
}

// test_lam_def_eq_eq_is_derived_proved removed: lam_def_eq_eq was a FALSE Eq shim
// backed by church_rosser_whnf; both are deleted (#2859). Its lam-injectivity
// consumers route through the constructive par_cd_lam_injectivity tower instead.

#[test]
fn test_def_eq_instantiate_both_is_joint_congruence() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("def_eq_instantiate_both")
        .expect("def_eq_instantiate_both should be registered");

    assert!(
        !def.is_axiom,
        "def_eq_instantiate_both must not be an axiom"
    );
    assert_eq!(def.category, AxiomCategory::DerivedLemma);
    // DerivedProved: both legs (def_eq_respects_subst #2872,
    // def_eq_instantiate_arg_congr #3221) are DerivedProved; its former
    // church_rosser_whnf leaf is retired (#2859).
    assert_eq!(def.proof_status, ProofStatus::DerivedProved);
    assert_eq!(
        def.axiom_deps,
        HashSet::new(),
        "def_eq_instantiate_both should be axiom-free after church_rosser_whnf retirement"
    );

    // Pi-shaped and conclusion is DefEq (instantiate ...) (instantiate ...)
    assert!(
        def.type_src.starts_with("forall "),
        "def_eq_instantiate_both should be Pi-shaped: {}",
        def.type_src
    );
    assert!(
        def.type_src.contains("instantiate B a"),
        "def_eq_instantiate_both should mention instantiate B a: {}",
        def.type_src
    );
    assert!(
        def.type_src.contains("instantiate B' a'"),
        "def_eq_instantiate_both should mention instantiate B' a': {}",
        def.type_src
    );
    let value = def
        .value_src
        .as_ref()
        .expect("def_eq_instantiate_both should carry a proof term");
    assert!(
        value.contains("DefEq.trans"),
        "def_eq_instantiate_both proof should use DefEq.trans: {value}"
    );
    assert!(
        value.contains("def_eq_respects_subst"),
        "def_eq_instantiate_both proof should reuse def_eq_respects_subst: {value}"
    );
    assert!(
        value.contains("def_eq_instantiate_arg_congr"),
        "def_eq_instantiate_both proof should reuse def_eq_instantiate_arg_congr: {value}"
    );
}

#[test]
fn test_packet_a_specializers_do_not_regress_type_preservation_leaves() {
    // Packet A introduces helpers only. Post-#2859 the structural
    // `church_rosser_whnf` leaf is RETIRED (the false WHNF Church-Rosser axiom
    // and its pi_def_eq_eq/lam_def_eq_eq shims are deleted; consumers re-point
    // onto the constructive confluence tower). Brick 9 then DELETED the FALSE
    // `def_eq_to_eq` bridge entirely (every consumer rerouted onto Typing.conv /
    // sort_def_eq_eq / def_eq_respects_lift_at), so it is no longer registered.
    let spec = build_spec_with_stack();

    // church_rosser_whnf is gone.
    assert!(
        spec.definitions().get("church_rosser_whnf").is_none(),
        "church_rosser_whnf should be retired (#2859)"
    );

    // def_eq_to_eq is gone (Brick 9, #2859).
    assert!(
        spec.definitions().get("def_eq_to_eq").is_none(),
        "def_eq_to_eq should be deleted (Brick 9, #2859)"
    );
}
