// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the ι×δ commutation spine machinery (#2859 Increment H++, Stage 4 —
//! Hindley-Rosen assembly). Pins that the delta_cong_star_list spine congruences
//! are registered, kernel-checked, DerivedProved, and carry zero axiom_deps.

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::test_utils::run_with_stack;
use crate::Specification;

fn build_iota_delta_spec() -> Specification {
    run_with_stack(|| {
        Specification::new_substitution_test_spec().expect("substitution test spec should build")
    })
}

/// The list no-confusion + δ*-list-trans bricks are DerivedProved with zero axiom deps.
#[test]
fn test_list_noconfusion_and_trans_is_derived_proved_zero_axiom() {
    let spec = build_iota_delta_spec();
    for name in [
        "list_nil_ne_cons",
        "list_cons_inj_head",
        "list_cons_inj_tail",
        "delta_cong_star_list_trans",
        "delta_cong_star_spine_cong",
        "recenv_ctor_no_defval_cname",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should carry no axiom dependencies: {:?}",
            def.axiom_deps
        );
    }
}

/// The ι×δ commutation reconstruction helpers are DerivedProved with zero axiom deps.
#[test]
fn test_iota_delta_comm_helpers_is_derived_proved_zero_axiom() {
    let spec = build_iota_delta_spec();
    for name in [
        "delta_cong_star_preserves_head_const",
        "list_head_some_delta_cong",
        "iota_reduct_recon_general",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should carry no axiom dependencies: {:?}",
            def.axiom_deps
        );
    }
}

/// The ι×δ commutation `iota_delta_comm` is DerivedProved with zero axiom deps.
#[test]
fn test_iota_delta_comm_is_derived_proved_zero_axiom() {
    let spec = build_iota_delta_spec();
    let def = spec
        .definitions()
        .get("iota_delta_comm")
        .expect("iota_delta_comm should be registered");
    assert!(!def.is_axiom, "iota_delta_comm should not be an axiom");
    assert_eq!(def.category, AxiomCategory::DerivedLemma);
    assert_eq!(def.proof_status, ProofStatus::DerivedProved);
    assert!(
        def.axiom_deps.is_empty(),
        "iota_delta_comm should carry no axiom dependencies: {:?}",
        def.axiom_deps
    );
}

/// THE TARGETS: `par_delta_sc` (the single-step β+ι/δ strong commutation), the
/// UNCONDITIONAL 3-way β+ι+δ Church-Rosser `par_reduces_cd_star_diamond`, and their
/// inversion / join helpers are all registered, kernel-checked, DerivedProved, and
/// carry zero axiom_deps. (The spec BUILDING at all is the kernel gate: every value
/// is elaborated + type-checked against its declared type in `add_definition`.)
#[test]
fn test_par_delta_sc_and_cd_star_diamond_are_derived_proved_zero_axiom() {
    let spec = build_iota_delta_spec();
    for name in [
        "delta_cong_app_lam_inv",
        "sc_beta_join_type",
        "sc_beta_join_body",
        "sc_beta_join_arg",
        "sc_cong_join_app_left",
        "sc_cong_join_app_right",
        "sc_cong_join_lam_left",
        "sc_cong_join_lam_right",
        "sc_cong_join_pi_left",
        "sc_cong_join_pi_right",
        "par_delta_sc",
        "par_reduces_cd_star_diamond",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should carry no axiom dependencies: {:?}",
            def.axiom_deps
        );
    }
}

/// The ι×δ spine-congruence bricks are DerivedProved with zero axiom deps.
#[test]
fn test_iota_delta_spine_infra_is_derived_proved_zero_axiom() {
    let spec = build_iota_delta_spec();
    for name in [
        "delta_cong_star_list_refl",
        "apply_spine_delta_cong_star",
        "delta_cong_star_list_append",
        "list_tail_delta_cong",
        "list_drop_delta_cong",
        "list_take_delta_cong",
        "kapp_args_delta_cong",
        "delta_reduct_eq_none_of_defval_none",
        "delta_cong_list_length_eq",
        "delta_cong_preserves_head_const",
        "delta_cong_spine_cong",
        "recmeta_some_defval_none",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should carry no axiom dependencies: {:?}",
            def.axiom_deps
        );
    }
}
