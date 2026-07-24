// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment H++ (#2859 computational-iota/delta track, DELTA INCREMENT Stage 4,
//! the HINDLEY-ROSEN redirect): the δ-only single-position reduction `delta_cong`,
//! its RT-closure `delta_cong_star`, the multi-step join witness, and the two basic
//! combinators. Pins that the inductives are registered and every derived brick is
//! DerivedProved (zero axiom_deps — kernel-checked closed terms).

use clean_kernel::Name;
use clean_verify::spec::{AxiomCategory, ProofStatus, Specification};
use clean_verify::test_utils::build_spec_with_stack;

fn assert_in_env(spec: &Specification, name: &str) {
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered in the spec environment"
    );
}

fn assert_derived_proved(spec: &Specification, name: &str) {
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert!(!def.is_axiom, "{name} must not be an axiom");
    assert_eq!(def.category, AxiomCategory::DerivedLemma, "{name} category");
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "{name} should be DerivedProved"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "{name} should carry zero axiom_deps: {:?}",
        def.axiom_deps
    );
}

#[test]
fn delta_cong_inductive_registered() {
    let spec = build_spec_with_stack();
    for name in [
        "delta_cong",
        "delta_cong.here",
        "delta_cong.app_f",
        "delta_cong.app_a",
        "delta_cong.lam_t",
        "delta_cong.lam_b",
        "delta_cong.pi_d",
        "delta_cong.pi_b",
        // Let promotion (task #28): the three let-component congruences.
        "delta_cong.let_t",
        "delta_cong.let_v",
        "delta_cong.let_b",
        "delta_cong.rec",
        "delta_cong_star",
        "delta_cong_star.refl",
        "delta_cong_star.step",
        "delta_cong_star.rec",
        "par_strips_witness_d_star",
        "par_strips_witness_d_star.intro",
    ] {
        assert_in_env(&spec, name);
    }
}

#[test]
fn delta_cong_star_combinators_derived_proved() {
    let spec = build_spec_with_stack();
    for name in ["delta_cong_subsumes_star", "delta_cong_star_trans"] {
        assert_in_env(&spec, name);
        assert_derived_proved(&spec, name);
    }
}

#[test]
fn delta_cong_cd_embeddings_derived_proved() {
    let spec = build_spec_with_stack();
    for name in ["delta_cong_subsumes_cd", "delta_cong_star_subsumes_cd_star"] {
        assert_in_env(&spec, name);
        assert_derived_proved(&spec, name);
    }
}

#[test]
fn delta_cong_star_congruences_derived_proved() {
    let spec = build_spec_with_stack();
    for name in [
        "delta_cong_star_app",
        "delta_cong_star_lam",
        "delta_cong_star_pi",
    ] {
        assert_in_env(&spec, name);
        assert_derived_proved(&spec, name);
    }
}
