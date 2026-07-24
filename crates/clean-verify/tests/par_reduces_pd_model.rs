// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment H+ (#2859 computational-iota/delta track, DELTA INCREMENT Stage 3):
//! the PROPER (Takahashi) 3-way (β+ι+δ) parallel reduction `par_reduces_pd`, its
//! RT-closure, the join witnesses, the basic combinators, and the
//! `par_reduces_cd ⊆ par_reduces_pd` embedding. Pins that the inductives are
//! registered and every derived brick is DerivedProved (zero axiom_deps —
//! kernel-checked closed terms).

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
fn par_reduces_pd_inductive_registered() {
    let spec = build_spec_with_stack();
    for name in [
        "par_reduces_pd",
        "par_reduces_pd.refl",
        "par_reduces_pd.beta",
        "par_reduces_pd.app",
        "par_reduces_pd.lam",
        "par_reduces_pd.pi",
        "par_reduces_pd.forall_",
        "par_reduces_pd.let_",
        // Let promotion (task #28): the trailing non-contracting let congruence.
        "par_reduces_pd.let_cong",
        // The two parallel contraction ctors — the whole point: each bakes in the
        // subterm reduction (par_reduces_pd env e e2) before firing the deterministic
        // iota / delta step.
        "par_reduces_pd.iota_p",
        "par_reduces_pd.delta_p",
        "par_reduces_pd.rec",
    ] {
        assert_in_env(&spec, name);
    }
}

#[test]
fn par_reduces_pd_star_substrate_registered() {
    let spec = build_spec_with_stack();
    for name in [
        "par_reduces_pd_star",
        "par_reduces_pd_star.refl",
        "par_reduces_pd_star.step",
        "par_strips_witness_pd",
        "par_strips_witness_pd.intro",
        "par_strips_witness_pd_star",
        "par_strips_witness_pd_star.intro",
    ] {
        assert_in_env(&spec, name);
    }
}

#[test]
fn par_reduces_pd_combinators_are_derived_proved() {
    let spec = build_spec_with_stack();
    for name in [
        "par_subsumes_par_pd_star",
        "par_reduces_pd_star_trans",
        "par_strips_witness_pd_to_star",
    ] {
        assert_derived_proved(&spec, name);
    }
}

#[test]
fn par_reduces_cd_subsumes_par_pd_is_derived_proved() {
    // The closure-coincidence bridge: every atomic 3-way step is a proper 3-way
    // step (atomic iota/delta map to the parallel iota_p/delta_p with a reflexive
    // premise).
    let spec = build_spec_with_stack();
    assert_derived_proved(&spec, "par_reduces_cd_subsumes_par_pd");
}

#[test]
fn par_reduces_cd_star_substrate_registered() {
    let spec = build_spec_with_stack();
    for name in [
        "par_reduces_cd_star",
        "par_reduces_cd_star.refl",
        "par_reduces_cd_star.step",
    ] {
        assert_in_env(&spec, name);
    }
    for name in [
        "par_subsumes_par_cd_star",
        "par_reduces_cd_star_trans",
        "par_reduces_cd_star_app",
        "par_reduces_cd_star_lam",
        "par_reduces_cd_star_pi",
        "par_reduces_cd_star_forall",
        "par_reduces_cd_star_beta",
        "par_reduces_cd_star_let",
    ] {
        assert_derived_proved(&spec, name);
    }
}

#[test]
fn par_reduces_pd_cd_star_sandwich_bridges_are_derived_proved() {
    // The closure-coincidence sandwich cd_star ⊆ pd_star ⊆ cd_star (plus the single
    // proper step ⊆ atomic multi-step) — what the eventual 3-way CR rides on.
    let spec = build_spec_with_stack();
    for name in [
        "par_reduces_pd_subsumes_par_cd_star",
        "par_reduces_cd_star_subsumes_par_pd_star",
        "par_reduces_pd_star_subsumes_par_cd_star",
    ] {
        assert_derived_proved(&spec, name);
    }
}

#[test]
fn par_reduces_pd_delta_substrate_bridges_are_derived_proved() {
    // The delta_p arm ingredients of the eventual par_subst_pd: the Stage-1 delta
    // E-core keystones (delta_lift_commutes / delta_subst_commutes) lifted into
    // single par_reduces_pd steps via delta_p. Demonstrates the Stage-1 delta
    // substrate plugs into the proper 3-way relation.
    let spec = build_spec_with_stack();
    for name in ["delta_step_lift_pd", "delta_step_subst_pd"] {
        assert_derived_proved(&spec, name);
    }
}
