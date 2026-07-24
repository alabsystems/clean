// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment F+ (#2859 computational-iota/delta track): the PROPER parallel
//! reduction `par_reduces_p` (parallel-iota) and its embeddings into / out of
//! `par_reduces_c`. Pins that the inductive + the two closure-bridge embeddings
//! are registered and DerivedProved (zero axiom_deps).

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
fn par_reduces_p_inductive_registered() {
    let spec = build_spec_with_stack();
    for name in [
        "par_reduces_p",
        "par_reduces_p.refl",
        "par_reduces_p.beta",
        "par_reduces_p.app",
        "par_reduces_p.lam",
        "par_reduces_p.pi",
        "par_reduces_p.forall_",
        "par_reduces_p.let_",
        // Let promotion (task #28): the trailing non-contracting let congruence.
        "par_reduces_p.let_cong",
        // The parallel-iota constructor — the whole point: it bakes in the subterm
        // reduction (par_reduces_p env e e2) before firing the deterministic iota.
        "par_reduces_p.iota_p",
        "par_reduces_p.rec",
    ] {
        assert_in_env(&spec, name);
    }
}

#[test]
fn par_reduces_p_embeddings_are_derived_proved() {
    let spec = build_spec_with_stack();
    // The two closure-bridge embeddings: par_reduces_c ⊆ par_reduces_p ⊆
    // par_reduces_c_star. Together they make the two RT-closures coincide, so
    // confluence of par_reduces_p_star will transfer to par_reduces_c_star.
    for name in [
        "par_reduces_c_subsumes_par_p",
        "par_reduces_p_subsumes_par_c_star",
    ] {
        assert_derived_proved(&spec, name);
    }
}

#[test]
fn par_reduces_p_star_substrate_registered() {
    let spec = build_spec_with_stack();
    // The RT-closure + single/multi join witnesses + combinators the strong
    // single-step diamond and its multi-step lift consume.
    for name in [
        "par_reduces_p_star",
        "par_reduces_p_star.refl",
        "par_reduces_p_star.step",
        "par_reduces_p_star.rec",
        "par_strips_witness_p",
        "par_strips_witness_p.intro",
        "par_strips_witness_p_star",
        "par_strips_witness_p_star.intro",
    ] {
        assert_in_env(&spec, name);
    }
    for name in [
        "par_subsumes_par_p_star",
        "par_reduces_p_star_trans",
        "par_strips_witness_p_to_star",
    ] {
        assert_derived_proved(&spec, name);
    }
}

#[test]
fn par_reduces_p_spine_congruences_registered() {
    let spec = build_spec_with_stack();
    // The (iota,app) spine-congruence substrate — the pointwise par-list relation
    // and apply_spine / list_append congruences the reduct congruence is built from.
    assert_in_env(&spec, "par_reduces_p_list");
    assert_in_env(&spec, "par_reduces_p_list.nil");
    assert_in_env(&spec, "par_reduces_p_list.cons");
    assert_in_env(&spec, "par_reduces_p_list.rec");
    for name in [
        "apply_spine_par_p",
        "par_reduces_p_list_refl",
        "par_reduces_p_list_append",
        "list_tail_par_p",
        "list_drop_par_p",
        "list_take_par_p",
        "kapp_args_par_p",
        "par_reduces_p_list_length_eq",
    ] {
        assert_derived_proved(&spec, name);
    }
}

#[test]
fn par_reduces_p_substitution_substrate_registered() {
    let spec = build_spec_with_stack();
    // The substitution substrate lifted from par_reduces_c through the embedding —
    // the v-congruence bases + the E-core, feeding the 1-step par_subst_p.
    for name in [
        "par_lift_p",
        "par_subst_refl_p",
        "iota_step_subst_p",
        // The FULL (par_reduces_p-valued) lift congruence — the first proof with a
        // real iota_p arm (IH + iota_lift_commutes + iota_p, one par-step).
        "par_lift_p_full",
        // The FULL (par_reduces_p-valued) reflexive substitution congruence —
        // single-step c→p mirror of par_subst_refl_full_c (bvar leaf via par_lift_p_full).
        "par_subst_refl_p_full",
        // The 1-step substitution lemma — the payoff of the parallel-iota relation
        // (iota arm assembles in ONE par-step via iota_p + iota_subst_commutes).
        "par_subst_p",
    ] {
        assert_derived_proved(&spec, name);
    }
}
