// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment G (#2859 computational-iota/delta track) — the δ analogue of the
//! Increment C keystone. Pins that the computational delta reduct `delta_reduct`,
//! the definition environment `DefEnv` + `defval_for` lookup, the graph predicate
//! `delta_step`, and the determinism lemma `delta_step_deterministic` are
//! registered and kernel-checked, and that `delta_step_deterministic` is
//! DerivedProved with zero axiom_deps — free, because `delta_reduct` is a total
//! function and `delta_step` is its graph.

use clean_kernel::Name;
use clean_verify::spec::{AxiomCategory, ProofStatus, Specification};
use clean_verify::test_utils::build_spec_with_stack;

fn assert_in_env(spec: &Specification, name: &str) {
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered in the spec environment"
    );
}

/// The DefEnv data model + reduct function + graph are registered (kernel-checked).
#[test]
fn delta_reduct_and_substrate_registered() {
    let spec = build_spec_with_stack();
    for name in [
        "DefEnv",
        "DefEnv.empty",
        "DefEnv.addDef",
        "defval_for",
        "delta_reduct",
        "delta_step",
    ] {
        assert_in_env(&spec, name);
    }
}

/// The δ keystone: `delta_step_deterministic` is DerivedProved, zero axiom_deps,
/// and depends on the reduct function + some-injectivity.
#[test]
fn delta_step_deterministic_is_derived_proved() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("delta_step_deterministic")
        .expect("delta_step_deterministic should be registered");

    assert!(
        !def.is_axiom,
        "delta_step_deterministic must not be an axiom"
    );
    assert_eq!(def.category, AxiomCategory::DerivedLemma);
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "delta_step_deterministic should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "delta_step_deterministic should carry zero axiom_deps: {:?}",
        def.axiom_deps
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("delta_step_deterministic should record dependencies");
    for expected in ["delta_reduct", "option_some_inj"] {
        assert!(
            deps.contains(expected),
            "delta_step_deterministic should depend on {expected}: {deps:?}"
        );
    }
}

/// The δ CPS inverter + the const-head discharge primitive are DerivedProved.
#[test]
fn delta_inverter_and_discharge_are_derived_proved() {
    let spec = build_spec_with_stack();
    for name in ["delta_reduct_some_inv", "delta_step_head_none_absurd"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} must not be an axiom");
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

    // The discharge primitive inverts via the CPS inverter (mirror of the iota one).
    let disc = spec
        .definitions()
        .get("delta_step_head_none_absurd")
        .expect("registered");
    assert!(
        disc.dependencies
            .as_ref()
            .expect("deps")
            .contains("delta_reduct_some_inv"),
        "delta_step_head_none_absurd should invert via delta_reduct_some_inv"
    );
}
