// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `the_red_env`: the single distinguished reduction environment DefEq is relative
//! to (church_rosser_whnf retirement track, deletion-plan choice 3c). Pins that it
//! is a value-ful Definition (NOT a postulated axiom — Guard 2) and that it
//! genuinely admits both an iota and a delta step (the two refl non-vacuity
//! witnesses are kernel-checked DerivedProved with ZERO axiom_deps — Guard 4).
//! These two facts are exactly the feasibility claim the deletion plan rests on:
//! the tightened iota_reduces / delta_reduces families are inhabited, not vacuous.

use clean_kernel::Name;
use clean_verify::spec::{AxiomCategory, ProofStatus, Specification};
use clean_verify::test_utils::build_spec_with_stack;

fn assert_in_env(spec: &Specification, name: &str) {
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered in the spec environment"
    );
}

#[test]
fn the_red_env_and_nonvacuity_witnesses_registered() {
    let spec = build_spec_with_stack();
    for name in [
        "the_red_env",
        "the_red_env_iota_nonvacuous",
        "the_red_env_delta_nonvacuous",
    ] {
        assert_in_env(&spec, name);
    }
}

#[test]
fn the_red_env_is_a_valueful_definition_not_an_axiom() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("the_red_env")
        .expect("the_red_env should be registered");
    // Guard 2: a value-ful Definition, never a value-less Axiom (which the ratchet
    // would count). Carries a RedEnv.mk value over a non-empty RecEnv + DefEnv.
    assert!(
        !def.is_axiom,
        "the_red_env must be a value-ful Definition, not an axiom (Guard 2)"
    );
    assert!(
        def.type_src.contains("RedEnv"),
        "the_red_env should have type RedEnv: {}",
        def.type_src
    );
    assert!(
        def.axiom_deps.is_empty(),
        "the_red_env must carry no axiom deps: {:?}",
        def.axiom_deps
    );
}

/// Front #1 Stage 3 pin: the_red_env is the value-level ALIAS of the
/// fidelity-gated reflection kernel_core_red_env, and the two Guard-4
/// witnesses fire on the REAL env (the reflected Nat.rec / the reflected
/// def_env_lift_closed_b entry — interned atoms kcre_name_25 / kcre_name_116).
#[test]
fn the_red_env_is_the_kernel_core_reflection_alias() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("the_red_env")
        .expect("the_red_env should be registered");
    assert!(
        def.value_src
            .as_deref()
            .is_some_and(|v| v.contains("kernel_core_red_env")),
        "the_red_env must alias kernel_core_red_env (Stage 3 swap), got: {:?}",
        def.value_src
    );
    let iota = spec
        .definitions()
        .get("the_red_env_iota_nonvacuous")
        .expect("iota witness should be registered");
    assert!(
        iota.type_src.contains("kcre_name_25"),
        "iota witness must fire on the reflected Nat.rec (kcre_name_25): {}",
        iota.type_src
    );
    let delta = spec
        .definitions()
        .get("the_red_env_delta_nonvacuous")
        .expect("delta witness should be registered");
    assert!(
        delta.type_src.contains("kcre_name_116"),
        "delta witness must fire on the reflected def_env_lift_closed_b (kcre_name_116): {}",
        delta.type_src
    );
}

#[test]
fn nonvacuity_witnesses_are_derived_proved_zero_axiom() {
    let spec = build_spec_with_stack();
    for name in [
        "the_red_env_iota_nonvacuous",
        "the_red_env_delta_nonvacuous",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} must not be an axiom");
        assert_eq!(def.category, AxiomCategory::DerivedLemma, "{name} category");
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (kernel-checked refl on the computational reduct)"
        );
        // Guard 4 substance: these are PURE computation — no axiom may sneak in.
        assert!(
            def.axiom_deps.is_empty(),
            "{name} must be a zero-axiom computational witness: {:?}",
            def.axiom_deps
        );
    }
}
