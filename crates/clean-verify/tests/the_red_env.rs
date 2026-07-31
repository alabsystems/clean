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

use std::collections::BTreeSet;

use clean_kernel::Name;
use clean_verify::red_env_reflect::committed_name_atom;
use clean_verify::spec::{AxiomCategory, ProofStatus, Specification};
use clean_verify::test_utils::build_spec_with_stack;

fn generated_name_atom(real_name: &str) -> String {
    committed_name_atom(real_name)
        .unwrap_or_else(|e| panic!("missing generated interning entry for {real_name}: {e}"))
}

fn assert_in_env(spec: &Specification, name: &str) {
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered in the spec environment"
    );
}

fn generated_name_atoms(spec: &Specification, helper: &str) -> BTreeSet<String> {
    spec.definitions()
        .get(helper)
        .unwrap_or_else(|| panic!("generated helper {helper} should be registered"))
        .elaborated_value
        .as_ref()
        .unwrap_or_else(|| panic!("generated helper {helper} should be valueful"))
        .collect_constants()
        .into_iter()
        .map(|name| name.to_string())
        .filter(|name| name.starts_with("kcre_name_"))
        .collect()
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
/// def_env_lift_closed_b entry). The witnesses consume generator-owned semantic
/// helper definitions; this test separately pins their exact semantic-name
/// atoms to the validated interning table (no substring matching).
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
    for helper in [
        "kcre_witness_nat_zero_redex",
        "kcre_witness_nat_zero_reduct",
    ] {
        assert!(
            iota.type_src.contains(helper),
            "iota witness must consume generated helper {helper}: {}",
            iota.type_src
        );
    }
    let nat_rec = generated_name_atom("Nat.rec");
    let nat_zero = generated_name_atom("Nat.zero");
    let nat = generated_name_atom("Nat");
    let nat_succ = generated_name_atom("Nat.succ");
    assert_eq!(
        generated_name_atoms(&spec, "kcre_witness_nat_zero_redex"),
        BTreeSet::from([nat_rec, nat_zero.clone()]),
        "generated redex must contain exactly the reflected Nat.rec and Nat.zero name atoms"
    );
    assert_eq!(
        generated_name_atoms(&spec, "kcre_witness_nat_zero_reduct"),
        BTreeSet::from([nat, nat_zero, nat_succ]),
        "generated reduct must contain exactly the semantic atoms in the reflected Nat.zero rule RHS"
    );
    let delta = spec
        .definitions()
        .get("the_red_env_delta_nonvacuous")
        .expect("delta witness should be registered");
    for helper in ["kcre_witness_delta_head", "kcre_witness_delta_value"] {
        assert!(
            delta.type_src.contains(helper),
            "delta witness must consume generated helper {helper}: {}",
            delta.type_src
        );
    }
    let delta_head = generated_name_atom("def_env_lift_closed_b");
    assert_eq!(
        generated_name_atoms(&spec, "kcre_witness_delta_head"),
        BTreeSet::from([delta_head]),
        "delta-head helper must resolve exactly to reflected def_env_lift_closed_b"
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
