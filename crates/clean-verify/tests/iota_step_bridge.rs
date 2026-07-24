// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment D (#2859 computational-iota/delta track): the bridge from the
//! computational `iota_step` to the abstract `iota_reduces` family. Pins that
//! `RecEnvWellformed` (the faithful-interface predicate) and `iota_step_to_reduces`
//! are registered and kernel-checked, and that the bridge is DerivedProved
//! conditional on `RecEnvWellformed` (its only axiom dep is `iota_reduces`, since
//! it constructs one — path D(i), the existing iota_reduces surface is preserved).

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
fn recenv_wellformed_and_bridge_registered() {
    let spec = build_spec_with_stack();
    for name in [
        "RecEnvWellformed",
        "RecEnvWellformed.mk",
        "RecEnvWellformed.rec",
        "iota_step_to_reduces",
    ] {
        assert_in_env(&spec, name);
    }
}

#[test]
fn iota_step_to_reduces_is_derived_proved() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("iota_step_to_reduces")
        .expect("iota_step_to_reduces should be registered");

    assert!(!def.is_axiom, "iota_step_to_reduces must not be an axiom");
    assert_eq!(def.category, AxiomCategory::DerivedLemma);
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "iota_step_to_reduces should be DerivedProved"
    );

    // Over the fixed `the_red_env` (the church-rosser tightening pinned the
    // bridge to `red_rec the_red_env`, dropping the earlier universally-
    // quantified `RecEnvWellformed env` premise): it takes a concrete
    // `iota_step (red_rec the_red_env) e e'` and constructs an `iota_reduces e e'`.
    // (Assertion re-pinned from the retired `RecEnvWellformed env`/`iota_step env`
    // surface, which had been stale-red since c318060c; unrelated to the
    // iota_reduces inductivization, which touches only the REVERSE bridge.)
    assert!(
        def.type_src
            .contains("iota_step (red_rec the_red_env) e e'")
            && def.type_src.contains("iota_reduces e e'"),
        "bridge signature drift: {}",
        def.type_src
    );
    // iota_reduces is now a genuine inductive (not a census axiom) after the
    // #2859 R1 drain; the bridge still names it as the family it inhabits.
    assert!(
        def.axiom_deps.contains("iota_reduces"),
        "bridge should record iota_reduces as the family it constructs: {:?}",
        def.axiom_deps
    );
}
