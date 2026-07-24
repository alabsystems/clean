// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The delta faithful-interface mirror of `iota_step_bridge`: the bridge from the
//! computational `delta_step` to the abstract `delta_reduces` family (the
//! church_rosser_whnf retirement track). Pins that `DefEnvWellformed` (the δ
//! mirror of `RecEnvWellformed`) and `delta_step_to_reduces` are registered and
//! kernel-checked, and that the bridge is DerivedProved conditional on
//! `DefEnvWellformed` (its only axiom dep is `delta_reduces`, the FoundationalRule
//! family it constructs — a single-step δ subject-reduction fact, strictly weaker
//! than confluence).

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
fn defenv_wellformed_and_bridge_registered() {
    let spec = build_spec_with_stack();
    for name in [
        "DefEnvWellformed",
        "DefEnvWellformed.mk",
        "DefEnvWellformed.rec",
        "delta_step_to_reduces",
        "delta_reduces_to_step",
    ] {
        assert_in_env(&spec, name);
    }
}

#[test]
fn delta_step_to_reduces_is_derived_proved() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("delta_step_to_reduces")
        .expect("delta_step_to_reduces should be registered");

    assert!(!def.is_axiom, "delta_step_to_reduces must not be an axiom");
    assert_eq!(def.category, AxiomCategory::DerivedLemma);
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "delta_step_to_reduces should be DerivedProved"
    );

    // After the family tightening it wraps the step directly (no DefEnvWellformed
    // projection). The env is the fixed the_red_env (NOT a `forall env`, NOT a
    // postulated env constant). It constructs a delta_reduces, so delta_reduces is
    // its only axiom dep.
    assert!(
        def.type_src
            .contains("delta_step (red_def the_red_env) e e'")
            && def.type_src.contains("delta_reduces e e'")
            && !def.type_src.contains("DefEnvWellformed"),
        "bridge signature drift: {}",
        def.type_src
    );
    assert!(
        def.axiom_deps.contains("delta_reduces"),
        "bridge should record delta_reduces as the axiom it constructs: {:?}",
        def.axiom_deps
    );

    // The reverse bridge is valid exactly because the family now carries a step.
    let rev = spec
        .definitions()
        .get("delta_reduces_to_step")
        .expect("delta_reduces_to_step should be registered");
    assert!(!rev.is_axiom, "delta_reduces_to_step must not be an axiom");
    assert_eq!(rev.proof_status, ProofStatus::DerivedProved);
    assert!(
        rev.type_src.contains("delta_reduces e e'")
            && rev
                .type_src
                .contains("delta_step (red_def the_red_env) e e'"),
        "reverse bridge signature drift: {}",
        rev.type_src
    );
}
