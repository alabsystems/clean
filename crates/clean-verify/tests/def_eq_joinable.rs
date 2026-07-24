// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `def_eq_joinable` (Brick 6 of the church_rosser_whnf retirement track): every
//! `DefEq e1 e2` yields a multi-step 3-way (β+ι+δ) join witness
//! `par_strips_witness_cd_star the_red_env e1 e2`, by structural `DefEq.rec`.
//!
//! Pins that the keystone `def_eq_joinable` and its two helper lemmas
//! (`join_symm`, `join_compose`) are registered, kernel-checked, `is_axiom:false`,
//! and `DerivedProved` with a real `value_src`. A green build of this test means
//! the kernel type-checked the proof terms (that IS the verification); the
//! `spec_axiom_closure_honesty` gate separately pins that their transitive
//! non-foundational closure is empty.

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
        def.value_src.as_ref().is_some_and(|v| !v.trim().is_empty()),
        "{name} should carry a real (non-empty) value_src"
    );
}

#[test]
fn def_eq_joinable_and_helpers_registered() {
    let spec = build_spec_with_stack();
    for name in ["join_symm", "join_compose", "def_eq_joinable"] {
        assert_in_env(&spec, name);
    }
}

#[test]
fn def_eq_joinable_is_derived_proved() {
    let spec = build_spec_with_stack();

    for name in ["join_symm", "join_compose", "def_eq_joinable"] {
        assert_derived_proved(&spec, name);
    }

    // Signature: carries the eight faithful interfaces i1..i8 over the LITERAL
    // the_red_env, and maps a DefEq into the 3-way join witness.
    let def = spec
        .definitions()
        .get("def_eq_joinable")
        .expect("def_eq_joinable should be registered");
    assert!(
        def.type_src.contains("DefEq e1 e2")
            && def
                .type_src
                .contains("par_strips_witness_cd_star the_red_env e1 e2"),
        "def_eq_joinable signature drift: {}",
        def.type_src
    );
    assert!(
        def.type_src
            .contains("RecEnvReductNotRedex (red_rec the_red_env)")
            && def.type_src.contains("RecEnvCtorNoDefVal the_red_env"),
        "def_eq_joinable should carry the faithful interfaces i1..i8 over the_red_env: {}",
        def.type_src
    );

    // The DerivedProved label claims an empty non-foundational closure: it must
    // not record any hand axiom_deps.
    assert!(
        def.axiom_deps.is_empty(),
        "def_eq_joinable should have zero axiom_deps: {:?}",
        def.axiom_deps
    );
}
