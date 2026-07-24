// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment B (#2859 computational-iota/delta track): the recursor-environment
//! data model. Pins that `OptionType`, `RecRule`/`RecRules`/`RecMeta`/`RecEnv`,
//! the `nat_eqb`/`name_eqb` decidable equalities, the field projectors, and the
//! name-keyed lookups are all registered and kernel-checked, and that
//! `option_some_inj` (the determinism ingredient) is DerivedProved with zero
//! axiom_deps. See `designs/2026-06-14-computational-iota-delta-track.md`.

use clean_kernel::Name;
use clean_verify::spec::{AxiomCategory, ProofStatus};
use clean_verify::test_utils::build_spec_with_stack;

fn assert_in_env(spec: &clean_verify::spec::Specification, name: &str) {
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered in the spec environment"
    );
}

/// The inductives + their auto-generated recursors/constructors are registered.
#[test]
fn rec_env_inductives_registered() {
    let spec = build_spec_with_stack();
    for name in [
        "OptionType",
        "OptionType.none",
        "OptionType.some",
        "OptionType.rec",
        "RecRule",
        "RecRule.mk",
        "RecRules",
        "RecRules.nil",
        "RecRules.cons",
        "RecMeta",
        "RecMeta.mk",
        "RecEnv",
        "RecEnv.empty",
        "RecEnv.addRec",
    ] {
        assert_in_env(&spec, name);
    }
}

/// `option_some_inj` (some x = some y -> x = y) is DerivedProved with zero
/// axiom_deps — the determinism ingredient for iota_step.
#[test]
fn option_some_inj_is_derived_proved() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("option_some_inj")
        .expect("option_some_inj should be registered");
    assert!(!def.is_axiom, "option_some_inj must not be an axiom");
    assert_eq!(def.category, AxiomCategory::DerivedLemma);
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "option_some_inj should be DerivedProved"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "option_some_inj should carry zero axiom_deps: {:?}",
        def.axiom_deps
    );
}

/// The decidable equalities, field projectors, and name-keyed lookups are all
/// registered (kernel-checked at spec build).
#[test]
fn rec_env_equality_projectors_and_lookups_registered() {
    let spec = build_spec_with_stack();
    for name in [
        // decidable equality
        "nat_is_zero",
        "nat_eqb",
        "name_eqb",
        // RecRule / RecMeta projectors
        "recrule_ctor_name",
        "recrule_num_fields",
        "recrule_rhs",
        "recmeta_num_params",
        "recmeta_num_motives",
        "recmeta_num_minors",
        "recmeta_num_indices",
        "recmeta_major_after_minors",
        // branch helpers + name-keyed lookups
        "opt_pick",
        "bool_pick",
        "recrule_in_rules",
        "recrules_for",
        "recmeta_for",
        "is_recursor",
        "recrule_for",
    ] {
        assert_in_env(&spec, name);
    }
}
