// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the abstract Hindley-Rosen tiling (#2859 Increment H++, Stage 4 —
//! Hindley-Rosen assembly).

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

/// Build the substitution subset of the spec. `add_par_reduces_cd_hr` is in the
/// substitution bundle (`in_substitution: true` in `bundles.rs`).
fn build_hr_spec() -> Specification {
    crate::test_utils::build_substitution_spec_with_stack()
}

/// The macro relations are registered with their recursors and constructors.
#[test]
fn test_hr_macro_relations_registered() {
    let spec = build_hr_spec();
    for name in [
        "m_step",
        "m_step.rec",
        "m_step.par",
        "m_step.delta",
        "m_star",
        "m_star.rec",
        "m_star.refl",
        "m_star.step",
        "m_step_join",
        "m_step_join.intro",
        "m_strip_witness",
        "m_strip_witness.intro",
        "m_star_join",
        "m_star_join.intro",
        "par_delta_commute_witness",
        "par_delta_commute_witness.intro",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered"
        );
    }
}

/// The abstract Hindley-Rosen combinators are DerivedProved with zero axiom deps.
#[test]
fn test_hr_combinators_are_derived_proved_zero_axiom() {
    let spec = build_hr_spec();
    for name in [
        "m_step_to_mstar",
        "m_star_trans",
        "m_diamond_of",
        "m_strip_of",
        "mstar_confluent_of",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
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
            def.axiom_deps.is_empty(),
            "{name} should carry no axiom dependencies: {:?}",
            def.axiom_deps
        );
        assert!(
            def.value_src.is_some(),
            "{name} should have a constructive proof term"
        );
    }
}
