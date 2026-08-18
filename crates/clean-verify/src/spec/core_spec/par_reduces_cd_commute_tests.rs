// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the β+ι/δ commutation star-tiling (#2859 Increment H++, Stage 4 —
//! Hindley-Rosen assembly).

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

fn build_hr_spec() -> Specification {
    crate::test_utils::build_substitution_spec_with_stack()
}

/// The commutation star-tiling lemmas are DerivedProved with zero axiom deps.
#[test]
fn test_hr_commute_lemmas_are_derived_proved_zero_axiom() {
    let spec = build_hr_spec();
    for name in ["par_delta_commute_one_of_sc", "par_delta_commute_of_sc"] {
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
    }
}

/// `par_delta_sc_witness` is registered with its recursor and constructor.
#[test]
fn test_par_delta_sc_witness_registered() {
    let spec = build_hr_spec();
    for name in [
        "par_delta_sc_witness",
        "par_delta_sc_witness.rec",
        "par_delta_sc_witness.intro",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered"
        );
    }
}
