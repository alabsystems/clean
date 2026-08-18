// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Hindley-Rosen closure-coincidence sandwich + composition
//! (#2859 Increment H++, Stage 4 — Hindley-Rosen assembly).

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

fn build_hr_spec() -> Specification {
    crate::test_utils::build_substitution_spec_with_stack()
}

/// The sandwich + composition lemmas are DerivedProved with zero axiom deps.
#[test]
fn test_hr_compose_lemmas_are_derived_proved_zero_axiom() {
    let spec = build_hr_spec();
    for name in [
        "m_step_appL",
        "m_step_appR",
        "m_step_lamL",
        "m_step_lamR",
        "m_step_piL",
        "m_step_piR",
        "m_star_appL",
        "m_star_appR",
        "m_star_app",
        "m_star_lam",
        "m_star_pi",
        "par_reduces_c_star_subsumes_cd_star",
        "m_step_to_cd_star",
        "m_star_to_cd_star",
        "par_reduces_cd_subsumes_m_star",
        "par_reduces_cd_star_subsumes_m_star",
        "par_reduces_cd_star_diamond_of_commute",
        "par_reduces_cd_star_diamond_of_sc",
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

/// `par_strips_witness_cd_star` is registered with its recursor and constructor.
#[test]
fn test_par_strips_witness_cd_star_registered() {
    let spec = build_hr_spec();
    for name in [
        "par_strips_witness_cd_star",
        "par_strips_witness_cd_star.rec",
        "par_strips_witness_cd_star.intro",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered"
        );
    }
}
