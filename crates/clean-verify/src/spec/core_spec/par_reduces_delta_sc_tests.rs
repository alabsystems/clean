// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the δ-substitution tower (#2859 Increment H++, Stage 4 —
//! Hindley-Rosen assembly). Pins that the three congruence lemmas are
//! registered, kernel-checked, DerivedProved, and carry zero axiom_deps.

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

fn build_delta_sc_spec() -> Specification {
    crate::test_utils::build_substitution_spec_with_stack()
}

/// The δ-substitution tower bricks are DerivedProved with zero axiom deps.
#[test]
fn test_delta_subst_tower_is_derived_proved_zero_axiom() {
    let spec = build_delta_sc_spec();
    for name in [
        "delta_lift_cong",
        "delta_subst_cong",
        "delta_substStar_body",
        "natrec_kexpr_cong0",
        "delta_subst_val",
        "delta_substStar_val",
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
    }
}
