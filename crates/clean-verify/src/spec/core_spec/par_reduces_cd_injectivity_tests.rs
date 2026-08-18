// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the cd-relation join-witness -> injectivity (I-half) tower
//! (`par_reduces_cd_injectivity.rs`).

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

/// Build the substitution subset of the spec. The cd-injectivity tower is in the
/// substitution bundle (`in_substitution: true`), so reaching this builder IS the
/// kernel-check witness: the closed proof terms were type-checked by `add_decl`
/// during spec construction, so an ill-typed or faked term would have failed
/// `new_substitution_test_spec()` before any assertion ran.
fn build_spec() -> Specification {
    crate::test_utils::build_substitution_spec_with_stack()
}

/// Every cd-relation pi/lam/sort shape-inversion + injectivity lemma is a
/// DerivedProved closed term with an empty axiom closure (genuine 0-axiom, not a
/// masquerade).
#[test]
fn test_par_reduces_cd_injectivity_is_zero_axiom_derived_proved() {
    let spec = build_spec();
    for &name in CD_INJECTIVITY_LEMMAS {
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
            "{name} should be DerivedProved (closed, kernel-checked term)"
        );
        assert!(
            def.value_src.is_some(),
            "{name} should carry a closed proof term"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} must have an EMPTY axiom closure (genuine 0-axiom): {:?}",
            def.axiom_deps
        );
    }
}

/// The cd-relation I-half lemmas landed by this module.
const CD_INJECTIVITY_LEMMAS: &[&str] = &[
    "par_reduces_cd_pi_inv_eq",
    "par_reduces_cd_lam_inv_eq",
    "par_reduces_cd_star_pi_inv",
    "par_reduces_cd_star_pi_inv_eq",
    "par_reduces_cd_star_lam_inv",
    "par_reduces_cd_star_lam_inv_eq",
    "par_cd_pi_injectivity_dom",
    "par_cd_pi_injectivity_cod",
    "par_cd_lam_injectivity_dom",
    "par_cd_lam_injectivity_cod",
    "par_reduces_cd_sort_inv_eq",
    "par_reduces_cd_star_sort_inv_eq",
    "par_cd_sort_injectivity",
];
