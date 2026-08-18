// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the hypothesis-free Church-Rosser over `faithful_red_env`
//! (#2859, real-env confluence discharge).

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

/// Build the substitution subset of the spec. `add_faithful_confluence` is in the
/// substitution bundle (`in_substitution: true` in `bundles.rs`). Building the spec
/// kernel-checks every registered `value_src`, so a successful build is proof that
/// both faithful-confluence proof terms type-check.
fn build_spec() -> Specification {
    crate::test_utils::build_substitution_spec_with_stack()
}

/// Both unconditional confluence corollaries are registered, DerivedProved, and
/// carry zero axiom dependencies (they only apply the DerivedProved star-diamonds
/// and the four DerivedProved faithful-env interface witnesses).
#[test]
fn test_faithful_confluence_derived_proved_zero_axiom() {
    let spec = build_spec();
    for name in [
        "par_reduces_c_star_diamond_faithful",
        "par_reduces_p_star_diamond_faithful",
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

/// The discharge witnesses these corollaries consume are themselves present and
/// DerivedProved — i.e. the four interfaces are honestly discharged, not carried.
#[test]
fn test_faithful_interface_witnesses_present_and_proved() {
    let spec = build_spec();
    for name in [
        "faithful_red_env_reduct_not_redex",
        "faithful_rec_env_ctor_no_recmeta",
        "faithful_rec_env_closed",
        "faithful_rec_env_lift_closed",
        "par_reduces_c_star_diamond",
        "par_reduces_p_star_diamond",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved"
        );
    }
}
