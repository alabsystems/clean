// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_verify::spec::ProofStatus;
use clean_verify::Specification;

fn build_substitution_spec_with_stack() -> Specification {
    clean_verify::test_utils::build_substitution_spec_with_stack()
}

#[test]
fn bvar_shift_boundary_helpers_are_constructive() {
    let spec = build_substitution_spec_with_stack();

    for name in [
        "lift_at_bvar_zero_succ",
        "instantiate_at_bvar_succ_eq_shift",
        "instantiate_at_bvar_succ_eq_from_zero_witnesses",
        "instantiate_at_bvar_succ_below_shift",
        "instantiate_at_bvar_add_succ_reduces",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert!(
            def.value_src.is_some(),
            "{name} should now have an explicit proof term"
        );
        assert!(!def.is_axiom, "{name} should not be a helper axiom");
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be fully constructive"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should not retain helper blockers: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn bvar_shift_above_frontier_helpers_are_constructive() {
    let spec = build_substitution_spec_with_stack();

    for name in [
        "instantiate_at_bvar_succ_above_shift",
        "instantiate_at_bvar_succ_gap_shift",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert!(
            def.value_src.is_some(),
            "{name} should now have an explicit proof term"
        );
        assert!(!def.is_axiom, "{name} should not remain a helper axiom");
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should now be fully constructive"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should not retain helper blockers: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn bvar_equality_witness_helpers_are_constructive() {
    let spec = build_substitution_spec_with_stack();

    for name in [
        "instantiate_bvar_at_eq_from_zero_witnesses",
        "instantiate_at_bvar_eq_from_zero_witnesses",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert!(
            def.value_src.is_some(),
            "{name} should now have an explicit proof term"
        );
        assert!(!def.is_axiom, "{name} should not be a helper axiom");
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be fully constructive"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should not retain helper blockers: {:?}",
            def.axiom_deps
        );
    }
}
