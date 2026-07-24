// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_verify::spec::ProofStatus;
use clean_verify::test_utils::run_with_stack;
use clean_verify::Specification;

fn build_substitution_spec_with_stack() -> Specification {
    run_with_stack(|| {
        Specification::new_substitution_test_spec()
            .expect("substitution/WHNF test spec should build")
    })
}

#[test]
fn bvar_lift_subst_bridge_helpers_are_constructive() {
    let spec = build_substitution_spec_with_stack();

    for name in [
        "instantiate_at_lift_at_zero_succ_commutes_bvar",
        "instantiate_at_lift_at_zero_commutes_bvar",
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
fn inst_overlift_cancel_is_derived_modulo_shift_succ() {
    let spec = build_substitution_spec_with_stack();

    let def = spec
        .definitions()
        .get("inst_overlift_cancel")
        .expect("inst_overlift_cancel should exist");
    assert!(
        def.value_src.is_some(),
        "inst_overlift_cancel should have an explicit proof term"
    );
    assert!(
        !def.is_axiom,
        "inst_overlift_cancel should not be a helper axiom"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "inst_overlift_cancel should be DerivedProved"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "inst_overlift_cancel should have no remaining axiom deps (lift_at_shift_succ now proved): {:?}",
        def.axiom_deps
    );
}
