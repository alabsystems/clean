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
fn bvar_shift_strict_above_helper_is_constructive() {
    let spec = build_substitution_spec_with_stack();
    let def = spec
        .definitions()
        .get("instantiate_at_bvar_succ_above_shift")
        .expect("instantiate_at_bvar_succ_above_shift should exist");

    assert!(
        def.value_src.is_some(),
        "instantiate_at_bvar_succ_above_shift should now have an explicit proof term"
    );
    assert!(
        !def.is_axiom,
        "instantiate_at_bvar_succ_above_shift should not be a helper axiom"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "instantiate_at_bvar_succ_above_shift should be fully constructive"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "instantiate_at_bvar_succ_above_shift should not retain helper blockers: {:?}",
        def.axiom_deps
    );
}
