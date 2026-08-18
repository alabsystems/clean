// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_verify::spec::ProofStatus;
use clean_verify::{ProofTerm, Specification};

fn build_substitution_spec_with_stack() -> Specification {
    clean_verify::test_utils::build_substitution_spec_with_stack()
}

#[test]
fn instantiate_wrapper_definitions_forward_through_structural_helpers() {
    let spec = build_substitution_spec_with_stack();

    for (def_name, helper_name) in [
        ("instantiate_app", "instantiate_at_app"),
        ("instantiate_lam", "instantiate_at_lam"),
        ("instantiate_pi", "instantiate_at_pi"),
    ] {
        let def = spec
            .get_definition(def_name)
            .unwrap_or_else(|| panic!("{def_name} should be registered"));

        assert!(
            !def.is_axiom,
            "{def_name} should no longer be tracked as a raw helper axiom"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{def_name} should be fully derived once {helper_name} is constructive"
        );
        assert!(
            def.value_src.is_some(),
            "{def_name} should carry a forwarding proof term"
        );
        let deps = def
            .dependencies
            .as_ref()
            .unwrap_or_else(|| panic!("{def_name} should record its forwarding dependency"));
        assert!(
            deps.contains(helper_name),
            "{def_name} dependencies should point to {helper_name}: {deps:?}"
        );
        assert!(
            !def.description
                .contains("Axiom - direct Eq.refl proof is still rejected"),
            "{def_name} description should describe the forwarding proof, got: {}",
            def.description
        );
        assert!(
            def.description.contains(helper_name),
            "{def_name} description should mention {helper_name}: {}",
            def.description
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{def_name} should have no remaining helper-axiom dependencies: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn instantiate_wrapper_proof_terms_verify() {
    let spec = build_substitution_spec_with_stack();

    for def_name in ["instantiate_app", "instantiate_lam", "instantiate_pi"] {
        let def = spec
            .get_definition(def_name)
            .unwrap_or_else(|| panic!("{def_name} should be registered"));
        let value_src = def
            .value_src
            .as_ref()
            .unwrap_or_else(|| panic!("{def_name} should have a proof term"));
        let proof = ProofTerm::new(def_name, value_src, "depth-zero instantiate wrapper");
        assert!(
            proof.verify(&spec).is_ok(),
            "{def_name} proof term should elaborate and type-check"
        );
    }
}
