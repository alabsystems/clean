// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::ProofStatus;
use crate::test_utils::build_implementation_soundness_spec_with_stack;

#[test]
fn test_is_closed_at_constructor_inversions_are_constructive() {
    let spec = build_implementation_soundness_spec_with_stack();

    for name in [
        "is_closed_at_app_fun",
        "is_closed_at_app_arg",
        "is_closed_at_lam_type",
        "is_closed_at_pi_type",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(
            !def.is_axiom,
            "{name} should be a constructive inversion lemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be fully constructive"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have no axiom deps: {:?}",
            def.axiom_deps
        );
        assert!(def.value_src.is_some(), "{name} should have a proof term");
    }
}

#[test]
fn test_app_admissibility_wrappers_reduce_to_closed_subexpressions() {
    let spec = build_implementation_soundness_spec_with_stack();

    for (name, inversion) in [
        ("kernel_input_admissible_app_fun", "is_closed_at_app_fun"),
        ("kernel_input_admissible_app_arg", "is_closed_at_app_arg"),
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be fully constructive"
        );
        let deps = def
            .dependencies
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should record dependencies"));
        assert!(
            deps.contains("KernelInputAdmissible") && deps.contains(inversion),
            "{name} should compose KernelInputAdmissible with {inversion}, got {deps:?}"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should not reintroduce admissibility axioms: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn test_lam_pi_admissibility_wrappers_reduce_to_closed_parameter_types() {
    let spec = build_implementation_soundness_spec_with_stack();

    for (name, inversion) in [
        ("kernel_input_admissible_lam_type", "is_closed_at_lam_type"),
        ("kernel_input_admissible_pi_type", "is_closed_at_pi_type"),
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be fully constructive"
        );
        let deps = def
            .dependencies
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should record dependencies"));
        assert!(
            deps.contains("KernelInputAdmissible") && deps.contains(inversion),
            "{name} should compose KernelInputAdmissible with {inversion}, got {deps:?}"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should not reintroduce admissibility axioms: {:?}",
            def.axiom_deps
        );
    }
}
