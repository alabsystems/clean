// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::ProofStatus;
use crate::test_utils::build_spec_with_stack;

#[test]
fn test_binder_witness_definitions_exist() {
    let spec = build_spec_with_stack();
    // The two binder-admissibility guards KernelLam/PiBodyAdmissible are RETIRED
    // as vestigial (census 18->16), alongside the body-type and level Skolems
    // (bound inside Lam/PiInferWitness).
    for retired in [
        "KernelLamBodyAdmissible",
        "KernelPiBodyAdmissible",
        "KernelLamBodyType",
        "KernelLamDomainLevel",
        "KernelPiDomainLevel",
        "KernelPiCodomainLevel",
    ] {
        assert!(
            !spec.definitions().contains_key(retired),
            "retired binder Skolem {retired} should be gone (vestigial or bound inside a witness)"
        );
    }
    // The packaged-existential witnesses that carry the real content are inductives.
    for name in ["LamInferWitness", "PiInferWitness"] {
        assert!(
            spec.definitions().contains_key(name),
            "expected witness inductive {name} to be registered"
        );
    }
}

#[test]
fn test_binder_structural_step_axioms_retired() {
    let spec = build_spec_with_stack();
    // The body-step projections are RETIRED (census 18->16): they were dead-end
    // ProdType.fst projections of the vestigial binder-admissibility guards,
    // consumed by nothing but tests + the ProofLibrary twin.
    // kernel_infer_lam_result_step was retired earlier (its type named
    // KernelLamBodyType).
    for retired in [
        "kernel_infer_lam_body_step",
        "kernel_infer_pi_body_step",
        "kernel_infer_lam_result_step",
    ] {
        assert!(
            !spec.definitions().contains_key(retired),
            "retired binder step projection {retired} should be gone"
        );
    }
}

#[test]
fn test_binder_witnesses_are_kernel_inductives() {
    let spec = build_spec_with_stack();
    // The guards KernelLam/PiBodyAdmissible are retired; the packaged-existential
    // witnesses that carry the real typing content are kernel-checked inductives,
    // NOT axioms.
    for name in ["LamInferWitness", "PiInferWitness"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(
            !def.is_axiom,
            "{name} must be a kernel inductive, not an axiom"
        );
    }
}

#[test]
fn test_binder_decompositions_are_derived() {
    let spec = build_spec_with_stack();
    // The consolidated lam/pi decompositions are no longer HelperAxioms: the
    // faithful KernelInferAccepts lam/pi constructors carry the Lam/PiInferWitness
    // existential directly, recovered via kernel_infer_inversion (Step 3).
    for name in [
        "kernel_infer_lam_decomposition",
        "kernel_infer_pi_decomposition",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(
            !def.is_axiom,
            "{name} should now be derived via kernel_infer_inversion (Step 3)"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (kernel-checked derivation)"
        );
        assert!(
            def.value_src
                .as_ref()
                .unwrap_or_else(|| panic!("{name} should carry a proof term"))
                .contains("kernel_infer_inversion"),
            "{name} should be derived via kernel_infer_inversion"
        );
    }
}
