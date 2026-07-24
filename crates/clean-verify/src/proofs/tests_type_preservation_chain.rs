// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused proof-library tests for the type-preservation chain.

use super::*;
use crate::test_utils::build_spec_with_stack;

// #464 Packet D: def_eq_to_eq demoted from HelperAxiom to DerivedLemma. #2859
// then retired the last structural leaf `church_rosser_whnf` (re-pointed onto the
// constructive confluence tower carrying a RedEnvFaithful the_red_env hypothesis).
// The remaining HelperAxiom leaf set is now empty, so the whole chain audits as
// constructive (the residual value-less def_eq_to_eq bridge is tracked by the
// no-new-axioms ratchet, not as a TypePreservation HelperAxiom leaf).

fn assert_proved(report: &DependencyAuditReport, proof_name: &str) {
    let result = report
        .results
        .get(proof_name)
        .unwrap_or_else(|| panic!("{proof_name} should have a dependency result"));

    assert_eq!(
        result.status,
        ProofStatus::DerivedProved,
        "{proof_name} should be fully constructive"
    );
    assert!(
        result.axiom_deps.is_empty(),
        "{proof_name} should not report helper-axiom dependencies: {:?}",
        result.axiom_deps
    );
    assert!(
        result.error.is_none(),
        "{proof_name} should not have an audit error: {:?}",
        result.error
    );
}

#[test]
fn test_type_preservation_chain_proofs_exist() {
    let lib = ProofLibrary::new();

    for name in [
        "beta_lam_dom_sort",
        "beta_lam_body_subst",
        "beta_type_preservation",
        "beta_type_expansion",
        "sort_universe_consistency",
    ] {
        lib.get(name)
            .unwrap_or_else(|| panic!("proof '{name}' missing from library"));
    }
}

#[test]
fn test_type_preservation_chain_proof_audit_status() {
    let spec = build_spec_with_stack();
    let lib = ProofLibrary::new();
    let report = lib.audit_dependencies(&spec);

    assert_proved(&report, "beta_lam_dom_sort");
    assert_proved(&report, "sort_universe_consistency");

    for name in [
        "TypePreservation",
        "type_preservation_helper",
        "beta_lam_body_subst",
        "beta_type_preservation",
        "beta_type_expansion",
    ] {
        assert_proved(&report, name);
    }
}
