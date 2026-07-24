// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dependency audit tests, error path coverage, and forward simulation
//! proof verification.
//!
//! Split from `proofs/tests.rs` -- Part of #2765.

use super::*;
use crate::test_utils::build_spec_with_stack;
use clean_kernel::{Level, LevelVec};

// =========================================================================
// Dependency Audit Tests (#326, #393)
// =========================================================================

/// Helper to verify a proof against the specification
fn verify_proof(proof_name: &str) -> Result<(), ProofError> {
    let spec = build_spec_with_stack();
    let lib = ProofLibrary::new();
    let proof = lib
        .get(proof_name)
        .ok_or_else(|| ProofError::UnknownProperty(proof_name.to_string()))?;
    proof.verify(&spec)
}

#[test]
fn test_audit_dependencies_type_preservation() {
    // Part of #326, #393: Proof dependency audit
    let spec = build_spec_with_stack();
    let lib = ProofLibrary::new();
    let report = lib.audit_dependencies(&spec);

    // TypePreservation should have a result
    let tp_result = report
        .results
        .get("TypePreservation")
        .expect("TypePreservation should have a dependency result");

    // Trust frontier: 0 HelperAxiom leaves remain. #2859 retired the last
    // structural leaf `church_rosser_whnf` (re-pointed onto the constructive
    // confluence tower carrying a RedEnvFaithful the_red_env hypothesis). The
    // audit (HelperAxiom-counting) therefore reports the chain as constructive;
    // the residual value-less def_eq_to_eq bridge is tracked separately by the
    // no-new-axioms ratchet, not as a TypePreservation HelperAxiom leaf.
    assert_eq!(tp_result.status, ProofStatus::DerivedProved);
    let expected_axioms: [&str; 0] = [];
    assert_eq!(
        tp_result.axiom_deps.len(),
        expected_axioms.len(),
        "{:?}",
        tp_result.axiom_deps
    );
    for ax in &expected_axioms {
        assert!(
            tp_result.axiom_deps.contains(*ax),
            "missing {ax}: {:?}",
            tp_result.axiom_deps
        );
    }

    // There should be no error
    assert!(
        tp_result.error.is_none(),
        "TypePreservation should not have an error: {:?}",
        tp_result.error
    );
}

#[test]
fn test_audit_dependencies_report_counts() {
    // Part of #326, #393: Verify audit report provides meaningful counts
    let spec = build_spec_with_stack();
    let lib = ProofLibrary::new();
    let report = lib.audit_dependencies(&spec);

    // We should have proofs in the report
    assert!(
        !report.results.is_empty(),
        "Audit report should have results"
    );

    // Total should equal sum of categories
    let total = report.fully_proved + report.pending + report.axioms + report.errors;
    assert_eq!(
        total,
        report.results.len(),
        "Category counts should sum to total results"
    );

    // Should have at least one pending proof (TypePreservation depends on HelperAxiom)
    assert!(report.pending > 0, "Should have at least one pending proof");
}

// ════════════════════════════════════════════════════════════════════════════
// Error path tests (#524)
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_proof_term_unknown_property_error() {
    // Part of #524: Test ProofError::UnknownProperty
    let spec = build_spec_with_stack();
    let proof = ProofTerm::new(
        "NonExistentProperty",
        "fun x => x",
        "Test unknown property error",
    );
    let result = proof.verify(&spec);
    let err = result.unwrap_err();
    assert!(matches!(err, ProofError::UnknownProperty(_)));
    assert!(err.to_string().contains("NonExistentProperty"));
}

#[test]
fn test_proof_term_parse_error() {
    // Part of #524: Test ProofError::ParseError
    let spec = build_spec_with_stack();
    // Use valid property with invalid proof syntax
    let proof = ProofTerm::new("Eq", "invalid [[[ syntax", "Test parse error");
    let result = proof.verify(&spec);
    let err = result.unwrap_err();
    assert!(matches!(err, ProofError::ParseError(_)));
    // Verify error message contains "proof" (the context where parsing failed)
    assert!(
        err.to_string().contains("proof"),
        "ParseError should mention 'proof' context: {}",
        err
    );
}

#[test]
fn test_proof_term_elab_error() {
    // Part of #524: Test ProofError::ElabError
    let spec = build_spec_with_stack();
    // Use valid property with undefined constant in proof
    let proof = ProofTerm::new("Eq", "UndefinedConstant", "Test elab error");
    let result = proof.verify(&spec);
    let err = result.unwrap_err();
    assert!(matches!(err, ProofError::ElabError(_)));
    // Verify error message contains context about what failed
    assert!(
        err.to_string().contains("proof"),
        "ElabError should mention 'proof' context: {}",
        err
    );
}

#[test]
fn test_proof_term_type_mismatch_error() {
    // Part of #524: Test ProofError::TypeMismatch
    let spec = build_spec_with_stack();
    // Nat.zero has type Nat, but has_type expects KExpr -> KExpr -> Type
    let proof = ProofTerm::new("has_type", "Nat.zero", "Test type mismatch error");
    let result = proof.verify(&spec);
    let err = result.unwrap_err();
    assert!(matches!(err, ProofError::TypeMismatch { .. }));
    // Verify error shows expected/actual mismatch
    let err_str = err.to_string();
    assert!(
        err_str.contains("expected") || err_str.contains("Expected"),
        "TypeMismatch should mention expected type: {}",
        err
    );
}

#[test]
fn test_universe_vector_only_mismatch_is_rejected() {
    let spec = build_spec_with_stack();
    let tc = clean_kernel::TypeChecker::with_mode(spec.env(), spec.env().mode());
    let eq_name = clean_kernel::name::Name::from_string("Eq");
    let expected = Expr::const_(eq_name.clone(), vec![Level::zero()]);
    let actual = Expr::const_(eq_name.clone(), vec![Level::succ(Level::zero())]);

    assert!(
        !tc.is_def_eq(&actual, &expected),
        "strict proof checking must reject differing constant universe vectors"
    );
    assert!(
        !verify::test_proof_type_matches(&tc, &actual, &expected),
        "verifier-level proof type matching must reject differing constant universe vectors"
    );

    let erased_expected = Expr::const_(eq_name.clone(), LevelVec::new());
    let erased_actual = Expr::const_(eq_name, LevelVec::new());
    assert_eq!(
        erased_actual, erased_expected,
        "the removed erase_const_levels fallback would have hidden this mismatch"
    );
}

// =========================================================================
// #461: Forward simulation and WHNF bridge proof existence tests
// =========================================================================

#[test]
fn test_forward_simulation_proofs_exist() {
    let lib = ProofLibrary::new();

    // WHNF bridge proofs
    lib.get("beta_reduces_preserves_def_eq")
        .expect("proof 'beta_reduces_preserves_def_eq' missing from library");
    lib.get("whnf_to_preserves_def_eq")
        .expect("proof 'whnf_to_preserves_def_eq' missing from library");

    // Forward simulation theorems
    lib.get("KernelWhnfSound")
        .expect("proof 'KernelWhnfSound' missing from library");
    lib.get("KernelInferSound")
        .expect("proof 'KernelInferSound' missing from library");
    lib.get("KernelDefEqSound")
        .expect("proof 'KernelDefEqSound' missing from library");

    // DefEq transport lemmas
    lib.get("def_eq_eq_left")
        .expect("proof 'def_eq_eq_left' missing from library");
    lib.get("def_eq_eq_right")
        .expect("proof 'def_eq_eq_right' missing from library");
}

#[test]
fn test_whnf_bridge_proofs_elaborate() {
    // Part of #461: verify the constructive WHNF bridge proofs
    for proof_name in ["beta_reduces_preserves_def_eq", "whnf_to_preserves_def_eq"] {
        let result = verify_proof(proof_name);
        assert!(
            result.is_ok(),
            "{proof_name} proof should elaborate and type-check: {:?}",
            result.err()
        );
    }
}

#[test]
fn test_forward_simulation_theorems_elaborate() {
    // Part of #461: verify the forward simulation proof terms
    for proof_name in ["KernelWhnfSound", "KernelInferSound", "KernelDefEqSound"] {
        let result = verify_proof(proof_name);
        assert!(
            result.is_ok(),
            "{proof_name} proof should elaborate and type-check: {:?}",
            result.err()
        );
    }
}

#[test]
fn test_def_eq_transport_proofs_elaborate() {
    // Part of #461: verify DefEq transport lemma proof terms
    for proof_name in ["def_eq_eq_left", "def_eq_eq_right"] {
        let result = verify_proof(proof_name);
        assert!(
            result.is_ok(),
            "{proof_name} proof should elaborate and type-check: {:?}",
            result.err()
        );
    }
}
