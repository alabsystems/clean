// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof backend result behavior tests.

use super::*;

#[test]
fn test_proof_backend_sat() {
    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
    let x = backend.fresh_int("x");
    backend.assert_formula(&format!("(> {} 0)", x));

    match backend.check_sat().unwrap() {
        AyProofResult::Sat => {}
        other => panic!("Expected SAT, got {:?}", other),
    }
}

#[test]
fn test_proof_backend_unsat_with_proof() {
    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
    let x = backend.fresh_int("x");
    // x > 0 AND x < 0 is UNSAT
    backend.assert_formula(&format!("(> {} 0)", x));
    backend.assert_formula(&format!("(< {} 0)", x));

    match backend.check_sat().unwrap() {
        AyProofResult::Unsat {
            proof, verified, ..
        } => {
            // Proof should be present when produce_proofs is enabled
            assert!(proof.is_some(), "Expected proof to be present");
            let proof_str = proof.unwrap();
            // Alethe proofs should contain proof commands
            assert!(!proof_str.is_empty(), "Proof should not be empty");
            // Not verified since no proof profile was set
            assert!(!verified, "Expected unverified without proof profile");
        }
        other => panic!("Expected UNSAT, got {:?}", other),
    }
}

#[test]
fn test_proof_backend_mod_div_generates_proof_with_auxiliaries() {
    // Regression test for #2429: exercises the export_alethe_with_problem_scope
    // code path with a LIA mod/div problem. The new API emits declare-fun for
    // proof-internal auxiliary variables not in the problem scope. For simple
    // mod/div, ay maps auxiliaries back to (mod x 3)/(div x 3) in the proof,
    // so declare-fun may not appear. The test verifies the proof path works
    // end-to-end with the new API regardless.
    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
    let x = backend.fresh_int("x");
    // (mod x 3) is always in [0, 2], so asserting it equals 4 is UNSAT.
    backend.assert_formula(&format!("(= (mod {} 3) 4)", x));

    match backend.check_sat().unwrap() {
        AyProofResult::Unsat { proof, .. } => {
            let proof_str = proof.expect("Expected proof for mod/div UNSAT");
            assert!(
                !proof_str.is_empty(),
                "Proof should not be empty for mod/div UNSAT"
            );
            // The proof should contain Alethe step commands
            assert!(
                proof_str.contains("(step"),
                "Alethe proof should contain step commands"
            );
            // Verify proof references mod/div operations (confirms LIA path exercised)
            assert!(
                proof_str.contains("mod") || proof_str.contains("div"),
                "Proof should reference mod/div operations"
            );
            // If declare-fun preamble is present, it must precede proof steps
            if let (Some(decl_pos), Some(step_pos)) =
                (proof_str.find("declare-fun"), proof_str.find("(step"))
            {
                assert!(
                    decl_pos < step_pos,
                    "Auxiliary declarations must precede proof steps"
                );
            }
        }
        other => panic!(
            "Expected UNSAT for impossible mod constraint, got {:?}",
            other
        ),
    }
}

#[test]
fn test_proof_backend_unsat_without_proof() {
    let mut backend = AyProofBackend::new_default(AyLogic::QfLia);
    let x = backend.fresh_int("x");
    // x > 0 AND x < 0 is UNSAT
    backend.assert_formula(&format!("(> {} 0)", x));
    backend.assert_formula(&format!("(< {} 0)", x));

    match backend.check_sat().unwrap() {
        AyProofResult::Unsat {
            proof, verified, ..
        } => {
            // Proof should NOT be present when produce_proofs is disabled
            assert!(proof.is_none(), "Expected no proof when disabled");
            // Not verified since no proof was produced
            assert!(!verified, "Expected unverified without proof");
        }
        other => panic!("Expected UNSAT, got {:?}", other),
    }
}
