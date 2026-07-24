// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_cnf_parse_dimacs() {
    let input = r#"
c This is a comment
p cnf 3 2
1 2 0
-1 3 0
"#;
    let formula = CnfFormula::parse_dimacs(input).unwrap();
    assert_eq!(formula.num_vars, 3);
    assert_eq!(formula.clauses.len(), 2);
    assert_eq!(formula.clauses[0], vec![1, 2]);
    assert_eq!(formula.clauses[1], vec![-1, 3]);
}

#[test]
fn test_drat_parse() {
    let input = r#"
1 -2 0
d 1 2 0
3 0
0
"#;
    let proof = DratProof::parse(input).unwrap();
    // 4 operations: Add([1,-2]), Delete([1,2]), Add([3]), Add([]) (empty clause)
    assert_eq!(proof.operations.len(), 4);

    match &proof.operations[0] {
        DratOp::Add(c) => assert_eq!(c, &vec![1, -2]),
        _ => panic!("Expected Add"),
    }

    match &proof.operations[1] {
        DratOp::Delete(c) => assert_eq!(c, &vec![1, 2]),
        _ => panic!("Expected Delete"),
    }

    match &proof.operations[2] {
        DratOp::Add(c) => assert_eq!(c, &vec![3]),
        _ => panic!("Expected Add"),
    }

    // The "0" line parses as Add of the empty clause (derivation of ⊥)
    match &proof.operations[3] {
        DratOp::Add(c) => assert!(c.is_empty(), "Empty clause should have no literals"),
        _ => panic!("Expected Add(empty clause)"),
    }
}

#[test]
fn test_lrat_parse() {
    let input = r#"
3 1 -2 0 1 2 0
4 d 1 2 0
5 0 3 0
"#;
    let proof = LratProof::parse(input).unwrap();
    assert_eq!(proof.operations.len(), 3);

    match &proof.operations[0] {
        LratOp::Add { id, clause, hints } => {
            assert_eq!(*id, 3);
            assert_eq!(clause, &vec![1, -2]);
            assert_eq!(hints, &vec![1, 2]);
        }
        _ => panic!("Expected Add"),
    }
}

#[test]
fn test_rup_simple() {
    // Formula: (x1 ∨ x2) ∧ (¬x1)
    // Adding x2 should be RUP (unit propagation: x1=false, so x2 must be true)
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, 2]);
    formula.add_clause(vec![-1]);

    let mut verifier = DratVerifier::new();
    verifier.init_formula(&formula);

    // x2 should be RUP
    assert!(verifier.is_rup(&[2]));

    // x1 should not be RUP
    assert!(!verifier.is_rup(&[1]));
}

#[test]
fn test_drat_verify_simple() {
    // Formula: (x1 ∨ x2) ∧ (¬x1) ∧ (¬x2)
    // This is UNSAT. Proof: derive x2 (RUP), then empty clause.
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, 2]);
    formula.add_clause(vec![-1]);
    formula.add_clause(vec![-2]);

    // DRAT proof: derive empty clause
    // After adding original clauses, unit prop gives conflict
    let mut proof = DratProof::new();
    proof.operations.push(DratOp::Add(vec![]));

    let verified = DratVerifier::verify(&formula, &proof)
        .expect("DRAT verifier should accept valid UNSAT proof");
    assert!(verified, "valid DRAT proof should verify as UNSAT");
}

#[test]
fn test_drat_verify_with_learned() {
    // Formula: (x1 ∨ x2) ∧ (¬x1 ∨ x3) ∧ (¬x2 ∨ ¬x3) ∧ (¬x1 ∨ ¬x2)
    // UNSAT proof requires learning clauses
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, 2]); // x1 ∨ x2
    formula.add_clause(vec![-1]); // ¬x1
    formula.add_clause(vec![-2]); // ¬x2

    let mut proof = DratProof::new();
    // Empty clause is RUP because x1=false, x2=false makes first clause false
    proof.operations.push(DratOp::Add(vec![]));

    let verified = DratVerifier::verify(&formula, &proof)
        .expect("DRAT verifier should accept learned empty-clause proof");
    assert!(verified, "learned DRAT proof should verify as UNSAT");
}

// ========================================================================
// Additional verification tests added by PROVER
// ========================================================================

#[test]
fn test_rup_chain_propagation() {
    // Formula that requires multi-step unit propagation for RUP
    // (x1 ∨ x2) ∧ (¬x1 ∨ x3) ∧ (¬x2 ∨ x4) ∧ (¬x3) ∧ (¬x4)
    // To show x1 ∨ x2 is conflicting: negate to ¬x1, ¬x2
    // From (¬x1 ∨ x3) and ¬x1: nothing new
    // From (¬x2 ∨ x4) and ¬x2: nothing new
    // But (x1 ∨ x2) conflicts with ¬x1, ¬x2
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, 2]); // x1 ∨ x2
    formula.add_clause(vec![-1, 3]); // ¬x1 ∨ x3
    formula.add_clause(vec![-2, 4]); // ¬x2 ∨ x4
    formula.add_clause(vec![-3]); // ¬x3
    formula.add_clause(vec![-4]); // ¬x4

    let mut verifier = DratVerifier::new();
    verifier.init_formula(&formula);

    // x1 should be RUP: negate to ¬x1, propagate from clauses
    // (¬x1 ∨ x3) unit clause -> x3=true
    // (¬x3) conflicts!
    assert!(verifier.is_rup(&[1]), "x1 should be RUP");

    // x2 should be RUP: negate to ¬x2
    // (¬x2 ∨ x4) -> x4=true
    // (¬x4) conflicts!
    assert!(verifier.is_rup(&[2]), "x2 should be RUP");
}

#[test]
fn test_rat_verification() {
    // Test RAT (not just RUP)
    // A clause C with pivot p is RAT if for every clause D containing ¬p,
    // the resolvent of C and D on p is RUP.
    //
    // Formula: (x1 ∨ x2) ∧ (¬x2 ∨ x3)
    // (x1) should be RAT with pivot x1 because no clause contains ¬x1
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, 2]); // x1 ∨ x2
    formula.add_clause(vec![-2, 3]); // ¬x2 ∨ x3

    let mut verifier = DratVerifier::new();
    verifier.init_formula(&formula);

    // (x1) should be RAT with pivot x1 because no clause contains ¬x1
    assert!(
        verifier.is_rat(&[1], 1),
        "(x1) should be RAT with pivot x1 (no clauses contain ¬x1)"
    );

    // (x1) is NOT RUP (no conflict when x1=false)
    assert!(
        !verifier.is_rup(&[1]),
        "(x1) should NOT be RUP on this formula"
    );

    // Now test with a clause that requires resolvent checking
    // Formula: (x1 ∨ x2) ∧ (¬x1 ∨ x2) ∧ (¬x2)
    // Adding (x1) with pivot x1:
    // - Clauses containing ¬x1: (¬x1 ∨ x2)
    // - Resolvent of (x1) and (¬x1 ∨ x2) = (x2)
    // - Is (x2) RUP? Negate to x2=false
    //   - (x1 ∨ x2) with x2=false: unit -> x1=true
    //   - (¬x1 ∨ x2) with x1=true, x2=false: both literals false -> CONFLICT!
    // So (x2) is RUP, so (x1) is RAT
    let mut formula2 = CnfFormula::new();
    formula2.add_clause(vec![1, 2]); // x1 ∨ x2
    formula2.add_clause(vec![-1, 2]); // ¬x1 ∨ x2
    formula2.add_clause(vec![-2]); // ¬x2

    let mut verifier2 = DratVerifier::new();
    verifier2.init_formula(&formula2);

    // (x1) should be RAT with pivot x1
    assert!(
        verifier2.is_rat(&[1], 1),
        "(x1) should be RAT with pivot x1 (resolvent x2 is RUP)"
    );
}

#[test]
fn test_clause_deletion() {
    // Test that clause deletion works correctly
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, 2]);
    formula.add_clause(vec![-1, 2]);
    formula.add_clause(vec![-2]);

    let mut proof = DratProof::new();
    // Delete (1 ∨ 2), then add empty clause (should still conflict)
    proof.operations.push(DratOp::Delete(vec![1, 2]));
    proof.operations.push(DratOp::Add(vec![]));

    let result = DratVerifier::verify(&formula, &proof);
    // After deletion, we have (¬x1 ∨ x2) ∧ (¬x2)
    // Negating empty clause gives no assignments
    // (¬x2) is unit -> x2=false
    // (¬x1 ∨ x2) with x2=false becomes unit (¬x1) -> x1=false
    // No conflict found (satisfiable: x1=false, x2=false)
    assert!(
        matches!(
            result,
            Err(DratError::NoEmptyClause) | Err(DratError::RupCheckFailed { .. })
        ),
        "Should fail - formula SAT after deletion: {:?}",
        result
    );
}

#[test]
fn test_drat_invalid_proof_rejected() {
    // Formula that is SATISFIABLE - should reject any UNSAT proof
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, 2]); // Satisfiable: x1=true OR x2=true

    let mut proof = DratProof::new();
    proof.operations.push(DratOp::Add(vec![])); // Try to add empty clause

    let result = DratVerifier::verify(&formula, &proof);
    assert!(
        matches!(
            result,
            Err(DratError::NoEmptyClause) | Err(DratError::RupCheckFailed { .. })
        ),
        "Should reject - formula is SAT: {:?}",
        result
    );
}

#[test]
fn test_lrat_basic_verification() {
    // LRAT proof for: (x1) ∧ (¬x1 ∨ x2) ∧ (¬x2)
    // Clause 1: x1
    // Clause 2: ¬x1 ∨ x2
    // Clause 3: ¬x2
    // Derive: x2 (from 1, 2) then empty (from x2, 3)
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]); // id=1: x1
    formula.add_clause(vec![-1, 2]); // id=2: ¬x1 ∨ x2
    formula.add_clause(vec![-2]); // id=3: ¬x2

    let mut proof = LratProof::new();
    // Add x2, using hints 1,2 (x1 and ¬x1∨x2 imply x2)
    proof.operations.push(LratOp::Add {
        id: 4,
        clause: vec![2],
        hints: vec![1, 2],
    });
    // Add empty clause, using hints 3,4 (¬x2 and x2 conflict)
    proof.operations.push(LratOp::Add {
        id: 5,
        clause: vec![],
        hints: vec![3, 4],
    });

    let result = LratVerifier::verify(&formula, &proof);
    assert!(
        result.is_ok(),
        "LRAT verification should succeed: {:?}",
        result
    );
}

#[test]
fn test_lrat_invalid_hint_rejected() {
    // LRAT with bad hint should be rejected
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]); // id=1
    formula.add_clause(vec![2]); // id=2

    let mut proof = LratProof::new();
    // Reference non-existent clause ID 99
    proof.operations.push(LratOp::Add {
        id: 3,
        clause: vec![1, 2],
        hints: vec![99],
    });

    let result = LratVerifier::verify(&formula, &proof);
    assert!(
        matches!(result, Err(DratError::InvalidHint { .. })),
        "Should reject - invalid hint ID: {:?}",
        result
    );
}

#[test]
fn test_drat_pigeon_hole_2_1() {
    // Pigeonhole principle PHP(2,1): 2 pigeons, 1 hole
    // Variables: p_i_j means pigeon i is in hole j
    // p_1_1 = 1, p_2_1 = 2
    //
    // Clauses:
    // - Each pigeon in some hole: (p_1_1), (p_2_1)
    // - At most one pigeon per hole: (¬p_1_1 ∨ ¬p_2_1)
    //
    // UNSAT: both pigeons must go to hole 1, but only one allowed
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]); // pigeon 1 in hole 1
    formula.add_clause(vec![2]); // pigeon 2 in hole 1
    formula.add_clause(vec![-1, -2]); // at most one pigeon in hole 1

    // Proof: empty clause is RUP
    // Negate empty: no assignments
    // (p_1_1) unit -> x1=true
    // (p_2_1) unit -> x2=true
    // (¬p_1_1 ∨ ¬p_2_1) with x1=true, x2=true -> conflict
    let mut proof = DratProof::new();
    proof.operations.push(DratOp::Add(vec![]));

    let result = DratVerifier::verify(&formula, &proof);
    assert!(
        result.is_ok(),
        "PHP(2,1) should be verified UNSAT: {:?}",
        result
    );
}

#[test]
fn test_large_variable_numbers() {
    // Test with large variable numbers to ensure no index issues
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1000]); // large var
    formula.add_clause(vec![-1000, 2000]);
    formula.add_clause(vec![-2000]);

    let mut proof = DratProof::new();
    proof.operations.push(DratOp::Add(vec![]));

    let result = DratVerifier::verify(&formula, &proof);
    assert!(
        result.is_ok(),
        "Large variable numbers should work: {:?}",
        result
    );
}

#[test]
fn test_empty_formula() {
    // Empty formula is trivially SAT
    let formula = CnfFormula::new();

    let mut proof = DratProof::new();
    proof.operations.push(DratOp::Add(vec![]));

    let result = DratVerifier::verify(&formula, &proof);
    assert!(
        matches!(
            result,
            Err(DratError::NoEmptyClause) | Err(DratError::RupCheckFailed { .. })
        ),
        "Empty formula is SAT, can't derive empty clause: {:?}",
        result
    );
}

#[test]
fn test_single_empty_clause_formula() {
    // Formula with empty clause is trivially UNSAT
    let mut formula = CnfFormula::new();
    formula.clauses.push(vec![]); // empty clause

    let mut proof = DratProof::new();
    proof.operations.push(DratOp::Add(vec![]));

    let result = DratVerifier::verify(&formula, &proof);
    assert!(result.is_ok(), "Formula with empty clause is UNSAT");
}

#[test]
fn test_proof_without_empty_clause() {
    // Proof that doesn't derive empty clause should be rejected
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]);
    formula.add_clause(vec![-1]);

    let mut proof = DratProof::new();
    // Only adds clauses but never empty clause
    proof.operations.push(DratOp::Add(vec![2]));

    let result = DratVerifier::verify(&formula, &proof);
    assert!(
        matches!(result, Err(DratError::NoEmptyClause)),
        "Should require empty clause: {:?}",
        result
    );
}

// ========================================================================
// Streaming/Incremental API Tests
// Per Ay Integration: designs/2026-01-28-incremental-certificate-verification.md
// ========================================================================

#[test]
fn test_streaming_lrat_basic() {
    // Same test as test_lrat_basic_verification but using streaming API
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]); // id=1: x1
    formula.add_clause(vec![-1, 2]); // id=2: ¬x1 ∨ x2
    formula.add_clause(vec![-2]); // id=3: ¬x2

    let mut verifier = StreamingLratVerifier::new();
    verifier.init_formula(&formula);

    // Step 1: Add x2
    let result = verifier.process_step(&LratOp::Add {
        id: 4,
        clause: vec![2],
        hints: vec![1, 2],
    });
    assert_eq!(result.unwrap(), StepResult::Continue);
    assert_eq!(verifier.steps_processed(), 1);
    assert!(!verifier.is_complete());

    // Step 2: Add empty clause
    let result = verifier.process_step(&LratOp::Add {
        id: 5,
        clause: vec![],
        hints: vec![3, 4],
    });
    assert_eq!(result.unwrap(), StepResult::Complete);
    assert_eq!(verifier.steps_processed(), 2);
    assert!(verifier.is_complete());
}

#[test]
fn test_streaming_checkpoint_resume() {
    // Test checkpoint/resume functionality
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]); // id=1: x1
    formula.add_clause(vec![-1, 2]); // id=2: ¬x1 ∨ x2
    formula.add_clause(vec![-2]); // id=3: ¬x2

    // Process first step
    let mut verifier = StreamingLratVerifier::new();
    verifier.init_formula(&formula);
    verifier
        .process_step(&LratOp::Add {
            id: 4,
            clause: vec![2],
            hints: vec![1, 2],
        })
        .unwrap();

    // Checkpoint
    let checkpoint = verifier.checkpoint();
    assert_eq!(checkpoint.steps_processed, 1);
    assert!(!checkpoint.derived_empty);

    // Simulate serialization round-trip
    let bytes = checkpoint.to_bytes();
    let restored = LratCheckpoint::from_bytes(&bytes).unwrap();
    assert_eq!(restored.steps_processed, 1);

    // Resume from checkpoint
    let mut resumed = StreamingLratVerifier::resume(restored);
    assert_eq!(resumed.steps_processed(), 1);
    assert!(!resumed.is_complete());

    // Continue with final step
    let result = resumed.process_step(&LratOp::Add {
        id: 5,
        clause: vec![],
        hints: vec![3, 4],
    });
    assert_eq!(result.unwrap(), StepResult::Complete);
    assert!(resumed.is_complete());
}

#[test]
fn test_streaming_progress_callback() {
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]);
    formula.add_clause(vec![-1, 2]);
    formula.add_clause(vec![-2]);

    let mut proof = LratProof::new();
    proof.operations.push(LratOp::Add {
        id: 4,
        clause: vec![2],
        hints: vec![1, 2],
    });
    proof.operations.push(LratOp::Add {
        id: 5,
        clause: vec![],
        hints: vec![3, 4],
    });

    let mut progress_calls = Vec::new();
    let result = verify_lrat_streaming(&formula, &proof, |done, total| {
        progress_calls.push((done, total));
    });

    result.expect("streaming LRAT verification should succeed");
    assert_eq!(progress_calls.len(), 2);
    assert_eq!(progress_calls[0], (1, 2)); // 1/2 done
    assert_eq!(progress_calls[1], (2, 2)); // 2/2 done (complete)
}

#[test]
fn test_streaming_early_error() {
    // Test that streaming API reports errors at the right step
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, 2]); // SAT formula

    let mut verifier = StreamingLratVerifier::new();
    verifier.init_formula(&formula);

    // Try to add invalid clause (no RUP proof)
    let result = verifier.process_step(&LratOp::Add {
        id: 2,
        clause: vec![3], // Can't derive x3 from just (x1 ∨ x2)
        hints: vec![1],
    });

    let err = result.expect_err("expected invalid clause to fail RUP check");
    if let DratError::RupCheckFailed { step, .. } = err {
        assert_eq!(step, 0); // Error at step 0
    } else {
        panic!("Expected RupCheckFailed error, got {err:?}");
    }
}

#[test]
fn test_streaming_clause_deletion() {
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]); // id=1
    formula.add_clause(vec![-1]); // id=2

    let mut verifier = StreamingLratVerifier::new();
    verifier.init_formula(&formula);
    assert_eq!(verifier.clause_count(), 2);

    // Delete clause 1
    verifier
        .process_step(&LratOp::Delete {
            id: 3,
            clause_ids: vec![1],
        })
        .unwrap();
    assert_eq!(verifier.clause_count(), 1);
    assert_eq!(verifier.steps_processed(), 1);
}

#[test]
fn test_checkpoint_serialization_roundtrip() {
    // Comprehensive checkpoint serialization test
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, -2, 3]);
    formula.add_clause(vec![-1, 2]);
    formula.add_clause(vec![-3, 4, -5]);

    let mut verifier = StreamingLratVerifier::new();
    verifier.init_formula(&formula);

    let checkpoint = verifier.checkpoint();
    let bytes = checkpoint.to_bytes();
    let restored = LratCheckpoint::from_bytes(&bytes).unwrap();

    assert_eq!(restored.num_vars, checkpoint.num_vars);
    assert_eq!(restored.next_id, checkpoint.next_id);
    assert_eq!(restored.steps_processed, checkpoint.steps_processed);
    assert_eq!(restored.derived_empty, checkpoint.derived_empty);
    assert_eq!(restored.clauses.len(), checkpoint.clauses.len());

    // Verify clause contents match
    for (id, clause) in &checkpoint.clauses {
        assert_eq!(restored.clauses.get(id), Some(clause));
    }
}

#[test]
fn test_checkpoint_from_bytes_error_handling() {
    // Too short - less than minimum header (33 bytes)
    let result = LratCheckpoint::from_bytes(&[0u8; 10]);
    assert!(
        matches!(result, Err(DratError::ParseError(_))),
        "Expected ParseError for short input, got {:?}",
        result
    );

    // Build truncated checkpoint: header says 1 clause but no clause data follows
    let mut bytes = Vec::new();
    // num_vars (8 bytes)
    bytes.extend_from_slice(&5u64.to_le_bytes());
    // next_id (8 bytes)
    bytes.extend_from_slice(&3u64.to_le_bytes());
    // steps_processed (8 bytes)
    bytes.extend_from_slice(&1u64.to_le_bytes());
    // derived_empty (1 byte)
    bytes.push(0);
    // clause_count (8 bytes) - claim 1 clause
    bytes.extend_from_slice(&1u64.to_le_bytes());
    // No clause data follows - should fail

    let result = LratCheckpoint::from_bytes(&bytes);
    assert!(
        matches!(result, Err(DratError::ParseError(_))),
        "Expected ParseError for truncated checkpoint, got {:?}",
        result
    );
}

/// Verify streaming API with a larger proof (PHP(3,2) - 3 pigeons, 2 holes)
///
/// Pigeonhole principle: 3 pigeons cannot fit into 2 holes.
/// Variables: p_i_j means pigeon i is in hole j
/// - p_1_1=1, p_1_2=2 (pigeon 1 in hole 1 or 2)
/// - p_2_1=3, p_2_2=4 (pigeon 2)
/// - p_3_1=5, p_3_2=6 (pigeon 3)
#[test]
fn test_streaming_larger_proof_php32() {
    let mut formula = CnfFormula::new();

    // Each pigeon must be in some hole
    formula.add_clause(vec![1, 2]); // id=1: p_1_1 ∨ p_1_2
    formula.add_clause(vec![3, 4]); // id=2: p_2_1 ∨ p_2_2
    formula.add_clause(vec![5, 6]); // id=3: p_3_1 ∨ p_3_2

    // At most one pigeon per hole (hole 1)
    formula.add_clause(vec![-1, -3]); // id=4: ¬p_1_1 ∨ ¬p_2_1
    formula.add_clause(vec![-1, -5]); // id=5: ¬p_1_1 ∨ ¬p_3_1
    formula.add_clause(vec![-3, -5]); // id=6: ¬p_2_1 ∨ ¬p_3_1

    // At most one pigeon per hole (hole 2)
    formula.add_clause(vec![-2, -4]); // id=7: ¬p_1_2 ∨ ¬p_2_2
    formula.add_clause(vec![-2, -6]); // id=8: ¬p_1_2 ∨ ¬p_3_2
    formula.add_clause(vec![-4, -6]); // id=9: ¬p_2_2 ∨ ¬p_3_2

    // LRAT proof for PHP(3,2) UNSAT
    // Derived clauses with hints for RUP checking
    let proof_ops = [
        // Derive (¬p_1_1 ∨ p_3_2): if p_1_1 and ¬p_3_2 both true, conflict
        // Negate to p_1_1 ∧ ¬p_3_2
        // From clause 3 (p_3_1 ∨ p_3_2) with ¬p_3_2: p_3_1 unit
        // From clause 5 (¬p_1_1 ∨ ¬p_3_1) with p_1_1, p_3_1: conflict!
        LratOp::Add {
            id: 10,
            clause: vec![-1, 6], // ¬p_1_1 ∨ p_3_2
            hints: vec![3, 5],
        },
        // Similarly: (¬p_2_1 ∨ p_3_2)
        LratOp::Add {
            id: 11,
            clause: vec![-3, 6], // ¬p_2_1 ∨ p_3_2
            hints: vec![3, 6],
        },
        // Derive p_3_2: negate to ¬p_3_2
        // From 10 (¬1 ∨ 6) with ¬6: ¬1 unit
        // From 11 (¬3 ∨ 6) with ¬6: ¬3 unit
        // From clause 1 (1 ∨ 2) with ¬1: 2 unit
        // From clause 2 (3 ∨ 4) with ¬3: 4 unit
        // From clause 7 (¬2 ∨ ¬4) with 2, 4: conflict!
        LratOp::Add {
            id: 12,
            clause: vec![6], // p_3_2
            hints: vec![10, 11, 1, 2, 7],
        },
        // Derive ¬p_1_2 from p_3_2 and clause 8
        LratOp::Add {
            id: 13,
            clause: vec![-2], // ¬p_1_2
            hints: vec![12, 8],
        },
        // Derive ¬p_2_2 from p_3_2 and clause 9
        LratOp::Add {
            id: 14,
            clause: vec![-4], // ¬p_2_2
            hints: vec![12, 9],
        },
        // Derive p_1_1 from ¬p_1_2 and clause 1
        LratOp::Add {
            id: 15,
            clause: vec![1], // p_1_1
            hints: vec![13, 1],
        },
        // Derive p_2_1 from ¬p_2_2 and clause 2
        LratOp::Add {
            id: 16,
            clause: vec![3], // p_2_1
            hints: vec![14, 2],
        },
        // Now p_1_1=true, p_2_1=true conflicts with clause 4
        LratOp::Add {
            id: 17,
            clause: vec![], // empty clause
            hints: vec![15, 16, 4],
        },
    ];

    let mut verifier = StreamingLratVerifier::new();
    verifier.init_formula(&formula);

    // Process all steps incrementally
    for (i, op) in proof_ops.iter().enumerate() {
        let result = verifier.process_step(op);
        match result {
            Ok(StepResult::Complete) => {
                assert!(
                    i == proof_ops.len() - 1,
                    "Should complete only on last step"
                );
                break;
            }
            Ok(StepResult::Continue) => continue,
            Err(e) => panic!("Step {} failed: {}", i, e),
        }
    }

    assert!(verifier.is_complete(), "Should derive empty clause");
    assert_eq!(verifier.steps_processed(), proof_ops.len());
}

#[test]
fn test_drat_reconstruct_returns_none_not_ill_typed() {
    // Regression test for #2461 F1: reconstruct_unsat_proof must return None
    // (graceful recovery through bridge/superposition, now fail-closed if that
    // lane also misses) rather than a bare False.elim constant without
    // arguments, which is ill-typed and causes close_goal to reject.
    let env = clean_kernel::Environment::new();
    let goal =
        clean_kernel::Expr::const_(clean_kernel::name::Name::from_string("SomeGoal"), vec![]);

    // Build a valid DRAT proof for a simple UNSAT formula
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, 2]);
    formula.add_clause(vec![-1]);
    formula.add_clause(vec![-2]);

    let mut proof = DratProof::new();
    proof.operations.push(DratOp::Add(vec![]));

    let result = verify_and_reconstruct_drat(&env, &formula, &proof, &goal);
    assert!(result.verified, "DRAT proof should verify as UNSAT");
    assert!(
        result.proof_term.is_none(),
        "reconstruct_unsat_proof should return None (not an ill-typed bare False.elim). \
         Callers recover through the checked bridge/superposition lane and \
         fail closed if it cannot produce a proof. Regression: #2461 F1."
    );
}

// ========================================================================
// Memory safety regression tests — Prover memory_verification phase
// ========================================================================

/// Characterize DratVerifier unbounded clause growth through the public API.
/// The DRAT proof format allows unlimited clause additions.  This test adds
/// many RUP-valid clauses to show the verifier accumulates them all without
/// any capacity enforcement.
///
/// Contrast with LRAT, which includes Delete operations to keep the active
/// clause set bounded (see test_streaming_lrat_deletion_bounds_clause_count).
///
/// Tracked by: #2041 (O(n^2) remove), unbounded growth is a related gap.
#[test]
fn test_drat_verifier_unbounded_clause_growth() {
    // Formula: (x1) ∧ (¬x1) — trivially UNSAT.
    // Any clause is RUP because unit propagation derives conflict immediately.
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]);
    formula.add_clause(vec![-1]);

    // Build a DRAT proof that adds 200 clauses before deriving empty.
    // Each addition is RUP-valid because the formula is already UNSAT.
    let mut proof = DratProof::new();
    for i in 2..202 {
        proof.operations.push(DratOp::Add(vec![i]));
    }
    proof.operations.push(DratOp::Add(vec![])); // derive empty

    // Verifier must accept all 201 operations (200 adds + empty clause).
    // This demonstrates that there is no capacity bound on clause additions.
    let result = DratVerifier::verify(&formula, &proof);
    assert!(
        result.is_ok(),
        "DRAT verifier should accept 200 added clauses on UNSAT formula: {:?}",
        result
    );
}

/// Verify RUP checking on a non-trivial formula where unit propagation
/// requires multi-step reasoning to derive contradiction.
///
/// The trivially-UNSAT formula test above (x1 ∧ ¬x1) exercises no real
/// RUP logic since every clause is vacuously RUP. This test uses a formula
/// where the added clauses require genuine multi-clause propagation to
/// confirm RUP validity.
///
/// Formula: (x1 ∨ x2) ∧ (¬x1 ∨ x3) ∧ (¬x2 ∨ x3) ∧ (¬x3)
/// This is UNSAT: x3 must be false (clause 4), so x1 must be false (clause 2
/// contrapositive) and x2 must be false (clause 3 contrapositive), but then
/// clause 1 (x1 ∨ x2) is violated.
///
/// Re: #2461, Re: #302
#[test]
fn test_drat_rup_nontrivial_propagation_chain() {
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, 2]); // C0: x1 ∨ x2
    formula.add_clause(vec![-1, 3]); // C1: ¬x1 ∨ x3
    formula.add_clause(vec![-2, 3]); // C2: ¬x2 ∨ x3
    formula.add_clause(vec![-3]); // C3: ¬x3

    // Learned clause (¬x1): negate to get x1=true.
    // Propagation: x1=true → C1 forces x3=true → C3 conflict. RUP valid.
    let mut proof = DratProof::new();
    proof.operations.push(DratOp::Add(vec![-1]));

    // Learned clause (¬x2): negate to get x2=true.
    // Propagation: x2=true → C2 forces x3=true → C3 conflict. RUP valid.
    proof.operations.push(DratOp::Add(vec![-2]));

    // Empty clause: negate = empty assignment.
    // Propagation: C3 forces x3=false → C1+C0 force x1=true or x2=true
    // but (¬x1) and (¬x2) are now active → conflict. RUP valid.
    proof.operations.push(DratOp::Add(vec![]));

    let result = DratVerifier::verify(&formula, &proof);
    assert!(
        matches!(result, Ok(true)),
        "DRAT proof with multi-step RUP propagation should verify as Ok(true): {:?}",
        result
    );

    // Negative test: on a SATISFIABLE formula, the empty clause is NOT RUP.
    // Formula: (x1 ∨ x2) — satisfiable, so adding [] must fail.
    let mut sat_formula = CnfFormula::new();
    sat_formula.add_clause(vec![1, 2]);

    let mut bad_proof = DratProof::new();
    bad_proof.operations.push(DratOp::Add(vec![])); // empty clause is not RUP on SAT formula

    let bad_result = DratVerifier::verify(&sat_formula, &bad_proof);
    assert!(
        bad_result.is_err() || matches!(bad_result, Ok(false)),
        "Empty clause should not be RUP on a satisfiable formula: {:?}",
        bad_result
    );
}

/// Verify that remove_clause via DRAT Delete operations maintains correctness
/// across multiple deletions (index-shift regression).
///
/// The test builds a formula, adds and deletes clauses via DRAT operations,
/// then checks the proof still verifies correctly.
///
/// Tracked by: #2041
#[test]
fn test_drat_remove_clause_correctness_via_delete_ops() {
    // Formula: (x1 ∨ x2) ∧ (¬x1) ∧ (¬x2) — UNSAT
    // The original clauses are never deleted, keeping the formula UNSAT
    // throughout. We add and delete auxiliary learned clauses to exercise
    // the index-shift logic in remove_clause.
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, 2]); // clause A
    formula.add_clause(vec![-1]); // clause B
    formula.add_clause(vec![-2]); // clause C

    let mut proof = DratProof::new();
    // Add (x3) — RUP because formula is already UNSAT
    proof.operations.push(DratOp::Add(vec![3]));
    // Add (x4) — also RUP
    proof.operations.push(DratOp::Add(vec![4]));
    // Add (x5 ∨ x6) — also RUP
    proof.operations.push(DratOp::Add(vec![5, 6]));
    // Delete (x3) — exercises remove_clause + watch index shift
    proof.operations.push(DratOp::Delete(vec![3]));
    // Delete (x5 ∨ x6) — exercises remove on multi-literal clause
    proof.operations.push(DratOp::Delete(vec![5, 6]));
    // Delete (x4) — exercises remove after two prior deletions
    proof.operations.push(DratOp::Delete(vec![4]));
    // Original UNSAT clauses remain — derive empty clause
    proof.operations.push(DratOp::Add(vec![]));

    let result = DratVerifier::verify(&formula, &proof);
    assert!(
        result.is_ok(),
        "DRAT proof with multiple add/delete cycles should verify: {:?}",
        result
    );
}

/// Performance test: deletion-heavy DRAT proof with many add/delete cycles.
///
/// Exercises the content_index reverse map to verify O(clause_len) amortized
/// removal scales correctly. With the old linear-scan remove_clause, this
/// would be O(N^2) over N add/delete cycles. With the reverse index, each
/// removal is O(clause_len) amortized.
///
/// Tracked by: #2041
#[test]
fn test_drat_deletion_heavy_proof() {
    // Formula: (x1) ∧ (¬x1) — trivially UNSAT
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]);
    formula.add_clause(vec![-1]);

    let mut proof = DratProof::new();
    let n: i32 = 500;

    // Add N clauses, each RUP-valid on the UNSAT formula
    for i in 2..(n + 2) {
        proof.operations.push(DratOp::Add(vec![i]));
    }

    // Delete all N clauses (reverse order to exercise different index patterns)
    for i in (2..(n + 2)).rev() {
        proof.operations.push(DratOp::Delete(vec![i]));
    }

    // Add and delete duplicate clauses (same content added multiple times)
    for _ in 0..50 {
        proof.operations.push(DratOp::Add(vec![999, -999]));
    }
    for _ in 0..50 {
        proof.operations.push(DratOp::Delete(vec![999, -999]));
    }

    // Derive empty clause — original UNSAT clauses still present
    proof.operations.push(DratOp::Add(vec![]));

    let result = DratVerifier::verify(&formula, &proof);
    assert!(
        result.is_ok(),
        "Deletion-heavy DRAT proof ({} add/delete cycles) should verify: {:?}",
        n + 50,
        result
    );
}

/// Verify that streaming LRAT verifier properly bounds clause count through
/// delete operations — contrast with DratVerifier's unbounded growth.
#[test]
fn test_streaming_lrat_deletion_bounds_clause_count() {
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]); // id=1
    formula.add_clause(vec![-1, 2]); // id=2
    formula.add_clause(vec![-2]); // id=3

    let mut verifier = StreamingLratVerifier::new();
    verifier.init_formula(&formula);
    assert_eq!(verifier.clause_count(), 3);

    // Add a derived clause
    verifier
        .process_step(&LratOp::Add {
            id: 4,
            clause: vec![2],
            hints: vec![1, 2],
        })
        .unwrap();
    assert_eq!(verifier.clause_count(), 4);

    // Delete the two clauses that are no longer needed
    verifier
        .process_step(&LratOp::Delete {
            id: 5,
            clause_ids: vec![1, 2],
        })
        .unwrap();
    assert_eq!(
        verifier.clause_count(),
        2,
        "LRAT deletion should reduce active clause count — \
         this bounds memory unlike DratVerifier"
    );

    // Complete the proof
    verifier
        .process_step(&LratOp::Add {
            id: 6,
            clause: vec![],
            hints: vec![3, 4],
        })
        .unwrap();
    assert!(verifier.is_complete());
}
