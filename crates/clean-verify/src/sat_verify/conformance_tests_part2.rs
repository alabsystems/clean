// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Differential conformance tests, part 2 — split from `conformance_tests.rs`
//! at a test-fn boundary (paragon files_over_1000 paydown). A `#[path]` child
//! of the parent module, so its private helpers resolve via `super::*`
//! exactly as before.

use super::*;

/// Rejects an LRAT delete step that targets a clause ID that is not active,
/// which prevents silent loss of synchronization with the clause database.
#[test]
fn test_conformance_lrat_delete_missing_clause_invalid() {
    let mut checker = LratChecker::new(1);
    checker
        .add_original(ClauseId(1), &lits(&[1]))
        .expect("original clause 1 should load");

    let error = checker
        .verify_proof(&[LratStep::Delete {
            clause_ids: vec![ClauseId(99)],
        }])
        .expect_err("deleting a missing LRAT clause should fail");
    assert_eq!(
        error,
        LratError::MissingClause(ClauseId(99)),
        "missing delete target should surface as MissingClause"
    );
}

// ---------------------------------------------------------------------------
// Valid FRAT proofs
// ---------------------------------------------------------------------------

/// Verifies a text-parsed FRAT proof for the minimal unsatisfiable formula,
/// ensuring the parser and checker agree on a finalized empty-clause proof.
#[test]
fn test_conformance_frat_simple_text_proof_valid() {
    let cnf = make_cnf(&[&[1], &[-1]]);
    let steps =
        parse_frat_text("o 1 1 0\no 2 -1 0\nl 3 0\nf 3 0\n").expect("valid FRAT text should parse");

    let result = verify_frat(&cnf, &steps).expect("simple FRAT proof should verify");
    assert!(
        result.valid,
        "simple FRAT proof should derive the empty clause"
    );
    assert!(
        result.empty_clause_finalized,
        "finalizing the empty clause should be recorded in the result"
    );
}

/// Verifies a FRAT proof that derives intermediate lemmas before the empty
/// clause, covering forward-checking RUP chains and finalization.
#[test]
fn test_conformance_frat_lemma_chain_valid() {
    let cnf = make_cnf(&[&[1, 2], &[-1], &[-2, 3], &[-3]]);
    let steps = chain_frat_steps();

    assert!(
        verify_frat_proof(&cnf, &steps),
        "FRAT lemma chain should verify as a valid refutation"
    );
}

/// Verifies that FRAT accepts proofs combining originals, deletions, a derived
/// contradiction, and finalization when the deleted clause is irrelevant.
#[test]
fn test_conformance_frat_with_delete_and_finalize_valid() {
    let cnf = make_cnf(&[&[1], &[-1], &[2]]);
    let steps = vec![
        FratStep::Original {
            id: FratClauseId(1),
            clause: vec![1],
        },
        FratStep::Original {
            id: FratClauseId(2),
            clause: vec![-1],
        },
        FratStep::Original {
            id: FratClauseId(3),
            clause: vec![2],
        },
        FratStep::Delete {
            id: FratClauseId(3),
            clause: vec![2],
        },
        FratStep::Lemma {
            id: FratClauseId(4),
            clause: Vec::new(),
        },
        FratStep::Finalize {
            id: FratClauseId(4),
        },
    ];

    assert!(
        verify_frat_proof(&cnf, &steps),
        "FRAT proof with a benign deletion should still verify"
    );
}

/// Verifies that FRAT `Add` steps can coexist with a valid refutation proof and
/// do not interfere with deriving and finalizing the empty clause.
#[test]
fn test_conformance_frat_with_add_step_valid() {
    let cnf = make_cnf(&[&[1], &[-1]]);
    let steps = vec![
        FratStep::Original {
            id: FratClauseId(1),
            clause: vec![1],
        },
        FratStep::Original {
            id: FratClauseId(2),
            clause: vec![-1],
        },
        FratStep::Add {
            id: FratClauseId(3),
            clause: vec![1, -1],
        },
        FratStep::Lemma {
            id: FratClauseId(4),
            clause: Vec::new(),
        },
        FratStep::Finalize {
            id: FratClauseId(4),
        },
    ];

    assert!(
        verify_frat_proof(&cnf, &steps),
        "FRAT add-step proof should remain valid when the empty clause is derived"
    );
}

// ---------------------------------------------------------------------------
// Invalid FRAT proofs
// ---------------------------------------------------------------------------

/// Rejects a FRAT lemma that is neither RUP nor RAT, preventing unsupported
/// contradictions from being smuggled into the active clause database.
#[test]
fn test_conformance_frat_bad_rup_invalid() {
    let cnf = make_cnf(&[&[1, 2], &[-1, 2]]);
    let steps = vec![
        FratStep::Original {
            id: FratClauseId(1),
            clause: vec![1, 2],
        },
        FratStep::Original {
            id: FratClauseId(2),
            clause: vec![-1, 2],
        },
        FratStep::Lemma {
            id: FratClauseId(3),
            clause: vec![-2],
        },
    ];

    let error = verify_frat(&cnf, &steps).expect_err("bad FRAT lemma should be rejected");
    match error {
        FratError::RupFailed { id, clause } => {
            assert_eq!(id, FratClauseId(3), "failing lemma ID should be preserved");
            assert_eq!(clause, vec![-2], "failing lemma clause should be preserved");
        }
        other => panic!("expected RupFailed, got {other:?}"),
    }
}

/// Rejects a FRAT proof as an UNSAT certificate when it never derives the empty
/// clause, even if all of its bookkeeping and original steps are well-formed.
#[test]
fn test_conformance_frat_no_empty_clause_invalid() {
    let cnf = make_cnf(&[&[1], &[-1]]);
    let steps = parse_frat_text("o 1 1 0\no 2 -1 0\n")
        .expect("FRAT text without contradiction should parse");

    let result = verify_frat(&cnf, &steps).expect("well-formed FRAT proof should still process");
    assert!(
        !result.valid,
        "FRAT proof without an empty clause must not be marked valid"
    );
    assert!(
        !result.empty_clause_finalized,
        "without an empty clause there should be nothing to finalize as a refutation"
    );
}

/// Rejects a FRAT proof that finalizes a clause ID that was never introduced,
/// since finalize must reference an active clause in the database.
#[test]
fn test_conformance_frat_missing_clause_id_invalid() {
    let cnf = make_cnf(&[&[1]]);
    let steps = vec![
        FratStep::Original {
            id: FratClauseId(1),
            clause: vec![1],
        },
        FratStep::Finalize {
            id: FratClauseId(99),
        },
    ];

    let error =
        verify_frat(&cnf, &steps).expect_err("finalizing a missing FRAT clause should be rejected");
    assert_eq!(
        error,
        FratError::MissingClauseId(FratClauseId(99)),
        "missing finalize target should surface as MissingClauseId"
    );
}

/// Rejects a FRAT proof that reuses a clause ID for a second original clause,
/// because FRAT clause identifiers must remain unique throughout the proof.
#[test]
fn test_conformance_frat_duplicate_clause_id_invalid() {
    // Both originals are in the CNF so the CNF-membership check passes and the
    // duplicate-id check is what fires (not OriginalNotInFormula).
    let cnf = make_cnf(&[&[1], &[2]]);
    let steps = vec![
        FratStep::Original {
            id: FratClauseId(1),
            clause: vec![1],
        },
        FratStep::Original {
            id: FratClauseId(1),
            clause: vec![2],
        },
    ];

    let error =
        verify_frat(&cnf, &steps).expect_err("duplicate FRAT clause IDs should be rejected");
    assert_eq!(
        error,
        FratError::DuplicateClauseId(FratClauseId(1)),
        "reusing FRAT clause ID 1 should fail deterministically"
    );
}

// ---------------------------------------------------------------------------
// Cross-format consistency
// ---------------------------------------------------------------------------

/// Checks that DRAT-to-LRAT conversion, direct LRAT verification, and FRAT
/// verification all accept the same minimal unsatisfiable formula.
#[test]
fn test_conformance_cross_format_simple_units_agree_valid() {
    let cnf = make_cnf(&[&[1], &[-1]]);
    let drat = vec![ProofStep::Add(Vec::new())];
    let lrat = vec![LratStep::Add {
        id: ClauseId(3),
        clause: Vec::new(),
        hints: vec![1, 2],
    }];
    let frat = vec![
        FratStep::Original {
            id: FratClauseId(1),
            clause: vec![1],
        },
        FratStep::Original {
            id: FratClauseId(2),
            clause: vec![-1],
        },
        FratStep::Lemma {
            id: FratClauseId(3),
            clause: Vec::new(),
        },
        FratStep::Finalize {
            id: FratClauseId(3),
        },
    ];

    assert!(
        verify_drat(&cnf, &drat),
        "DRAT path should accept the unit contradiction"
    );
    assert!(
        verify_lrat_proof(1, &[(1, &[1]), (2, &[-1])], &lrat),
        "direct LRAT path should accept the unit contradiction"
    );
    assert!(
        verify_frat_proof(&cnf, &frat),
        "FRAT path should accept the unit contradiction"
    );
}

/// Checks that all three proof formats agree on a chained propagation refutation
/// where the contradiction is reached only after multiple intermediate lemmas.
#[test]
fn test_conformance_cross_format_chain_agree_valid() {
    let cnf = make_cnf(&[&[1, 2], &[-1], &[-2, 3], &[-3]]);
    let drat = vec![
        ProofStep::Add(vec![2]),
        ProofStep::Add(vec![3]),
        ProofStep::Add(Vec::new()),
    ];

    assert!(
        verify_drat(&cnf, &drat),
        "DRAT path should accept the chain refutation"
    );
    assert!(
        verify_lrat_proof(3, &chain_originals(), &chain_lrat_steps()),
        "direct LRAT path should accept the chain refutation"
    );
    assert!(
        verify_frat_proof(&cnf, &chain_frat_steps()),
        "FRAT path should accept the chain refutation"
    );
}

/// Checks that all three proof formats agree on the `PHP(2,1)` contradiction,
/// providing a second non-trivial benchmark beyond simple unit propagation.
#[test]
fn test_conformance_cross_format_php21_agree_valid() {
    let cnf = make_cnf(&[&[1], &[2], &[-1, -2]]);
    let drat = vec![ProofStep::Add(vec![-2]), ProofStep::Add(Vec::new())];

    assert!(
        verify_drat(&cnf, &drat),
        "DRAT path should accept the PHP(2,1) refutation"
    );
    assert!(
        verify_lrat_proof(2, &php21_originals(), &php21_lrat_steps()),
        "direct LRAT path should accept the PHP(2,1) refutation"
    );
    assert!(
        verify_frat_proof(&cnf, &php21_frat_steps()),
        "FRAT path should accept the PHP(2,1) refutation"
    );
}

// ---------------------------------------------------------------------------
// Regressions
// ---------------------------------------------------------------------------

/// Regression test for #3321: an apparently well-formed proof must still be
/// rejected as a refutation if it never derives the empty clause.
#[test]
fn test_conformance_regression_3321_empty_clause_check_invalid() {
    let cnf = make_cnf(&[&[1, 2], &[-1], &[-2]]);
    let drat = vec![ProofStep::Add(vec![2])];
    let lrat = vec![LratStep::Add {
        id: ClauseId(4),
        clause: lits(&[2]),
        hints: vec![1, 2],
    }];
    let frat = vec![
        FratStep::Original {
            id: FratClauseId(1),
            clause: vec![1, 2],
        },
        FratStep::Original {
            id: FratClauseId(2),
            clause: vec![-1],
        },
        FratStep::Original {
            id: FratClauseId(3),
            clause: vec![-2],
        },
        FratStep::Lemma {
            id: FratClauseId(4),
            clause: vec![2],
        },
    ];

    let drat_error = convert_drat_to_lrat(&cnf, &drat)
        .expect_err("DRAT proof without empty clause should be rejected");
    assert_eq!(
        drat_error,
        ConvertError::NoEmptyClause,
        "DRAT conversion should fail specifically with NoEmptyClause"
    );

    let mut checker = LratChecker::new(2);
    checker
        .add_original(ClauseId(1), &lits(&[1, 2]))
        .expect("original clause 1 should load");
    checker
        .add_original(ClauseId(2), &lits(&[-1]))
        .expect("original clause 2 should load");
    checker
        .add_original(ClauseId(3), &lits(&[-2]))
        .expect("original clause 3 should load");
    let lrat_result = checker
        .verify_proof(&lrat)
        .expect("LRAT steps should still be structurally verifiable");
    assert!(
        !lrat_result.valid,
        "LRAT result should remain invalid when no empty clause is derived"
    );

    let frat_result = verify_frat(&cnf, &frat).expect("FRAT steps should process cleanly");
    assert!(
        !frat_result.valid,
        "FRAT result should remain invalid when no empty clause is derived"
    );
}

/// Regression test for #3323: a DRAT clause whose own negation is contradictory
/// must be accepted immediately instead of being rejected as non-RUP.
#[test]
fn test_conformance_regression_3323_drat_contradiction_detection_valid() {
    let cnf = make_cnf(&[&[1], &[-1]]);
    let proof = parse_drat_proof("1 -1 0\n0\n").expect("regression DRAT text should parse cleanly");

    let lrat_steps =
        convert_drat_to_lrat(&cnf, &proof).expect("trivial contradiction should convert");
    match &lrat_steps[0] {
        LratStep::Add { clause, hints, .. } => {
            assert_eq!(
                clause,
                &lits(&[1, -1]),
                "the first LRAT step should preserve the contradictory clause"
            );
            assert!(
                hints.is_empty(),
                "a self-contradictory clause should not require explicit LRAT hints"
            );
        }
        other => panic!("expected an LRAT Add step, got {other:?}"),
    }
    assert!(
        verify_drat(&cnf, &proof),
        "the converted proof should still verify end-to-end after the contradiction step"
    );
}

/// Regression test for #3324: deleting a clause that was never present must be
/// rejected instead of being silently ignored during DRAT conversion.
#[test]
fn test_conformance_regression_3324_delete_missing_clause_invalid() {
    let cnf = make_cnf(&[&[1], &[-1]]);
    let proof = vec![ProofStep::Delete(vec![7, 8]), ProofStep::Add(Vec::new())];

    let error = convert_drat_to_lrat(&cnf, &proof)
        .expect_err("phantom DRAT deletions should not be accepted");
    match error {
        ConvertError::DeletionNotFound { step, clause } => {
            assert_eq!(
                step, 0,
                "the deletion failure should be attributed to the first step"
            );
            assert_eq!(
                clause,
                vec![7, 8],
                "the missing deleted clause should be preserved for debugging"
            );
        }
        other => panic!("expected DeletionNotFound, got {other:?}"),
    }
}

/// Regression test for #3327: contradictory unit propagation must count as a
/// conflict across DRAT conversion, direct LRAT checking, and FRAT checking.
#[test]
fn test_conformance_regression_3327_contradictory_unit_propagation_valid() {
    let cnf = make_cnf(&[&[1, 2], &[-2, 3], &[1, -3], &[-1]]);
    let drat = vec![ProofStep::Add(vec![1]), ProofStep::Add(Vec::new())];
    let lrat = vec![
        LratStep::Add {
            id: ClauseId(5),
            clause: lits(&[1]),
            hints: vec![1, 2, 3],
        },
        LratStep::Add {
            id: ClauseId(6),
            clause: Vec::new(),
            hints: vec![4, 5],
        },
    ];
    let frat = vec![
        FratStep::Original {
            id: FratClauseId(1),
            clause: vec![1, 2],
        },
        FratStep::Original {
            id: FratClauseId(2),
            clause: vec![-2, 3],
        },
        FratStep::Original {
            id: FratClauseId(3),
            clause: vec![1, -3],
        },
        FratStep::Original {
            id: FratClauseId(4),
            clause: vec![-1],
        },
        FratStep::Lemma {
            id: FratClauseId(5),
            clause: vec![1],
        },
        FratStep::Lemma {
            id: FratClauseId(6),
            clause: Vec::new(),
        },
        FratStep::Finalize {
            id: FratClauseId(6),
        },
    ];

    assert!(
        verify_drat(&cnf, &drat),
        "DRAT conversion should accept a proof whose conflict arises from contradictory propagation"
    );
    assert!(
        verify_lrat_proof(
            3,
            &[(1, &[1, 2]), (2, &[-2, 3]), (3, &[1, -3]), (4, &[-1])],
            &lrat,
        ),
        "LRAT should accept the same contradictory-propagation refutation"
    );
    assert!(
        verify_frat_proof(&cnf, &frat),
        "FRAT should accept the same contradictory-propagation refutation"
    );
}
