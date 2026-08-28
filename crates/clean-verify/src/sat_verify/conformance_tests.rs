// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Differential conformance test infrastructure for SAT proof checkers.

use crate::sat_verify::cdcl::proof_logging::{parse_drat_proof, ProofStep};
use crate::sat_verify::drat_to_lrat::{convert_drat_to_lrat, ConvertError};
use crate::sat_verify::frat::{parse_frat_text, verify_frat, FratClauseId, FratError, FratStep};
use crate::sat_verify::lrat::{
    parse_text_lrat, CheckableLratProof, ClauseId, LratChecker, LratError, LratProof, LratStep,
};
use crate::sat_verify::proof_checker::ProofChecker;
use crate::sat_verify::types::Lit;

fn make_cnf(clauses: &[&[i32]]) -> Vec<Vec<i32>> {
    clauses.iter().map(|clause| clause.to_vec()).collect()
}

fn lits(clause: &[i32]) -> Vec<Lit> {
    clause.iter().copied().map(Lit).collect()
}

fn max_var_in_cnf(cnf: &[Vec<i32>]) -> u32 {
    cnf.iter()
        .flat_map(|clause| clause.iter())
        .map(|lit| lit.unsigned_abs())
        .max()
        .unwrap_or(0)
}

fn verify_drat(cnf: &[Vec<i32>], drat: &[ProofStep]) -> bool {
    let lrat_steps = match convert_drat_to_lrat(cnf, drat) {
        Ok(steps) => steps,
        Err(_) => return false,
    };

    let mut checker = LratChecker::new(max_var_in_cnf(cnf));
    for (index, clause) in cnf.iter().enumerate() {
        let id = ClauseId(u64::try_from(index + 1).expect("clause index should fit in u64"));
        if checker.add_original(id, &lits(clause)).is_err() {
            return false;
        }
    }

    match checker.verify_proof(&lrat_steps) {
        Ok(result) => result.valid && result.refuted,
        Err(_) => false,
    }
}

fn verify_lrat_proof(num_vars: u32, originals: &[(u64, &[i32])], steps: &[LratStep]) -> bool {
    let mut checker = LratChecker::new(num_vars);
    for (id, clause) in originals {
        if checker.add_original(ClauseId(*id), &lits(clause)).is_err() {
            return false;
        }
    }

    match checker.verify_proof(steps) {
        Ok(result) => result.valid && result.refuted,
        Err(_) => false,
    }
}

fn verify_frat_proof(cnf: &[Vec<i32>], steps: &[FratStep]) -> bool {
    match verify_frat(cnf, steps) {
        Ok(result) => result.valid,
        Err(_) => false,
    }
}

fn chain_originals() -> Vec<(u64, &'static [i32])> {
    vec![(1, &[1, 2]), (2, &[-1]), (3, &[-2, 3]), (4, &[-3])]
}

fn chain_lrat_steps() -> Vec<LratStep> {
    vec![
        LratStep::Add {
            id: ClauseId(5),
            clause: lits(&[2]),
            hints: vec![1, 2],
        },
        LratStep::Add {
            id: ClauseId(6),
            clause: lits(&[3]),
            hints: vec![3, 5],
        },
        LratStep::Add {
            id: ClauseId(7),
            clause: Vec::new(),
            hints: vec![6, 4],
        },
    ]
}

fn chain_frat_steps() -> Vec<FratStep> {
    vec![
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
            clause: vec![-2, 3],
        },
        FratStep::Original {
            id: FratClauseId(4),
            clause: vec![-3],
        },
        FratStep::Lemma {
            id: FratClauseId(5),
            clause: vec![2],
        },
        FratStep::Lemma {
            id: FratClauseId(6),
            clause: vec![3],
        },
        FratStep::Lemma {
            id: FratClauseId(7),
            clause: Vec::new(),
        },
        FratStep::Finalize {
            id: FratClauseId(7),
        },
    ]
}

fn php21_originals() -> Vec<(u64, &'static [i32])> {
    vec![(1, &[1]), (2, &[2]), (3, &[-1, -2])]
}

fn php21_lrat_steps() -> Vec<LratStep> {
    vec![
        LratStep::Add {
            id: ClauseId(4),
            clause: lits(&[-2]),
            hints: vec![3, 1],
        },
        LratStep::Add {
            id: ClauseId(5),
            clause: Vec::new(),
            hints: vec![2, 4],
        },
    ]
}

fn php21_frat_steps() -> Vec<FratStep> {
    vec![
        FratStep::Original {
            id: FratClauseId(1),
            clause: vec![1],
        },
        FratStep::Original {
            id: FratClauseId(2),
            clause: vec![2],
        },
        FratStep::Original {
            id: FratClauseId(3),
            clause: vec![-1, -2],
        },
        FratStep::Lemma {
            id: FratClauseId(4),
            clause: vec![-2],
        },
        FratStep::Lemma {
            id: FratClauseId(5),
            clause: Vec::new(),
        },
        FratStep::Finalize {
            id: FratClauseId(5),
        },
    ]
}

// ---------------------------------------------------------------------------
// Valid DRAT proofs
// ---------------------------------------------------------------------------

/// Verifies the minimal DRAT refutation for `[x1]` and `[~x1]` by parsing text,
/// converting it to LRAT, and checking that the empty clause is accepted.
#[test]
fn test_conformance_drat_simple_empty_clause_valid() {
    let cnf = make_cnf(&[&[1], &[-1]]);
    let proof = parse_drat_proof("0\n").expect("simple DRAT text should parse");

    assert!(
        verify_drat(&cnf, &proof),
        "simple DRAT refutation should convert and verify successfully"
    );
}

/// Verifies a DRAT proof that derives a unit clause and then the contradiction,
/// exercising a non-trivial RUP chain before the empty clause.
#[test]
fn test_conformance_drat_rup_chain_valid() {
    let cnf = make_cnf(&[&[1, 2], &[-1, 2], &[-2]]);
    let proof = vec![ProofStep::Add(vec![2]), ProofStep::Add(Vec::new())];

    assert!(
        verify_drat(&cnf, &proof),
        "RUP-chain DRAT proof should verify after DRAT-to-LRAT conversion"
    );
}

/// Verifies that DRAT deletion steps do not invalidate a correct refutation when
/// the deleted clause is irrelevant to deriving the empty clause.
#[test]
fn test_conformance_drat_with_deletion_valid() {
    let cnf = make_cnf(&[&[1], &[-1], &[1, 2]]);
    let proof = vec![ProofStep::Delete(vec![1, 2]), ProofStep::Add(Vec::new())];

    assert!(
        verify_drat(&cnf, &proof),
        "DRAT proof with a benign deletion should still verify"
    );
}

/// Verifies that a clause whose negation is immediately contradictory is treated
/// as a valid DRAT step before the final empty clause is derived.
#[test]
fn test_conformance_drat_self_contradictory_clause_valid() {
    let cnf = make_cnf(&[&[1], &[-1]]);
    let proof = parse_drat_proof("1 -1 0\n0\n").expect("self-contradictory DRAT text should parse");

    assert!(
        verify_drat(&cnf, &proof),
        "self-contradictory DRAT addition should be accepted as trivial RUP"
    );
}

// ---------------------------------------------------------------------------
// Invalid DRAT proofs
// ---------------------------------------------------------------------------

/// Rejects a DRAT proof that tries to derive the empty clause from a satisfiable
/// one-clause CNF, which cannot possibly justify the contradiction by RUP.
#[test]
fn test_conformance_drat_bad_rup_invalid() {
    let cnf = make_cnf(&[&[1, 2]]);
    let proof = parse_drat_proof("0\n").expect("invalid DRAT text should still parse");

    let error =
        convert_drat_to_lrat(&cnf, &proof).expect_err("bad DRAT RUP step should be rejected");
    match error {
        ConvertError::RupFailed { step, clause } => {
            assert_eq!(step, 0, "the first DRAT step should be reported as failing");
            assert_eq!(
                clause,
                Vec::<i32>::new(),
                "the rejected clause should be the attempted empty clause"
            );
        }
        other => panic!("expected RupFailed for bad DRAT proof, got {other:?}"),
    }
}

/// Rejects a DRAT proof that derives a useful intermediate lemma but never
/// reaches the empty clause, because it is not a complete UNSAT refutation.
#[test]
fn test_conformance_drat_missing_empty_clause_invalid() {
    let cnf = make_cnf(&[&[1, 2], &[-1], &[-2]]);
    let proof = vec![ProofStep::Add(vec![2])];

    let error = convert_drat_to_lrat(&cnf, &proof)
        .expect_err("DRAT proof without an empty clause should be rejected");
    assert_eq!(
        error,
        ConvertError::NoEmptyClause,
        "missing empty clause should surface as NoEmptyClause"
    );
}

/// Rejects a DRAT proof whose deletion step references a clause that never
/// existed, since the converter treats phantom deletions as malformed input.
#[test]
fn test_conformance_drat_delete_missing_clause_invalid() {
    let cnf = make_cnf(&[&[1], &[-1]]);
    let proof = vec![ProofStep::Delete(vec![99, 100]), ProofStep::Add(Vec::new())];

    let error = convert_drat_to_lrat(&cnf, &proof)
        .expect_err("deleting a missing DRAT clause should fail conversion");
    match error {
        ConvertError::DeletionNotFound { step, clause } => {
            assert_eq!(step, 0, "the deletion failure should be reported on step 0");
            assert_eq!(
                clause,
                vec![99, 100],
                "the missing deleted clause should be preserved in the error"
            );
        }
        other => panic!("expected DeletionNotFound, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Valid LRAT proofs
// ---------------------------------------------------------------------------

/// Verifies the canonical LRAT refutation for `[x1]` and `[~x1]` using explicit
/// hints, confirming the checker accepts the simplest valid empty-clause proof.
#[test]
fn test_conformance_lrat_simple_empty_clause_valid() {
    let originals = vec![(1_u64, &[1][..]), (2_u64, &[-1][..])];
    let steps = vec![LratStep::Add {
        id: ClauseId(3),
        clause: Vec::new(),
        hints: vec![1, 2],
    }];

    assert!(
        verify_lrat_proof(1, &originals, &steps),
        "minimal LRAT proof should verify as a refutation"
    );
}

/// Verifies a multi-step LRAT proof that derives two unit lemmas and then the
/// empty clause, covering chained hint-guided propagation.
#[test]
fn test_conformance_lrat_rup_chain_valid() {
    let originals = chain_originals();
    let steps = chain_lrat_steps();

    assert!(
        verify_lrat_proof(3, &originals, &steps),
        "chained LRAT proof should verify and refute the formula"
    );
}

/// Verifies that LRAT deletion steps interleaved with valid additions preserve
/// correctness when later hints only reference clauses that remain active.
#[test]
fn test_conformance_lrat_interleaved_delete_valid() {
    let originals = chain_originals();
    let steps = vec![
        LratStep::Add {
            id: ClauseId(5),
            clause: lits(&[2]),
            hints: vec![1, 2],
        },
        LratStep::Delete {
            clause_ids: vec![ClauseId(1)],
        },
        LratStep::Add {
            id: ClauseId(6),
            clause: lits(&[3]),
            hints: vec![3, 5],
        },
        LratStep::Add {
            id: ClauseId(7),
            clause: Vec::new(),
            hints: vec![6, 4],
        },
    ];

    assert!(
        verify_lrat_proof(3, &originals, &steps),
        "LRAT proof with safe interleaved deletion should still verify"
    );
}

/// Verifies a text-parsed LRAT proof and cross-checks it through the generic
/// `ProofChecker` wrapper so both LRAT entry points agree on validity.
#[test]
fn test_conformance_lrat_text_parsed_valid() {
    let steps = parse_text_lrat("4 -2 0 3 1 0\n5 0 2 4 0\n").expect("valid LRAT text should parse");
    let proof = CheckableLratProof {
        proof: LratProof {
            num_vars: 2,
            original_clauses: php21_originals()
                .iter()
                .map(|(id, clause)| (ClauseId(*id), lits(clause)))
                .collect(),
            steps: steps.clone(),
        },
    };

    assert!(
        verify_lrat_proof(2, &php21_originals(), &steps),
        "parsed LRAT proof should verify through LratChecker"
    );
    assert_eq!(
        proof.proof_size(),
        steps.len(),
        "proof_size should report the number of LRAT steps"
    );
    assert!(
        proof.check().is_ok(),
        "the generic ProofChecker wrapper should also accept the same LRAT proof"
    );
}

// ---------------------------------------------------------------------------
// Invalid LRAT proofs
// ---------------------------------------------------------------------------

/// Rejects an LRAT proof whose hint sequence stops after a unit propagation
/// without ever reaching a conflict, so the derived clause is not justified.
#[test]
fn test_conformance_lrat_wrong_hint_sequence_invalid() {
    let mut checker = LratChecker::new(2);
    checker
        .add_original(ClauseId(1), &lits(&[1, 2]))
        .expect("original clause 1 should load");
    checker
        .add_original(ClauseId(2), &lits(&[-1]))
        .expect("original clause 2 should load");

    let error = checker
        .verify_proof(&[LratStep::Add {
            id: ClauseId(3),
            clause: lits(&[2]),
            hints: vec![1],
        }])
        .expect_err("incomplete LRAT hint chain should fail");
    match error {
        LratError::VerificationFailed(message) => {
            assert!(
                message.contains("ended without deriving a conflict"),
                "expected an incomplete hint-chain error, got: {message}"
            );
        }
        other => panic!("expected VerificationFailed, got {other:?}"),
    }
}

/// Rejects an LRAT proof whose first hint clause is not unit and not conflicting
/// under the current assignment, because such a hint cannot justify propagation.
#[test]
fn test_conformance_lrat_non_unit_hint_invalid() {
    let mut checker = LratChecker::new(2);
    checker
        .add_original(ClauseId(1), &lits(&[1, 2]))
        .expect("original clause 1 should load");
    checker
        .add_original(ClauseId(2), &lits(&[-1]))
        .expect("original clause 2 should load");

    let error = checker
        .verify_proof(&[LratStep::Add {
            id: ClauseId(3),
            clause: Vec::new(),
            hints: vec![1, 2],
        }])
        .expect_err("non-unit LRAT hint should be rejected");
    match error {
        LratError::VerificationFailed(message) => {
            assert!(
                message.contains("not unit or conflicting"),
                "expected a non-unit hint error, got: {message}"
            );
        }
        other => panic!("expected VerificationFailed, got {other:?}"),
    }
}

/// Rejects an LRAT proof that references a non-existent hint clause ID, because
/// every hint must name an active clause in the current database.
#[test]
fn test_conformance_lrat_missing_hint_clause_invalid() {
    let mut checker = LratChecker::new(1);
    checker
        .add_original(ClauseId(1), &lits(&[1]))
        .expect("original clause 1 should load");
    checker
        .add_original(ClauseId(2), &lits(&[-1]))
        .expect("original clause 2 should load");

    let error = checker
        .verify_proof(&[LratStep::Add {
            id: ClauseId(3),
            clause: Vec::new(),
            hints: vec![1, 99],
        }])
        .expect_err("missing LRAT hint clause should fail");
    assert_eq!(
        error,
        LratError::MissingHintClause(ClauseId(99)),
        "referencing hint clause 99 should be reported precisely"
    );
}

/// Rejects an LRAT proof that reuses an existing clause ID, because clause IDs
/// are globally unique across original and derived clauses.
#[test]
fn test_conformance_lrat_duplicate_id_invalid() {
    let mut checker = LratChecker::new(1);
    checker
        .add_original(ClauseId(1), &lits(&[1]))
        .expect("original clause 1 should load");
    checker
        .add_original(ClauseId(2), &lits(&[-1]))
        .expect("original clause 2 should load");

    let error = checker
        .verify_proof(&[LratStep::Add {
            id: ClauseId(1),
            clause: Vec::new(),
            hints: vec![1, 2],
        }])
        .expect_err("duplicate LRAT clause IDs should fail");
    assert_eq!(
        error,
        LratError::DuplicateClauseId(ClauseId(1)),
        "reusing clause ID 1 should be rejected as a duplicate"
    );
}

// Part 2 (LRAT rejection paths, FRAT, cross-checker differentials) lives in a
// #[path] child module so the parent's private helpers stay visible — the
// paragon files_over_1000 split at a test-fn boundary, behavior identical.
#[path = "conformance_tests_part2.rs"]
mod part2;
