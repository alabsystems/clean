// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRAT oracle-conformance corpus and text rendering.

use crate::tactic::drat::types::{CnfFormula, LratOp, LratProof};

use super::LratCorpusCase;

/// Build the maintained corpus of LRAT test cases.
///
/// Fixtures are inlined from the same logical shapes as the unit tests in
/// `drat/tests.rs` and `ay_proof_tests/support.rs`. See design doc section 3.
pub fn build_corpus() -> Vec<LratCorpusCase> {
    vec![
        // Case 1: Simple UNSAT — (x1) ∧ (¬x1 ∨ x2) ∧ (¬x2)
        // Provenance: test_lrat_basic_verification in drat/tests.rs
        build_simple_unsat(),
        // Case 2: Contradiction — (x1) ∧ (¬x1)
        // Provenance: contradiction_lrat_proof in ay_proof_tests/support.rs
        build_contradiction(),
        // Case 3: PHP(2,1) — pigeonhole (2 pigeons, 1 hole)
        // Provenance: test_drat_pigeon_hole_2_1 in drat/tests.rs (adapted to LRAT)
        build_php_2_1(),
        // Case 4: Expected rejection — SAT formula with bogus proof
        // Provenance: test_drat_invalid_proof_rejected in drat/tests.rs
        build_sat_rejected(),
        // Case 5: Streaming/checkpoint parity — same shape as simple_unsat,
        // verified through all three internal code paths (batch, streaming,
        // checkpoint/resume) to confirm agreement.
        // Provenance: test_streaming_checkpoint_resume in drat/tests.rs
        build_streaming_checkpoint_parity(),
    ]
}

fn build_simple_unsat() -> LratCorpusCase {
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]); // id=1: x1
    formula.add_clause(vec![-1, 2]); // id=2: ¬x1 ∨ x2
    formula.add_clause(vec![-2]); // id=3: ¬x2

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

    LratCorpusCase {
        name: "simple_unsat",
        formula,
        proof,
        expected_internal: true,
    }
}

fn build_contradiction() -> LratCorpusCase {
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]); // id=1: x1
    formula.add_clause(vec![-1]); // id=2: ¬x1

    let mut proof = LratProof::new();
    proof.operations.push(LratOp::Add {
        id: 3,
        clause: vec![],
        hints: vec![1, 2],
    });

    LratCorpusCase {
        name: "contradiction",
        formula,
        proof,
        expected_internal: true,
    }
}

fn build_php_2_1() -> LratCorpusCase {
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]); // id=1: pigeon 1 in hole 1
    formula.add_clause(vec![2]); // id=2: pigeon 2 in hole 1
    formula.add_clause(vec![-1, -2]); // id=3: at most one pigeon per hole

    let mut proof = LratProof::new();
    // Hint chain: clause 1 (x1=true), clause 2 (x2=true),
    // clause 3 (¬x1 ∨ ¬x2 conflicts with x1=true, x2=true).
    proof.operations.push(LratOp::Add {
        id: 4,
        clause: vec![],
        hints: vec![1, 2, 3],
    });

    LratCorpusCase {
        name: "php_2_1",
        formula,
        proof,
        expected_internal: true,
    }
}

fn build_sat_rejected() -> LratCorpusCase {
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1, 2]); // id=1: satisfiable (x1 ∨ x2)

    let mut proof = LratProof::new();
    // Bogus proof: tries to derive empty clause from a single non-unit clause
    proof.operations.push(LratOp::Add {
        id: 2,
        clause: vec![],
        hints: vec![1],
    });

    LratCorpusCase {
        name: "sat_rejected",
        formula,
        proof,
        expected_internal: false,
    }
}

fn build_streaming_checkpoint_parity() -> LratCorpusCase {
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]); // id=1
    formula.add_clause(vec![-1, 2]); // id=2
    formula.add_clause(vec![-2]); // id=3

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

    LratCorpusCase {
        name: "streaming_checkpoint_parity",
        formula,
        proof,
        expected_internal: true,
    }
}

/// Render a `CnfFormula` as DIMACS CNF text.
pub fn render_dimacs(formula: &CnfFormula) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    let _ = writeln!(out, "p cnf {} {}", formula.num_vars, formula.clauses.len());
    for clause in &formula.clauses {
        for lit in clause {
            let _ = write!(out, "{} ", lit);
        }
        out.push_str("0\n");
    }
    out
}

/// Render an `LratProof` as LRAT text.
pub fn render_lrat(proof: &LratProof) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    for op in &proof.operations {
        match op {
            LratOp::Add { id, clause, hints } => {
                let _ = write!(out, "{} ", id);
                for lit in clause {
                    let _ = write!(out, "{} ", lit);
                }
                out.push_str("0 ");
                for hint in hints {
                    let _ = write!(out, "{} ", hint);
                }
                out.push_str("0\n");
            }
            LratOp::Delete { id, clause_ids } => {
                let _ = write!(out, "{} d ", id);
                for cid in clause_ids {
                    let _ = write!(out, "{} ", cid);
                }
                out.push_str("0\n");
            }
        }
    }
    out
}
