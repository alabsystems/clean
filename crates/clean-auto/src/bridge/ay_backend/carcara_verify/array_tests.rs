// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::verify_alethe_proof;

const DECLARATIONS: &str = "(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const i (_ BitVec 64))
(declare-const j (_ BitVec 64))
(declare-const k (_ BitVec 64))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))";

fn row_problem(conclusion: &str) -> String {
    format!("{DECLARATIONS}\n(assert (not (= i j)))\n(assert (not {conclusion}))\n(check-sat)")
}

fn row_proof(conclusion: &str, premises: &str) -> String {
    format!("(assume guard (not (= i j)))\n(assume neg (not {conclusion}))\n(step row (cl {conclusion}) :rule arrays_row {premises})\n(step done (cl) :rule resolution :premises (row neg))")
}

#[test]
fn array_read_over_write_checks_64_bit_index_guard() {
    let conclusion = "(= (select (store a i x) j) (select a j))";
    assert!(matches!(
        verify_alethe_proof(
            &row_problem(conclusion),
            &row_proof(conclusion, ":premises (guard)")
        ),
        Ok(true)
    ));
}

#[test]
fn array_read_over_write_rejects_changed_array_index_and_missing_guard() {
    for conclusion in [
        "(= (select (store a i x) j) (select b j))",
        "(= (select (store a i x) j) (select a k))",
        "(= (select (store a i x) k) (select a k))",
    ] {
        assert!(verify_alethe_proof(
            &row_problem(conclusion),
            &row_proof(conclusion, ":premises (guard)")
        )
        .is_err());
    }
    let conclusion = "(= (select (store a i x) j) (select a j))";
    assert!(verify_alethe_proof(&row_problem(conclusion), &row_proof(conclusion, "")).is_err());
    let forged = row_proof(conclusion, ":premises (guard)").replace(
        "(assume guard (not (= i j)))",
        "(assume guard (not (= i k)))",
    );
    assert!(verify_alethe_proof(&row_problem(conclusion), &forged).is_err());
}

#[test]
fn array_read_at_written_index_checks_value_and_index() {
    for (conclusion, valid) in [
        ("(= (select (store a i x) i) x)", true),
        ("(= (select (store a i x) j) x)", false),
        ("(= (select (store a i x) i) y)", false),
    ] {
        let problem = format!("{DECLARATIONS}\n(assert (not {conclusion}))\n(check-sat)");
        let proof = format!("(assume neg (not {conclusion}))\n(step row (cl {conclusion}) :rule arrays_idx)\n(step done (cl) :rule resolution :premises (row neg))");
        let result = verify_alethe_proof(&problem, &proof);
        if valid {
            assert!(matches!(result, Ok(true)));
        } else {
            assert!(result.is_err());
        }
    }
}

#[test]
fn array_proofs_still_reject_holes_and_unknown_rules() {
    let conclusion = "(= (select (store a i x) j) (select a j))";
    let proof = row_proof(conclusion, ":premises (guard)");
    assert!(matches!(
        verify_alethe_proof(
            &row_problem(conclusion),
            &proof.replace(":rule arrays_row", ":rule hole")
        ),
        Ok(false)
    ));
    assert!(verify_alethe_proof(
        &row_problem(conclusion),
        &proof.replace(":rule arrays_row", ":rule unverified_array_row")
    )
    .is_err());
}
