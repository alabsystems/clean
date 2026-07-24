// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Determinism-focused proof trail regressions.

use super::*;
use crate::theories::equality::EqualityTheory;

fn solve_array_row_same_propagation_trail() -> Vec<ProofTrailEntry> {
    use crate::theories::arrays::ArrayTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(ArrayTheory::new()));

    let a0 = smt.const_term("a0");
    let i0 = smt.const_term("i0");
    let v0 = smt.const_term("v0");
    let r0 = smt.const_term("r0");
    let store0 = smt.store_term(a0, i0, v0);
    let select0 = smt.select_term(store0, i0);
    let _ = smt.assert_eq(select0, r0);

    let a1 = smt.const_term("a1");
    let i1 = smt.const_term("i1");
    let v1 = smt.const_term("v1");
    let r1 = smt.const_term("r1");
    let store1 = smt.store_term(a1, i1, v1);
    let select1 = smt.select_term(store1, i1);
    let _ = smt.assert_eq(select1, r1);

    match smt.solve() {
        SmtResult::Sat(_) => {}
        result => panic!("expected SAT for array row-same propagation fixture, got {result:?}"),
    }

    smt.proof_trail().to_vec()
}

fn solve_three_theory_array_arith_conflict_trail() -> Vec<ProofTrailEntry> {
    use crate::theories::arithmetic::ArithmeticTheory;
    use crate::theories::arrays::ArrayTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArithmeticTheory::new()));
    smt.add_theory(Box::new(ArrayTheory::new()));

    let a = smt.const_term("a");
    let i = smt.const_term("i");
    let v = smt.const_term("v");
    let r = smt.const_term("r");
    let store_aiv = smt.store_term(a, i, v);
    let select_result = smt.select_term(store_aiv, i);

    let _ = smt.assert_eq(select_result, r);
    smt.add_clause(vec![TheoryLiteral::Lt(v, r)]);

    match smt.solve() {
        SmtResult::Unsat(_) => {}
        result => {
            panic!("expected UNSAT for array/equality/arithmetic conflict fixture, got {result:?}")
        }
    }

    smt.proof_trail().to_vec()
}

#[test]
fn test_proof_trail_array_row_same_propagation_order_deterministic() {
    let first = solve_array_row_same_propagation_trail();
    let second = solve_array_row_same_propagation_trail();

    assert_eq!(
        first, second,
        "re-running the same multi-store array problem should preserve propagation trail order"
    );
    assert_eq!(
        first.len(),
        2,
        "fixture should emit one row-same propagation per store/select pair"
    );
    assert!(
        first.iter().all(|entry| matches!(
            entry,
            ProofTrailEntry::TheoryPropagation {
                theory_name: "Arrays",
                ..
            }
        )),
        "fixture should record only Array-theory propagation entries: {first:?}"
    );
}

#[test]
fn test_proof_trail_three_theory_conflict_deterministic_across_runs() {
    let first = solve_three_theory_array_arith_conflict_trail();
    let second = solve_three_theory_array_arith_conflict_trail();

    assert_eq!(
        first, second,
        "re-running the same three-theory UNSAT problem should preserve the full conflict trace"
    );
    assert!(
        first
            .iter()
            .any(|entry| matches!(entry, ProofTrailEntry::TheoryConflict { .. })),
        "fixture should record at least one theory conflict: {first:?}"
    );
}
