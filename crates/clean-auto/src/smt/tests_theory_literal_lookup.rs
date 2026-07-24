// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_theory_literal_to_sat_literal_eq_reverse_lookup_reuses_existing_var() {
    let mut smt = SmtSolver::new();
    let a = smt.const_term("a");
    let b = smt.const_term("b");

    smt.add_clause(vec![TheoryLiteral::Eq(a, b)]);

    let forward = smt
        .theory_literal_to_sat_literal(&TheoryLiteral::Eq(a, b))
        .expect("forward Eq lookup should succeed");
    let reversed = smt
        .theory_literal_to_sat_literal(&TheoryLiteral::Eq(b, a))
        .expect("reversed Eq lookup should reuse the same SAT variable");

    assert_eq!(
        reversed, forward,
        "Eq lookup should be orientation-insensitive once the atom is interned"
    );
}

#[test]
fn test_theory_literal_to_sat_literal_neq_reverse_lookup_reuses_existing_var() {
    let mut smt = SmtSolver::new();
    let a = smt.const_term("a");
    let b = smt.const_term("b");

    smt.add_clause(vec![TheoryLiteral::Eq(a, b)]);

    let forward = smt
        .theory_literal_to_sat_literal(&TheoryLiteral::Neq(a, b))
        .expect("forward Neq lookup should succeed");
    let reversed = smt
        .theory_literal_to_sat_literal(&TheoryLiteral::Neq(b, a))
        .expect("reversed Neq lookup should reuse the same SAT variable");

    assert_eq!(
        reversed, forward,
        "Neq lookup should be orientation-insensitive once the atom is interned"
    );
    assert!(
        !reversed.is_pos(),
        "Neq lookup should preserve negative polarity of the equality atom"
    );
}
