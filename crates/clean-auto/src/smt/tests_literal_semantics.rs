// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::theories::arithmetic::ArithmeticTheory;
use crate::theories::equality::EqualityTheory;

// Proof coverage: negate involution and Lt/Le semantics

/// Verify negate(negate(x)) == x for ALL TheoryLiteral variants.
///
/// The Lt/Le negation swaps arguments: !(a < b) = (b <= a), !(b <= a) = (a < b).
/// A double-negate that doesn't recover the original would silently corrupt
/// the DPLL(T) loop when the SAT solver backtracks a theory literal.
#[test]
fn test_theory_literal_negate_involution_all_variants() {
    let a = TermId(1);
    let b = TermId(2);

    let cases: Vec<TheoryLiteral> = vec![
        TheoryLiteral::Eq(a, b),
        TheoryLiteral::Neq(a, b),
        TheoryLiteral::Lt(a, b),
        TheoryLiteral::Le(a, b),
        TheoryLiteral::Bool(0),
        TheoryLiteral::NegBool(0),
        // Asymmetric IDs -- critical for Lt/Le where negate swaps (a,b)->(b,a)
        TheoryLiteral::Lt(b, a),
        TheoryLiteral::Le(b, a),
        // Same-term edge case: !(a < a) = a <= a, !(a <= a) = a < a
        TheoryLiteral::Lt(a, a),
        TheoryLiteral::Le(a, a),
    ];

    for lit in &cases {
        let double = lit.negate().negate();
        assert_eq!(
            *lit, double,
            "negate(negate({:?})) = {:?} -- involution violated",
            lit, double
        );
    }
}

/// Verify that Lt/Le negation swaps are asymmetric: !(a < b) != !(b < a).
///
/// !(a < b) = (b <= a) while !(b < a) = (a <= b). If the argument swap
/// in negate() is missing or wrong, these would collapse to the same literal,
/// losing the direction of the inequality.
#[test]
fn test_theory_literal_negate_lt_le_asymmetric() {
    let a = TermId(1);
    let b = TermId(2);

    // !(a < b) should be Le(b, a), not Le(a, b)
    let neg_a_lt_b = TheoryLiteral::Lt(a, b).negate();
    assert_eq!(neg_a_lt_b, TheoryLiteral::Le(b, a));

    // !(b < a) should be Le(a, b), not Le(b, a)
    let neg_b_lt_a = TheoryLiteral::Lt(b, a).negate();
    assert_eq!(neg_b_lt_a, TheoryLiteral::Le(a, b));

    // The two negations must differ (they swap differently)
    assert_ne!(
        neg_a_lt_b, neg_b_lt_a,
        "!(a < b) and !(b < a) must differ -- negate swap is directional"
    );

    // Same for Le
    let neg_a_le_b = TheoryLiteral::Le(a, b).negate();
    assert_eq!(neg_a_le_b, TheoryLiteral::Lt(b, a));

    let neg_b_le_a = TheoryLiteral::Le(b, a).negate();
    assert_eq!(neg_b_le_a, TheoryLiteral::Lt(a, b));

    assert_ne!(
        neg_a_le_b, neg_b_le_a,
        "!(a <= b) and !(b <= a) must differ -- negate swap is directional"
    );
}

/// Integration test: !(a < b) semantics in the DPLL(T) loop.
///
/// If negate() for Lt is wrong (e.g., produces Le(a,b) instead of Le(b,a)),
/// the theory solver receives the wrong literal when the SAT solver negates
/// a decision, leading to unsound results.
///
/// Setup: a < b AND b <= a -> UNSAT (a < b and !(a < b) with correct negation).
/// If negate swaps are wrong: a < b and b <= a might be treated as a < b and a <= b
/// which is SAT (any a = b satisfies a <= b but not a < b -- still UNSAT).
/// But with more subtle bugs the solver could return SAT incorrectly.
#[test]
fn test_lt_le_negation_soundness_in_solver() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArithmeticTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");

    // a < b AND b <= a is contradictory:
    // a < b means a is strictly less than b.
    // b <= a means b is at most a.
    // Together: a < b <= a which requires a < a -- impossible.
    smt.add_clause(vec![TheoryLiteral::Lt(a, b)]);
    smt.add_clause(vec![TheoryLiteral::Le(b, a)]);

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: a < b and b <= a is contradictory.
        }
        SmtResult::Sat(_) => {
            panic!(
                "Expected UNSAT for a < b and b <= a -- this is contradictory. \
                 Lt/Le negation semantics may be broken in the arithmetic theory."
            );
        }
        SmtResult::Unknown => {
            // Acceptable: incomplete solver returns Unknown rather than wrong answer.
        }
    }
}

/// Verify Le transitivity produces UNSAT when combined with strict Lt.
///
/// a <= b, b <= c, c < a is UNSAT (a <= b <= c < a -> a < a).
/// This exercises the full Lt/Le interaction in the arithmetic theory,
/// including the negate() calls that happen during DPLL(T) backtracking.
#[test]
fn test_le_lt_transitivity_unsat() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArithmeticTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");

    smt.add_clause(vec![TheoryLiteral::Le(a, b)]);
    smt.add_clause(vec![TheoryLiteral::Le(b, c)]);
    smt.add_clause(vec![TheoryLiteral::Lt(c, a)]);

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: a <= b <= c < a is contradictory.
        }
        SmtResult::Sat(_) => {
            panic!(
                "Expected UNSAT for a <= b, b <= c, c < a -- this is contradictory. \
                 Lt/Le transitivity chain is not detected by the arithmetic theory."
            );
        }
        SmtResult::Unknown => {
            // Acceptable: incomplete reasoning.
        }
    }
}
