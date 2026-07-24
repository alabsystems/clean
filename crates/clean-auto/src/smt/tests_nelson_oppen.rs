// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nelson-Oppen core integration and DPLL(T) conflict-loop tests.
//!
//! Extracted from the main tests.rs to reduce file size (#2386 structural cleanup).
//! Covers the shared multi-theory integration cases that still live in this module.
//! Sibling modules now own the theory-order, Unknown-propagation, and fixpoint
//! forwarding regressions split out during the hotspot reduction.

use super::*;
use crate::theories::equality::EqualityTheory;

/// Regression test for #2302: Nelson-Oppen theory combination via SAT interface.
///
/// Setup: a = b, f(a) = c, f(b) = d, c < d.
/// EqualityTheory: a=b → congruence → f(a)=f(b). With f(a)=c and f(b)=d,
/// deduces c=d. ArithmeticTheory has c<d but doesn't know c=d.
/// Without #2302: ArithmeticTheory sees c<d as satisfiable (c,d independent).
/// With #2302: deduced c=d is propagated, ArithmeticTheory gets c=d AND c<d → UNSAT.
#[test]
fn test_nelson_oppen_congruence_to_arithmetic() {
    use crate::theories::arithmetic::ArithmeticTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArithmeticTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let d = smt.const_term("d");
    let f_a = smt.app_term("f", vec![a]);
    let f_b = smt.app_term("f", vec![b]);

    // EqualityTheory: a=b → congruence: f(a)=f(b)
    // With f(a)=c and f(b)=d → c=d (deduced, NOT in encoding)
    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_eq(f_a, c);
    let _ = smt.assert_eq(f_b, d);

    // ArithmeticTheory: c < d
    // Combined with deduced c=d → c < c → contradiction
    smt.add_clause(vec![TheoryLiteral::Lt(c, d)]);

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: congruence deduced c=d, propagated to ArithmeticTheory
        }
        other => {
            panic!(
                "Expected UNSAT (Nelson-Oppen: c=d via congruence, c<d), got {:?}",
                match other {
                    SmtResult::Sat(_) =>
                        "Sat (bug: congruence-deduced c=d not propagated to arithmetic)",
                    SmtResult::Unknown => "Unknown",
                    _ => unreachable!(),
                }
            );
        }
    }
}

/// Integration test: all 3 real theories in one SmtSolver (#2323).
///
/// Setup: EqualityTheory + ArithmeticTheory + ArrayTheory.
/// - store(a, i, v), select(store(a, i, v), i) = r  (equality + array)
/// - v < r  (arithmetic)
///
/// ROW-same: select(store(a,i,v),i) = v, combined with r = select_result = v,
/// gives v = r. But v < r contradicts v = r → UNSAT.
///
/// This requires all 3 theories cooperating:
/// - ArrayTheory: produces ROW-same propagation (select_result = v)
/// - EqualityTheory: deduces r = v from select_result = r and select_result = v
/// - ArithmeticTheory: detects v < r contradicts v = r
#[test]
fn test_three_theory_unsat_array_equality_arithmetic() {
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

    // select(store(a,i,v), i) = r
    let _ = smt.assert_eq(select_result, r);
    // v < r  (arithmetic constraint)
    smt.add_clause(vec![TheoryLiteral::Lt(v, r)]);

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: ROW-same → select_result = v, with select_result = r
            // gives r = v, contradicting v < r.
        }
        other => {
            panic!(
                "Expected UNSAT (3-theory: array ROW-same + equality + arith), got {:?}",
                match other {
                    SmtResult::Sat(_) => "Sat (bug: theory interaction incomplete)",
                    SmtResult::Unknown => "Unknown",
                    _ => unreachable!(),
                }
            );
        }
    }
}

/// Integration test: 3 real theories with satisfiable constraints (#2323).
///
/// Verifies that EqualityTheory + ArithmeticTheory + ArrayTheory can agree
/// on SAT when all constraints are consistent.
///
/// Setup:
/// - store(a, i, v), select(store(a, i, v), j) where i ≠ j
/// - select(a, j) = r  (equality)
/// - v < r  (arithmetic — exercises ArithmeticTheory with a real Lt constraint)
///
/// ROW-diff: i ≠ j → select(store(a,i,v), j) = select(a, j) = r.
/// ArithmeticTheory: v < r is independent of the array/equality constraints
/// (v is the stored value at index i; r is the value at index j). Consistent → SAT.
#[test]
fn test_three_theory_sat_consistent() {
    use crate::theories::arithmetic::ArithmeticTheory;
    use crate::theories::arrays::ArrayTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArithmeticTheory::new()));
    smt.add_theory(Box::new(ArrayTheory::new()));

    let a = smt.const_term("a");
    let i = smt.const_term("i");
    let j = smt.const_term("j");
    let v = smt.const_term("v");
    let r = smt.const_term("r");
    let store_aiv = smt.store_term(a, i, v);
    let select_store_j = smt.select_term(store_aiv, j);
    let select_a_j = smt.select_term(a, j);

    // i ≠ j
    let _ = smt.assert_neq(i, j);
    // select(a, j) = r
    let _ = smt.assert_eq(select_a_j, r);
    // select(store(a,i,v), j) = r (consistent with ROW-diff)
    let _ = smt.assert_eq(select_store_j, r);
    // v < r — arithmetic constraint giving ArithmeticTheory actual work.
    // v is the stored value at index i, r is the read value at index j.
    // These are independent terms, so v < r is satisfiable.
    smt.add_clause(vec![TheoryLiteral::Lt(v, r)]);

    match smt.solve() {
        SmtResult::Sat(_) => {
            // Correct: all constraints are consistent.
            // ArithmeticTheory processes Lt(v, r) and finds no contradiction.
        }
        other => {
            panic!(
                "Expected SAT (3-theory consistent), got {:?}",
                match other {
                    SmtResult::Unsat(_) => "Unsat (bug: spurious theory conflict with 3 theories)",
                    SmtResult::Unknown => "Unknown",
                    _ => unreachable!(),
                }
            );
        }
    }
}

/// Integration test: BCP resolves disjunction with multiple real theories (#2323).
///
/// NOTE: Despite the original name suggesting backtracking, this test is
/// resolved entirely by BCP at decision level 0. The unit clause (a≠b)
/// forces v0=false, making clause (a=b OR c=d) unit on c=d. No decisions
/// or backtracks occur. Renamed from `test_multi_theory_backtrack_disjunction`
/// for accuracy. See `test_dpll_t_transitivity_conflict_forces_resolve`
/// for a test that actually exercises the DPLL(T) theory-conflict loop.
///
/// Setup:
/// - (a = b) OR (c = d)           — disjunction
/// - a ≠ b                         — unit clause forces v0=false
/// - store(arr, c, v), select(store(arr, c, v), c) = w  (array)
/// - d = w                         — consistent with c=d branch
///
/// BCP: [-v0] forces c=d via unit propagation. All theories consistent.
#[test]
fn test_multi_theory_bcp_disjunction() {
    use crate::theories::arrays::ArrayTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArrayTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let d = smt.const_term("d");
    let arr = smt.const_term("arr");
    let v = smt.const_term("v");
    let w = smt.const_term("w");
    let store_cv = smt.store_term(arr, c, v);
    let select_result = smt.select_term(store_cv, c);

    // Disjunction: (a = b) OR (c = d)
    smt.add_clause(vec![TheoryLiteral::Eq(a, b), TheoryLiteral::Eq(c, d)]);
    // Unit clause: a ≠ b (BCP forces c=d via the disjunction)
    let _ = smt.assert_neq(a, b);
    // Array setup: select(store(arr, c, v), c) = w
    let _ = smt.assert_eq(select_result, w);
    // d = w — consistent when c = d holds
    let _ = smt.assert_eq(d, w);

    match smt.solve() {
        SmtResult::Sat(model) => {
            // BCP resolved: c=d must hold via unit propagation.
            assert!(
                model.equalities.contains(&(c, d)) || model.equalities.contains(&(d, c)),
                "Expected c=d in model via BCP"
            );
        }
        other => {
            panic!(
                "Expected SAT (BCP resolves disjunction), got {:?}",
                match other {
                    SmtResult::Unsat(_) => "Unsat",
                    SmtResult::Unknown => "Unknown",
                    _ => unreachable!(),
                }
            );
        }
    }
}

/// Integration test: DPLL(T) theory conflict forces a second solve iteration.
///
/// This test requires the DPLL(T) outer loop to iterate: the first SAT
/// model satisfies all clauses but violates equality transitivity, the
/// theory returns a conflict, a blocking clause is added, and the CDCL
/// solver re-solves to find a theory-consistent model.
///
/// Previously, this returned UNSAT due to a bug where sat_solve_with_theory()
/// called reset_propagation_queue() without backtracking the CDCL solver.
/// solve()'s initial propagation hit the blocking clause at a stale decision
/// level and misclassified it as level-0 UNSAT.
///
/// Fix: backtrack_to_root() + reset_propagation_queue() in sat_solve_with_theory.
///
/// Setup (EqualityTheory only):
/// - (a=b) OR (b=c)              — disjunction, at least one must hold
/// - a ≠ c                        — unit clause
///
/// First CDCL solve: VSIDS decides v0=T (a=b), v1=T (b=c) (positive polarity).
/// Model: {a=b, b=c, a≠c}. Theory detects: a=b ∧ b=c → a=c by transitivity,
/// contradicting a≠c → conflict. Blocking clause ¬(a=b ∧ b=c) added.
///
/// Second CDCL solve: blocking clause prevents both a=b and b=c from being
/// true simultaneously. Solver finds model with exactly one of them → SAT.
#[test]
fn test_dpll_t_transitivity_conflict_forces_resolve() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");

    // (a=b) OR (b=c) — at least one must hold
    smt.add_clause(vec![TheoryLiteral::Eq(a, b), TheoryLiteral::Eq(b, c)]);
    // a ≠ c — incompatible with BOTH a=b AND b=c (transitivity gives a=c)
    let _ = smt.assert_neq(a, c);

    match smt.solve() {
        SmtResult::Sat(_model) => {
            // Correct: DPLL(T) found a theory-consistent model after
            // rejecting the first model where both a=b and b=c held.
            // The model has exactly one of a=b or b=c.
        }
        SmtResult::Unsat(_) => {
            panic!(
                "Expected SAT (a=b xor b=c is consistent with a≠c), \
                 got UNSAT — DPLL(T) loop may not be adding blocking clause correctly"
            );
        }
        SmtResult::Unknown => {
            panic!(
                "Expected SAT, got Unknown — DPLL(T) may have hit iteration limit \
                 before finding a theory-consistent model"
            );
        }
    }
}

/// Integration test: arithmetic-implied equalities forwarded to EUF (#2364).
///
/// Setup: x <= c, c <= x (so x = c), y <= c, c <= y (so y = c), f(x) != f(y).
///
/// ArithmeticTheory: x = c = y (both squeezed to the same constant).
/// Without #2364: ArithmeticTheory never tells EUF that x = y.
///                EUF sees f(x) != f(y) with x, y unrelated → SAT (wrong).
/// With #2364:    ArithmeticTheory deduces x = y, propagates to SAT.
///                EUF gets x = y → congruence → f(x) = f(y) → contradiction
///                with f(x) != f(y) → UNSAT (correct).
#[test]
fn test_nelson_oppen_arithmetic_to_euf_equality() {
    use crate::theories::arithmetic::ArithmeticTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArithmeticTheory::new()));

    let x = smt.const_term("x");
    let y = smt.const_term("y");
    let c = smt.const_term("c");
    let f_x = smt.app_term("f", vec![x]);
    let f_y = smt.app_term("f", vec![y]);

    // x <= c and c <= x → arithmetic forces x = c
    smt.add_clause(vec![TheoryLiteral::Le(x, c)]);
    smt.add_clause(vec![TheoryLiteral::Le(c, x)]);

    // y <= c and c <= y → arithmetic forces y = c
    smt.add_clause(vec![TheoryLiteral::Le(y, c)]);
    smt.add_clause(vec![TheoryLiteral::Le(c, y)]);

    // EqualityTheory: f(x) != f(y) — contradicts x = y (via congruence)
    let _ = smt.assert_neq(f_x, f_y);

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: ArithmeticTheory deduces x = c = y, propagates x = y
            // to SAT. EUF derives f(x) = f(y) by congruence. f(x) != f(y)
            // contradicts → UNSAT.
        }
        SmtResult::Sat(_) => {
            panic!(
                "Expected UNSAT: arithmetic implies x = c = y, so f(x) = f(y) by \
                 congruence, contradicting f(x) != f(y). \
                 ArithmeticTheory may not be propagating deduced equalities (#2364)."
            );
        }
        SmtResult::Unknown => {
            panic!(
                "Expected UNSAT, got Unknown — DPLL(T) may have hit iteration limit. \
                 ArithmeticTheory equality propagation may not be integrated (#2364)."
            );
        }
    }
}
