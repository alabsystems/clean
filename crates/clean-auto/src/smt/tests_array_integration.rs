// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::theories::arrays::ArrayTheory;
use crate::theories::equality::EqualityTheory;

/// Regression test for #2325: collect_array_propagations must create SAT
/// variables on demand for theory-deduced equalities not in the original
/// encoding.
///
/// Setup: select(store(a, i, v), i) = r, r != v
/// ROW axiom: select(store(a, i, v), i) = v
/// Therefore: r = v (transitivity), contradicting r != v -> UNSAT
///
/// Before #2325 fix: Eq(select_result, v) had no SAT variable because it
/// was never part of the original problem. The propagation was silently
/// dropped, allowing the solver to return Sat (unsound).
/// After fix: SAT variable created on demand -> propagation reaches the
/// solver -> EqualityTheory detects transitivity violation -> UNSAT.
#[test]
fn test_array_propagation_creates_var_on_demand() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArrayTheory::new()));

    // Terms: a, i, v, r, store(a, i, v), select(store(a, i, v), i)
    let a = smt.const_term("a");
    let i = smt.const_term("i");
    let v = smt.const_term("v");
    let r = smt.const_term("r");
    let store_aiv = smt.app_term("store", vec![a, i, v]);
    let select_result = smt.app_term("select", vec![store_aiv, i]);

    // Assert select(store(a,i,v), i) = r -- creates var for Eq(select_result, r)
    let _ = smt.assert_eq(select_result, r);
    // Assert r != v -- creates var for Eq(r, v), negated
    let _ = smt.assert_neq(r, v);

    // No SAT variable for Eq(select_result, v): the equality the array
    // theory will deduce via ROW-same axiom. This is the #2325 gap.

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: ROW axiom forces select(store(a,i,v),i) = v,
            // combined with select_result = r gives r = v by transitivity,
            // contradicting r != v.
        }
        other => {
            panic!(
                "Expected UNSAT (ROW axiom + transitivity), got {:?}",
                match other {
                    SmtResult::Sat(_) => "Sat (soundness gap: array propagation dropped)",
                    SmtResult::Unknown => "Unknown",
                    _ => unreachable!(),
                }
            );
        }
    }
}

/// Regression test for #2314: collect_array_propagations must find
/// existing SAT variables even when the Eq field order is reversed.
///
/// Setup: select(store(a, i, v), i) = r, r != v, plus a clause that
/// registers Eq(v, select_result) -- note v comes FIRST. The array
/// theory's ROW-same axiom produces pending equality (select_result, v)
/// with select_result first, which is the reverse field order.
///
/// Without #2314 fix: the single-order lookup for Eq(select_result, v)
/// misses the registered Eq(v, select_result), creates a duplicate SAT
/// variable, and the propagation may not correctly interact with existing
/// clauses -- potentially returning Sat or Unknown instead of UNSAT.
/// With #2314 fix: the dual-lookup finds Eq(v, select_result) -> the
/// existing variable is reused -> propagation connects correctly -> UNSAT.
#[test]
fn test_array_propagation_reversed_eq_order_lookup() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArrayTheory::new()));

    // Terms: a, i, v, r, store(a, i, v), select(store(a, i, v), i)
    let a = smt.const_term("a");
    let i = smt.const_term("i");
    let v = smt.const_term("v");
    let r = smt.const_term("r");
    let store_aiv = smt.app_term("store", vec![a, i, v]);
    let select_result = smt.app_term("select", vec![store_aiv, i]);

    // Register Eq(v, select_result) in REVERSED order from what the array
    // theory will produce. This clause puts the variable in theory_to_var
    // keyed as Eq(v, select_result). The array's ROW-same axiom will produce
    // (select_result, v) -- the reverse. The dual-lookup is needed to find it.
    //
    // We also include a dummy alternative so this isn't a unit clause
    // (a unit clause would immediately force the equality true, making the
    // propagation redundant before it even fires).
    let dummy = smt.const_term("dummy");
    smt.add_clause(vec![
        TheoryLiteral::Eq(v, select_result),
        TheoryLiteral::Eq(a, dummy),
    ]);

    // Assert select(store(a,i,v), i) = r
    let _ = smt.assert_eq(select_result, r);
    // Assert r != v -- combined with ROW-same (select_result = v) and
    // select_result = r gives r = v by transitivity, contradicting r != v.
    let _ = smt.assert_neq(r, v);

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: ROW-same forces select(store(a,i,v),i) = v,
            // combined with select_result = r gives r = v (transitivity),
            // contradicting r != v. The reversed-order Eq was found via
            // dual-lookup in collect_array_propagations (#2314).
        }
        other => {
            panic!(
                "Expected UNSAT (reversed Eq order lookup #2314), got {:?}",
                match other {
                    SmtResult::Sat(_) =>
                        "Sat (bug: reversed Eq lookup missed, duplicate var created)",
                    SmtResult::Unknown => "Unknown",
                    _ => unreachable!(),
                }
            );
        }
    }
}

/// Regression test for #2325: ROW-diff axiom propagations also benefit
/// from on-demand SAT variable creation.
///
/// Setup: i != j, select(store(a, i, v), j) = r, select(a, j) != r
/// ROW-diff axiom: i != j -> select(store(a, i, v), j) = select(a, j)
/// Therefore: r = select(a, j) (transitivity), contradicting select(a, j) != r -> UNSAT
///
/// No SAT variable exists for Eq(select_store_result, select_base_result)
/// because the user never directly related these terms.
#[test]
fn test_array_row_diff_propagation_creates_var_on_demand() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArrayTheory::new()));

    // Terms: a, i, j, v, r, store(a,i,v), select(store(a,i,v), j), select(a, j)
    let a = smt.const_term("a");
    let i = smt.const_term("i");
    let j = smt.const_term("j");
    let v = smt.const_term("v");
    let r = smt.const_term("r");
    let store_aiv = smt.app_term("store", vec![a, i, v]);
    let select_store_j = smt.app_term("select", vec![store_aiv, j]);
    let select_a_j = smt.app_term("select", vec![a, j]);

    // Assert i != j -- triggers ROW-diff axiom
    let _ = smt.assert_neq(i, j);
    // Assert select(store(a,i,v), j) = r
    let _ = smt.assert_eq(select_store_j, r);
    // Assert select(a, j) != r
    let _ = smt.assert_neq(select_a_j, r);

    // No SAT variable for Eq(select_store_j, select_a_j). The array theory
    // deduces this via ROW-diff, but without #2325 fix, the propagation is
    // dropped and the solver incorrectly returns Sat.

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: ROW-diff forces select(store(a,i,v),j) = select(a,j),
            // combined with select_store_j = r gives select(a,j) = r,
            // contradicting select(a,j) != r.
        }
        other => {
            panic!(
                "Expected UNSAT (ROW-diff axiom + transitivity), got {:?}",
                match other {
                    SmtResult::Sat(_) => "Sat (soundness gap: array propagation dropped)",
                    SmtResult::Unknown => "Unknown",
                    _ => unreachable!(),
                }
            );
        }
    }
}
