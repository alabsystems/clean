// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nelson-Oppen isolation, ordering, and multi-iteration tests.

use super::*;
use crate::theories::equality::EqualityTheory;

/// Nelson-Oppen isolation: theory registration order must not affect correctness.
///
/// EUF->Arith vs Arith->EUF registration should both produce UNSAT for the
/// same problem: a=b, f(a)=c, f(b)=d, c<d.
/// If the result differs, the propagation pipeline has an ordering dependency.
#[test]
fn test_nelson_oppen_theory_order_independence_unsat() {
    use crate::theories::arithmetic::ArithmeticTheory;

    // Order 1: EUF first, Arithmetic second
    let result1 = {
        let mut smt = SmtSolver::new();
        smt.add_theory(Box::new(EqualityTheory::new()));
        smt.add_theory(Box::new(ArithmeticTheory::new()));
        let a = smt.const_term("a");
        let b = smt.const_term("b");
        let c = smt.const_term("c");
        let d = smt.const_term("d");
        let f_a = smt.app_term("f", vec![a]);
        let f_b = smt.app_term("f", vec![b]);
        let _ = smt.assert_eq(a, b);
        let _ = smt.assert_eq(f_a, c);
        let _ = smt.assert_eq(f_b, d);
        smt.add_clause(vec![TheoryLiteral::Lt(c, d)]);
        smt.solve()
    };

    // Order 2: Arithmetic first, EUF second
    let result2 = {
        let mut smt = SmtSolver::new();
        smt.add_theory(Box::new(ArithmeticTheory::new()));
        smt.add_theory(Box::new(EqualityTheory::new()));
        let a = smt.const_term("a");
        let b = smt.const_term("b");
        let c = smt.const_term("c");
        let d = smt.const_term("d");
        let f_a = smt.app_term("f", vec![a]);
        let f_b = smt.app_term("f", vec![b]);
        let _ = smt.assert_eq(a, b);
        let _ = smt.assert_eq(f_a, c);
        let _ = smt.assert_eq(f_b, d);
        smt.add_clause(vec![TheoryLiteral::Lt(c, d)]);
        smt.solve()
    };

    assert!(
        matches!(result1, SmtResult::Unsat(_)),
        "EUF-first order should be UNSAT, got {:?}",
        std::mem::discriminant(&result1)
    );
    assert!(
        matches!(result2, SmtResult::Unsat(_)),
        "Arith-first order should be UNSAT, got {:?} - theory ordering dependence detected",
        std::mem::discriminant(&result2)
    );
}

/// Nelson-Oppen isolation: SAT result must also be order-independent.
///
/// Both theory registration orders must agree on SAT for a satisfiable
/// problem with interleaved EUF and arithmetic constraints.
#[test]
fn test_nelson_oppen_theory_order_independence_sat() {
    use crate::theories::arithmetic::ArithmeticTheory;

    // Problem: a != b, f(a) = c, f(b) = d, c < d (satisfiable)
    let build_and_solve = |euf_first: bool| -> SmtResult {
        let mut smt = SmtSolver::new();
        if euf_first {
            smt.add_theory(Box::new(EqualityTheory::new()));
            smt.add_theory(Box::new(ArithmeticTheory::new()));
        } else {
            smt.add_theory(Box::new(ArithmeticTheory::new()));
            smt.add_theory(Box::new(EqualityTheory::new()));
        }
        let a = smt.const_term("a");
        let b = smt.const_term("b");
        let c = smt.const_term("c");
        let d = smt.const_term("d");
        let f_a = smt.app_term("f", vec![a]);
        let f_b = smt.app_term("f", vec![b]);
        let _ = smt.assert_neq(a, b);
        let _ = smt.assert_eq(f_a, c);
        let _ = smt.assert_eq(f_b, d);
        smt.add_clause(vec![TheoryLiteral::Lt(c, d)]);
        smt.solve()
    };

    let result1 = build_and_solve(true);
    let result2 = build_and_solve(false);

    assert!(
        matches!(result1, SmtResult::Sat(_)),
        "EUF-first order should be SAT (a!=b allows f(a)!=f(b)), got {:?}",
        std::mem::discriminant(&result1)
    );
    assert!(
        matches!(result2, SmtResult::Sat(_)),
        "Arith-first order should also be SAT - theory ordering dependence detected, got {:?}",
        std::mem::discriminant(&result2)
    );
}

/// Nelson-Oppen isolation: backtrack in one theory must not corrupt another.
///
/// After a theory conflict + backtrack + successful re-solve, both theories
/// must be in clean states. We test this by solving two related problems
/// sequentially on the SAME SmtSolver instance - the second problem would
/// give a wrong answer if backtrack state leaked between theories.
#[test]
fn test_nelson_oppen_backtrack_isolation() {
    use crate::theories::arithmetic::ArithmeticTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArithmeticTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");

    // Phase 1: (a=b OR b=c), a!=c - SAT via DPLL(T) conflict+backtrack
    // EUF detects a=b and b=c -> a=c (transitivity) conflicts with a!=c.
    // Solver backtracks and finds model with exactly one of a=b, b=c.
    smt.add_clause(vec![TheoryLiteral::Eq(a, b), TheoryLiteral::Eq(b, c)]);
    let _ = smt.assert_neq(a, c);

    match smt.solve() {
        SmtResult::Sat(_) => {
            // Correct: DPLL(T) found consistent model after conflict+backtrack.
        }
        other => {
            panic!(
                "Phase 1 expected SAT (one of a=b, b=c), got {:?} - \
                 DPLL(T) backtrack may be broken",
                std::mem::discriminant(&other)
            );
        }
    }

    // Phase 2: add new constraint a < b on the SAME solver instance.
    // If theories didn't fully backtrack from Phase 1, arithmetic might
    // retain stale bounds or EUF might retain stale equalities.
    smt.add_clause(vec![TheoryLiteral::Lt(a, b)]);

    match smt.solve() {
        SmtResult::Sat(_) => {
            // Correct: a < b is consistent with one-of a=b,b=c + a!=c.
            // (a=b is ruled out by a<b since a<b contradicts a=b,
            //  so b=c must hold. That's consistent with a!=c and a<b.)
        }
        SmtResult::Unknown => {
            // Acceptable but concerning - may indicate iteration limit hit.
        }
        SmtResult::Unsat(_) => {
            panic!(
                "Phase 2 expected SAT or Unknown after adding a<b, got UNSAT - \
                 backtrack state may have leaked between theory combination phases"
            );
        }
    }
}

/// Nelson-Oppen isolation: three-theory order independence.
///
/// Array + EUF + Arithmetic: ROW-same + congruence + bound violation.
/// Tests all 6 permutations of theory registration order.
#[test]
fn test_nelson_oppen_three_theory_order_permutations() {
    use crate::theories::arithmetic::ArithmeticTheory;
    use crate::theories::arrays::ArrayTheory;

    let solve_with_order = |order: [u8; 3]| -> SmtResult {
        let mut smt = SmtSolver::new();
        for &idx in &order {
            match idx {
                0 => {
                    smt.add_theory(Box::new(EqualityTheory::new()));
                }
                1 => {
                    smt.add_theory(Box::new(ArithmeticTheory::new()));
                }
                2 => {
                    smt.add_theory(Box::new(ArrayTheory::new()));
                }
                _ => unreachable!(),
            }
        }
        let a = smt.const_term("a");
        let i = smt.const_term("i");
        let v = smt.const_term("v");
        let r = smt.const_term("r");
        let store_aiv = smt.store_term(a, i, v);
        let select_result = smt.select_term(store_aiv, i);
        let _ = smt.assert_eq(select_result, r);
        smt.add_clause(vec![TheoryLiteral::Lt(v, r)]);
        smt.solve()
    };

    // All 6 permutations
    let permutations: [[u8; 3]; 6] = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];

    for perm in &permutations {
        let result = solve_with_order(*perm);
        assert!(
            matches!(result, SmtResult::Unsat(_)),
            "3-theory permutation {:?} should be UNSAT (ROW-same gives v=r, v<r contradiction), \
             got {:?} - theory ordering dependence in 3-way combination",
            perm,
            std::mem::discriminant(&result)
        );
    }
}

/// Nelson-Oppen: multi-iteration DPLL(T) propagation convergence.
///
/// This requires multiple DPLL(T) iterations:
/// Iteration 1: Arith deduces x=y (squeezed bounds), returns Propagation.
/// Iteration 2: SAT model includes x=y -> EUF derives f(x)=f(y) by congruence.
///              With f(x)=a and f(y)=b from input, EUF deduces a=b.
///              But a!=b from input -> EUF conflict -> UNSAT.
///
/// This exercises the Arith->SAT->EUF pipeline across iterations, verifying
/// that propagated equalities survive the DPLL(T) iteration boundary.
#[test]
fn test_nelson_oppen_multi_iteration_convergence() {
    use crate::theories::arithmetic::ArithmeticTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArithmeticTheory::new()));

    let x = smt.const_term("x");
    let y = smt.const_term("y");
    let c = smt.const_term("c");
    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let f_x = smt.app_term("f", vec![x]);
    let f_y = smt.app_term("f", vec![y]);

    // Arith: x = c = y (squeezed bounds)
    smt.add_clause(vec![TheoryLiteral::Le(x, c)]);
    smt.add_clause(vec![TheoryLiteral::Le(c, x)]);
    smt.add_clause(vec![TheoryLiteral::Le(y, c)]);
    smt.add_clause(vec![TheoryLiteral::Le(c, y)]);

    // EUF: f(x) = a, f(y) = b
    let _ = smt.assert_eq(f_x, a);
    let _ = smt.assert_eq(f_y, b);

    // EUF: a != b - contradicts f(x)=f(y) (from x=y via congruence)
    // because f(x)=a and f(y)=b and f(x)=f(y) -> a=b by transitivity.
    let _ = smt.assert_neq(a, b);

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: Arith propagated x=y -> EUF derived f(x)=f(y) ->
            // a=b by transitivity -> conflict with a!=b.
        }
        SmtResult::Sat(_) => {
            panic!(
                "Expected UNSAT: x=c=y (bounds) -> f(x)=f(y) (congruence) -> a=b \
                 (transitivity with f(x)=a, f(y)=b) contradicts a!=b. \
                 Multi-iteration propagation may be incomplete."
            );
        }
        SmtResult::Unknown => {
            panic!(
                "Expected UNSAT, got Unknown - multi-iteration propagation may have hit \
                 iteration limit before convergence."
            );
        }
    }
}

/// Nelson-Oppen: theory check after SAT should not have stale conflict state.
///
/// If EUF's internal conflict flags are not properly cleared on backtrack,
/// a subsequent SAT-consistent check might incorrectly return Conflict.
/// This test creates a scenario where EUF first detects a conflict, then
/// the solver backtracks and tries a consistent assignment.
#[test]
fn test_nelson_oppen_no_stale_conflict_after_backtrack() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let d = smt.const_term("d");

    // (a=b OR c=d) - disjunction
    smt.add_clause(vec![TheoryLiteral::Eq(a, b), TheoryLiteral::Eq(c, d)]);
    // a != b - forces c=d in the final model
    let _ = smt.assert_neq(a, b);
    // c != d would make it UNSAT, but we DON'T add that - should be SAT with c=d.

    match smt.solve() {
        SmtResult::Sat(model) => {
            // Correct: c=d must hold (a=b is excluded by a!=b).
            // If stale conflict state leaked, we'd get Unsat here.
            assert!(
                model.equalities.contains(&(c, d)) || model.equalities.contains(&(d, c)),
                "Model should contain c=d (the only satisfying assignment)"
            );
        }
        SmtResult::Unsat(_) => {
            panic!(
                "Expected SAT (c=d satisfies all constraints), got UNSAT - \
                 stale EUF conflict state may not be cleared on backtrack"
            );
        }
        SmtResult::Unknown => {
            panic!("Expected SAT, got Unknown - EUF backtrack may be broken");
        }
    }
}
