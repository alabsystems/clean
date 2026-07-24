// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property-based and regression tests for CDCL solver soundness.
//!
//! Split from `tests.rs` to stay under file-size limits. Contains proptest
//! strategies for random CNF generation, soundness properties, and
//! targeted regression tests for specific algorithm invariants.

use super::*;
use proptest::prelude::*;

/// Strategy for generating a literal with bounded variable index
fn arb_lit(max_vars: u32) -> impl Strategy<Value = Lit> {
    (0..max_vars, any::<bool>()).prop_map(|(v, sign)| Lit::new(Var::new(v), sign))
}

/// Strategy for generating a clause with bounded size
fn arb_clause(max_vars: u32, max_lits: usize) -> impl Strategy<Value = Vec<Lit>> {
    (1..=max_lits).prop_flat_map(move |len| prop::collection::vec(arb_lit(max_vars), len))
}

/// Strategy for generating a CNF formula
fn arb_cnf(
    max_vars: u32,
    max_clauses: usize,
    max_lits_per_clause: usize,
) -> impl Strategy<Value = Vec<Vec<Lit>>> {
    (1..=max_clauses).prop_flat_map(move |num_clauses| {
        prop::collection::vec(arb_clause(max_vars, max_lits_per_clause), num_clauses)
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// Property: If solver returns Sat(model), the model must satisfy all clauses
    #[test]
    fn prop_cdcl_soundness_sat_model_satisfies(
        clauses in arb_cnf(8, 20, 5)
    ) {
        // Find max var in clauses
        let max_var = clauses
            .iter()
            .flat_map(|c| c.iter())
            .map(|l| l.var().raw())
            .max()
            .unwrap_or(0);

        let mut solver = CdclSolver::new(max_var as usize + 1);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        if let SolveResult::Sat(model) = solver.solve() {
            // Verify every clause has at least one satisfied literal
            for clause in &clauses {
                let satisfied = clause.iter().any(|lit| {
                    let var_idx = lit.var().index();
                    if var_idx < model.len() {
                        let assigned = model[var_idx];
                        (lit.is_pos() && assigned) || (lit.is_neg() && !assigned)
                    } else {
                        false
                    }
                });
                prop_assert!(
                    satisfied,
                    "Clause {:?} not satisfied by model {:?}",
                    clause,
                    model
                );
            }
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// Property: If solver returns Unsat, brute force confirms no model exists
    /// (Only tested on small instances for tractability)
    #[test]
    fn prop_cdcl_unsat_no_model_brute_force(
        clauses in arb_cnf(5, 10, 3)
    ) {
        let max_var = clauses
            .iter()
            .flat_map(|c| c.iter())
            .map(|l| l.var().raw())
            .max()
            .unwrap_or(0) as usize;

        let mut solver = CdclSolver::new(max_var + 1);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        if let SolveResult::Unsat(_) = solver.solve() {
            // Brute force check: no assignment should satisfy
            let num_vars = max_var + 1;
            for assignment in 0..(1u64 << num_vars) {
                let model: Vec<bool> =
                    (0..num_vars).map(|i| (assignment >> i) & 1 == 1).collect();

                let all_satisfied = clauses.iter().all(|clause| {
                    clause.iter().any(|lit| {
                        let var_idx = lit.var().index();
                        (lit.is_pos() && model[var_idx])
                            || (lit.is_neg() && !model[var_idx])
                    })
                });

                prop_assert!(
                    !all_satisfied,
                    "Solver returned Unsat but model {:?} satisfies all clauses",
                    model
                );
            }
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// Property: Solving twice on identical input gives consistent results
    #[test]
    fn prop_cdcl_deterministic(
        clauses in arb_cnf(6, 15, 4)
    ) {
        let max_var = clauses
            .iter()
            .flat_map(|c| c.iter())
            .map(|l| l.var().raw())
            .max()
            .unwrap_or(0);

        let mut solver1 = CdclSolver::new(max_var as usize + 1);
        let mut solver2 = CdclSolver::new(max_var as usize + 1);

        for clause in &clauses {
            solver1.add_clause(clause.clone());
            solver2.add_clause(clause.clone());
        }

        let result1 = solver1.solve();
        let result2 = solver2.solve();

        // Both should agree on satisfiability
        match (&result1, &result2) {
            (SolveResult::Sat(_), SolveResult::Sat(_)) => {}
            (SolveResult::Unsat(_), SolveResult::Unsat(_)) => {}
            (SolveResult::Unknown, _) | (_, SolveResult::Unknown) => {
                // Unknown is acceptable
            }
            _ => {
                prop_assert!(
                    false,
                    "Inconsistent results: {:?} vs {:?}",
                    result1,
                    result2
                );
            }
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Property: Adding a tautology clause doesn't change satisfiability
    #[test]
    fn prop_cdcl_tautology_preserves_sat(
        clauses in arb_cnf(5, 10, 3),
        taut_var in 0..5u32
    ) {
        let max_var = clauses
            .iter()
            .flat_map(|c| c.iter())
            .map(|l| l.var().raw())
            .max()
            .unwrap_or(0)
            .max(taut_var);

        let mut solver_base = CdclSolver::new(max_var as usize + 1);
        for clause in &clauses {
            solver_base.add_clause(clause.clone());
        }
        let result_base = solver_base.solve();

        let mut solver_taut = CdclSolver::new(max_var as usize + 1);
        for clause in &clauses {
            solver_taut.add_clause(clause.clone());
        }
        // Add tautology: (x OR !x)
        let v = Var::new(taut_var);
        solver_taut.add_clause(vec![Lit::pos(v), Lit::neg(v)]);
        let result_taut = solver_taut.solve();

        match (&result_base, &result_taut) {
            (SolveResult::Sat(_), SolveResult::Sat(_)) => {}
            (SolveResult::Unsat(_), SolveResult::Unsat(_)) => {}
            (SolveResult::Unknown, _) | (_, SolveResult::Unknown) => {}
            _ => {
                prop_assert!(
                    false,
                    "Tautology changed satisfiability: {:?} vs {:?}",
                    result_base,
                    result_taut
                );
            }
        }
    }
}

/// Performance guard: BCP conflict-path watch copy must stay O(W) in the
/// number of remaining watches.
///
/// In `analysis.rs` `propagate()`, on conflict, the solver copies the
/// remaining watch-list suffix with `extend_from_slice`. Under the
/// two-watched-literal invariant, each clause appears at most once in a
/// given watch list, so unconditional copy is both correct and linear.
///
/// A regression to per-entry dedup scanning (for example `Vec::contains`)
/// would restore O(W²) behavior when a conflict occurs at the front of a
/// large watch list.
///
/// This test constructs formulas where many binary clauses share a
/// watched literal, forcing the conflict path to copy large watch-list
/// suffixes. We measure solving time at two watch-list sizes.
///
/// Regression test for performance_proofs P1 iter 1230.
#[test]
fn test_bcp_conflict_path_watch_copy_scaling() {
    use std::time::Instant;

    // Construct a formula where literal x0 appears in many binary clauses:
    //   (!y_i) for i in 0..N         -- force all y_i = false at level 0
    //   (x0 v y_i) for i in 0..N     -- all watch !x0
    //   (!x0)                         -- force x0 = false, triggering BCP
    //
    // When x0 = false is propagated:
    //   Each (x0 v y_i) becomes unit with y_i, but y_i is already false.
    //   Conflict occurs at the first such clause. The conflict-path then
    //   copies all remaining watches unconditionally: O(W).
    let measure = |n: u32| -> u128 {
        let num_vars = (n + 1) as usize;
        let mut solver = CdclSolver::new(num_vars);
        let x0 = Var::new(0);

        // Unit clauses forcing y_i = false
        for i in 0..n {
            solver.add_clause(vec![Lit::neg(Var::new(i + 1))]);
        }

        // Binary clauses: (x0 v y_i) — all watch !x0
        for i in 0..n {
            solver.add_clause(vec![Lit::pos(x0), Lit::pos(Var::new(i + 1))]);
        }

        // Unit clause: !x0 — triggers BCP over all watches
        solver.add_clause(vec![Lit::neg(x0)]);

        let start = Instant::now();
        let result = solver.solve();
        let elapsed = start.elapsed().as_nanos();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "formula with {n} shared watches should be UNSAT"
        );
        elapsed
    };

    let t_small = measure(50); // 50 watches on !x0
    let t_large = measure(500); // 500 watches on !x0

    // 10x watches with O(W) copy gives ~10x.
    let ratio = t_large as f64 / t_small.max(1) as f64;
    eprintln!(
        "BCP conflict-path watch copy: 10x watches gave {ratio:.1}x time \
         (50w={t_small}ns, 500w={t_large}ns)"
    );
    // Linear (O(W)) gives ~10x for 10x watches. Allow up to 30x for
    // measurement noise. Quadratic (O(W²)) would give ~100x.
    assert!(
        ratio < 30.0,
        "BCP conflict-path scaling: 10x watches gave {ratio:.1}x time \
         (expected <30x for O(W); quadratic regression detected)"
    );
}

/// Assert that every multi-literal learned clause has correct polarity:
/// non-asserting literals (lits[1..]) must be FALSE, and at most one
/// literal may be TRUE (the asserting literal).
fn assert_learned_clause_polarity(solver: &CdclSolver) -> bool {
    let mut checked_any = false;
    for (ci, clause) in solver.clauses.iter().enumerate() {
        if !clause.learned || clause.lits.len() <= 1 {
            continue;
        }
        checked_any = true;
        for (li, &lit) in clause.lits[1..].iter().enumerate() {
            let val = solver.lit_value(lit);
            assert_eq!(
                val,
                types::LBool::False,
                "Learned clause {} (idx {}): non-asserting literal at position {} \
                 should be FALSE but was {:?}. \
                 Clause: {:?} (origins: {:?})",
                ci,
                li + 1,
                li + 1,
                val,
                clause.lits,
                clause.origins,
            );
        }

        let num_true = clause
            .lits
            .iter()
            .filter(|&&l| solver.lit_value(l) == types::LBool::True)
            .count();
        assert!(
            num_true <= 1,
            "Learned clause {} has {} TRUE literals — \
             suggests polarity inversion. Clause: {:?}",
            ci,
            num_true,
            clause.lits,
        );
    }
    checked_any
}

/// Verify that non-asserting literals in learned clauses have correct polarity.
///
/// The 1UIP conflict analysis must store non-asserting literals as they
/// appear in the reason/conflict clause (FALSE at their decision level).
/// A polarity inversion (storing `lit.not()` instead of `lit`) makes the
/// learned clause trivially satisfied after backtracking, preventing BCP
/// from reusing it in future search.
///
/// Uses all 8 clauses over 3 variables (complete clause set): trivially
/// UNSAT, and the 3-literal clause width prevents BCP from propagating
/// everything at a single decision level — forcing the solver to make
/// decisions at multiple levels and produce multi-literal learned clauses.
///
/// Regression test for algorithm_audit P1 iter 1264. Fixture replaced per
/// #2685 (the original 2-variable binary-clause formula produced no
/// multi-literal learned clauses, making the polarity check vacuous).
#[test]
fn test_learned_clause_polarity_correct() {
    // All 2^3 = 8 clauses on 3 variables. Every assignment falsifies
    // exactly one clause, so the formula is UNSAT. Because every clause
    // has width 3, BCP cannot propagate from a single decision — the
    // solver must decide at two levels before a conflict occurs, and
    // the 1UIP analysis produces a 2-literal learned clause containing
    // one literal from each level.
    let mut solver = CdclSolver::new(3);
    let a = Var::new(0);
    let b = Var::new(1);
    let c = Var::new(2);

    solver.add_clause(vec![Lit::pos(a), Lit::pos(b), Lit::pos(c)]);
    solver.add_clause(vec![Lit::pos(a), Lit::pos(b), Lit::neg(c)]);
    solver.add_clause(vec![Lit::pos(a), Lit::neg(b), Lit::pos(c)]);
    solver.add_clause(vec![Lit::pos(a), Lit::neg(b), Lit::neg(c)]);
    solver.add_clause(vec![Lit::neg(a), Lit::pos(b), Lit::pos(c)]);
    solver.add_clause(vec![Lit::neg(a), Lit::pos(b), Lit::neg(c)]);
    solver.add_clause(vec![Lit::neg(a), Lit::neg(b), Lit::pos(c)]);
    solver.add_clause(vec![Lit::neg(a), Lit::neg(b), Lit::neg(c)]);

    let result = solver.solve();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Complete 3-variable clause set must be UNSAT, got {:?}",
        result
    );

    assert!(
        assert_learned_clause_polarity(&solver),
        "Complete 3-variable clause set must produce at least one multi-literal \
         learned clause; if this fails, the polarity check never ran (vacuous test)"
    );

    let expected = vec![Lit::neg(a), Lit::neg(c)];
    let learned: Vec<_> = solver
        .clauses
        .iter()
        .filter(|clause| clause.learned && clause.lits.len() > 1)
        .map(|clause| clause.lits.clone())
        .collect();
    assert!(
        learned.iter().any(|clause| clause == &expected),
        "Complete 3-variable clause set should learn {:?}; learned clauses were {:?}",
        expected,
        learned
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// Property: Adding a contradictory unit clause makes formula UNSAT
    #[test]
    fn prop_cdcl_contradiction_makes_unsat(
        clauses in arb_cnf(5, 8, 3)
    ) {
        let max_var = clauses
            .iter()
            .flat_map(|c| c.iter())
            .map(|l| l.var().raw())
            .max()
            .unwrap_or(0);

        // Use a fresh variable for contradiction
        let fresh_var = max_var + 1;
        let v = Var::new(fresh_var);

        let mut solver = CdclSolver::new(fresh_var as usize + 2);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }
        // Add contradiction: x AND !x
        solver.add_clause(vec![Lit::pos(v)]);
        solver.add_clause(vec![Lit::neg(v)]);

        let result = solver.solve();
        prop_assert!(
            matches!(result, SolveResult::Unsat(_)),
            "Adding contradiction should make formula UNSAT, got {:?}",
            result
        );
    }
}
