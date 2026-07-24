// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the CDCL SAT solver.

use super::*;

#[test]
fn test_var_lit_basic() {
    let v = Var::new(5);
    assert_eq!(v.index(), 5);

    let pos = Lit::pos(v);
    let neg = Lit::neg(v);

    assert!(pos.is_pos());
    assert!(!pos.is_neg());
    assert!(!neg.is_pos());
    assert!(neg.is_neg());

    assert_eq!(pos.var(), v);
    assert_eq!(neg.var(), v);

    assert_eq!(pos.not(), neg);
    assert_eq!(neg.not(), pos);
}

#[test]
fn test_empty_solver() {
    let mut solver = CdclSolver::new(0);
    assert_eq!(solver.solve(), SolveResult::Sat(vec![]));
}

#[test]
fn test_single_positive() {
    // x = true
    let mut solver = CdclSolver::new(1);
    let x = Var::new(0);
    solver.add_clause(vec![Lit::pos(x)]);
    match solver.solve() {
        SolveResult::Sat(model) => {
            assert!(model[0]); // x = true
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_single_negative() {
    // !x = true (x = false)
    let mut solver = CdclSolver::new(1);
    let x = Var::new(0);
    solver.add_clause(vec![Lit::neg(x)]);
    match solver.solve() {
        SolveResult::Sat(model) => {
            assert!(!model[0]); // x = false
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_contradiction() {
    // x AND !x = UNSAT
    let mut solver = CdclSolver::new(1);
    let x = Var::new(0);
    solver.add_clause(vec![Lit::pos(x)]);
    solver.add_clause(vec![Lit::neg(x)]);
    assert!(matches!(solver.solve(), SolveResult::Unsat(_)));
}

#[test]
fn test_unsat_core_extraction() {
    // Test that unsat core contains the conflicting clauses
    // Clauses: (x), (!x), (y OR z) - should only need first two for UNSAT
    let mut solver = CdclSolver::new(3);
    let x = Var::new(0);
    let y = Var::new(1);
    let z = Var::new(2);
    solver.add_clause(vec![Lit::pos(x)]); // Clause 0
    solver.add_clause(vec![Lit::neg(x)]); // Clause 1
    solver.add_clause(vec![Lit::pos(y), Lit::pos(z)]); // Clause 2 (irrelevant)

    match solver.solve() {
        SolveResult::Unsat(Some(core)) => {
            // Core should contain clauses 0 and 1 (the contradicting ones)
            assert!(
                core.clause_indices.contains(&0),
                "Core should contain clause 0"
            );
            assert!(
                core.clause_indices.contains(&1),
                "Core should contain clause 1"
            );
            // Clause 2 shouldn't be in the core (it's not needed for UNSAT)
            assert!(
                !core.clause_indices.contains(&2),
                "Core should not contain irrelevant clause 2"
            );
        }
        SolveResult::Unsat(None) => {
            panic!("Expected unsat core to be present");
        }
        _ => panic!("Expected UNSAT"),
    }
}

#[test]
fn test_unsat_core_pigeonhole() {
    // 2 pigeons, 1 hole - all clauses contribute to unsat
    let mut solver = CdclSolver::new(2);
    let p1 = Var::new(0);
    let p2 = Var::new(1);
    solver.add_clause(vec![Lit::pos(p1)]); // Clause 0: pigeon 1 in hole
    solver.add_clause(vec![Lit::pos(p2)]); // Clause 1: pigeon 2 in hole
    solver.add_clause(vec![Lit::neg(p1), Lit::neg(p2)]); // Clause 2: at most one per hole

    match solver.solve() {
        SolveResult::Unsat(Some(core)) => {
            // All three clauses are needed for the unsatisfiability:
            // - Clause 0 forces p1=true
            // - Clause 1 forces p2=true
            // - Clause 2 requires p1=false OR p2=false, conflict
            // The conflict analysis should find all contributing clauses
            assert!(
                core.clause_indices.contains(&0),
                "Pigeonhole core should contain clause 0 (p1), got {:?}",
                core.clause_indices
            );
            assert!(
                core.clause_indices.contains(&1),
                "Pigeonhole core should contain clause 1 (p2), got {:?}",
                core.clause_indices
            );
            assert!(
                core.clause_indices.contains(&2),
                "Pigeonhole core should contain clause 2 (at-most-one), got {:?}",
                core.clause_indices
            );
        }
        SolveResult::Unsat(None) => {
            panic!("Expected unsat core to be present");
        }
        _ => panic!("Expected UNSAT"),
    }
}

#[test]
fn test_unsat_core_nested_learning() {
    // 3x2 pigeonhole problem: 3 pigeons, 2 holes
    // This requires multiple conflicts and learned clauses before reaching UNSAT.
    // The shared fixture in the parent module encodes:
    // - 3 at-least-one clauses, one per pigeon
    // - 6 at-most-one clauses, all same-hole pigeon pairs
    let mut solver = CdclSolver::new(6);
    add_pigeonhole_3x2_formula(&mut solver);

    // Total clauses: 3 (at-least-one) + 6 (at-most-one) = 9 original clauses

    match solver.solve() {
        SolveResult::Unsat(Some(core)) => {
            // The unsat core must contain the essential original clauses.
            // At minimum, we need:
            // - The at-least-one clauses for all 3 pigeons (otherwise one pigeon has no constraint)
            // - Enough at-most-one clauses to derive the conflict
            //
            // A minimal core for 3x2 pigeonhole typically includes all 9 clauses,
            // but we verify the core is non-empty and properly traces through learned clauses.
            assert!(
                !core.clause_indices.is_empty(),
                "Unsat core should not be empty"
            );

            // Verify that learned clause origins are properly traced:
            // The core should contain at least some of the at-least-one clauses (0, 1, 2)
            // and some of the at-most-one clauses (3-8).
            let has_at_least_one = core.clause_indices.iter().any(|&idx| idx < 3);
            let has_at_most_one = core.clause_indices.iter().any(|&idx| idx >= 3);

            assert!(
                has_at_least_one,
                "Core should contain at-least-one clauses, got {:?}",
                core.clause_indices
            );
            assert!(
                has_at_most_one,
                "Core should contain at-most-one clauses, got {:?}",
                core.clause_indices
            );

            // Verify all indices are valid original clauses
            for &idx in &core.clause_indices {
                assert!(
                    idx < 9,
                    "Core index {} should be < 9 (number of original clauses)",
                    idx
                );
            }
        }
        SolveResult::Unsat(None) => {
            panic!("Expected unsat core to be present for nested learning test");
        }
        _ => panic!("Expected UNSAT for 3x2 pigeonhole"),
    }
}

#[test]
fn test_simple_sat() {
    // (x OR y) AND (!x OR y) = y
    let mut solver = CdclSolver::new(2);
    let x = Var::new(0);
    let y = Var::new(1);
    solver.add_clause(vec![Lit::pos(x), Lit::pos(y)]);
    solver.add_clause(vec![Lit::neg(x), Lit::pos(y)]);
    match solver.solve() {
        SolveResult::Sat(model) => {
            // Must have y = true
            assert!(model[1]);
            // x can be either value
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_unit_propagation() {
    // (x) AND (x OR y) AND (!x OR z)
    // Unit: x = true -> z = true (from !x OR z)
    let mut solver = CdclSolver::new(3);
    let x = Var::new(0);
    let y = Var::new(1);
    let z = Var::new(2);
    solver.add_clause(vec![Lit::pos(x)]);
    solver.add_clause(vec![Lit::pos(x), Lit::pos(y)]);
    solver.add_clause(vec![Lit::neg(x), Lit::pos(z)]);
    match solver.solve() {
        SolveResult::Sat(model) => {
            assert!(model[0]); // x = true
            assert!(model[2]); // z = true (propagated)
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_pigeonhole_2_1() {
    // 2 pigeons, 1 hole - each pigeon must be in the hole
    // p1 AND p2 AND (!p1 OR !p2) = UNSAT
    let mut solver = CdclSolver::new(2);
    let p1 = Var::new(0);
    let p2 = Var::new(1);
    solver.add_clause(vec![Lit::pos(p1)]); // pigeon 1 in hole
    solver.add_clause(vec![Lit::pos(p2)]); // pigeon 2 in hole
    solver.add_clause(vec![Lit::neg(p1), Lit::neg(p2)]); // at most one per hole
    assert!(matches!(solver.solve(), SolveResult::Unsat(_)));
}

#[test]
fn test_three_coloring_triangle() {
    // Color a triangle with 3 colors - should be satisfiable
    // Variables: v0_c0, v0_c1, v0_c2, v1_c0, v1_c1, v1_c2, v2_c0, v2_c1, v2_c2
    let mut solver = CdclSolver::new(9);

    // Helper to get variable for vertex v, color c
    let var = |v: u32, c: u32| Var::new(v * 3 + c);

    // Each vertex has at least one color
    for v in 0..3 {
        solver.add_clause(vec![
            Lit::pos(var(v, 0)),
            Lit::pos(var(v, 1)),
            Lit::pos(var(v, 2)),
        ]);
    }

    // Each vertex has at most one color
    for v in 0..3 {
        for c1 in 0..3 {
            for c2 in (c1 + 1)..3 {
                solver.add_clause(vec![Lit::neg(var(v, c1)), Lit::neg(var(v, c2))]);
            }
        }
    }

    // Adjacent vertices have different colors (triangle: 0-1, 1-2, 0-2)
    let edges = [(0, 1), (1, 2), (0, 2)];
    for (v1, v2) in edges {
        for c in 0..3 {
            solver.add_clause(vec![Lit::neg(var(v1, c)), Lit::neg(var(v2, c))]);
        }
    }

    match solver.solve() {
        SolveResult::Sat(model) => {
            // Verify each vertex has exactly one color
            for v in 0..3 {
                let colors: Vec<bool> = (0..3).map(|c| model[(v * 3 + c) as usize]).collect();
                assert_eq!(colors.iter().filter(|&&x| x).count(), 1);
            }
            // Verify adjacent vertices have different colors
            for (v1, v2) in edges {
                let c1 = (0..3).find(|&c| model[(v1 * 3 + c) as usize]).unwrap();
                let c2 = (0..3).find(|&c| model[(v2 * 3 + c) as usize]).unwrap();
                assert_ne!(c1, c2);
            }
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_two_coloring_triangle() {
    // Color a triangle with 2 colors - should be UNSAT (triangle is not bipartite)
    let mut solver = CdclSolver::new(6);

    let var = |v: u32, c: u32| Var::new(v * 2 + c);

    // Each vertex has at least one color
    for v in 0..3 {
        solver.add_clause(vec![Lit::pos(var(v, 0)), Lit::pos(var(v, 1))]);
    }

    // Each vertex has at most one color
    for v in 0..3 {
        solver.add_clause(vec![Lit::neg(var(v, 0)), Lit::neg(var(v, 1))]);
    }

    // Adjacent vertices have different colors
    let edges = [(0, 1), (1, 2), (0, 2)];
    for (v1, v2) in edges {
        for c in 0..2 {
            solver.add_clause(vec![Lit::neg(var(v1, c)), Lit::neg(var(v2, c))]);
        }
    }

    assert!(matches!(solver.solve(), SolveResult::Unsat(_)));
}

#[test]
fn test_tautology_ignored() {
    // (x OR !x) is a tautology - should be satisfied trivially
    let mut solver = CdclSolver::new(1);
    let x = Var::new(0);
    solver.add_clause(vec![Lit::pos(x), Lit::neg(x)]);
    match solver.solve() {
        SolveResult::Sat(_) => {}
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_duplicate_literals() {
    // (x OR x) should be simplified to (x)
    let mut solver = CdclSolver::new(1);
    let x = Var::new(0);
    solver.add_clause(vec![Lit::pos(x), Lit::pos(x)]);
    match solver.solve() {
        SolveResult::Sat(model) => {
            assert!(model[0]);
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_conflict_limit() {
    // Create a hard problem and limit conflicts
    let mut solver = CdclSolver::new(5);
    // Create some clauses that will cause conflicts
    for i in 0..5 {
        let v = Var::new(i);
        solver.add_clause(vec![Lit::pos(v)]);
        solver.add_clause(vec![Lit::neg(v)]);
    }
    solver.set_conflict_limit(1);
    // Should hit conflict limit
    let result = solver.solve();
    assert!(matches!(
        result,
        SolveResult::Unsat(_) | SolveResult::Unknown
    ));
}

#[test]
fn test_proptest_regression_1() {
    // Reproduces a proptest failure case
    // Clauses from the failing test (Lit(n) = var n/2, sign n%2)
    // Lit(0) = var0+, Lit(1) = var0-, Lit(2) = var1+, Lit(3) = var1-, etc.
    //
    // CNF interpretation:
    // Clause 0: [Lit(6), Lit(1)] = [var3+, var0-] = (x3 v !x0)
    // Clause 1: [Lit(4), Lit(7)] = [var2+, var3-] = (x2 v !x3)
    // Clause 2-4: [Lit(3)] = [var1-] = (!x1)
    // Clause 5: [Lit(5), Lit(1)] = [var2-, var0-] = (!x2 v !x0)
    // Clause 6: [Lit(8), Lit(6)] = [var4+, var3+] = (x4 v x3)
    // Clause 7: [Lit(4), Lit(0)] (after dedup) = [var2+, var0+] = (x2 v x0)
    //
    // Satisfying model: x0=F, x1=F, x2=T, x3=T, x4=F
    // Check:
    // - (x3 v !x0) = (T v T) = T
    // - (x2 v !x3) = (T v F) = T
    // - (!x1) = T
    // - (!x2 v !x0) = (F v T) = T
    // - (x4 v x3) = (F v T) = T
    // - (x2 v x0) = (T v F) = T
    let clauses: Vec<Vec<Lit>> = vec![
        vec![Lit(6), Lit(1)],         // var3+, var0-
        vec![Lit(4), Lit(7)],         // var2+, var3-
        vec![Lit(3)],                 // var1- (unit)
        vec![Lit(3)],                 // var1- (unit, duplicate)
        vec![Lit(3)],                 // var1- (unit, duplicate)
        vec![Lit(5), Lit(1)],         // var2-, var0-
        vec![Lit(8), Lit(6)],         // var4+, var3+
        vec![Lit(4), Lit(0), Lit(0)], // var2+, var0+, var0+
    ];

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

    let result = solver.solve();

    // Verify the result
    match result {
        SolveResult::Sat(model) => {
            // Verify model satisfies all clauses
            for (i, clause) in clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|lit| {
                    let var_idx = lit.var().index();
                    (lit.is_pos() && model[var_idx]) || (lit.is_neg() && !model[var_idx])
                });
                assert!(
                    satisfied,
                    "Clause {} {:?} not satisfied by model {:?}",
                    i, clause, model
                );
            }
        }
        SolveResult::Unsat(_) => {
            // Brute force check
            let num_vars = max_var as usize + 1;
            for assignment in 0..(1u64 << num_vars) {
                let model: Vec<bool> = (0..num_vars).map(|i| (assignment >> i) & 1 == 1).collect();

                let all_satisfied = clauses.iter().all(|clause| {
                    clause.iter().any(|lit| {
                        let var_idx = lit.var().index();
                        (lit.is_pos() && model[var_idx]) || (lit.is_neg() && !model[var_idx])
                    })
                });

                assert!(
                    !all_satisfied,
                    "Solver returned Unsat but model {:?} satisfies all clauses",
                    model
                );
            }
        }
        SolveResult::Unknown => {
            // Acceptable
        }
    }
}

#[test]
fn test_new_var_dynamic() {
    let mut solver = CdclSolver::new(0);
    let v1 = solver.new_var();
    let v2 = solver.new_var();
    assert_eq!(v1, Var::new(0));
    assert_eq!(v2, Var::new(1));
    assert_eq!(solver.num_vars(), 2);

    solver.add_clause(vec![Lit::pos(v1), Lit::pos(v2)]);
    solver.add_clause(vec![Lit::neg(v1)]);
    match solver.solve() {
        SolveResult::Sat(model) => {
            assert!(!model[0]); // v1 = false
            assert!(model[1]); // v2 = true
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_stats() {
    let mut solver = CdclSolver::new(2);
    let x = Var::new(0);
    let y = Var::new(1);
    solver.add_clause(vec![Lit::pos(x)]);
    solver.add_clause(vec![Lit::neg(x), Lit::pos(y)]);
    solver.solve();

    let stats = solver.stats();
    assert!(stats.propagations > 0);
}

#[test]
fn test_chain_implication() {
    // x1 -> x2 -> x3 -> x4 -> x5
    // (x1) AND (!x1 OR x2) AND (!x2 OR x3) AND (!x3 OR x4) AND (!x4 OR x5)
    let mut solver = CdclSolver::new(5);
    let vars: Vec<Var> = (0..5).map(Var::new).collect();

    solver.add_clause(vec![Lit::pos(vars[0])]);
    for i in 0..4 {
        solver.add_clause(vec![Lit::neg(vars[i]), Lit::pos(vars[i + 1])]);
    }

    match solver.solve() {
        SolveResult::Sat(model) => {
            // All should be true due to chain
            for (i, &val) in model.iter().enumerate() {
                assert!(val, "Variable {i} should be true");
            }
        }
        _ => panic!("Expected SAT"),
    }
}

/// Test that unit theory clauses don't pollute the unsat core with non-original indices.
///
/// Regression test for #2327 follow-up: add_theory_clause stores its clause
/// index in unit_clause_origins, but these indices point beyond num_original_clauses
/// into learned territory. collect_unsat_core_level0 adds them raw via
/// unit_clause_origins without checking whether they are original — unlike the
/// multi-literal path that goes through add_clause_origins and checks `learned`.
#[test]
fn test_unsat_core_theory_clause_indices_are_valid() {
    // Setup: 2 original clauses force x=true.
    // Then add a unit theory clause asserting !x (simulating a theory propagation).
    // The resulting UNSAT core should only contain original clause indices (0..num_original).
    let mut solver = CdclSolver::new(2);
    let x = Var::new(0);
    let y = Var::new(1);

    // Original clause 0: (x)
    solver.add_clause(vec![Lit::pos(x)]);
    // Original clause 1: (y) — irrelevant filler
    solver.add_clause(vec![Lit::pos(y)]);

    let num_original = solver.clauses.len();

    // Simulate theory propagation: add unit clause (!x) as learned theory clause.
    // This should conflict with clause 0 (x is already true at level 0).
    let result = solver.add_theory_clause(vec![Lit::neg(x)]);
    assert!(
        result.is_none(),
        "Unit theory clause contradicting x should return None (UNSAT)"
    );

    // The solver should be UNSAT now. Check the core indices.
    if let Some(core) = solver.take_unsat_core() {
        for &idx in &core.clause_indices {
            // BUG EXPOSURE: idx may be >= num_original (pointing to the learned theory clause).
            // This assertion documents the expected behavior: core indices should be
            // original clause indices only.
            if idx >= num_original as u32 {
                // This is the bug: unit theory clause index leaked into unsat core.
                // The core should trace through the theory clause to find
                // original clause 0 (which forced x=true), not include the
                // theory clause's own index.
                panic!(
                    "Unsat core contains non-original clause index {idx} \
                     (num_original={num_original}). Unit theory clauses should not \
                     leak into the unsat core. Core: {:?}",
                    core.clause_indices
                );
            }
        }
    }
}
