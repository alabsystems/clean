// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CDCL SAT Solver Fuzz Target
//!
//! Fuzzes the CDCL solver with random CNF formulas. Uses `arbitrary` to
//! generate structurally valid inputs (bounded variables, bounded clauses).
//! Verifies SAT models satisfy all clauses (catches soundness bugs).

#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use clean_auto::{CdclSolver, Lit, SolveResult, Var};
use libfuzzer_sys::fuzz_target;

/// A fuzzable CNF formula with bounded size to prevent OOM
#[derive(Debug, Clone)]
struct FuzzCnf {
    num_vars: u32,
    clauses: Vec<Vec<(u32, bool)>>,
}

impl<'a> Arbitrary<'a> for FuzzCnf {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let num_vars: u32 = u.int_in_range(1..=64)?;
        let num_clauses: usize = u.int_in_range(0..=128)?;

        let mut clauses = Vec::with_capacity(num_clauses);
        for _ in 0..num_clauses {
            let clause_len: usize = u.int_in_range(1..=8)?;
            let mut clause = Vec::with_capacity(clause_len);
            for _ in 0..clause_len {
                let var: u32 = u.int_in_range(0..=(num_vars - 1))?;
                let positive: bool = u.arbitrary()?;
                clause.push((var, positive));
            }
            // Deduplicate by variable index
            clause.sort_by_key(|&(v, _)| v);
            clause.dedup_by_key(|x| x.0);
            if !clause.is_empty() {
                clauses.push(clause);
            }
        }

        Ok(FuzzCnf { num_vars, clauses })
    }
}

fuzz_target!(|cnf: FuzzCnf| {
    let mut solver = CdclSolver::new(cnf.num_vars as usize);

    // Build clause database
    for clause in &cnf.clauses {
        let lits: Vec<Lit> = clause
            .iter()
            .map(|&(var_idx, positive)| {
                let var = Var::new(var_idx);
                if positive {
                    Lit::pos(var)
                } else {
                    Lit::neg(var)
                }
            })
            .collect();
        solver.add_clause(lits);
    }

    let result = solver.solve();

    // If SAT, verify model satisfies every clause (catches soundness bugs)
    if let SolveResult::Sat(model) = result {
        for clause in &cnf.clauses {
            let satisfied = clause.iter().any(|&(var_idx, positive)| {
                let idx = var_idx as usize;
                idx < model.len() && model[idx] == positive
            });
            assert!(
                satisfied,
                "SOUNDNESS BUG: model does not satisfy clause {:?}",
                clause
            );
        }
    }
});
