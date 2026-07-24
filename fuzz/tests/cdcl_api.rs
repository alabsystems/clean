// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_auto::{CdclSolver, Lit, SolveResult, Var};

#[test]
fn test_cdcl_api_is_exposed_to_fuzz_crate() {
    let mut solver = CdclSolver::new(1);
    let var = Var::new(0);
    solver.add_clause(vec![Lit::pos(var)]);

    match solver.solve() {
        SolveResult::Sat(model) => assert_eq!(model, vec![true]),
        other => panic!("expected SAT result for unit clause, got {other:?}"),
    }
}
