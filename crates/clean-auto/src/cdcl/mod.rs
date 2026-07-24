// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CDCL SAT solver (ported from MiniSat/Glucose design)
//!
//! This module implements a Conflict-Driven Clause Learning (CDCL) SAT solver,
//! the core algorithm used in modern SAT solvers like MiniSat, Glucose, and Z3.
//!
//! # Algorithm Overview
//!
//! 1. **Unit Propagation (BCP)**: If a clause has all but one literal false,
//!    the remaining literal must be true.
//!
//! 2. **Decision**: Pick an unassigned variable and assign it a value.
//!
//! 3. **Conflict Analysis**: When a conflict occurs, analyze the implication
//!    graph to learn a new clause that prevents the same conflict.
//!
//! 4. **Backtracking**: Jump back to an appropriate decision level.
//!
//! # Key Features
//!
//! - Two-watched literals for efficient unit propagation
//! - VSIDS decision heuristic with activity decay
//! - 1UIP conflict analysis with origin tracking for UNSAT cores
//! - LBD (Literal Block Distance) computation for learned clauses
//! - Learned clause deletion (reduce_db) with activity-based ranking
//! - Luby sequence restarts
//! - Phase saving for decision polarity

mod analysis;
mod clause_db;
mod solver;
mod trail;
mod types;
mod vsids;

#[cfg(feature = "fuzz")]
pub use solver::CdclSolver;
#[cfg(not(feature = "fuzz"))]
pub(crate) use solver::CdclSolver;
pub(crate) use trail::{CdclTrailEntry, CdclTrailKind};
pub(crate) use types::ClauseRef;
#[cfg(feature = "fuzz")]
pub use types::{Lit, SolveResult, Var};
#[cfg(not(feature = "fuzz"))]
pub(crate) use types::{Lit, SolveResult, Var};

#[cfg(test)]
fn add_pigeonhole_3x2_formula(solver: &mut CdclSolver) {
    let var = |pigeon: u32, hole: u32| Var::new(pigeon * 2 + hole);

    for pigeon in 0..3 {
        solver.add_clause(vec![Lit::pos(var(pigeon, 0)), Lit::pos(var(pigeon, 1))]);
    }

    for hole in 0..2 {
        for first_pigeon in 0..3 {
            for second_pigeon in (first_pigeon + 1)..3 {
                solver.add_clause(vec![
                    Lit::neg(var(first_pigeon, hole)),
                    Lit::neg(var(second_pigeon, hole)),
                ]);
            }
        }
    }
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_proptest;
