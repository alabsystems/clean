// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boolean Constraint Propagation (BCP)
//!
//! Implements unit propagation to fixpoint for the abstract CDCL state.
//! This is the core deduction engine: when a clause has all but one literal
//! falsified, the remaining literal must be true.

use super::{var_of, CdclError, CdclState};

/// Result of a single BCP step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BcpStepResult {
    /// A literal was propagated from the given clause index.
    Propagated { literal: i32, clause_idx: usize },
    /// A clause is entirely falsified -- conflict.
    Conflict { clause_idx: usize },
    /// No further propagation is possible; fixpoint reached.
    Fixpoint,
}

/// Perform one step of BCP: scan clauses for a unit or conflict.
pub fn bcp_step(state: &CdclState) -> BcpStepResult {
    for (ci, clause) in state.clauses.iter().enumerate() {
        let mut unassigned_lit = None;
        let mut unassigned_count = 0;
        let mut satisfied = false;
        for &lit in clause {
            match state.eval_literal(lit) {
                Some(true) => {
                    satisfied = true;
                    break;
                }
                Some(false) => {}
                None => {
                    unassigned_count += 1;
                    unassigned_lit = Some(lit);
                }
            }
        }
        if satisfied {
            continue;
        }
        if unassigned_count == 0 {
            return BcpStepResult::Conflict { clause_idx: ci };
        }
        if unassigned_count == 1 {
            if let Some(lit) = unassigned_lit {
                return BcpStepResult::Propagated {
                    literal: lit,
                    clause_idx: ci,
                };
            }
        }
    }
    BcpStepResult::Fixpoint
}

/// Run BCP to fixpoint, returning all propagated literals or a conflict.
pub fn bcp_loop(state: &mut CdclState) -> Result<Vec<i32>, CdclError> {
    let mut propagated = Vec::new();
    loop {
        match bcp_step(state) {
            BcpStepResult::Propagated {
                literal,
                clause_idx,
            } => {
                state.assign(literal, Some(clause_idx))?;
                propagated.push(literal);
            }
            BcpStepResult::Conflict { clause_idx } => {
                return Err(CdclError::Conflict(clause_idx));
            }
            BcpStepResult::Fixpoint => {
                return Ok(propagated);
            }
        }
    }
}

/// S05: Check propagation completeness -- no unit clause remains un-propagated.
pub fn check_propagation_complete(state: &CdclState) -> Result<(), CdclError> {
    for (ci, clause) in state.clauses.iter().enumerate() {
        let mut unassigned_count = 0;
        let mut satisfied = false;
        for &lit in clause {
            match state.eval_literal(lit) {
                Some(true) => {
                    satisfied = true;
                    break;
                }
                Some(false) => {}
                None => unassigned_count += 1,
            }
        }
        if !satisfied && unassigned_count == 1 {
            return Err(CdclError::WatchInvariantViolation(ci));
        }
    }
    Ok(())
}
