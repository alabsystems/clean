// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The pinned reduction/conversion **budget** (design §3 principle 3, §5.1).
//!
//! Every reduction and conversion step is metered. Exhaustion is **not** a third
//! verdict: it surfaces as [`BudgetError::OutOfBudget`], and the soundness
//! callers (`def_eq` rejection sites, `check`) collapse it to *reject* — they
//! can never fail open (design §4.3 / §5.1). The budget is a deterministic,
//! genesis-pinnable scalar so a verdict is reproducible across machines.
//!
//! The counter only ever *decrements* (`step` consumes one unit and errors at
//! zero); it carries no fixed-width *arithmetic on values* beyond the
//! saturating/checked decrement of its own fuel, which is policy-clean (it is a
//! step *count*, never a term value).

/// Exhaustion of the pinned budget — the single error type threaded through
/// `whnf`/`def_eq`/`infer`. Distinct from a *negative* def-eq result: a caller
/// that gets `Err(OutOfBudget)` knows the kernel *gave up*, not that the terms
/// were unequal (design §5.1: no `bool` conflating "unequal" with "gave up").
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BudgetError {
    /// The pinned step budget was exhausted.
    #[error("out of budget (deterministic, genesis-pinned)")]
    OutOfBudget,
}

/// A deterministic step meter. Threaded by `&mut` through reduction and
/// conversion so the *total* work of one decision is bounded.
#[derive(Clone, Copy, Debug)]
pub struct Budget {
    fuel: u64,
}

impl Budget {
    /// A budget of `fuel` steps.
    #[must_use]
    pub fn new(fuel: u64) -> Self {
        Budget { fuel }
    }

    /// The default genesis-pinned budget for top-level decisions. Generous
    /// enough for the corpus shapes M1 exercises; the real genesis value is
    /// pinned in the manifest (design §10).
    #[must_use]
    pub fn default_budget() -> Self {
        Budget::new(1_000_000)
    }

    /// Remaining fuel (for diagnostics/tests).
    #[must_use]
    pub fn remaining(&self) -> u64 {
        self.fuel
    }

    /// Consume one step. Returns `Err(OutOfBudget)` once the meter hits zero, so
    /// no work proceeds past the pinned bound. `checked_sub` keeps this
    /// policy-clean (no silent wrap; fuel is a step count, not a term value).
    pub fn step(&mut self) -> Result<(), BudgetError> {
        match self.fuel.checked_sub(1) {
            Some(next) => {
                self.fuel = next;
                Ok(())
            }
            None => Err(BudgetError::OutOfBudget),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_budget_exhausts_to_error_not_a_third_state() {
        let mut b = Budget::new(2);
        assert!(b.step().is_ok());
        assert!(b.step().is_ok());
        assert_eq!(b.step(), Err(BudgetError::OutOfBudget));
        // Stays exhausted.
        assert_eq!(b.step(), Err(BudgetError::OutOfBudget));
    }

    #[test]
    fn test_zero_budget_errors_immediately() {
        let mut b = Budget::new(0);
        assert_eq!(b.step(), Err(BudgetError::OutOfBudget));
    }
}
