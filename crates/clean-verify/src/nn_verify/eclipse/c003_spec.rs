// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C003 ECLipsE convergence theorem specification.
//!
//! C003 proves ECLipsE iterative refinement converges via the Banach fixed-point
//! theorem. If the refinement operator is a contraction with Lipschitz constant
//! `L < 1`, iterates converge geometrically to a unique fixed point, with error
//! bound `L^n / (1 - L) * ||x_1 - x_0||`.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use crate::spec::ProofStatus;

/// Proof status for the C003 ECLipsE convergence theorem.
pub(crate) const C003_ECLIPSE_CONVERGENCE_STATUS: ProofStatus = ProofStatus::DerivedPending;

/// Proof-spec wrapper for C003.
///
/// C003 proves ECLipsE iterative refinement converges via the Banach fixed-point
/// theorem. If the refinement operator is a contraction with Lipschitz constant
/// `L < 1`, iterates converge geometrically to a unique fixed point, with error
/// bound `L^n / (1 - L) * ||x_1 - x_0||`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct C003ConvergenceSpec {
    status: ProofStatus,
}

impl C003ConvergenceSpec {
    /// Create the C003 proof spec with its current proof status.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            status: C003_ECLIPSE_CONVERGENCE_STATUS,
        }
    }

    /// Return the tracked proof status for C003.
    #[must_use]
    pub(crate) fn status(&self) -> ProofStatus {
        self.status
    }
}

impl Default for C003ConvergenceSpec {
    fn default() -> Self {
        Self::new()
    }
}
