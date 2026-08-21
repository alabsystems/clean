// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The cost half of GAP 2, as a verdict rather than a printout.**
//!
//! Until 2026-08-20 `cost_is_uniform()` was called in exactly one place in the
//! whole repository — inside an `eprintln!`. The cost comparison the module
//! docs advertised as the thing that sharpens "both said the same value" had no
//! failure mode at all: the committed record would have published
//! `cost_uniform_on_every_chain = true` identically had every offset differed.
//! That is the vacuity pattern this programme keeps meeting, so cost is now a
//! [`CostVerdict`] that [`super::ChainReport::is_green`] consults.
//!
//! # What a cost gate catches, and what it cannot
//!
//! * **A per-input divergence** — a mis-encoded body that reaches the right
//!   answer by a different route on *some* input — is caught by uniformity.
//! * **A constant error is NOT caught by uniformity.** A wrong harness overhead
//!   shifts every row equally and leaves the offsets perfectly uniform. Only
//!   comparing the measured offset against a *declared* one catches that, which
//!   is why [`super::ChainReport::expected_cost_offset`] exists and why
//!   `Uniform(k)` alone is not the green condition.
//! * **Neither check alone suffices.** The declared offset would be a tuning
//!   knob if the subtracted overhead were also free; it is not — the overhead is
//!   independently *counted* from the instructions the harness emits
//!   (`crystal_a3_harness_step_overhead_is_derived_not_tuned`). One check fixes
//!   the constant, the other fixes the consequence of getting it wrong.
//! * **An absent measurement is never a passing one.** The old predicate was
//!   `cost_offsets.len() == 1`, which is *true* of a chain where eleven of
//!   twelve rows produced no cost datum at all. [`CostVerdict::Unpriced`]
//!   refuses that, and [`CostVerdict::Loose`] refuses a threshold that was
//!   accepted without ever being shown necessary — an upper bound compared
//!   against an exact step count is not a correspondence.

use std::collections::BTreeMap;

/// The verdict for a chain's COST correspondence.
///
/// Every variant but [`CostVerdict::Uniform`] is a failure, and
/// [`super::ChainReport::is_green`] treats it as one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CostVerdict {
    /// Every row priced, every threshold pinned tight from below, one offset.
    Uniform(i64),
    /// Rows priced but disagree on the offset: the step structures diverge.
    Divergent,
    /// Some row produced no cost datum at all.
    Unpriced {
        /// Rows in the chain.
        rows: usize,
        /// Rows that produced an offset.
        priced: usize,
    },
    /// Some row's fuel threshold was accepted but never shown necessary.
    Loose {
        /// How many rows were loose.
        loose: usize,
    },
}

impl CostVerdict {
    /// Fold a chain's per-row cost data into one verdict, fail-closed.
    ///
    /// The order of the checks is the order of severity of the *absence* of
    /// information: no datum at all, then a datum that is only an upper bound,
    /// then genuinely conflicting data.
    #[must_use]
    pub(crate) fn of(rows: usize, loose: usize, offsets: &BTreeMap<i64, usize>) -> Self {
        let priced: usize = offsets.values().sum();
        if rows == 0 || priced != rows {
            return CostVerdict::Unpriced { rows, priced };
        }
        if loose != 0 {
            return CostVerdict::Loose { loose };
        }
        match offsets.iter().next() {
            Some((off, n)) if *n == priced && offsets.len() == 1 => CostVerdict::Uniform(*off),
            _ => CostVerdict::Divergent,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn offsets(pairs: &[(i64, usize)]) -> BTreeMap<i64, usize> {
        pairs.iter().copied().collect()
    }

    #[test]
    fn test_a_fully_priced_tight_single_offset_chain_is_uniform() {
        assert_eq!(
            CostVerdict::of(6, 0, &offsets(&[(0, 6)])),
            CostVerdict::Uniform(0)
        );
    }

    #[test]
    fn test_an_empty_chain_has_no_cost() {
        assert_eq!(
            CostVerdict::of(0, 0, &offsets(&[])),
            CostVerdict::Unpriced { rows: 0, priced: 0 }
        );
    }

    #[test]
    fn test_one_priced_row_out_of_twelve_is_not_uniform() {
        // The exact shape the retired `cost_offsets.len() == 1` predicate
        // called uniform.
        assert_eq!(
            CostVerdict::of(12, 0, &offsets(&[(0, 1)])),
            CostVerdict::Unpriced {
                rows: 12,
                priced: 1
            }
        );
    }

    #[test]
    fn test_a_loose_threshold_beats_a_single_offset() {
        assert_eq!(
            CostVerdict::of(6, 2, &offsets(&[(0, 6)])),
            CostVerdict::Loose { loose: 2 }
        );
    }

    #[test]
    fn test_two_offsets_are_divergent() {
        assert_eq!(
            CostVerdict::of(6, 0, &offsets(&[(0, 5), (1, 1)])),
            CostVerdict::Divergent
        );
    }
}
