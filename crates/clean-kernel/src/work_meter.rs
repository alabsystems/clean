// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The kernel work meter: the unit every structural walk pays in.
//!
//! # Why this exists
//!
//! A heartbeat was charged once per `whnf_impl`, `is_def_eq_core` and
//! `infer_type` call, on the premise that what the kernel does between two
//! ticks is O(1). It is not. A cache probe whose 32-bit hashes agree compares
//! its keys structurally (`ExprEqWalk`), and that walk is as
//! long as the key whenever the two keys are distinct allocations. trust-ir's
//! gate 9 (trust-ir 67b91383) spent six hours inside such probes under a
//! 5,000,000-heartbeat budget: a division loop by repeated subtraction builds a
//! `Nat.sub` chain one link per iteration, every whnf-cache probe of the chain
//! walks it, and the work grows quadratically while the heartbeat count grows
//! linearly. A budget that does not bound work is not a budget.
//!
//! # What is charged
//!
//! One unit per node a structural walk ENTERS:
//! - expression equality (`Expr` / `ExprKind` `PartialEq`), so every cache
//!   probe that reaches a key comparison and every explicit `==` pays for the
//!   nodes it compares;
//! - the default dispatch of the fold engines (`ExprFolderOpt`, `ExprFolder`,
//!   `ExprVisitor`), which carry instantiate, abstract, lift and level
//!   substitution;
//! - the miss path of the memoized substitution folds (instantiate, abstract,
//!   lift, lower, free-variable and level-parameter substitution), one unit
//!   per distinct node they fold;
//! - the hand-written scans and rebuilds a checker runs over terms and
//!   certificates: the loose-bound-variable range scan, beta normalization,
//!   the certificate path's free-variable abstraction, rebinding and
//!   support walks;
//! - the equivalence manager's structural walk and the def-eq context walk;
//!
//! and one unit per probe of a type-checker cache (a lookup or an insert), so
//! that even millions of O(1) cache hits are paid for.
//!
//! # What is not charged, and why
//!
//! A walk is charged when its length is the size of a term or certificate,
//! which reduction can grow without bound between two heartbeats. Walks whose
//! length the declarations fix are not: an application spine is at most the
//! head's arity, and a universe level is as large as the universe structure
//! the declarations wrote. Native `Nat` literal arithmetic is one step per
//! operation and costs the size of its literals: products are capped at 256
//! limbs (`BigNat::checked_mul_big`) and `pow` at exponent 1,023, but an
//! addition may grow a literal by one bit a step, so literal size is a residual
//! this meter does not price. Walks outside a checker's operations
//! (declaration admission scans, display, serialization, drop) are not checker
//! work; they may charge the meter, but no checker is billed for them.
//!
//! # How a unit becomes a heartbeat
//!
//! The meter is a per-thread, monotone count of units. A
//! [`TypeChecker`](crate::tc::TypeChecker) reads it at the boundaries of its
//! own operations and bills itself for what was charged INSIDE them. Work
//! charged on the thread while the checker is between operations (an
//! elaborator's own comparisons, another checker's work) is never billed to it.
//!
//! A heartbeat buys one step and [`UNITS_PER_HEARTBEAT`] units of walking:
//! every tick grants that allowance, and only the walking past what the ticks
//! granted is billed, at one heartbeat per [`UNITS_PER_HEARTBEAT`] units,
//! drawn from both the checker's own budget and the ambient declaration
//! budget. The bank of unspent allowance is capped at 1,024 steps' worth. So a
//! check whose walks stay within its steps' allowance spends exactly the
//! heartbeats it spent before, and work that spends `B` heartbeats walked at
//! most `B` × [`UNITS_PER_HEARTBEAT`] units plus the capped bank, whatever the
//! steps do. The rate and its measurements are `docs/DECISIONS.md`
//! `DR-KERNEL-WORK-METER-20261014`.
//!
//! The conversion only moves budget counters: no reduction, comparison or
//! cache answer reads the meter, so no answer can depend on it, only whether a
//! budget refuses first. A spent budget surfaces as `HeartbeatExceeded` (or
//! `DeclarationBudgetExhausted`), never as an acceptance.

use std::cell::Cell;

/// Units of walking one heartbeat buys.
///
/// One unit is one node entered by a structural walk or one cache probe. A
/// heartbeat was, and still is, one `whnf_impl` / `is_def_eq_core` /
/// `infer_type` step; each step now also pays for this many units, and walking
/// past that allowance is billed at this rate. See `docs/DECISIONS.md`
/// `DR-KERNEL-WORK-METER-20261014` for the measurements behind the value.
pub const UNITS_PER_HEARTBEAT: u64 = 1_024;

thread_local! {
    /// Units charged on this thread since it started. Monotone modulo 2^64.
    static CHARGED: Cell<u64> = const { Cell::new(0) };
}

/// Units charged on this thread so far (monotone, wrapping at 2^64).
///
/// Only differences of two readings mean anything.
#[inline]
#[must_use]
pub(crate) fn charged() -> u64 {
    CHARGED.with(Cell::get)
}

#[inline]
fn add(units: u64) {
    CHARGED.with(|charged| charged.set(charged.get().wrapping_add(units)));
}

/// Which walk a charge pays for (diagnostic attribution only).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Walk {
    /// Fold engine node (instantiate, abstract, lift, level substitution, ...).
    Fold,
    /// Equivalence-manager or def-eq context walk node.
    Equiv,
    /// One type-checker cache probe (lookup or insert).
    Probe,
}

/// Charge `units` nodes of the walk `walk`.
#[inline]
pub(crate) fn charge(walk: Walk, units: u64) {
    #[cfg(any(test, feature = "inference-stats"))]
    stats::record(walk, units);
    #[cfg(not(any(test, feature = "inference-stats")))]
    let _ = walk;
    add(units);
}

/// Charge one structural equality walk that entered `visits` node pairs.
///
/// `collided` is true when the walk answered `false` although the roots' full
/// metadata words (32-bit hash, depth, flags, loose-bvar range) were equal: a
/// collision of that word, the only case a wider hash could have refused in
/// O(1).
#[inline]
pub(crate) fn charge_equality(visits: u64, collided: bool) {
    if visits == 0 {
        return;
    }
    #[cfg(any(test, feature = "test-fixtures"))]
    if mutant::equality_charge_dropped() {
        return;
    }
    #[cfg(any(test, feature = "inference-stats"))]
    stats::record_equality(visits, collided);
    #[cfg(not(any(test, feature = "inference-stats")))]
    let _ = collided;
    add(visits);
}

/// Mutation hooks for the tests that pin the meter (never compiled into a
/// production build: `test-fixtures` is enabled only through
/// `[dev-dependencies]`).
#[cfg(any(test, feature = "test-fixtures"))]
pub mod mutant {
    use std::cell::Cell;

    thread_local! {
        static DROP_EQUALITY_CHARGE: Cell<bool> = const { Cell::new(false) };
    }

    pub(super) fn equality_charge_dropped() -> bool {
        DROP_EQUALITY_CHARGE.with(Cell::get)
    }

    /// Run `f` with the MUTANT that drops the structural-equality charge: the
    /// kernel as it was before the meter, where an equality walk spent no
    /// budget. A guard that still refuses under this mutant is not testing the
    /// charge. Restores the previous state even if `f` panics.
    pub fn with_equality_charge_dropped<R>(f: impl FnOnce() -> R) -> R {
        struct Restore(bool);
        impl Drop for Restore {
            fn drop(&mut self) {
                DROP_EQUALITY_CHARGE.with(|flag| flag.set(self.0));
            }
        }
        let _restore = Restore(DROP_EQUALITY_CHARGE.with(|flag| flag.replace(true)));
        f()
    }
}

/// Diagnostic per-walk totals. Reading or resetting them never resets the work meter.
/// Available in tests or with `inference-stats`; absent from ordinary builds.
#[cfg(any(test, feature = "inference-stats"))]
pub mod stats {
    use super::Walk;
    use std::cell::Cell;

    /// Totals charged on this thread since the last [`take`].
    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
    pub struct WorkStats {
        /// Structural equality walks that entered at least one node pair.
        pub equality_walks: u64,
        /// Node pairs those walks entered.
        pub equality_visits: u64,
        /// Walks that answered `false` with equal root metadata words.
        pub collided_walks: u64,
        /// Node pairs entered by the collided walks.
        pub collided_visits: u64,
        /// Fold-engine nodes.
        pub fold_nodes: u64,
        /// Equivalence-manager and def-eq context walk nodes.
        pub equiv_nodes: u64,
        /// Type-checker cache probes.
        pub probes: u64,
        /// Heartbeat sites reached (one per `whnf` / `is_def_eq` / `infer`
        /// step), whatever the checker's limit.
        pub step_ticks: u64,
        /// Heartbeats the checkers' settlements converted from units.
        pub work_heartbeats: u64,
    }

    thread_local! {
        static STATS: Cell<WorkStats> = const {
            Cell::new(WorkStats {
                equality_walks: 0,
                equality_visits: 0,
                collided_walks: 0,
                collided_visits: 0,
                fold_nodes: 0,
                equiv_nodes: 0,
                probes: 0,
                step_ticks: 0,
                work_heartbeats: 0,
            })
        };
    }

    fn update(f: impl FnOnce(&mut WorkStats)) {
        STATS.with(|cell| {
            let mut stats = cell.get();
            f(&mut stats);
            cell.set(stats);
        });
    }

    pub(super) fn record(walk: Walk, units: u64) {
        update(|stats| {
            let slot = match walk {
                Walk::Fold => &mut stats.fold_nodes,
                Walk::Equiv => &mut stats.equiv_nodes,
                Walk::Probe => &mut stats.probes,
            };
            *slot = slot.saturating_add(units);
        });
    }

    pub(super) fn record_equality(visits: u64, collided: bool) {
        update(|stats| {
            stats.equality_walks = stats.equality_walks.saturating_add(1);
            stats.equality_visits = stats.equality_visits.saturating_add(visits);
            if collided {
                stats.collided_walks = stats.collided_walks.saturating_add(1);
                stats.collided_visits = stats.collided_visits.saturating_add(visits);
            }
        });
    }

    /// One heartbeat site reached (a step).
    pub(crate) fn record_step_tick() {
        update(|stats| stats.step_ticks = stats.step_ticks.saturating_add(1));
    }

    /// `heartbeats` converted from units by a checker's settlement.
    pub(crate) fn record_work_heartbeats(heartbeats: u64) {
        update(|stats| stats.work_heartbeats = stats.work_heartbeats.saturating_add(heartbeats));
    }

    /// This thread's totals since the last call, which zeroes them.
    #[must_use]
    pub fn take() -> WorkStats {
        STATS.with(|cell| cell.replace(WorkStats::default()))
    }
}

#[cfg(test)]
#[path = "work_meter_tests.rs"]
mod tests;
