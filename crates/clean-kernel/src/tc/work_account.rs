// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A checker's account with the kernel work meter.
//!
//! The meter (`crate::work_meter`) counts every structural walk on the thread.
//! A checker bills itself only for the units charged INSIDE its own
//! operations: an operation opens a metered scope ([`MeteredScope`]); the
//! outermost scope re-reads the meter on entry, so work done on the thread
//! while the checker was idle (an elaborator's own comparisons, another
//! checker's operations) is never billed to it, and settles on exit, so work
//! after the operation's last heartbeat tick is never lost. Inside a scope,
//! every heartbeat site settles first, so a spent budget is seen at the very
//! next check.
//!
//! # The allowance
//!
//! Every heartbeat tick grants [`UNITS_PER_HEARTBEAT`] units of credit, and a
//! settlement bills only the units past the credit banked so far. The bank
//! holds at most [`CREDIT_CAP`] units (1,024 steps' worth), so steps taken long
//! ago cannot pay for a burst of walking much later. So a heartbeat is one step
//! plus that much walking, a check whose walks stay inside its steps'
//! allowance spends exactly the heartbeats it did before the meter, and any
//! window of a checker's work that spends `B` heartbeats walked at most
//! `B` × [`UNITS_PER_HEARTBEAT`] + [`CREDIT_CAP`] units (every unit is covered
//! by a tick's credit or billed as a heartbeat, and both spend the budget; the
//! cap is what the window may have inherited). Resetting or setting the budget
//! clears the credit and the carry.
//!
//! # The innermost checker pays, once
//!
//! A checker's operation may run another checker (a sub-checker built for one
//! constructor field, a nested elaboration check). Heartbeat TICKS already
//! behave this way: the inner checker's steps draw the inner checker's counter
//! and the ambient declaration pot, never the outer counter. Work units follow
//! the same rule. Every settlement publishes the units it billed to the
//! thread's [`NESTED_BILLED`] total, and a checker's next settlement deducts
//! what was published since its own last reading. So the units an inner
//! checker billed are billed to it alone, and drawn from the ambient
//! declaration budget exactly once.
//!
//! The account only moves budget counters. No reduction, comparison or cache
//! reads it, so it cannot change an answer, only whether the budget refuses
//! first (and a refusal is never an acceptance).

use super::TypeChecker;
use crate::work_meter::{charged, UNITS_PER_HEARTBEAT};
use std::cell::Cell;

/// The most walking, in units, a checker's banked step allowance may hold.
pub(super) const CREDIT_CAP: u64 = 1_024 * UNITS_PER_HEARTBEAT;

thread_local! {
    /// Units accounted for on this thread by any checker's settlement, billed
    /// or paid from its steps' allowance (monotone, wrapping). An enclosing
    /// checker deducts what was accounted for inside its window, so nested
    /// work is accounted for once (see the module docs).
    static NESTED_BILLED: Cell<u64> = const { Cell::new(0) };
}

fn nested_billed() -> u64 {
    NESTED_BILLED.with(Cell::get)
}

/// Per-checker meter reading, unconverted remainder and scope depth.
pub(super) struct WorkAccount {
    /// Meter reading up to which this checker has billed itself.
    seen: Cell<u64>,
    /// [`NESTED_BILLED`] reading at the same moment as `seen`.
    seen_billed: Cell<u64>,
    /// Units owed beyond the allowance but worth less than one heartbeat.
    carry: Cell<u64>,
    /// Units of walking the steps taken so far have already paid for: each
    /// heartbeat tick grants one heartbeat's worth (see the module docs).
    credit: Cell<u64>,
    /// Nesting depth of open metered scopes.
    depth: Cell<u32>,
}

impl WorkAccount {
    pub(super) fn new() -> Self {
        Self {
            seen: Cell::new(charged()),
            seen_billed: Cell::new(nested_billed()),
            carry: Cell::new(0),
            credit: Cell::new(0),
            depth: Cell::new(0),
        }
    }

    /// Forget work charged and billed on the thread since the last reading.
    fn rebaseline(&self) {
        self.seen.set(charged());
        self.seen_billed.set(nested_billed());
    }

    /// Whole heartbeats owed for this checker's own units since the last
    /// reading: what was charged, less what nested checkers billed meanwhile.
    /// The own units are published as billed; the sub-heartbeat remainder is
    /// carried.
    fn take_heartbeats(&self) -> u64 {
        let now = charged();
        let charged_since = now.wrapping_sub(self.seen.replace(now));
        let billed_now = nested_billed();
        let billed_by_others = billed_now.wrapping_sub(self.seen_billed.get());
        // A nested checker can only have billed units charged inside this
        // window, so the difference is this checker's own work. Saturate in
        // case a nested checker settled work charged before this window (it
        // cannot overcharge this checker, only undercharge by that much).
        let own = charged_since.saturating_sub(billed_by_others);
        let published = billed_now.wrapping_add(own);
        NESTED_BILLED.with(|billed| billed.set(published));
        self.seen_billed.set(published);
        // The steps already paid for up to a heartbeat's worth of walking
        // each; only the excess is owed.
        let units = self.carry.get().saturating_add(own);
        let covered = units.min(self.credit.get());
        self.credit.set(self.credit.get() - covered);
        let owed = units - covered;
        self.carry.set(owed % UNITS_PER_HEARTBEAT);
        owed / UNITS_PER_HEARTBEAT
    }

    /// One step (a heartbeat tick) was taken: it pays for a heartbeat's worth
    /// of walking.
    pub(super) fn grant_step(&self) {
        self.credit
            .set((self.credit.get() + UNITS_PER_HEARTBEAT).min(CREDIT_CAP));
    }

    /// A fresh budget starts with no banked allowance and nothing owed, so a
    /// budget of `B` heartbeats bounds the walking it admits to `B` heartbeats'
    /// worth of units.
    pub(super) fn reset_budget(&self) {
        self.credit.set(0);
        self.carry.set(0);
    }
}

/// An open metered scope; settles the checker's account when the outermost
/// one closes.
pub(super) struct MeteredScope<'a, 'env> {
    checker: &'a TypeChecker<'env>,
}

impl Drop for MeteredScope<'_, '_> {
    fn drop(&mut self) {
        let account = &self.checker.work;
        let depth = account.depth.get();
        if depth == 1 {
            // Settle while the scope still counts as open.
            self.checker.settle_kernel_work();
        }
        account.depth.set(depth.saturating_sub(1));
    }
}

impl<'env> TypeChecker<'env> {
    /// Open a metered scope for one checker operation.
    #[inline]
    pub(super) fn metered_scope(&self) -> MeteredScope<'_, 'env> {
        let depth = self.work.depth.get();
        if depth == 0 {
            self.work.rebaseline();
        }
        self.work.depth.set(depth.saturating_add(1));
        MeteredScope { checker: self }
    }

    /// Enter one public checker operation: settle the cache theory, then open
    /// the operation's metered scope.
    #[inline]
    pub(super) fn begin_operation(&self) -> MeteredScope<'_, 'env> {
        self.ensure_cache_theory();
        self.metered_scope()
    }

    /// Convert the units charged inside this checker's open operations into
    /// heartbeats and draw them from both budgets.
    ///
    /// Outside every metered scope there is nothing of this checker's to
    /// bill: the meter is re-read so that what ran on the thread meanwhile is
    /// not billed to the next operation either.
    #[inline]
    pub(super) fn settle_kernel_work(&self) {
        if self.work.depth.get() == 0 {
            self.work.rebaseline();
            return;
        }
        let heartbeats = self.work.take_heartbeats();
        if heartbeats != 0 {
            self.consume_work_heartbeats(heartbeats);
        }
    }

    /// A heartbeat TICK outside every metered scope means an operation reached
    /// a heartbeat site without opening one, so the walks it ran before that
    /// tick were not billed. Counted in test builds so the entry-point battery
    /// can require zero.
    #[inline]
    pub(super) fn note_tick_scope(&self) {
        #[cfg(test)]
        if self.work.depth.get() == 0 {
            UNSCOPED_TICKS.with(|count| count.set(count.get().saturating_add(1)));
        }
    }
}

#[cfg(test)]
thread_local! {
    /// Heartbeat ticks taken outside every metered scope (test builds).
    pub(super) static UNSCOPED_TICKS: Cell<u64> = const { Cell::new(0) };
}

impl TypeChecker<'_> {
    /// Account representation work needed while replaying a checked local
    /// context. This grants no authority and never resets either budget.
    pub(crate) fn metered_scoped_operation<T>(
        &self,
        operation: impl FnOnce() -> T,
    ) -> Result<T, super::TypeError> {
        let _scope = self.begin_operation();
        self.tick_heartbeat()?;
        let result = operation();
        self.tick_heartbeat()?;
        Ok(result)
    }
}
