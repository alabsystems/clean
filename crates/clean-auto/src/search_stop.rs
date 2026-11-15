// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What can stop a counted search short of its own decision.
//!
//! Trust's P4a plan (BUDGET-1 in Trust's `docs/DECISION_QUEUE.md`): a search
//! is decided by counts alone, and a clock is only a backstop. A fired
//! backstop answers "could not run". It is never "not proved", never
//! `Unknown`, never a refusal. [`SearchStop`] carries the two things, besides
//! a search's own counts, that end it without a decision:
//!
//! * **The caller's backstop.** [`SearchStop::backstop_fired`] is the only way
//!   to read the clock, and it latches. Once it has answered `true`, the search
//!   reports a fired backstop, whatever it returns afterwards.
//!
//!   The latch, not where the polls sit, is what makes every answer either the
//!   counts' answer or a fired backstop. A search reads [`SearchStop::has_fired`]
//!   when it ends, never the clock, so a decision the counts reached is never
//!   thrown away for arriving late, and a search whose backstop no poll saw fire
//!   answers exactly what its counts decide, idle or loaded.
//!
//!   Where the polls sit decides only what a backstop that does fire pre-empts.
//!   They come after the count checks that can end a step: fuel, the goal-depth
//!   rail, and superposition's iteration bound, budget charge, saturation and
//!   empty-clause checks. So a count that has decided is not pre-empted. Some
//!   come before a cheap shape check (the lane's own peel of the `∀`,
//!   `prove_eq_rewrite`'s `parse_eq`). There a backstop that fires answers
//!   could-not-run where the shape check would have refused: honest, never a
//!   wrong answer.
//! * **A count of the language that cut a decision procedure short.**
//!   [`SearchStop::note_count_limit`] keeps the first one, so a search that
//!   ends without a proof can name it. Only the SMT solver's CDCL conflict
//!   limit (`smt::SMT_CONFLICT_LIMIT`) is noted today. Every other count ends
//!   its branch without a note, so a search with nothing noted is not thereby
//!   exhaustive.
//!
//! One search runs on one thread, so the state is a `Cell`, not an atomic.

use std::cell::Cell;
use std::time::Instant;

/// The backstop of one counted search, and what stopped it short.
pub(crate) struct SearchStop {
    /// The caller's backstop. `None` is a search bounded by its counts alone.
    backstop: Option<Instant>,
    /// Latched by the first poll that found the backstop passed.
    fired: Cell<bool>,
    /// The first count of the language that stopped a decision procedure.
    count_limit: Cell<Option<&'static str>>,
    /// Backstop polls made: one per search step that reached a poll site. An
    /// observation for this crate's determinism tests; it decides nothing.
    #[cfg(test)]
    polls: Cell<u64>,
}

impl SearchStop {
    /// A search stopped from outside its counts only by `backstop`.
    pub(crate) fn new(backstop: Option<Instant>) -> Self {
        Self {
            backstop,
            fired: Cell::new(false),
            count_limit: Cell::new(None),
            #[cfg(test)]
            polls: Cell::new(0),
        }
    }

    /// Poll the backstop, latching a fired one.
    ///
    /// Call this only where the search's own counts have already decided to go
    /// on and more work follows. `true` means: stop now, and report a fired
    /// backstop.
    pub(crate) fn backstop_fired(&self) -> bool {
        #[cfg(test)]
        {
            self.polls.set(self.polls.get().saturating_add(1));
            slowdown::pause();
        }
        if self.fired.get() {
            return true;
        }
        let fired = self.backstop.is_some_and(passed);
        if fired {
            self.fired.set(true);
        }
        #[cfg(test)]
        slowdown::after_read(self.polls.get());
        fired
    }

    /// Whether a poll has found the backstop passed. Reads no clock.
    pub(crate) fn has_fired(&self) -> bool {
        self.fired.get()
    }

    /// Record that `limit`, a count of the language, stopped a decision
    /// procedure before it decided. The first one is kept.
    pub(crate) fn note_count_limit(&self, limit: &'static str) {
        if self.count_limit.get().is_none() {
            self.count_limit.set(Some(limit));
        }
    }

    /// The first count of the language that stopped a decision procedure.
    pub(crate) fn count_limit(&self) -> Option<&'static str> {
        self.count_limit.get()
    }

    /// Backstop polls this search made (test observation only).
    #[cfg(test)]
    pub(crate) fn polls(&self) -> u64 {
        self.polls.get()
    }
}

/// Whether the instant `at` has passed: the lane's one clock read.
fn passed(at: Instant) -> bool {
    #[cfg(test)]
    {
        if slowdown::backstop_forced_past() {
            return true;
        }
    }
    Instant::now() >= at
}

/// A slow-host seam for this crate's tests, never compiled into production.
///
/// While a [`slowdown::Slowdown`] guard is alive on a thread, every backstop
/// poll on that thread first sleeps for its pause, so each search step takes
/// longer, as on a loaded machine. A count-decided search must answer the same
/// under it, and must answer a fired backstop, never "not proved", when the
/// pauses carry it past its backstop.
///
/// While a [`slowdown::PassAfterPoll`] guard is alive, a backstop passes at an
/// exact point instead: right after a chosen poll has read the clock. That poll
/// and every one before it see the backstop unpassed; any clock read after it
/// sees it passed. No sleep is involved, so the test is exact on a loaded
/// machine. It is how a test checks that nothing reads the clock after the
/// search's last poll and throws away a decision the counts reached.
#[cfg(test)]
pub(crate) mod slowdown {
    use std::cell::Cell;
    use std::time::Duration;

    thread_local! {
        static PAUSE: Cell<Duration> = const { Cell::new(Duration::ZERO) };
        /// The poll after whose clock read the backstop counts as passed.
        static PASS_AFTER: Cell<Option<u64>> = const { Cell::new(None) };
        /// Set once that poll has read the clock.
        static PASSED: Cell<bool> = const { Cell::new(false) };
    }

    /// Makes every backstop pass right after the `poll`-th poll of a search
    /// reads the clock; restores the previous setting when dropped.
    pub(crate) struct PassAfterPoll {
        previous: Option<u64>,
        previous_passed: bool,
    }

    impl PassAfterPoll {
        /// The backstop passes right after poll number `poll` (1-based) has
        /// read the clock.
        pub(crate) fn new(poll: u64) -> Self {
            Self {
                previous: PASS_AFTER.with(|after| after.replace(Some(poll))),
                previous_passed: PASSED.with(|passed| passed.replace(false)),
            }
        }
    }

    impl Drop for PassAfterPoll {
        fn drop(&mut self) {
            PASS_AFTER.with(|after| after.set(self.previous));
            PASSED.with(|passed| passed.set(self.previous_passed));
        }
    }

    /// Called by every poll after its clock read, with its 1-based number.
    pub(super) fn after_read(poll: u64) {
        if PASS_AFTER.with(Cell::get) == Some(poll) {
            PASSED.with(|passed| passed.set(true));
        }
    }

    /// Whether a [`PassAfterPoll`] guard's poll has read the clock.
    pub(super) fn backstop_forced_past() -> bool {
        PASSED.with(Cell::get)
    }

    /// Restores the previous pause when dropped.
    pub(crate) struct Slowdown {
        previous: Duration,
    }

    impl Slowdown {
        /// Pause `per_poll` at every backstop poll on this thread.
        pub(crate) fn new(per_poll: Duration) -> Self {
            Self {
                previous: PAUSE.with(|pause| pause.replace(per_poll)),
            }
        }
    }

    impl Drop for Slowdown {
        fn drop(&mut self) {
            PAUSE.with(|pause| pause.set(self.previous));
        }
    }

    pub(super) fn pause() {
        let pause = PAUSE.with(Cell::get);
        if !pause.is_zero() {
            std::thread::sleep(pause);
        }
    }
}
