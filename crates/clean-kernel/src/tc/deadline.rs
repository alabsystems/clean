// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ambient, per-thread deadline: the cooperative interrupt that
//! [`TypeError::Interrupted`] was reserved for.
//!
//! # Why this exists
//!
//! `clean-server` answers a request at its `timeout_ms`, and until 2026-10-15
//! it could not stop the work behind the request: the work is synchronous, a
//! synchronous Rust call cannot be stopped from outside, and the request's
//! `tokio::time::timeout` could not even fire while the call held its runtime
//! worker. The server now runs the work on a thread of its own and answers the
//! timeout at the deadline (`crates/clean-server/src/handlers/work.rs`); this
//! module is how the abandoned work learns that nobody is waiting for it any
//! more, and stops.
//!
//! # What it is
//!
//! [`run_until`] installs a deadline on the current thread for one call. The
//! kernel's cooperative tick sites poll it: the ones the heartbeat and the
//! declaration budget already use (`infer_type`, `whnf_impl`,
//! `is_def_eq_core`, the retained-certificate inference), the certificate
//! verifier's recursion and reduction, and, outside the kernel, the
//! automation's work-budget charges (`clean-auto`'s `work_budget::charge`).
//! A poll reads the clock once every [`CLOCK_EVERY`] polls. The first read
//! that finds the deadline passed FIRES it, and it stays fired until the call
//! returns (the latch). From then on the work degrades exactly as it does when
//! a heartbeat is spent: `infer_type` and the certificate verifier refuse with
//! `Interrupted`, `whnf` returns its input unreduced and `is_def_eq_core`
//! answers "not shown equal". The degradations only ever take a step away,
//! and their output is never used, because of the next rule.
//!
//! # A fired deadline is never a verdict
//!
//! [`run_until`] returns `None` whenever the deadline fired during the call,
//! whatever the call itself returned, so nothing computed after the latch
//! closed (an under-reduced term, a refused step, an `Ok` that a degraded path
//! happened to produce) reaches the caller. Work the deadline
//! never interrupted returns exactly what it returns without one: a poll that
//! does not fire changes nothing.
//!
//! # Scope
//!
//! The deadline is thread-local. Threads the work starts (a rayon pool, the
//! kernel's parallel stub upgrade) do not inherit it, and run to their own
//! limits; a batch that wants each item bounded installs the deadline inside
//! each item (`clean-server`'s batch handlers do). Work that is
//! bounded by construction and fills process-wide state — the cubical
//! authority's canonical table, the elaborator's prelude seeding — runs with
//! the deadline suspended ([`with_deadline_suspended`]), so a deadline can
//! never leave a half-built table behind for the next caller.
//!
//! It bounds the work only as tightly as the tick sites are dense. Work that
//! spends its time between ticks — parsing, one large instantiation, a single
//! big-number operation, a decision procedure bounded by its own counts — runs
//! to its end; `clean-server` bounds how much such abandoned work can pile up
//! (`handlers/work.rs`).
//!
//! # Disabled by default
//!
//! No thread has a deadline until [`run_until`] installs one. Without one, a
//! poll is one thread-local load and a compare, and no verdict anywhere can
//! move.
//!
//! [`TypeError::Interrupted`]: super::TypeError::Interrupted

use std::cell::Cell;
use std::time::Instant;

/// Polls between two reads of the clock.
///
/// A tick costs from tens of nanoseconds (a cache-missing `whnf` of a small
/// term) up; reading the clock every 1,024 polls keeps the clock's cost out of
/// the measurements and stops the work well within a millisecond of its
/// deadline on dense tick sites.
pub(crate) const CLOCK_EVERY: u32 = 1024;

/// This thread's deadline state. One `thread_local!` entry, so a poll pays for
/// one thread-local lookup.
struct Ambient {
    /// The deadline of the call in progress; `None` when there is none.
    deadline: Cell<Option<Instant>>,
    /// The latch: a poll found the deadline passed.
    fired: Cell<bool>,
    /// Polls left before the next clock read.
    countdown: Cell<u32>,
}

thread_local! {
    static AMBIENT: Ambient = const {
        Ambient {
            deadline: Cell::new(None),
            fired: Cell::new(false),
            countdown: Cell::new(0),
        }
    };
}

/// Whether this thread has an ambient deadline, including one not yet fired.
/// Reusing a worker's refusal must not hide a caller-side interruption.
pub(crate) fn deadline_is_armed() -> bool {
    AMBIENT.with(|ambient| ambient.deadline.get().is_some())
}

/// The state [`run_until`] and [`with_deadline_suspended`] restore on exit,
/// unwinding included.
struct Restore {
    deadline: Option<Instant>,
    fired: bool,
}

impl Restore {
    fn install(deadline: Option<Instant>, fired: bool) -> Self {
        AMBIENT.with(|a| {
            let saved = Restore {
                deadline: a.deadline.replace(deadline),
                fired: a.fired.replace(fired),
            };
            // The first poll reads the clock: a deadline already passed stops
            // the work before its first step.
            a.countdown.set(0);
            saved
        })
    }
}

impl Drop for Restore {
    fn drop(&mut self) {
        AMBIENT.with(|a| {
            a.deadline.set(self.deadline);
            a.fired.set(self.fired);
            // The enclosing call's next poll reads the clock again, so an
            // enclosing deadline that passed meanwhile fires at once.
            a.countdown.set(0);
        });
    }
}

/// Run `f` under `deadline` on this thread.
///
/// Returns `None` if the deadline fired while `f` ran, discarding what `f`
/// returned: the work was interrupted, and nothing it computed is a verdict.
/// Otherwise `Some` of what `f` returned. A `deadline` of `None` installs no
/// deadline of its own. A call inside another keeps the earlier of the two
/// deadlines, and one made after the enclosing deadline fired is interrupted
/// at once. The enclosing state is restored on return and on unwinding.
///
/// # Contract
///
/// ENSURES: `Some(v)` only if no poll during `f` found the deadline passed,
///          and then `v` is what `f` returned
/// ENSURES: the thread's deadline state after the call is the state before it
#[must_use]
pub fn run_until<T>(deadline: Option<Instant>, f: impl FnOnce() -> T) -> Option<T> {
    let (enclosing, enclosing_fired) = AMBIENT.with(|a| (a.deadline.get(), a.fired.get()));
    let effective = match (enclosing, deadline) {
        (Some(outer), Some(inner)) => Some(outer.min(inner)),
        (outer, inner) => outer.or(inner),
    };
    let restore = Restore::install(effective, enclosing_fired);
    let out = f();
    let fired = AMBIENT.with(|a| a.fired.get());
    drop(restore);
    (!fired).then_some(out)
}

/// Run `f` with this thread's deadline suspended, then restore it exactly.
///
/// For work that is bounded by construction and must not be left half done:
/// building a process-wide table, seeding a fixed set of repo-authored
/// declarations. The suspended region is UNBOUNDED, so it is never appropriate
/// around anything user input can grow.
pub(crate) fn with_deadline_suspended<T>(f: impl FnOnce() -> T) -> T {
    let _restore = Restore::install(None, false);
    f()
}

/// Poll the deadline: `true` means it has passed, stop.
///
/// Reads the clock once every [`CLOCK_EVERY`] polls and latches. Always
/// `false` on a thread with no deadline.
#[inline]
pub fn poll_deadline() -> bool {
    AMBIENT.with(|a| {
        let Some(deadline) = a.deadline.get() else {
            return false;
        };
        if a.fired.get() {
            return true;
        }
        let countdown = a.countdown.get();
        if countdown > 0 {
            a.countdown.set(countdown - 1);
            return false;
        }
        a.countdown.set(CLOCK_EVERY - 1);
        if Instant::now() >= deadline {
            a.fired.set(true);
            return true;
        }
        false
    })
}

/// Has this thread's deadline fired? Reads the latch, never the clock.
#[inline]
#[must_use]
pub(crate) fn deadline_fired() -> bool {
    AMBIENT.with(|a| a.fired.get())
}

#[cfg(test)]
#[path = "deadline_tests.rs"]
mod tests;
