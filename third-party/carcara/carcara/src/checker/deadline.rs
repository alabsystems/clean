//! Added in Clean (not part of upstream Carcara): the checker stops at a deadline its caller sets
//! (`Config::deadline`).
//!
//! A step's resource budget (`budget.rs`) bounds what one step builds, not how long a proof takes:
//! a proof can repeat an affordable step, and some comparisons are bounded by nothing but time
//! (alpha-equivalence of a shared term read under a different binding on every path; see
//! third-party/carcara/DOWNSTREAM.md, "Performance: `Polyeq` caches the pairs it finds unequal",
//! and "The checker stops at a deadline"). So a caller may give the checker a deadline. The
//! checker reads the clock before and after every command, and the comparisons poll it as they go
//! ([`expired`] reads the clock once every [`POLL_INTERVAL`] polls). A comparison that sees the
//! deadline pass stops early, whatever it then answers, and
//! the command it ran in is refused with `CheckerError::DeadlineExceeded`, and so the proof: no
//! answer given past the deadline is used. A check that ends before its deadline is the check it
//! was without one.
//!
//! The deadline is kept per thread, for the check running on it: a walk deep in a rule reads it
//! without its caller's configuration being passed down to it.

use std::{cell::Cell, time::Instant};

/// How many polls [`expired`] answers from its flag before it reads the clock again. A poll costs
/// a thread-local read; reading the clock costs some tens of nanoseconds.
const POLL_INTERVAL: u32 = 1 << 12;

thread_local! {
    /// The deadline of the check running on this thread, if any.
    static DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
    /// Whether that check has seen its deadline pass: once set, it stays set until the check ends.
    static PASSED: Cell<bool> = const { Cell::new(false) };
    /// Polls left before [`expired`] reads the clock.
    static COUNTDOWN: Cell<u32> = const { Cell::new(0) };
}

/// The deadline of a check, set on its thread for as long as this lives. A check run inside
/// another keeps the earlier of the two deadlines, and the outer one's is restored when it ends.
#[must_use]
pub struct Armed {
    previous: Option<Instant>,
    previous_passed: bool,
}

/// Sets `deadline` as the deadline of the check about to run on this thread.
pub fn arm(deadline: Option<Instant>) -> Armed {
    let previous = DEADLINE.get();
    let effective = match (previous, deadline) {
        (Some(outer), Some(inner)) => Some(outer.min(inner)),
        (outer, inner) => outer.or(inner),
    };
    DEADLINE.set(effective);
    let previous_passed = PASSED.replace(false);
    COUNTDOWN.set(0);
    Armed { previous, previous_passed }
}

impl Drop for Armed {
    fn drop(&mut self) {
        DEADLINE.set(self.previous);
        PASSED.set(self.previous_passed);
        COUNTDOWN.set(0);
    }
}

/// Whether the check running on this thread has passed its deadline, cheaply enough to be polled
/// once per term a walk visits: it reads the clock once every [`POLL_INTERVAL`] calls. Once it has
/// answered `true`, it answers `true` until the check ends. Always `false` without a deadline.
pub fn expired() -> bool {
    if PASSED.get() {
        return true;
    }
    let Some(deadline) = DEADLINE.get() else {
        return false;
    };
    let left = COUNTDOWN.get();
    if left > 0 {
        COUNTDOWN.set(left - 1);
        return false;
    }
    COUNTDOWN.set(POLL_INTERVAL);
    passed(deadline)
}

/// [`expired`], reading the clock now.
pub fn expired_now() -> bool {
    PASSED.get() || DEADLINE.get().is_some_and(passed)
}

fn passed(deadline: Instant) -> bool {
    let passed = Instant::now() >= deadline;
    PASSED.set(passed);
    passed
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn a_deadline_is_kept_per_check_and_restored() {
        assert!(!expired_now() && !expired());
        let later = Instant::now() + Duration::from_secs(3600);
        let outer = arm(Some(later));
        assert!(!expired_now());
        {
            // An inner check with a passed deadline passes; the outer one's is restored after it.
            let _inner = arm(Some(Instant::now() - Duration::from_millis(1)));
            assert!(expired_now() && expired());
        }
        assert_eq!(DEADLINE.get(), Some(later));
        assert!(!expired_now());
        {
            // An inner check without a deadline keeps the outer one's.
            let _inner = arm(None);
            assert_eq!(DEADLINE.get(), Some(later));
        }
        drop(outer);
        assert_eq!(DEADLINE.get(), None);
        assert!(!expired_now() && !expired());

        // `expired` reads the clock at its first poll and then once every `POLL_INTERVAL`.
        let _passed = arm(Some(Instant::now()));
        assert!(expired());
        assert!(expired_now());
    }
}
