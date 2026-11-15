// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::time::{Duration, Instant};

/// A wait for something that must happen: a one-minute hang detector.
const HANG: Duration = Duration::from_secs(60);

/// Without a deadline neither read ever stops a load.
#[test]
fn without_a_deadline_nothing_stops() {
    for _ in 0..5_000 {
        assert!(check().is_ok());
        assert!(poll().is_ok());
    }
}

/// `check` reads the clock: one module is one read, so a deadline that passes
/// between two modules stops the load at the next one, where the kernel's poll
/// would read the clock only a thousand polls later.
///
/// The first `check` must find the deadline ahead. That fails only when this
/// thread waits longer than the whole window between making the deadline and
/// that check (a machine loaded past its cores); such a run decides nothing,
/// and the next one gets a window twice as long, within the hang detector.
/// The verdicts are read only from a run whose first `check` found the
/// deadline ahead.
#[test]
fn check_reads_the_clock_where_a_poll_would_not() {
    let give_up = Instant::now() + HANG;
    let mut window = Duration::from_secs(1);
    loop {
        match check_after_a_window(window) {
            Some((stopped, finished)) => {
                assert!(stopped, "`check` did not see the deadline that had passed");
                assert_eq!(finished, None, "`check` latches the caller's deadline");
                return;
            }
            // The deadline had passed by the first `check`: this run decided
            // nothing, so the next gets twice the window, inside the hang
            // detector. Every way out of the loop asserts.
            None => {
                assert!(
                    Instant::now() < give_up,
                    "the first `check` never ran inside its window"
                );
                window = window.saturating_mul(2);
            }
        }
    }
}

/// One run of [`check_reads_the_clock_where_a_poll_would_not`]: `None` when
/// the deadline `window` away had passed by the first `check`, else whether
/// the `check` after it stopped, and what `run_until` answered.
fn check_after_a_window(window: Duration) -> Option<(bool, Option<()>)> {
    let deadline = Instant::now() + window;
    let mut ahead = false;
    let mut stopped = false;
    let finished = run_until(Some(deadline), || {
        if check().is_err() {
            return;
        }
        ahead = true;
        let give_up = Instant::now() + HANG;
        while Instant::now() < deadline {
            assert!(Instant::now() < give_up, "the deadline never passed");
            std::thread::sleep(Duration::from_millis(10));
        }
        assert!(
            poll().is_ok(),
            "the kernel's poll read the clock right after `check` did: this test's premise"
        );
        stopped = matches!(check(), Err(ImportError::Interrupted));
    });
    ahead.then_some((stopped, finished))
}

/// A passed deadline stops the first read, and every read after it.
#[test]
fn a_passed_deadline_stops_every_read() {
    let mut seen = None;
    let finished = run_until(Some(Instant::now()), || {
        seen = Some((check().is_err(), poll().is_err(), check().is_err()));
    });
    assert_eq!(seen, Some((true, true, true)));
    assert_eq!(finished, None);
}
