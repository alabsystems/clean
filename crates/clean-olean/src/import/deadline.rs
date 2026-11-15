// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The caller's deadline, read by the module loaders.
//!
//! # Why
//!
//! A load runs under whatever deadline its caller installed on the thread with
//! `clean_kernel::tc::run_until` (`clean-server`'s `importModule` installs its
//! request's). The kernel's tick sites poll that deadline, but reading the
//! module files, decoding them and converting their declarations reach none,
//! so a load past its deadline ran to its end: the server answered the timeout
//! error at the deadline and dropped what the load returned, but the load kept
//! its work slot until it had read, decoded and registered every module.
//!
//! # What the loaders read
//!
//! * [`check`] before each module is read, decoded or registered, and once
//!   more when the load has finished. It reads the clock.
//! * [`poll`] before each declaration of a module is converted: the kernel's
//!   own poll, one thread-local read that reads the clock once every 1,024
//!   polls, as the kernel's tick sites do.
//!
//! A load that finds the deadline passed stops at once with
//! [`ImportError::Interrupted`]. What it changed in the caller's environment
//! is a partial load, which a caller with a deadline drops (`run_until` already
//! answers `None` for it). The module cache gets an entry only from a decode
//! that finished with the deadline not passed (`load/cached.rs`): a decode reads
//! nothing but the module's bytes, so such an entry is the one a load with no
//! deadline makes, and a load cut anywhere leaves the cache holding whole
//! modules or nothing.
//!
//! # Without a deadline
//!
//! No caller but the server installs one. Then both reads find none and
//! nothing changes: no load stops, no error is new.

use super::ImportError;
use clean_kernel::tc::{poll_deadline, run_until};

/// Stop when the caller's deadline has passed. Reads the clock now.
pub(super) fn check() -> Result<(), ImportError> {
    if passed() {
        Err(ImportError::Interrupted)
    } else {
        Ok(())
    }
}

/// Stop when the kernel's poll finds the caller's deadline passed: for loops
/// whose steps are short and many (one declaration's conversion).
pub(super) fn poll() -> Result<(), ImportError> {
    if poll_deadline() {
        Err(ImportError::Interrupted)
    } else {
        Ok(())
    }
}

/// Has the caller's deadline passed? Reads the clock, and latches the deadline
/// when it has (so the caller's `run_until` answers `None`).
///
/// The kernel's poll reads the clock only once every 1,024 polls, and one
/// module is one poll here, so a poll alone could miss a deadline by a
/// thousand modules. A `run_until` with no deadline of its own keeps the
/// caller's, and restores it on return with the poll's countdown at zero, so
/// the poll after it reads the clock (`clean_kernel::tc::run_until`: "the
/// enclosing call's next poll reads the clock again").
fn passed() -> bool {
    let _ = run_until(None, || ());
    poll_deadline()
}

#[cfg(test)]
#[path = "deadline_tests.rs"]
mod tests;
