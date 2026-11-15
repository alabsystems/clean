// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test-build gate between trust-ledger mints and exact ledger assertions.
//!
//! The sorry/trustedAy counters and location maps are process-global, and
//! the lib test binary runs tests in parallel. Many tests outside this module
//! mint sorries as a side effect (the `init_nn_verify_*` registrations among
//! them) without taking `serial_test_guard`, so a guard on the ledger tests
//! alone orders them only among themselves: a concurrent mint lands between
//! a ledger test's reset and its `assert_eq!`.
//!
//! In test builds every mint holds this gate shared ([`admit_mint`]), and a
//! ledger test holds it exclusively ([`exclusive_trust_counters`]) for its
//! whole body, so no other thread mints while it reads. Production builds do
//! not compile this module and mint with no lock.

use std::cell::Cell;
use std::marker::PhantomData;
use std::sync::{MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard};

static MINT_GATE: RwLock<()> = RwLock::new(());

thread_local! {
    /// True on a thread that mints under the exclusive guard: the ledger
    /// test's own thread, or a thread it admitted. Those mints are the ones
    /// the test measures, and taking the shared lock there would deadlock.
    static ADMITTED: Cell<bool> = const { Cell::new(false) };
}

/// Exclusive hold on the trust ledger for one test body; also serializes
/// against every other `serial_test_guard` test.
pub(crate) struct ExclusiveTrustCounters {
    // Field order is drop order: release the gate before the serial lock.
    _write: RwLockWriteGuard<'static, ()>,
    _serial: MutexGuard<'static, ()>,
}

/// Take the serial test lock, then wait until no other thread is minting and
/// keep every other thread from minting until the guard drops.
pub(crate) fn exclusive_trust_counters() -> ExclusiveTrustCounters {
    let serial = crate::test_utils::serial_test_guard();
    let write = MINT_GATE
        .write()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    ADMITTED.with(|flag| flag.set(true));
    ExclusiveTrustCounters {
        _write: write,
        _serial: serial,
    }
}

impl ExclusiveTrustCounters {
    /// Let the calling thread (one the test spawned in a `thread::scope`)
    /// mint while this guard is held. The borrow ties the admission to the
    /// guard, and the admission ends when the returned token drops.
    pub(crate) fn admit_this_thread(&self) -> AdmittedThread<'_> {
        ADMITTED.with(|flag| flag.set(true));
        AdmittedThread {
            _guard: PhantomData,
        }
    }
}

impl Drop for ExclusiveTrustCounters {
    fn drop(&mut self) {
        ADMITTED.with(|flag| flag.set(false));
    }
}

/// A spawned thread's admission to mint under an [`ExclusiveTrustCounters`].
pub(crate) struct AdmittedThread<'a> {
    _guard: PhantomData<&'a ExclusiveTrustCounters>,
}

impl Drop for AdmittedThread<'_> {
    fn drop(&mut self) {
        ADMITTED.with(|flag| flag.set(false));
    }
}

/// Held across one mint (counters and location together). `None` on a
/// thread the exclusive guard admitted.
pub(crate) fn admit_mint() -> Option<RwLockReadGuard<'static, ()>> {
    if ADMITTED.with(Cell::get) {
        return None;
    }
    Some(
        MINT_GATE
            .read()
            .unwrap_or_else(|poisoned| poisoned.into_inner()),
    )
}
