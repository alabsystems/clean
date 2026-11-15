// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Freeing large values off the async runtime.
//!
//! # Why
//!
//! A writer that publishes an environment (`shared_env.rs`) let the old one go
//! on the async side: the old environment after a publish, the copy a stale
//! publish refused, the environment `loadEnvironment` read when its request
//! was cancelled. So did the proof-state methods (the copy a failed tactic ran
//! on, a state refused at the lifecycle limit), the sessions (a closed one,
//! the copy an `addDecl` replaced or left), and every request cancelled after
//! its work answered (the answer channel, `work.rs`). Freeing an environment
//! walks every constant it holds, so the runtime worker that dropped it served
//! nothing else meanwhile: on a one-thread runtime, every request waited for
//! the free.
//!
//! # What happens now
//!
//! [`free_off_runtime`] hands a value to Tokio's blocking pool and returns at
//! once; the free runs there. [`OffRuntime`] is a value the async side holds
//! and never frees itself: dropping it, a cancelled request's drop included,
//! frees it through [`free_off_runtime`]. Off a runtime (a pool thread, a
//! plain thread, a test outside one) a value is freed where it is dropped:
//! there is no runtime worker to keep free.
//!
//! # Why the blocking pool, not the work pool
//!
//! * A free is not request work. It has no deadline to run under (a drop
//!   cannot be interrupted), no answer, and no timeout to wait inside, so
//!   nothing the work pool adds applies to it.
//! * The work pool's slots bound request work. A free that took one would make
//!   a request wait behind memory being returned, and a free waiting for a slot
//!   (behind requests holding theirs up to their timeouts) would keep a whole
//!   environment alive meanwhile: more memory exactly when the server is
//!   busiest.
//! * A drop cannot wait for anything. A slot is awaited; the blocking pool is
//!   entered from a plain function.
//! * Frees cannot outrun what they undo. Each environment freed here was
//!   made by work on the pool (a copy, a decode), replaced by a writer, or
//!   copied into a session its Rust caller opened, so the work pool's slots,
//!   the writers' turns and the sessions bound how fast they come, and a free
//!   costs no more than the copy it undoes. The blocking pool's threads are
//!   reused, so the frees cost no thread each.
//!
//! # Shared values: whoever lets go last frees off the runtime
//!
//! A value several holders share (a cached proof state, which the cache and
//! the requests reading it hold; a session's environment, which the session
//! map and an `addDecl` hold) is freed where its LAST holder lets it go. The
//! cache and the session map free their shares off the runtime, but when a
//! request still held one (a state evicted or closed while a tactic ran on it,
//! a session closed while an `addDecl` waited for its slot), the request's
//! share was the last, and it went where the request's future was dropped: on
//! a runtime worker (R36's open items). [`Shared`] is such a share: whichever
//! holder lets it go last, wherever, frees the value through
//! [`free_off_runtime`]. [`Arc::into_inner`] decides which holder that is,
//! exactly once however the holders race, so no free is missed and none runs
//! twice.

use std::mem;
use std::sync::Arc;

/// Free `value` on Tokio's blocking pool when this thread is a runtime
/// worker, else here.
pub(crate) fn free_off_runtime<T: Send + 'static>(value: T) {
    match tokio::runtime::Handle::try_current() {
        // The free runs on its own; nothing waits for it.
        Ok(runtime) => drop(runtime.spawn_blocking(move || drop(value))),
        Err(_) => drop(value),
    }
}

/// A value the async side holds but never frees itself: dropping it frees it
/// with [`free_off_runtime`]. `T::default()` must be cheap (it stands in for
/// the value once it is taken out); an empty `Environment` allocates nothing.
pub(crate) struct OffRuntime<T: Default + Send + 'static> {
    value: T,
    /// Whether `value` is still the held one (not taken by `into_inner`).
    held: bool,
}

impl<T: Default + Send + 'static> OffRuntime<T> {
    pub(crate) fn new(value: T) -> Self {
        Self { value, held: true }
    }

    /// The value, for a caller that frees what it replaces itself.
    pub(crate) fn into_inner(mut self) -> T {
        self.held = false;
        mem::take(&mut self.value)
    }
}

impl<T: Default + Send + 'static> std::ops::Deref for OffRuntime<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.value
    }
}

impl<T: Default + Send + 'static> Drop for OffRuntime<T> {
    fn drop(&mut self) {
        if self.held {
            free_off_runtime(mem::take(&mut self.value));
        }
    }
}

/// A share of a value that the last holder to let it go frees off the runtime
/// (see "Shared values" above). Cloning makes another share, and the value is
/// read through it (`Deref`); nobody changes a shared value in place (a
/// writer copies it and replaces the share).
pub(crate) struct Shared<T: Send + Sync + 'static> {
    /// `Some` for as long as the share exists: only its drop takes it.
    share: Option<Arc<T>>,
}

impl<T: Send + Sync + 'static> Shared<T> {
    pub(crate) fn new(value: T) -> Self {
        Self {
            share: Some(Arc::new(value)),
        }
    }

    fn arc(&self) -> &Arc<T> {
        match &self.share {
            Some(share) => share,
            // Only `drop` empties it, and nothing reads a share being dropped.
            None => unreachable!("a share is emptied only by its own drop"),
        }
    }
}

impl<T: Send + Sync + std::fmt::Debug + 'static> std::fmt::Debug for Shared<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&**self, f)
    }
}

impl<T: Send + Sync + 'static> Clone for Shared<T> {
    fn clone(&self) -> Self {
        Self {
            share: Some(Arc::clone(self.arc())),
        }
    }
}

impl<T: Send + Sync + 'static> std::ops::Deref for Shared<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.arc()
    }
}

impl<T: Send + Sync + 'static> Drop for Shared<T> {
    fn drop(&mut self) {
        // `into_inner` hands the value to exactly one of the holders that let
        // their shares go, the last; the others only drop a count.
        if let Some(last) = self.share.take().and_then(Arc::into_inner) {
            free_off_runtime(last);
        }
    }
}
