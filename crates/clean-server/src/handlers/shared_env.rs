// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The server's shared kernel environment, and how a writer changes it.
//!
//! # Why
//!
//! Two writers computed a new environment from the old one and installed it,
//! and each got that wrong in its own way (open items of R32, fixed by R34 in
//! `docs/DECISIONS.md`):
//!
//! * `loadEnvironment`'s merge held the environment's write lock while it
//!   re-checked every loaded declaration, so every request that reads the
//!   environment waited for the whole merge (up to its timeout, fifty seconds
//!   by default).
//! * `importModule` cloned the environment, loaded its modules into the clone
//!   holding nothing, and installed the clone. A change that landed meanwhile
//!   (a merge, the verify family's set-up) was overwritten: a lost update.
//!
//! # What a writer does now
//!
//! * Every change to the environment is counted: [`SharedEnv`] carries a
//!   revision, and a write guard that hands out the environment mutably
//!   counts a change when it is let go. Seeding what is already there
//!   ([`SharedEnv::seed`]) counts none.
//! * A writer whose work is long ([`SharedEnv::update`]) never holds the
//!   write lock while it works. It copies the environment under a read hold,
//!   lets the hold go, computes on the copy on the work pool under its
//!   request's deadline, and then takes the write lock only to publish: the
//!   copy replaces the environment when the revision is still the one it
//!   copied. When the environment changed meanwhile the copy is dropped, never
//!   installed, and the work runs again on a fresh copy of the current
//!   environment, inside the same timeout. Readers wait for nothing but the
//!   swap.
//! * Writers that publish a whole environment (`loadEnvironment` in either
//!   mode, `importModule`) take turns ([`SharedEnv::writer_turn`]), first come
//!   first served, so two of them never compute against the same environment
//!   and redo each other's work. The verify family's set-up takes no turn (it
//!   would wait for a whole import); it seeds the logical prelude only when
//!   it is missing, and a copy that seeding made stale is computed again.
//!   Seeding runs on the work pool ([`SharedEnv::seed`]): the kernel copies
//!   the whole environment for each inductive it adds and frees the copy.
//!
//! * The environment a publish replaces, and a copy that is never installed
//!   (a stale one, or one whose request was cancelled after its work answered,
//!   whether it waited to publish or had not yet taken the answer), are freed
//!   off the async runtime (`off_runtime.rs`): freeing an environment walks
//!   every constant it holds, and a runtime worker doing it served nothing
//!   else meanwhile.
//!
//! # Lock order
//!
//! A writer's turn, then a work slot, then the environment (`work.rs`): a
//! turn is held while waiting for a slot, which is safe because no slot holder
//! ever waits for a turn (only writers take one, and they take it first). The
//! read hold a copy is made under is let go before the work runs, and nothing
//! waits for a slot while holding the environment.

use std::ops::{Deref, DerefMut};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Instant;

use clean_kernel::Environment;
use tokio::sync::{Mutex, MutexGuard, OwnedRwLockReadGuard, RwLock, RwLockReadGuard};

use super::off_runtime::{free_off_runtime, OffRuntime};
use super::work::{WorkError, WorkPool};

/// How many changes the shared environment has had. Read and written only
/// while its lock is held, so the lock orders every access.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Revision(u64);

/// The kernel environment every request reads. Cloning shares it.
#[derive(Clone)]
pub(crate) struct SharedEnv {
    env: Arc<RwLock<Environment>>,
    revision: Arc<AtomicU64>,
    writers: Arc<Mutex<()>>,
}

/// What a writer whose copy went stale gets from a publish: the environment
/// changed after the copy was made, and the copy was not installed.
struct Stale;

impl SharedEnv {
    pub(crate) fn new(env: Environment) -> Self {
        Self {
            env: Arc::new(RwLock::new(env)),
            revision: Arc::new(AtomicU64::new(0)),
            writers: Arc::new(Mutex::new(())),
        }
    }

    /// Hold the environment for reading.
    pub(crate) async fn read(&self) -> RwLockReadGuard<'_, Environment> {
        self.env.read().await
    }

    /// Hold the environment for reading, for work that outlives the borrow
    /// (work on the pool).
    pub(crate) async fn read_owned(&self) -> OwnedRwLockReadGuard<Environment> {
        Arc::clone(&self.env).read_owned().await
    }

    /// Hold the environment for writing. A change made through the guard is
    /// counted when it is let go (see [`EnvWriteGuard`]).
    pub(crate) async fn write(&self) -> EnvWriteGuard<'_> {
        EnvWriteGuard {
            env: self.env.write().await,
            revision: &self.revision,
            changed: false,
        }
    }

    /// Seed the environment: run `seed`, kernel set-up that adds its
    /// declarations only when they are missing (the `init_*` family), on the
    /// work pool in a slot of its own, holding the environment for writing
    /// (the lock order above: the slot, then the environment; no turn). It
    /// counts a change only when it added something: when the environment's
    /// generation or its counts of constants and inductives moved, so seeding
    /// an environment that has everything leaves a writer's copy current.
    ///
    /// On the pool because the kernel adds each inductive transactionally: it
    /// copies the whole environment first and frees the copy after
    /// (`Environment::add_inductive`). The verify family's set-up seeded on a
    /// runtime worker, four copies and frees of an environment that lacked the
    /// prelude, 0.8 to 1.5 s in a debug build (review of 2026-10-19), and an
    /// environment `loadEnvironment` replaces lacks it again. It has no
    /// deadline: the set-up is fixed, and the kernel adds an inductive whole.
    pub(crate) async fn seed<R: Send + 'static>(
        &self,
        work: &WorkPool,
        seed: impl FnOnce(&mut Environment) -> R + Send + 'static,
    ) -> Result<R, WorkError> {
        let slot = work.slot().await?;
        let mut held = Arc::clone(&self.env).write_owned().await;
        let revision = Arc::clone(&self.revision);
        WorkPool::run_in(slot, None, move || {
            let before = Shape::of(&held);
            let out = seed(&mut held);
            if Shape::of(&held) != before {
                // Counted holding the lock, which orders every read of it.
                revision.fetch_add(1, Ordering::Relaxed);
            }
            out
        })
        .await
    }

    /// Wait for this writer's turn among the writers that publish a whole
    /// environment. Await it inside the request's timeout, before its work
    /// slot (the lock order above).
    pub(crate) async fn writer_turn(&self) -> MutexGuard<'_, ()> {
        self.writers.lock().await
    }

    /// Install `env` in place of the environment, in the writer's turn.
    /// Await it inside the request's timeout. The old environment is freed
    /// after the lock is let go, off the runtime; so is `env` when the request
    /// is cancelled before it is installed.
    pub(crate) async fn replace(&self, env: Environment) {
        let env = OffRuntime::new(env);
        let _turn = self.writer_turn().await;
        let mut held = self.write().await;
        let old = std::mem::replace(&mut *held, env.into_inner());
        drop(held);
        free_off_runtime(old);
    }

    /// Change the environment by `work`, which runs on `pool` under
    /// `deadline` on a copy of the environment and returns the copy changed
    /// (or why it refuses). The copy is published only if the environment has
    /// not changed since it was made; otherwise the work runs again on a copy
    /// of the current environment. Await it inside the request's timeout: a
    /// timeout that fires drops the copy, and nothing is published.
    ///
    /// `work` returns `Err` to refuse; nothing is published then. A copy that
    /// is not installed, and the environment one replaces, are freed off the
    /// runtime.
    pub(crate) async fn update<T, E>(
        &self,
        pool: &WorkPool,
        deadline: Option<Instant>,
        work: impl Fn(Environment) -> Result<(Environment, T), E> + Send + Sync + 'static,
    ) -> Result<Result<T, E>, WorkError>
    where
        T: Send + 'static,
        E: Send + 'static,
    {
        let work = Arc::new(work);
        let _turn = self.writer_turn().await;
        loop {
            let slot = pool.slot().await?;
            let held = self.read_owned().await;
            let from = self.revision_held();
            let job = Arc::clone(&work);
            let outcome = WorkPool::run_in(slot, deadline, move || {
                let copy = Environment::clone(&held);
                // The copy is made: readers and the verify family's set-up go
                // on while the work runs.
                drop(held);
                job(copy)
            })
            .await?;
            let (env, value) = match outcome {
                Ok(done) => done,
                Err(refused) => return Ok(Err(refused)),
            };
            // From here a drop (a stale copy, a request cancelled while it
            // waits to publish) frees the copy off the runtime. Before here,
            // a request cancelled after the work sent the copy but before it
            // was taken leaves it in the answer channel, which frees it off
            // the runtime too (`work.rs`, `Answer`); between the two there is
            // no await, so nothing can cancel the request there.
            let env = OffRuntime::new(env);
            match self.publish(from, env).await {
                Ok(()) => return Ok(Ok(value)),
                Err(Stale) => tracing::info!(
                    "the environment changed while a writer worked on its copy; \
                     working again on a copy of the current environment"
                ),
            }
        }
    }

    /// Install `env` if the environment's revision is still `from`. A stale
    /// `env` and the environment it replaces are freed off the runtime.
    async fn publish(&self, from: Revision, env: OffRuntime<Environment>) -> Result<(), Stale> {
        let mut held = self.write().await;
        if self.revision_held() != from {
            return Err(Stale);
        }
        let old = std::mem::replace(&mut *held, env.into_inner());
        drop(held);
        free_off_runtime(old);
        Ok(())
    }

    /// The revision. Read it holding the lock: the hold orders it.
    fn revision_held(&self) -> Revision {
        Revision(self.revision.load(Ordering::Relaxed))
    }

    /// The revision now.
    #[cfg(test)]
    pub(crate) async fn revision(&self) -> Revision {
        let _held = self.read().await;
        self.revision_held()
    }

    #[cfg(test)]
    pub(crate) fn try_read(
        &self,
    ) -> Result<RwLockReadGuard<'_, Environment>, tokio::sync::TryLockError> {
        self.env.try_read()
    }

    #[cfg(test)]
    pub(crate) fn try_write(&self) -> Result<EnvWriteGuard<'_>, tokio::sync::TryLockError> {
        Ok(EnvWriteGuard {
            env: self.env.try_write()?,
            revision: &self.revision,
            changed: false,
        })
    }
}

/// The environment held for writing. Handing it out mutably counts a change,
/// whatever the caller then does with it: the count may run ahead of the
/// changes, never behind (a writer whose copy it made stale only works
/// again). [`SharedEnv::seed`] counts only a change the kernel counts.
pub(crate) struct EnvWriteGuard<'a> {
    env: tokio::sync::RwLockWriteGuard<'a, Environment>,
    revision: &'a AtomicU64,
    changed: bool,
}

impl Deref for EnvWriteGuard<'_> {
    type Target = Environment;

    fn deref(&self) -> &Environment {
        &self.env
    }
}

impl DerefMut for EnvWriteGuard<'_> {
    fn deref_mut(&mut self) -> &mut Environment {
        self.changed = true;
        &mut self.env
    }
}

impl Drop for EnvWriteGuard<'_> {
    fn drop(&mut self) {
        // Runs before the lock is let go: the guard's fields drop after this.
        if self.changed {
            self.revision.fetch_add(1, Ordering::Relaxed);
        }
    }
}

/// What [`SharedEnv::seed`] compares: every declaration the kernel adds
/// moves the generation (`Environment::generation`) or a count.
#[derive(PartialEq, Eq)]
struct Shape {
    generation: u64,
    constants: usize,
    inductives: usize,
}

impl Shape {
    fn of(env: &Environment) -> Self {
        Self {
            generation: env.generation(),
            constants: env.num_constants(),
            inductives: env.num_inductives(),
        }
    }
}

#[cfg(test)]
#[path = "shared_env_tests.rs"]
mod tests;
