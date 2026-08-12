// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Serialized process-environment mutation for this crate's tests — THE
//! blessed choke point for `std::env::set_var` / `std::env::remove_var`.
//!
//! `set_var`/`remove_var` mutate process-global state, so unserialized use
//! races parallel test threads (and any env reader mid-flight). Every test
//! that must mutate the environment routes through this module, which
//! (a) serializes mutation behind one process-wide lock and
//! (b) restores the previous value on scope exit, even on panic.
//!
//! This is the ONLY place in the crate allowed to call the raw mutators; the
//! Trust toolchain's deny-by-default `env_mutation` wall stays armed
//! everywhere else. (`unknown_lints` keeps the stock-rustc build green — the
//! lint name is Trust-only.)

use std::sync::{Mutex, MutexGuard, OnceLock};

/// One process-wide lock for all environment mutation in a test binary.
fn env_mutex() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

/// Acquire the process-wide environment lock explicitly (guard-style use).
///
/// A poisoned lock (a previous test panicked while holding it) is recovered:
/// the guards below restore state on unwind, so the environment stays
/// consistent even after a panic.
pub(crate) fn lock_env() -> MutexGuard<'static, ()> {
    env_mutex().lock().unwrap_or_else(|e| e.into_inner())
}

/// RAII guard: sets one env var, restoring the previous state on drop (also on
/// panic).
///
/// Does NOT itself take [`lock_env`] — compose with [`lock_env`] or the
/// `with_*` helpers, which do. (Taking the lock per-guard would deadlock the
/// multi-guard helpers.)
pub(crate) struct ScopedEnvVar {
    key: String,
    previous: Option<String>,
}

impl ScopedEnvVar {
    /// Set `key=value` for the guard's lifetime.
    pub(crate) fn set(key: &str, value: &str) -> Self {
        let previous = std::env::var(key).ok();
        // Blessed choke point: serialized by lock_env()/with_* callers and
        // restored on drop — the one place raw set_var is allowed.
        #[allow(unknown_lints, env_mutation)]
        std::env::set_var(key, value);
        Self {
            key: key.to_owned(),
            previous,
        }
    }
}

impl Drop for ScopedEnvVar {
    fn drop(&mut self) {
        // Blessed choke point: restore the captured pre-test state.
        #[allow(unknown_lints, env_mutation)]
        match &self.previous {
            Some(value) => std::env::set_var(&self.key, value),
            None => std::env::remove_var(&self.key),
        }
    }
}

/// Run `f` with `vars` set, serialized behind the process-wide env lock;
/// previous values are restored afterwards (also on panic).
pub(crate) fn with_serialized_env_vars<T>(vars: &[(&str, &str)], f: impl FnOnce() -> T) -> T {
    let _env_lock = lock_env();
    let _guards: Vec<_> = vars
        .iter()
        .map(|(key, value)| ScopedEnvVar::set(key, value))
        .collect();
    f()
}
