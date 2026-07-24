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

/// RAII guard: sets or removes one env var, restoring the previous state on
/// drop (also on panic).
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

    /// Remove `key` for the guard's lifetime.
    pub(crate) fn unset(key: &str) -> Self {
        let previous = std::env::var(key).ok();
        // Blessed choke point: see `set`.
        #[allow(unknown_lints, env_mutation)]
        std::env::remove_var(key);
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

/// Run `f` with `vars` removed, serialized behind the process-wide env lock;
/// previous values are restored afterwards (also on panic).
pub(crate) fn with_serialized_env_vars_removed<T>(vars: &[&str], f: impl FnOnce() -> T) -> T {
    let _env_lock = lock_env();
    let _guards: Vec<_> = vars.iter().map(|key| ScopedEnvVar::unset(key)).collect();
    f()
}

/// Scoped editor for tests that walk a knob through several set/remove states
/// (e.g. probing an env parser's `"0"` / `"1"` / unset behavior).
///
/// Every key touched is captured once on first touch and restored when the
/// [`with_env_edits`] scope ends (also on panic).
pub(crate) struct EnvEditor {
    saved: Vec<(String, Option<String>)>,
}

impl EnvEditor {
    fn save_once(&mut self, key: &str) {
        if !self.saved.iter().any(|(k, _)| k == key) {
            self.saved.push((key.to_owned(), std::env::var(key).ok()));
        }
    }

    /// Set `key=value` until the end of the scope or the next edit of `key`.
    pub(crate) fn set(&mut self, key: &str, value: &str) {
        self.save_once(key);
        // Blessed choke point: serialized by with_env_edits, restored on exit.
        #[allow(unknown_lints, env_mutation)]
        std::env::set_var(key, value);
    }

    /// Remove `key` until the end of the scope or the next edit of `key`.
    pub(crate) fn remove(&mut self, key: &str) {
        self.save_once(key);
        // Blessed choke point: serialized by with_env_edits, restored on exit.
        #[allow(unknown_lints, env_mutation)]
        std::env::remove_var(key);
    }
}

impl Drop for EnvEditor {
    fn drop(&mut self) {
        // Restore in reverse touch order (first-touched wins last).
        #[allow(unknown_lints, env_mutation)]
        for (key, previous) in self.saved.drain(..).rev() {
            match previous {
                Some(value) => std::env::set_var(&key, value),
                None => std::env::remove_var(&key),
            }
        }
    }
}

/// Run `f` with exclusive, restore-on-exit access to the process environment
/// via an [`EnvEditor`].
pub(crate) fn with_env_edits<T>(f: impl FnOnce(&mut EnvEditor) -> T) -> T {
    let _env_lock = lock_env();
    let mut editor = EnvEditor { saved: Vec::new() };
    f(&mut editor)
    // editor drops (restores) before _env_lock releases.
}
