// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scoped process-environment overrides.
//!
//! The process environment is shared by every thread. A bare `set_var` followed
//! by a later `remove_var` can therefore leak configuration into an unrelated
//! operation, destroy an ambient value, or race an env-gated reader. This guard
//! serializes every production override in this crate, captures the exact
//! previous [`OsString`], and restores it while still holding the lock.
//!
//! The lock is re-entrant on one thread because an operation-level override may
//! call a lower-level helper that needs a narrower override. A per-thread layer
//! model keeps the mutex owned until the last live scope ends and recomputes the
//! effective value when scopes are dropped in any order. Guards are deliberately
//! `!Send` and `!Sync`: the thread that creates a layer must also remove it. A
//! guard may still remain on the calling thread while worker threads read the
//! configured environment.

use std::cell::RefCell;
use std::ffi::{OsStr, OsString};
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::{Mutex, MutexGuard};

static PROCESS_ENV_LOCK: Mutex<()> = Mutex::new(());

thread_local! {
    static PROCESS_ENV_STATE: RefCell<ThreadEnvState> = const {
        RefCell::new(ThreadEnvState::new())
    };
}

struct EnvLayer {
    id: u64,
    overrides: Vec<(OsString, Option<OsString>)>,
}

struct ThreadEnvState {
    lock: Option<MutexGuard<'static, ()>>,
    next_id: u64,
    layers: Vec<EnvLayer>,
    baselines: Vec<(OsString, Option<OsString>)>,
}

impl ThreadEnvState {
    const fn new() -> Self {
        Self {
            lock: None,
            next_id: 0,
            layers: Vec::new(),
            baselines: Vec::new(),
        }
    }

    fn effective_override(&self, key: &OsStr) -> Option<Option<OsString>> {
        self.layers.iter().rev().find_map(|layer| {
            layer
                .overrides
                .iter()
                .find(|(candidate, _)| candidate == key)
                .map(|(_, value)| value.clone())
        })
    }
}

/// A lock-scoped set of process-environment overrides.
///
/// A key's ambient value is captured when the first live layer mutates it.
/// Dropping any guard removes that layer and reapplies the newest surviving
/// override, or the exact ambient value when no surviving layer touches the
/// key. This remains correct during unwinding and out-of-order explicit drops.
#[must_use = "dropping the guard immediately restores its environment overrides"]
pub(crate) struct ScopedEnv {
    id: u64,
    _not_send_or_sync: PhantomData<Rc<()>>,
}

impl ScopedEnv {
    /// Acquire the process-wide environment lock for this scope.
    pub(crate) fn new() -> Self {
        let needs_lock = PROCESS_ENV_STATE.with(|cell| cell.borrow().layers.is_empty());
        let acquired_lock = if needs_lock {
            Some(
                PROCESS_ENV_LOCK
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner),
            )
        } else {
            None
        };
        PROCESS_ENV_STATE.with(move |cell| {
            let mut state = cell.borrow_mut();
            debug_assert_eq!(state.layers.is_empty(), needs_lock);
            let id = state
                .next_id
                .checked_add(1)
                .expect("process environment guard id overflow");
            if let Some(lock) = acquired_lock {
                debug_assert!(state.lock.is_none());
                state.lock = Some(lock);
            }
            state.next_id = id;
            state.layers.push(EnvLayer {
                id,
                overrides: Vec::new(),
            });
            Self {
                id,
                _not_send_or_sync: PhantomData,
            }
        })
    }

    /// Override `key` until this guard is dropped.
    pub(crate) fn set(&mut self, key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) {
        self.set_override(
            key.as_ref().to_os_string(),
            Some(value.as_ref().to_os_string()),
        );
    }

    /// Remove `key` until this guard is dropped.
    pub(crate) fn remove(&mut self, key: impl AsRef<OsStr>) {
        self.set_override(key.as_ref().to_os_string(), None);
    }

    /// Set `key` only when it has no ambient value.
    pub(crate) fn set_if_unset(&mut self, key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) {
        let key = key.as_ref().to_os_string();
        if std::env::var_os(&key).is_none() {
            self.set(key, value);
        }
    }

    fn set_override(&mut self, key: OsString, value: Option<OsString>) {
        PROCESS_ENV_STATE.with(|cell| {
            let mut state = cell.borrow_mut();
            debug_assert!(state.lock.is_some());
            let layer_index = state
                .layers
                .iter()
                .position(|layer| layer.id == self.id)
                .expect("process environment guard layer is live");

            if state
                .baselines
                .iter()
                .all(|(candidate, _)| candidate != &key)
            {
                debug_assert!(state.layers.iter().all(|layer| {
                    layer
                        .overrides
                        .iter()
                        .all(|(candidate, _)| candidate != &key)
                }));
                state.baselines.push((key.clone(), std::env::var_os(&key)));
            }

            let layer = &mut state.layers[layer_index];
            if let Some((_, current)) = layer
                .overrides
                .iter_mut()
                .find(|(candidate, _)| candidate == &key)
            {
                *current = value;
            } else {
                layer.overrides.push((key.clone(), value));
            }

            let effective = state
                .effective_override(&key)
                .expect("the updated layer supplies an effective override");
            apply_value(&key, effective.as_deref());
        });
    }
}

impl Drop for ScopedEnv {
    fn drop(&mut self) {
        let lock = PROCESS_ENV_STATE.with(|cell| {
            let mut state = cell.borrow_mut();
            let layer_index = state
                .layers
                .iter()
                .position(|layer| layer.id == self.id)
                .expect("process environment guard layer is live at drop");
            let removed = state.layers.remove(layer_index);

            for (key, _) in removed.overrides {
                if let Some(effective) = state.effective_override(&key) {
                    apply_value(&key, effective.as_deref());
                } else {
                    let baseline_index = state
                        .baselines
                        .iter()
                        .position(|(candidate, _)| candidate == &key)
                        .expect("mutated process environment key has a baseline");
                    let (_, baseline) = state.baselines.remove(baseline_index);
                    apply_value(&key, baseline.as_deref());
                }
            }

            if state.layers.is_empty() {
                debug_assert!(state.baselines.is_empty());
                state.lock.take()
            } else {
                None
            }
        });

        // Make the release order explicit: restoration and layer removal both
        // happen before another thread can acquire the process environment lock.
        drop(lock);
    }
}

fn apply_value(key: &OsStr, value: Option<&OsStr>) {
    match value {
        Some(value) => set_var(key, value),
        None => remove_var(key),
    }
}

/// The only process-environment set call in non-test code. The custom Trust
/// lint is blessed here—not at a module or crate root—because callers hold
/// [`PROCESS_ENV_LOCK`] through [`ScopedEnv`].
#[allow(unknown_lints, env_mutation)]
fn set_var(key: &OsStr, value: &OsStr) {
    std::env::set_var(key, value);
}

/// The only process-environment remove call in non-test code. See [`set_var`].
#[allow(unknown_lints, env_mutation)]
fn remove_var(key: &OsStr) {
    std::env::remove_var(key);
}

/// Acquire the same process-wide environment lock used by ScopedEnv.
///
/// This lower-level API is retained for crate tests and small helpers that
/// create one or more ScopedEnvVar values explicitly. Do not construct a
/// ScopedEnv while holding this guard: ScopedEnv provides its own same-thread
/// re-entrancy and owns the lock for its full lifetime.
pub fn lock_env() -> MutexGuard<'static, ()> {
    PROCESS_ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// Persistently set an environment variable.
///
/// This is reserved for callers that intentionally change process-lifetime
/// configuration. Temporary overrides must use ScopedEnv or the grouped
/// helpers below.
pub fn set_persistent(key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) {
    let _lock = lock_env();
    set_var(key.as_ref(), value.as_ref());
}

/// Persistently remove an environment variable. See set_persistent.
pub fn remove_persistent(key: impl AsRef<OsStr>) {
    let _lock = lock_env();
    remove_var(key.as_ref());
}

/// One temporary environment override.
///
/// Callers must hold lock_env; the grouped helpers below do so automatically.
/// Values are retained as OsString so restoration is exact even for non-Unicode
/// ambient values.
#[must_use = "keep the guard alive for the full override scope"]
pub struct ScopedEnvVar {
    key: OsString,
    previous: Option<OsString>,
}

impl ScopedEnvVar {
    /// Set key=value for the guard's lifetime.
    pub fn set(key: &str, value: &str) -> Self {
        let key = OsString::from(key);
        let previous = std::env::var_os(&key);
        set_var(&key, OsStr::new(value));
        Self { key, previous }
    }

    /// Remove key for the guard's lifetime.
    pub fn unset(key: &str) -> Self {
        let key = OsString::from(key);
        let previous = std::env::var_os(&key);
        remove_var(&key);
        Self { key, previous }
    }
}

impl Drop for ScopedEnvVar {
    fn drop(&mut self) {
        apply_value(&self.key, self.previous.as_deref());
    }
}

/// Run f with vars set under the process-wide lock and restore every prior
/// value on return or unwind.
pub fn with_serialized_env_vars<T>(vars: &[(&str, &str)], f: impl FnOnce() -> T) -> T {
    let _lock = lock_env();
    let _guards: Vec<_> = vars
        .iter()
        .map(|(key, value)| ScopedEnvVar::set(key, value))
        .collect();
    f()
}

/// Run f with vars removed under the process-wide lock and restore every prior
/// value on return or unwind.
pub fn with_serialized_env_vars_removed<T>(vars: &[&str], f: impl FnOnce() -> T) -> T {
    let _lock = lock_env();
    let _guards: Vec<_> = vars.iter().map(|key| ScopedEnvVar::unset(key)).collect();
    f()
}

/// Restore-on-drop editor for tests that walk several states of the same key.
pub struct EnvEditor {
    saved: Vec<(OsString, Option<OsString>)>,
}

impl EnvEditor {
    fn save_once(&mut self, key: &OsStr) {
        if self.saved.iter().all(|(candidate, _)| candidate != key) {
            self.saved.push((key.to_os_string(), std::env::var_os(key)));
        }
    }

    /// Set key=value until the editor is dropped or the key is edited again.
    pub fn set(&mut self, key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) {
        let key = key.as_ref();
        self.save_once(key);
        set_var(key, value.as_ref());
    }

    /// Remove key until the editor is dropped or the key is edited again.
    pub fn remove(&mut self, key: impl AsRef<OsStr>) {
        let key = key.as_ref();
        self.save_once(key);
        remove_var(key);
    }
}

impl Drop for EnvEditor {
    fn drop(&mut self) {
        for (key, previous) in self.saved.drain(..).rev() {
            apply_value(&key, previous.as_deref());
        }
    }
}

/// Run f with exclusive restore-on-exit access through an EnvEditor.
pub fn with_env_edits<T>(f: impl FnOnce(&mut EnvEditor) -> T) -> T {
    let _lock = lock_env();
    let mut editor = EnvEditor { saved: Vec::new() };
    f(&mut editor)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc;
    use std::time::Duration;

    fn key(tag: &str) -> String {
        format!("CLEAN_SCOPED_ENV_{tag}_{}", std::process::id())
    }

    #[test]
    fn restores_absent_and_existing_values_exactly() {
        let absent = key("ABSENT");
        let existing = key("EXISTING");
        let mut baseline = ScopedEnv::new();
        baseline.remove(&absent);
        baseline.set(&existing, "ambient");

        {
            let mut overrides = ScopedEnv::new();
            overrides.set(&absent, "temporary");
            overrides.set(&existing, "changed");
            assert_eq!(
                std::env::var_os(&absent).as_deref(),
                Some(OsStr::new("temporary"))
            );
            assert_eq!(
                std::env::var_os(&existing).as_deref(),
                Some(OsStr::new("changed"))
            );
        }

        assert_eq!(std::env::var_os(&absent), None);
        assert_eq!(
            std::env::var_os(&existing).as_deref(),
            Some(OsStr::new("ambient"))
        );
    }

    #[test]
    fn nested_guards_restore_outer_then_ambient_values() {
        let key = key("NESTED");
        let mut ambient = ScopedEnv::new();
        ambient.set(&key, "ambient");
        {
            let mut outer = ScopedEnv::new();
            outer.set(&key, "outer");
            {
                let mut inner = ScopedEnv::new();
                inner.set(&key, "inner");
                assert_eq!(std::env::var(&key).expect("inner value"), "inner");
            }
            assert_eq!(std::env::var(&key).expect("outer value"), "outer");
        }
        assert_eq!(std::env::var(&key).expect("ambient value"), "ambient");
    }

    #[test]
    fn out_of_order_drop_keeps_inner_value_and_lock_until_final_scope() {
        let key = key("OUT_OF_ORDER");
        assert_eq!(
            std::env::var_os(&key),
            None,
            "the pid-qualified test key must start absent"
        );

        let mut outer = ScopedEnv::new();
        outer.set(&key, "outer");
        let mut inner = ScopedEnv::new();
        inner.set(&key, "inner");

        drop(outer);
        assert_eq!(
            std::env::var(&key).expect("inner value survives outer drop"),
            "inner",
            "removing an older layer must not overwrite a newer live layer"
        );

        let (started_tx, started_rx) = mpsc::channel();
        let (acquired_tx, acquired_rx) = mpsc::channel();
        let competitor_key = key.clone();
        let competitor = std::thread::spawn(move || {
            started_tx.send(()).expect("announce competitor");
            let _scope = ScopedEnv::new();
            acquired_tx
                .send(std::env::var_os(&competitor_key))
                .expect("announce competitor acquisition");
        });
        started_rx.recv().expect("competitor started");
        assert!(
            matches!(
                acquired_rx.recv_timeout(Duration::from_millis(50)),
                Err(mpsc::RecvTimeoutError::Timeout)
            ),
            "dropping the outer guard must not release the lock while the inner guard lives"
        );

        drop(inner);
        assert_eq!(
            acquired_rx
                .recv_timeout(Duration::from_secs(2))
                .expect("competitor acquires after final local scope"),
            None,
            "the final local scope restores the original absent baseline before unlock"
        );
        competitor.join().expect("competitor thread");
        assert_eq!(std::env::var_os(&key), None);
    }

    #[test]
    fn unwinding_restores_the_previous_value() {
        let key = key("UNWIND");
        let mut ambient = ScopedEnv::new();
        ambient.set(&key, "ambient");
        let result = std::panic::catch_unwind(|| {
            let mut overrides = ScopedEnv::new();
            overrides.set(&key, "temporary");
            panic!("exercise guard drop during unwinding");
        });
        assert!(result.is_err());
        assert_eq!(std::env::var(&key).expect("ambient value"), "ambient");
    }

    #[test]
    fn concurrent_scopes_are_serialized() {
        let key = key("SERIAL");
        assert_eq!(
            std::env::var_os(&key),
            None,
            "the pid-qualified test key must start absent"
        );

        let (first_ready_tx, first_ready_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let first_key = key.clone();
        let first = std::thread::spawn(move || {
            let mut scope = ScopedEnv::new();
            scope.set(&first_key, "first");
            first_ready_tx.send(()).expect("announce first scope");
            release_rx.recv().expect("release first scope");
        });
        first_ready_rx.recv().expect("first scope acquired");

        let (second_started_tx, second_started_rx) = mpsc::channel();
        let (second_acquired_tx, second_acquired_rx) = mpsc::channel();
        let second_key = key.clone();
        let second = std::thread::spawn(move || {
            second_started_tx.send(()).expect("announce second thread");
            let mut scope = ScopedEnv::new();
            let observed = std::env::var_os(&second_key);
            scope.set(&second_key, "second");
            second_acquired_tx
                .send(observed)
                .expect("announce second scope");
        });
        second_started_rx.recv().expect("second thread started");
        assert!(
            matches!(
                second_acquired_rx.recv_timeout(Duration::from_millis(50)),
                Err(mpsc::RecvTimeoutError::Timeout)
            ),
            "a second scope must wait for the first guard"
        );

        release_tx.send(()).expect("release first scope");
        assert_eq!(
            second_acquired_rx
                .recv_timeout(Duration::from_secs(2))
                .expect("second scope acquires after release"),
            None,
            "the first scope must restore before releasing the lock"
        );
        first.join().expect("first thread");
        second.join().expect("second thread");
    }

    #[cfg(unix)]
    #[test]
    fn env_editor_preserves_non_utf8_values_and_restores_ambient_state() {
        use std::os::unix::ffi::OsStringExt;

        let key = key("NON_UTF8");
        let ambient = std::env::var_os(&key);
        let non_utf8 = OsString::from_vec(vec![b'p', b'a', b't', b'h', 0xff]);

        with_env_edits(|env| {
            env.set(&key, &non_utf8);
            assert_eq!(
                std::env::var_os(&key).as_ref(),
                Some(&non_utf8),
                "the editor must not coerce an OsStr value through UTF-8"
            );
        });

        assert_eq!(
            std::env::var_os(&key),
            ambient,
            "the editor must restore the exact ambient value"
        );
    }
}
