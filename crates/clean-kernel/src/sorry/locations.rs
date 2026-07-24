// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Location tracking for sorry and trustedAy creation sites.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Mutex;

thread_local! {
    /// Stack of override keys for sorry location recording.
    /// When non-empty, `record_sorry_location()` uses the top key instead of
    /// `file:line`. Nested calls push/pop correctly.
    static SORRY_LOCATION_KEY_STACK: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
}

struct SorryLocationKeyGuard;

impl Drop for SorryLocationKeyGuard {
    fn drop(&mut self) {
        SORRY_LOCATION_KEY_STACK.with(|stack| {
            let popped = stack.borrow_mut().pop();
            debug_assert!(
                popped.is_some(),
                "with_sorry_location_key guard dropped with empty stack"
            );
        });
    }
}

/// Execute `f` while recording sorry locations under `key` instead of
/// the raw `file:line` caller location. Nest-safe: inner calls push
/// their own key and restore the outer one on return, even if `f` panics.
pub fn with_sorry_location_key<T>(key: &'static str, f: impl FnOnce() -> T) -> T {
    SORRY_LOCATION_KEY_STACK.with(|stack| stack.borrow_mut().push(key));
    let _guard = SorryLocationKeyGuard;
    f()
}

/// Tracks trustedAy caller locations by file:line.
static AY_LOCATIONS: Mutex<Option<HashMap<String, u64>>> = Mutex::new(None);

/// Initialize trustedAy location tracking.
pub fn enable_ay_location_tracking() {
    if let Ok(mut guard) = AY_LOCATIONS.lock() {
        if guard.is_none() {
            *guard = Some(HashMap::new());
        }
    }
}

/// Record a trustedAy term at a specific caller location.
///
/// Auto-initializes the location map on first call so that callers before
/// `enable_ay_location_tracking()` are still recorded. Without this, the
/// ratchet test (which calls `enable_ay_location_tracking` at assertion
/// time) misses all locations from earlier tests in a single-threaded run.
#[track_caller]
pub(crate) fn record_ay_location() {
    let caller = std::panic::Location::caller();
    let location = format!("{}:{}", caller.file(), caller.line());

    if let Ok(mut guard) = AY_LOCATIONS.lock() {
        let map = guard.get_or_insert_with(HashMap::new);
        *map.entry(location).or_insert(0) += 1;
    }
}

/// Get trustedAy caller locations and counts.
pub fn ay_locations() -> Option<HashMap<String, u64>> {
    AY_LOCATIONS.lock().ok().and_then(|guard| guard.clone())
}

/// Tracks sorry term locations by caller location.
/// Key: caller location string (file:line), Value: count at that location.
static SORRY_LOCATIONS: Mutex<Option<HashMap<String, u64>>> = Mutex::new(None);

/// Initialize sorry location tracking.
/// Call this to enable detailed sorry location tracking.
/// If not called, locations are not tracked (for performance).
pub fn enable_sorry_location_tracking() {
    if let Ok(mut guard) = SORRY_LOCATIONS.lock() {
        if guard.is_none() {
            *guard = Some(HashMap::new());
        }
    }
}

/// Record a sorry term at a specific location.
/// Auto-initializes location tracking on first call so the census always
/// captures caller data without requiring explicit `enable_sorry_location_tracking()`.
///
/// When a `with_sorry_location_key` override is active on this thread, the
/// override key is recorded instead of the raw `file:line` caller location.
#[track_caller]
pub(crate) fn record_sorry_location() {
    let location = SORRY_LOCATION_KEY_STACK.with(|stack| {
        let s = stack.borrow();
        if let Some(key) = s.last() {
            (*key).to_string()
        } else {
            let caller = std::panic::Location::caller();
            format!("{}:{}", caller.file(), caller.line())
        }
    });

    if let Ok(mut guard) = SORRY_LOCATIONS.lock() {
        let map = guard.get_or_insert_with(HashMap::new);
        *map.entry(location).or_insert(0) += 1;
    }
}

/// Get sorry term locations and counts.
/// Returns None if location tracking was not enabled.
/// Returns Some(map) with file:line -> count entries.
pub fn sorry_locations() -> Option<HashMap<String, u64>> {
    SORRY_LOCATIONS.lock().ok().and_then(|guard| guard.clone())
}

/// Reset sorry location tracking.
pub fn reset_sorry_locations() {
    if let Ok(mut guard) = SORRY_LOCATIONS.lock() {
        if let Some(ref mut map) = *guard {
            map.clear();
        }
    }
}
