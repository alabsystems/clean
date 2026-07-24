// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Counters and policy for sorry/trusted proof accounting.

use std::cell::Cell;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Once;

use super::kind::SorryKind;

/// Global counter for sorry term generation.
/// Tracks how many times any sorry term was created.
pub(crate) static SORRY_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Lifetime counter — monotonically increases, never reset.
/// Used by sorry_census to get true cumulative count regardless of test resets.
pub(crate) static SORRY_LIFETIME_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Global counter for explicit/user sorry creation.
pub(crate) static EXPLICIT_SORRY_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Lifetime explicit sorry counter.
pub(crate) static EXPLICIT_SORRY_LIFETIME_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Global counter for synthetic/internal sorry creation.
pub(crate) static SYNTHETIC_SORRY_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Lifetime synthetic sorry counter.
pub(crate) static SYNTHETIC_SORRY_LIFETIME_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Global counter for Ay trusted proof generation.
/// Tracks how many times a trustedAy term was created (across all crates).
/// Centralized here so clean-auto and clean-elab share the same counter.
pub(crate) static AY_PROOF_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Lifetime counter for Ay trusted proof generation — monotonically increases, never reset.
/// Used by trusted_ratchet to get true cumulative count regardless of test resets.
pub(crate) static AY_LIFETIME_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Counter for Ay proof reconstruction failures (#2186).
pub(crate) static AY_RECONSTRUCTION_FAILURE_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Counter for bridge reconstruction successes (#2395).
/// Tracks how many Ay-proved goals were reconstructed into kernel proofs,
/// avoiding trustedAy axioms entirely.
pub(crate) static AY_RECONSTRUCTION_SUCCESS_COUNTER: AtomicU64 = AtomicU64::new(0);

thread_local! {
    /// Per-thread view of reconstruction successes for stable parallel-test assertions.
    static LOCAL_AY_RECONSTRUCTION_SUCCESS_COUNTER: Cell<u64> = const { Cell::new(0) };
}

/// Reset the sorry counter to zero.
/// Call this at the start of tests to isolate sorry tracking.
///
/// # Thread Safety
/// In parallel tests, another thread may increment the counter between
/// reset and your assertions. Consider taking `crate::test_utils::serial_test_guard()`
/// for strict testing.
pub fn reset_sorry_counter() {
    SORRY_COUNTER.store(0, Ordering::SeqCst);
    EXPLICIT_SORRY_COUNTER.store(0, Ordering::SeqCst);
    SYNTHETIC_SORRY_COUNTER.store(0, Ordering::SeqCst);
}

/// Get the current sorry count.
///
/// Returns the total number of sorry terms generated since the last reset
/// (or since program start if never reset).
pub fn sorry_count() -> u64 {
    SORRY_COUNTER.load(Ordering::SeqCst)
}

/// Get the current explicit sorry count.
pub fn explicit_sorry_count() -> u64 {
    EXPLICIT_SORRY_COUNTER.load(Ordering::SeqCst)
}

/// Get the current synthetic sorry count.
pub fn synthetic_sorry_count() -> u64 {
    SYNTHETIC_SORRY_COUNTER.load(Ordering::SeqCst)
}

/// Get the lifetime sorry count (never reset).
///
/// Returns the total number of sorry terms generated since program start.
/// Unlike `sorry_count()`, this is not affected by `reset_sorry_counter()`.
pub fn sorry_lifetime_count() -> u64 {
    SORRY_LIFETIME_COUNTER.load(Ordering::SeqCst)
}

pub(crate) fn record_sorry_creation(kind: SorryKind) {
    SORRY_COUNTER.fetch_add(1, Ordering::SeqCst);
    SORRY_LIFETIME_COUNTER.fetch_add(1, Ordering::SeqCst);
    match kind {
        SorryKind::Explicit => {
            EXPLICIT_SORRY_COUNTER.fetch_add(1, Ordering::SeqCst);
            EXPLICIT_SORRY_LIFETIME_COUNTER.fetch_add(1, Ordering::SeqCst);
        }
        SorryKind::Synthetic => {
            SYNTHETIC_SORRY_COUNTER.fetch_add(1, Ordering::SeqCst);
            SYNTHETIC_SORRY_LIFETIME_COUNTER.fetch_add(1, Ordering::SeqCst);
        }
    }
}

/// Reset the Ay proof counter to zero.
/// Call this at the start of tests to isolate Ay proof tracking.
pub fn reset_ay_counter() {
    AY_PROOF_COUNTER.store(0, Ordering::SeqCst);
}

/// Get the current Ay proof count.
///
/// Returns the total number of Ay trusted proofs generated since the last reset
/// (or since program start if never reset).
pub fn ay_proof_count() -> u64 {
    AY_PROOF_COUNTER.load(Ordering::SeqCst)
}

/// Get the lifetime Ay proof count (never reset).
///
/// Returns the total number of Ay trusted proofs generated since program start.
/// Unlike `ay_proof_count()`, this is not affected by `reset_ay_counter()`.
pub fn ay_lifetime_count() -> u64 {
    AY_LIFETIME_COUNTER.load(Ordering::SeqCst)
}

pub(crate) fn record_ay_creation() {
    AY_PROOF_COUNTER.fetch_add(1, Ordering::SeqCst);
    AY_LIFETIME_COUNTER.fetch_add(1, Ordering::SeqCst);
}

/// Reset the Ay reconstruction failure counter to zero.
pub fn reset_ay_reconstruction_failure_counter() {
    AY_RECONSTRUCTION_FAILURE_COUNTER.store(0, Ordering::SeqCst);
}

/// Get the Ay reconstruction failure count (ill-typed proof terms that fell back to trustedAy).
pub fn ay_reconstruction_failure_count() -> u64 {
    AY_RECONSTRUCTION_FAILURE_COUNTER.load(Ordering::SeqCst)
}

/// Record a Ay reconstruction failure.
pub fn record_ay_reconstruction_failure() {
    AY_RECONSTRUCTION_FAILURE_COUNTER.fetch_add(1, Ordering::SeqCst);
}

/// Reset the Ay reconstruction success counter to zero.
pub fn reset_ay_reconstruction_success_counter() {
    AY_RECONSTRUCTION_SUCCESS_COUNTER.store(0, Ordering::SeqCst);
    reset_local_ay_reconstruction_success_counter();
}

/// Get the Ay reconstruction success count (goals reconstructed without trustedAy).
pub fn ay_reconstruction_success_count() -> u64 {
    AY_RECONSTRUCTION_SUCCESS_COUNTER.load(Ordering::SeqCst)
}

/// Reset the current thread's view of reconstruction successes.
///
/// Parallel Rust tests share the process-global counter, so tests that need
/// exact per-test assertions should use this local view instead of resetting
/// global state that other threads may be updating concurrently.
pub fn reset_local_ay_reconstruction_success_counter() {
    LOCAL_AY_RECONSTRUCTION_SUCCESS_COUNTER.with(|count| count.set(0));
}

/// Get the current thread's reconstruction success count.
///
/// This only reports successes recorded on the calling thread and is intended
/// for deterministic test assertions inside parallel suites.
pub fn local_ay_reconstruction_success_count() -> u64 {
    LOCAL_AY_RECONSTRUCTION_SUCCESS_COUNTER.with(Cell::get)
}

/// Record a Ay reconstruction success (#2395).
pub fn record_ay_reconstruction_success() {
    AY_RECONSTRUCTION_SUCCESS_COUNTER.fetch_add(1, Ordering::SeqCst);
    LOCAL_AY_RECONSTRUCTION_SUCCESS_COUNTER.with(|count| {
        count.set(count.get().saturating_add(1));
    });
}

/// Assert that no sorry terms were generated since the last reset.
/// Panics with a descriptive message if any sorry terms were created.
///
/// # Thread Safety
/// In parallel tests, sorry terms from other threads may trigger this assert.
/// For strict testing, ensure tests using this are run serially.
#[track_caller]
pub fn assert_no_sorry() {
    let count = sorry_count();
    assert!(
        count == 0,
        "Expected no sorry terms, but {} sorry term(s) were generated. \
         This indicates incomplete proof reconstruction.",
        count
    );
}

/// Cached DENY_SORRY mode flag (initialized once on first access).
static DENY_SORRY_CHECKED: Once = Once::new();
static DENY_SORRY_ENABLED: AtomicBool = AtomicBool::new(false);

/// Check if DENY_SORRY mode is enabled.
/// When set to "1" or "true", sorry term creation will panic.
/// Enable via: `DENY_SORRY=1 cargo test`
///
/// The result is cached on first call to avoid repeated env var lookups.
pub fn deny_sorry_enabled() -> bool {
    DENY_SORRY_CHECKED.call_once(|| {
        let enabled = std::env::var("DENY_SORRY")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false);
        DENY_SORRY_ENABLED.store(enabled, Ordering::SeqCst);
    });
    DENY_SORRY_ENABLED.load(Ordering::SeqCst)
}
