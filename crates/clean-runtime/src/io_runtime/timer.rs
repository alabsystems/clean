// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Timer operations: monoMsNow, monoNanosNow.
//!
//! These implement Lean 4's `IO.monoMsNow` and `IO.monoNanosNow` using
//! [`std::time::Instant`] relative to a process-wide epoch. The values are
//! monotonically non-decreasing and suitable for elapsed-time measurement.

use std::time::Instant;

use super::{IoError, IoRuntime, IoValue};

/// Process-wide epoch for monotonic timing.
///
/// `Instant::now()` is called once at process startup (via `lazy_static`
/// equivalent using `std::sync::OnceLock`). All subsequent timer reads
/// compute duration since this epoch.
fn epoch() -> &'static Instant {
    use std::sync::OnceLock;
    static EPOCH: OnceLock<Instant> = OnceLock::new();
    EPOCH.get_or_init(Instant::now)
}

impl IoRuntime {
    /// Get monotonic time in milliseconds since process start.
    /// Implements `IO.monoMsNow`.
    pub(super) fn exec_mono_ms_now(&self) -> Result<IoValue, IoError> {
        let elapsed = epoch().elapsed();
        let ms = elapsed.as_millis();
        // Saturate to u64::MAX if somehow the process runs for >584 million years
        let ms_u64 = u64::try_from(ms).unwrap_or(u64::MAX);
        Ok(IoValue::Nat(ms_u64))
    }

    /// Get monotonic time in nanoseconds since process start.
    /// Implements `IO.monoNanosNow`.
    pub(super) fn exec_mono_nanos_now(&self) -> Result<IoValue, IoError> {
        let elapsed = epoch().elapsed();
        let ns = elapsed.as_nanos();
        let ns_u64 = u64::try_from(ns).unwrap_or(u64::MAX);
        Ok(IoValue::Nat(ns_u64))
    }
}
