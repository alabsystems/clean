// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scheduling for checked stub upgrades; no kernel-checking policy lives here.

use std::ffi::OsStr;
use std::sync::OnceLock;

/// Match the checking thread's stack. This reserves address space, not RAM.
const WORKER_STACK_SIZE: usize = 1024 * 1024 * 1024;

/// Both positive counts are upper bounds, never permission to exceed hardware.
/// Admission supplies a positive decimal CARGO_BUILD_JOBS; malformed admission
/// selects the existing serial path. Rayon retains its zero/invalid auto default.
pub(super) fn worker_count(
    available: usize,
    cargo_jobs: Option<&OsStr>,
    rayon_threads: Option<&OsStr>,
) -> usize {
    let available = available.max(1);
    let cargo_cap = cargo_jobs.map_or(available, |raw| {
        raw.to_str()
            .filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
            .and_then(|s| s.parse::<usize>().ok())
            .filter(|cap| *cap > 0)
            .unwrap_or(1)
    });
    let rayon_cap = rayon_threads
        .and_then(OsStr::to_str)
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|cap| *cap > 0)
        .unwrap_or(available);
    available.min(cargo_cap).min(rayon_cap)
}

/// Snapshot the admitted budget on first use, as with the pool itself. A
/// one-worker budget or failed pool construction uses the unchanged serial path.
pub(super) fn pool() -> Option<&'static rayon::ThreadPool> {
    static POOL: OnceLock<Option<rayon::ThreadPool>> = OnceLock::new();
    POOL.get_or_init(|| {
        let threads = worker_count(
            std::thread::available_parallelism().map_or(1, usize::from),
            std::env::var_os("CARGO_BUILD_JOBS").as_deref(),
            std::env::var_os("RAYON_NUM_THREADS").as_deref(),
        );
        if threads < 2 {
            return None;
        }
        rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .stack_size(WORKER_STACK_SIZE)
            .thread_name(|i| format!("clean-stub-check-{i}"))
            .build()
            .ok()
    })
    .as_ref()
}
