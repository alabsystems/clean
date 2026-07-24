// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::time::Instant;

#[inline]
pub(crate) fn micros_to_u64(micros: u128) -> u64 {
    u64::try_from(micros).unwrap_or(u64::MAX)
}

pub(crate) fn with_stats<R, S>(
    run: impl FnOnce() -> Vec<R>,
    compute_stats: impl FnOnce(&[R], u64) -> S,
) -> (Vec<R>, S) {
    let wall_start = Instant::now();
    let results = run();
    let wall_time_us = micros_to_u64(wall_start.elapsed().as_micros());
    let stats = compute_stats(&results, wall_time_us);
    (results, stats)
}

pub(crate) fn with_thread_pool<T: Send>(num_threads: usize, run: impl FnOnce() -> T + Send) -> T {
    match rayon::ThreadPoolBuilder::new()
        .num_threads(num_threads)
        .build()
    {
        Ok(pool) => pool.install(run),
        // Pool construction only fails when the OS cannot spawn threads; fall
        // back to running on the current thread (same results, reduced
        // parallelism) rather than panicking.
        Err(_) => run(),
    }
}
