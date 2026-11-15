// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch certificate verification helpers.

mod build;
mod build_types;
mod common;
mod runner;
mod verify;

pub use build::{
    batch_build_verify, batch_build_verify_sequential, batch_build_verify_sequential_with_stats,
    batch_build_verify_with_stats, batch_build_verify_with_stats_progress,
    batch_build_verify_with_stats_threads, batch_build_verify_with_threads,
};
pub use build_types::{BatchBuildInput, BatchBuildResult, BatchBuildStats, BuilderFn};
pub use runner::{BatchBuildVerifier, BatchVerifier};
pub use verify::{
    batch_verify, batch_verify_sequential, batch_verify_sequential_with_stats,
    batch_verify_with_stats, batch_verify_with_threads, BatchVerifyInput, BatchVerifyResult,
    BatchVerifyStats,
};
// Crate-internal since 2026-10-15: `BatchVerifier` (`with_progress`, `with_threads`) is how
// callers outside the kernel reach them, and none called them directly.
#[cfg(test)]
pub(crate) use verify::{batch_verify_with_stats_progress, batch_verify_with_stats_threads};
