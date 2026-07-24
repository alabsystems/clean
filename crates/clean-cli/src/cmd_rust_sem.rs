// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch the `clean verify rust` subcommand into the `clean-rust-sem`
//! library's CLI module.
//!
//! The actual argument parsing (clap derives), example pipeline, and
//! descriptor registration live in [`clean_rust_sem::cli`]. This wrapper
//! exists only to convert the typed
//! [`RustSemCliError`](clean_rust_sem::cli::RustSemCliError) into `anyhow`
//! context for the top-level CLI dispatcher (see `lib.rs::dispatch_sync`).
//!
//! Part of Epic #3436 (#3451): nests the Rust verification surface under a
//! top-level `verify` aggregator so future language migrations (`verify c`,
//! …) can drop in without reshaping the clap tree.

use clean_rust_sem::cli::{run as rust_sem_run, RustVerifyArgs};

/// Entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_rust_verify_command(args: RustVerifyArgs) -> anyhow::Result<()> {
    rust_sem_run(args).map_err(anyhow::Error::from)
}
