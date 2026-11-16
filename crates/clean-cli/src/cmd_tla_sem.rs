// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch the `clean verify tla` subcommand into the `clean-tla`
//! library's CLI module.
//!
//! The actual argument parsing (clap derives), obligation pipeline, and
//! descriptor registration live in [`clean_tla::cli`]. This wrapper exists
//! only to convert the typed [`TlaCliError`](clean_tla::cli::TlaCliError)
//! into `anyhow` context for the top-level CLI dispatcher (see
//! `lib.rs::dispatch_sync`).
//!
//! Part of Epic #3436 Phase 4 (#3452): exposes the TLA+ obligation
//! automation as a sibling of `verify rust` under the `verify` verb tree.

use clean_tla::cli::{run as tla_run, TlaVerifyArgs};

/// Entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_tla_verify_command(args: TlaVerifyArgs) -> anyhow::Result<()> {
    tla_run(args).map_err(anyhow::Error::from)
}
