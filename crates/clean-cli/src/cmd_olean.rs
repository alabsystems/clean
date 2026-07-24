// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch the `clean olean <verb>` subcommand into the `clean-olean`
//! library's CLI module.
//!
//! The actual argument parsing (clap derives), overlay generation, batch
//! verification, and library access live in [`clean_olean::cli`]. This
//! wrapper exists only to convert the typed
//! [`OleanCliError`](clean_olean::cli::OleanCliError) into `anyhow` context
//! for the top-level CLI dispatcher (see `lib.rs::dispatch_sync`).
//!
//! Part of Epic #3436: absorbs the deprecated standalone `.olean` binaries
//! (`generate_namespace_overlay` per #3442, `verify_olean_batch` per #3441)
//! into the unified `clean` CLI surface via a single `OleanCommands` enum.

use clean_olean::cli::{run as olean_run, OleanArgs};

/// Entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_olean_command(args: OleanArgs) -> anyhow::Result<()> {
    olean_run(args).map_err(anyhow::Error::from)
}
