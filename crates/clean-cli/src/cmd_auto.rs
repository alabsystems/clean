// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch the `clean auto prove` / `clean auto premise` subcommands into the `clean-auto`
//! library's CLI module.
//!
//! The actual argument parsing (clap derives), demo catalog, and descriptor
//! registration live in [`clean_auto::cli`]. These wrappers exist only to
//! convert the typed automation CLI errors into `anyhow` context for the
//! top-level CLI dispatcher (see `lib.rs::dispatch_sync`).
//!
//! Part of Epic #3436 (#3454): nests the automation surface under a
//! top-level `auto` aggregator so future automation verbs (`auto premise`,
//! `auto smt`, …) can drop in without reshaping the clap tree.

use clean_auto::cli::{run as auto_run, run_premise, AutoProveArgs, PremiseArgs};

/// Entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_auto_prove_command(args: AutoProveArgs) -> anyhow::Result<()> {
    auto_run(args).map_err(anyhow::Error::from)
}

/// Entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_auto_premise_command(args: PremiseArgs) -> anyhow::Result<()> {
    run_premise(args).map_err(anyhow::Error::from)
}
