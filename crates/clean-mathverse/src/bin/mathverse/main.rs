// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse Library CLI — search, browse, inspect, and manage the library.
//!
//! Primary user-facing CLI for the Mathverse Library. Provides search, listing,
//! inspection, statistics, and download capabilities across the unified
//! verified mathematics corpus.
//!
//! Argument parsing is built on `clap` (derive API) for uniform `--help`
//! output and shell completion generation via `clap_complete`. Subcommands
//! forward any remaining positional / flag arguments to the per-command
//! handlers in `commands::*`, which parse them as before. This preserves all
//! historical flag behavior while giving the CLI a single help surface and a
//! `completion <shell>` subcommand (see #3472).

mod cli;

// Re-export the library-side `mathverse_bin_cmds::commands` module under the crate
// root so `crate::commands::*` paths in `cli.rs` resolve without duplicating
// subcommand handlers. The command implementations live in
// `clean_mathverse::mathverse_bin_cmds::commands` so both this binary and the unified
// `clean mathverse <verb>` dispatch (#3512) share a single source of truth.
pub(crate) use clean_mathverse::mathverse_bin_cmds::commands;

use crate::cli::Cli;

fn main() {
    let cli = Cli::parse_args();
    cli::dispatch(cli);
}
