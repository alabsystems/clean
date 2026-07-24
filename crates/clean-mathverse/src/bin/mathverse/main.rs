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

use std::path::PathBuf;

use clean_mathverse::build_library::load_built_library;
use clean_mathverse::library::MathverseLibrary;

use crate::cli::Cli;

fn main() {
    let cli = Cli::parse_args();
    cli::dispatch(cli);
}

/// Discover the mathverse library directory. Checks:
/// 1. $MATHVERSE_LIBRARY_PATH
/// 2. ./data/mathverse-library/
/// 3. $HOME/.mathverse/library/
pub(crate) fn discover_library_path() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("MATHVERSE_LIBRARY_PATH") {
        let p = PathBuf::from(path);
        if p.is_dir() {
            return Some(p);
        }
    }
    let local = PathBuf::from("data/mathverse-library");
    if local.is_dir() {
        return Some(local);
    }
    if let Ok(home) = std::env::var("HOME") {
        let home_path = PathBuf::from(home).join(".mathverse/library");
        if home_path.is_dir() {
            return Some(home_path);
        }
    }
    None
}

/// Load the mathverse library or print a helpful error and exit.
pub(crate) fn load_library() -> MathverseLibrary {
    let path = match discover_library_path() {
        Some(p) => p,
        None => {
            eprintln!("Error: Mathverse library not found.");
            eprintln!();
            eprintln!("Searched:");
            eprintln!("  1. $MATHVERSE_LIBRARY_PATH (not set or not a directory)");
            eprintln!("  2. ./data/mathverse-library/ (not found)");
            if let Ok(home) = std::env::var("HOME") {
                eprintln!("  3. {}/.mathverse/library/ (not found)", home);
            } else {
                eprintln!("  3. $HOME/.mathverse/library/ ($HOME not set)");
            }
            eprintln!();
            eprintln!(
                "Run `mathverse download` to fetch the library, or set MATHVERSE_LIBRARY_PATH."
            );
            std::process::exit(1);
        }
    };
    match load_built_library(&path) {
        Ok(lib) => lib,
        Err(e) => {
            eprintln!("Error loading library from {}: {e}", path.display());
            std::process::exit(1);
        }
    }
}
