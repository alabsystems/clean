// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Library-hosted command implementations for the `mathverse` CLI.
//!
//! Originally lived under `src/bin/mathverse/` as binary-private modules. Moved
//! into the library under Epic #3436 / issue #3512 so the same functions can
//! be invoked from both the standalone `mathverse` binary AND the unified
//! `clean mathverse <verb>` clap dispatch (see [`crate::cli::dispatch`]).
//!
//! All `cmd_*` functions retain their original ad-hoc `&[String]` argv
//! signature and their `std::process::exit` behavior on error. The standalone
//! binary calls them directly; the unified CLI reconstructs an argv vector
//! from its parsed clap args and calls them the same way.

pub mod commands;
pub mod fmt;

use std::path::PathBuf;

use crate::build_library::load_built_library;
use crate::library::MathverseLibrary;

/// Discover the mathverse library directory. Checks:
/// 1. $MATHVERSE_LIBRARY_PATH
/// 2. ./data/mathverse-library/
/// 3. $HOME/.mathverse/library/
pub fn discover_library_path() -> Option<PathBuf> {
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
pub fn load_library() -> MathverseLibrary {
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
