// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean-cli` deprecation shim.
//!
//! The canonical binary is now `clean` (owned by the `clean` package). This
//! shim preserves the historical `clean-cli` name so existing invocations keep
//! working, prints a one-line deprecation notice to stderr, and then re-exec's
//! the `clean` binary with the same argv, preserving the exit code.
//!
//! Part of #3438, Epic #3436.

use std::env;
use std::path::PathBuf;
use std::process::{Command, ExitCode};

const DEPRECATION_NOTICE: &str =
    "clean-cli is deprecated; use 'clean' — will be removed in a future release";

/// Resolve the sibling `clean` binary next to the current executable, falling
/// back to PATH resolution.
fn resolve_clean_binary() -> PathBuf {
    if let Ok(current) = env::current_exe() {
        if let Some(dir) = current.parent() {
            let candidate = dir.join(if cfg!(windows) { "clean.exe" } else { "clean" });
            if candidate.is_file() {
                return candidate;
            }
        }
    }
    // Fall back to PATH lookup; Command::new("clean") will use it.
    PathBuf::from("clean")
}

fn run() -> std::io::Result<i32> {
    eprintln!("{DEPRECATION_NOTICE}");

    let clean = resolve_clean_binary();
    let argv: Vec<String> = env::args().skip(1).collect();

    // On Unix, prefer exec so the child replaces the process image; this gives
    // the child direct ownership of the terminal and signals, and collapses
    // the argv[0] back to `clean` for any diagnostics.
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        let err = Command::new(&clean).args(&argv).exec();
        // `exec` only returns on failure.
        Err(err)
    }

    // Portable fallback (Windows): spawn the child, forward exit code.
    #[cfg(not(unix))]
    {
        let status = Command::new(&clean).args(&argv).status()?;
        if let Some(code) = status.code() {
            return Ok(code);
        }
        // Terminated by signal (unreachable on Windows, but preserve behaviour).
        return Ok(1);
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => {
            // Clamp to u8 for ExitCode; non-representable codes fall back to 1.
            ExitCode::from(u8::try_from(code).unwrap_or(1))
        }
        Err(err) => {
            eprintln!("clean-cli: failed to exec 'clean': {err}");
            ExitCode::from(127)
        }
    }
}
