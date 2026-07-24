// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean-discover` deprecation shim.
//!
//! The canonical entry point for AI-driven proof discovery is now
//! `clean discover` (dispatched by the unified `clean` binary). This
//! shim preserves the historical `clean-discover` binary name so
//! existing scripts keep running, prints a one-line deprecation notice
//! to stderr, and then re-exec's the `clean` binary with `discover`
//! prepended to argv.
//!
//! Part of #3449. Epic: #3436.

use std::env;
use std::path::PathBuf;
use std::process::{Command, ExitCode};

const DEPRECATION_NOTICE: &str =
    "clean-discover is deprecated; use 'clean discover' — will be removed in a future release";

/// Resolve the sibling `clean` binary next to the current executable,
/// falling back to PATH resolution.
fn resolve_clean_binary() -> PathBuf {
    if let Ok(current) = env::current_exe() {
        if let Some(dir) = current.parent() {
            let candidate = dir.join(if cfg!(windows) { "clean.exe" } else { "clean" });
            if candidate.is_file() {
                return candidate;
            }
        }
    }
    PathBuf::from("clean")
}

fn run() -> std::io::Result<i32> {
    eprintln!("{DEPRECATION_NOTICE}");

    let clean = resolve_clean_binary();
    let mut argv: Vec<String> = vec!["discover".to_string()];
    argv.extend(env::args().skip(1));

    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        let err = Command::new(&clean).args(&argv).exec();
        Err(err)
    }

    #[cfg(not(unix))]
    {
        let status = Command::new(&clean).args(&argv).status()?;
        Ok(status.code().unwrap_or(1))
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => ExitCode::from(u8::try_from(code).unwrap_or(1)),
        Err(err) => {
            eprintln!("clean-discover: failed to exec 'clean': {err}");
            ExitCode::from(127)
        }
    }
}
