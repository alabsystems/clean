// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compatibility shim for the legacy `verify_olean_batch` binary.
//!
//! Part of Epic #3436 (Phase 3, #3441). The canonical entry point now lives
//! under `clean olean verify-batch` in the unified `clean` CLI. This shim
//! exists to keep external scripts that still shell out to
//! `verify_olean_batch` working for one release: it prints a deprecation
//! notice on stderr and exec's `clean olean verify-batch <args…>` with the
//! user's arguments forwarded verbatim.

use std::env;
use std::path::PathBuf;
use std::process::{Command, ExitCode};

const DEPRECATION_NOTICE: &str =
    "warning: `verify_olean_batch` is deprecated — use `clean olean verify-batch` instead. \
     The legacy binary will be removed after the next release. See Epic #3436 / #3441.";

/// Resolve the sibling `clean` binary next to the current executable, falling
/// back to PATH resolution. Callers can override via the `CLEAN_BIN`
/// environment variable — useful in CI or in-tree `cargo run` flows.
fn resolve_clean_binary() -> PathBuf {
    if let Ok(explicit) = env::var("CLEAN_BIN") {
        return PathBuf::from(explicit);
    }
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
    let mut argv: Vec<String> = vec!["olean".to_owned(), "verify-batch".to_owned()];
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
        if let Some(code) = status.code() {
            Ok(code)
        } else {
            Ok(1)
        }
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => ExitCode::from(u8::try_from(code).unwrap_or(1)),
        Err(err) => {
            eprintln!("verify_olean_batch: failed to exec 'clean': {err}");
            eprintln!(
                "hint: set CLEAN_BIN to the path of the unified `clean` binary, \
                 or run `cargo run -p clean-cli -- olean verify-batch <args…>` directly."
            );
            ExitCode::from(127)
        }
    }
}
