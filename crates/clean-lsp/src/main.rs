// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean LSP standalone entry point — passthrough shim.
//!
//! The canonical LSP server now lives under the unified `clean lsp`
//! subcommand (Epic #3436 Phase 3, #3450). This binary is **retained** (not
//! deprecated) because editor configurations hard-code the `clean-lsp`
//! executable path — e.g. Neovim lspconfig `cmd = { "clean-lsp" }`, VS Code
//! generic LSP clients pointing at `./target/release/clean-lsp`. Changing
//! those paths is outside our control, so the shim must keep working
//! indefinitely while the implementation consolidates into `clean lsp`.
//!
//! # Silence contract
//!
//! The shim MUST NOT emit any output to stderr during normal operation.
//! LSP clients frame JSON-RPC messages on stdin/stdout; some editors also
//! buffer, parse, or display stderr from their language-server subprocess.
//! A deprecation eprintln — like the one used by the `verify_olean_batch` /
//! `clean-discover` shims — would surface as a spurious IDE warning every
//! time the server starts. We therefore emit no banner, no deprecation
//! notice, no informational messages. Errors resolving the `clean` binary
//! are still printed to stderr because at that point there is no running
//! LSP session to corrupt.
//!
//! # Resolution order
//!
//! 1. `CLEAN_BIN` environment variable (overrides everything; useful in CI
//!    and tests).
//! 2. Sibling `clean` / `clean.exe` next to the current executable —
//!    standard Cargo layout (`target/{debug,release}/clean-lsp`).
//! 3. Bare `clean` on `PATH`.
//!
//! # Platform behavior
//!
//! On Unix we `exec` the `clean` binary in-place so the LSP client keeps
//! talking to the same PID and the stdin/stdout file descriptors pass
//! through untouched. On other platforms we `Command::status()` and
//! propagate the child exit code.
//!
//! Part of #3450. Epic: #3436. Design:
//! `designs/2026-04-18-unified-cli-feature-index.md`.

use std::env;
use std::path::PathBuf;
use std::process::{Command, ExitCode};

/// Resolve the sibling `clean` binary next to the current executable, with an
/// environment-variable override for CI and test environments.
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

/// Exec the unified `clean lsp` command with the user's argv forwarded
/// verbatim. Editors pass flags like `--stdio` which flow through unchanged.
fn run() -> std::io::Result<i32> {
    let clean = resolve_clean_binary();
    let mut argv: Vec<String> = vec!["lsp".to_owned()];
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
            // Only printed when the `clean` binary itself cannot be located
            // or exec'd. At this point no LSP session exists to corrupt.
            eprintln!("clean-lsp: failed to exec 'clean': {err}");
            eprintln!(
                "hint: set CLEAN_BIN to the path of the unified `clean` binary, \
                 ensure it is on PATH, or install it next to `clean-lsp`."
            );
            ExitCode::from(127)
        }
    }
}
