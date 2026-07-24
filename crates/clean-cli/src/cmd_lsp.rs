// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch the `clean lsp` subcommand into the `clean-lsp` library's CLI
//! module.
//!
//! The actual argument parsing (clap derives), stdio/TCP server routing, and
//! LSP protocol implementation live in [`clean_lsp::cli`] and
//! [`clean_lsp`]. This wrapper exists only to convert the typed
//! [`LspCliError`](clean_lsp::cli::LspCliError) into `anyhow` context for the
//! top-level async CLI dispatcher (see `lib.rs::run`).
//!
//! Part of Epic #3436 Phase 3 (#3450): absorbs the standalone `clean-lsp`
//! binary under `clean lsp`. The standalone binary is retained as a
//! passthrough shim because editor configurations hard-code its path.

use clean_lsp::cli::{run as lsp_run, LspArgs};

/// Async entry point wired from `run()` in `lib.rs`.
///
/// The top-level CLI runs inside `#[tokio::main]`, so the LSP server can be
/// awaited directly without constructing a nested runtime.
pub(crate) async fn handle_lsp_command(args: LspArgs) -> anyhow::Result<()> {
    lsp_run(args).await.map_err(anyhow::Error::from)
}
