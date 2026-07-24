// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lsp` — unified CLI surface for the clean Language Server.
//!
//! This module exposes the clap argument struct, the descriptor array used by
//! `clean features` / `clean help`, and the async dispatch entry point
//! [`run`]. It absorbs the standalone `clean-lsp` binary into the top-level
//! `clean` CLI per Epic #3436 Phase 3 (#3450).
//!
//! | Old binary                          | New CLI path                |
//! |-------------------------------------|-----------------------------|
//! | `clean-lsp` (stdio LSP server)      | `clean lsp [--stdio]`       |
//! | `clean-lsp` (TCP LSP server, test)  | `clean lsp --tcp <addr>`    |
//!
//! The standalone `clean-lsp` binary is **retained** as a thin passthrough
//! shim because editor configurations hard-code its path. The shim re-exec's
//! `clean lsp` with identical arguments, so `cmd = { "clean-lsp" }` clients
//! keep working while the canonical entry point lives under the unified CLI.
//!
//! Unlike the deprecation shims absorbed by #3441/#3442/#3449 (which eprintln
//! a deprecation notice), the LSP shim runs silently: LSP uses stdio for the
//! JSON-RPC protocol and any stderr chatter during startup can confuse
//! editor clients that buffer/parse both streams.
//!
//! The module is gated behind the `cli` Cargo feature so non-CLI consumers of
//! `clean-lsp` (the library API used by test harnesses and in-process
//! integrations) keep a minimal dependency graph (no clap, no
//! `clean-features`).
//!
//! Part of #3450. Epic: #3436. Design:
//! `designs/2026-04-18-unified-cli-feature-index.md`.

use clap::Args;
use clean_features::FeatureDescriptor;

mod descriptors;

pub use descriptors::FEATURES;

/// `clean lsp` argument surface.
///
/// The legacy `clean-lsp` binary takes no arguments and reads/writes the LSP
/// protocol over stdin/stdout. `--stdio` is accepted for forward compatibility
/// with editor launch scripts that pass the flag explicitly (the default LSP
/// convention in VS Code's generic client and several Neovim configurations).
///
/// `--tcp <addr>` exposes the existing [`crate::run_server_tcp`] entry point
/// for integration-testing clients and IDE configurations that prefer a TCP
/// transport over stdio.
#[derive(Debug, Clone, Args)]
pub struct LspArgs {
    /// Explicitly request stdio transport (default; accepted for
    /// forward-compatibility with editor launch scripts).
    #[arg(long, conflicts_with = "tcp")]
    pub stdio: bool,

    /// Bind a TCP listener on this address instead of serving over stdio.
    /// Intended for integration tests and development tooling.
    #[arg(long, value_name = "ADDR")]
    pub tcp: Option<String>,
}

// -- Errors -------------------------------------------------------------------

/// Errors surfaced by `clean lsp` dispatch.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum LspCliError {
    /// TCP transport bind/accept failed.
    #[error("LSP TCP transport failed: {0}")]
    Tcp(#[from] std::io::Error),
}

// -- Entry points -------------------------------------------------------------

/// Dispatch entry point for `clean lsp`.
///
/// The top-level `clean-cli` binary constructs the clap args via its own
/// parser and awaits the resulting future. Stdio mode runs the LSP server
/// until the client closes stdin; TCP mode runs until the listener accept
/// loop returns an error.
pub async fn run(args: LspArgs) -> Result<(), LspCliError> {
    if let Some(addr) = args.tcp.as_deref() {
        crate::run_server_tcp(addr).await?;
        return Ok(());
    }
    // `--stdio` (or no transport flag) → default stdio transport.
    crate::run_server().await;
    Ok(())
}

/// Compile-time assertion that [`FEATURES`] is non-empty. Guards against
/// accidentally shipping an empty descriptor array, which would silently
/// disappear from `clean features` without any drift-test failure.
const _: () = {
    assert!(
        !FEATURES.is_empty(),
        "clean-lsp cli must expose at least one FeatureDescriptor"
    );
    let _: &[FeatureDescriptor] = FEATURES;
};

#[cfg(test)]
mod tests;
