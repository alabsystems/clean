// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean Language Server Protocol implementation
//!
//! This crate provides an LSP server for clean, enabling IDE support for:
//! - Real-time parse error diagnostics
//! - Type error diagnostics
//! - Hover information (types, documentation)
//! - Go to definition
//! - Find references
//! - Document symbols
//! - Code completion
//! - Lean4-compatible RPC endpoints for infoview (`$/lean/rpc/*`)
//! - Direct goal methods (`$/lean/plainGoal`, `$/lean/plainTermGoal`)
//!
//! # Architecture
//!
//! The server uses `tower-lsp` for the LSP framework with async/await.
//! Document state is managed incrementally using `ropey` for efficient
//! text rope operations.
//!
//! # Example
//!
//! ```text
//! use clean_lsp::run_server;
//!
//! #[tokio::main]
//! async fn main() {
//!     run_server().await;
//! }
//! ```

pub mod backend;
pub mod diagnostics;
pub mod document;
pub mod report_validation;
pub mod rpc;

/// Unified `clean lsp` CLI surface.
///
/// Gated behind the `cli` feature so non-CLI consumers of `clean-lsp`
/// (test harnesses, the library API) do not pay for clap + `clean-features`
/// unless they opt in. Registered by `clean-cli`'s `registry.rs` via
/// `v.extend(clean_lsp::cli::FEATURES)` — part of Epic #3436 Phase 3
/// (#3450).
#[cfg(feature = "cli")]
pub mod cli;

pub use backend::CleanBackend;
pub use document::Document;
pub use rpc::{
    PlainGoalParams, PlainGoalResponse, PlainTermGoalParams, PlainTermGoalResponse, RpcCallParams,
    RpcConnectParams, RpcConnected, RpcKeepAliveParams, RpcReleaseParams, RpcSessionManager,
};

// Domain-prefixed alias for collision-free imports
pub use document::ParseError as LspParseError;
pub use document::TypeError as LspTypeError;

use tower_lsp::{LspService, Server};

/// Build the LSP service with Lean4 RPC custom methods
fn build_service() -> (LspService<CleanBackend>, tower_lsp::ClientSocket) {
    LspService::build(CleanBackend::new)
        // $/lean/rpc/connect - Start RPC session
        .custom_method("$/lean/rpc/connect", |backend: &CleanBackend, params| {
            std::future::ready(backend.rpc_connect(params))
        })
        // $/lean/rpc/call - Invoke RPC procedure
        .custom_method("$/lean/rpc/call", |backend: &CleanBackend, params| {
            std::future::ready(backend.rpc_call(params))
        })
        // $/lean/rpc/release - Release references (notification)
        .custom_method("$/lean/rpc/release", |backend: &CleanBackend, params| {
            backend.rpc_release(params);
            std::future::ready(Ok(()))
        })
        // $/lean/rpc/keepAlive - Keep session alive (notification)
        .custom_method("$/lean/rpc/keepAlive", |backend: &CleanBackend, params| {
            backend.rpc_keep_alive(params);
            std::future::ready(Ok(()))
        })
        // $/lean/plainGoal - Get tactic goals as plain text
        .custom_method("$/lean/plainGoal", |backend: &CleanBackend, params| {
            std::future::ready(Ok(backend.plain_goal(params)))
        })
        // $/lean/plainTermGoal - Get expected type as plain text
        .custom_method("$/lean/plainTermGoal", |backend: &CleanBackend, params| {
            std::future::ready(Ok(backend.plain_term_goal(params)))
        })
        .finish()
}

/// Run the LSP server on stdin/stdout
pub async fn run_server() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = build_service();
    Server::new(stdin, stdout, socket).serve(service).await;
}

/// Run the LSP server on a TCP socket (for testing)
pub async fn run_server_tcp(addr: &str) -> Result<(), std::io::Error> {
    let listener = tokio::net::TcpListener::bind(addr).await?;
    tracing::info!("LSP server listening on {}", addr);

    loop {
        let (stream, _) = listener.accept().await?;
        let (read, write) = tokio::io::split(stream);

        let (service, socket) = build_service();
        tokio::spawn(async move {
            Server::new(read, write, socket).serve(service).await;
        });
    }
}

// Tests are in the individual modules
