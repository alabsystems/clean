// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feature descriptors for the `clean lsp` subcommand.
//!
//! The top-level binary registers these via
//! `v.extend(clean_lsp::cli::FEATURES)` in `clean-cli`'s `registry.rs`.
//! Keep the path segments in sync with the clap tree defined in
//! [`super::LspArgs`]; the drift tests in
//! `crates/clean-cli/tests/feature_coverage.rs` enforce this contract.

use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

const UNIFIED_CLI_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const ORPHAN_INVENTORY_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "CLI orphan inventory — standalone binary absorption",
    target: "designs/2026-04-18-cli-orphan-inventory.md",
};

const ISSUE_3436: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic: unified CLI as feature index",
    target: "#3436",
};

const ISSUE_3450: Reference = Reference {
    kind: RefKind::Issue,
    label: "Absorb clean-lsp into clean lsp (retain standalone shim)",
    target: "#3450",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-lsp",
    target: "clean-lsp",
};

const LSP_DESCRIPTION: &str = "\
Start the clean Language Server Protocol implementation.

Serves the LSP protocol to IDE clients: real-time parse and type error \
diagnostics, hover type info, go-to-definition, find references, document \
symbols, completion, and Lean4-compatible RPC endpoints for infoview \
(`$/lean/rpc/*` and `$/lean/plainGoal` / `$/lean/plainTermGoal`).

The default transport is stdio — the client launches the server as a \
subprocess and reads/writes framed JSON-RPC on its stdin/stdout. Pass \
`--stdio` explicitly for forward-compatibility with editor launch scripts \
that pass the flag as a convention. Pass `--tcp <ADDR>` to bind a TCP \
listener instead (useful for integration tests and IDE configurations that \
prefer TCP over spawning a subprocess).

The legacy `clean-lsp` standalone binary is retained as a thin passthrough \
shim because editor configurations hard-code its path (e.g. Neovim \
lspconfig `cmd = { \"clean-lsp\" }`). The shim silently re-exec's \
`clean lsp` with identical arguments so existing configurations keep \
working. Part of #3450, Epic #3436.
";

const LSP_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["lsp"],
    domain_root: Some("lsp"),
    alternative_forms: &[],
    feature_gate: None,
    summary: "clean Language Server (LSP) — IDE diagnostics, hover, goto, infoview RPC",
    description: LSP_DESCRIPTION,
    category: Category::Dev,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean lsp",
            what: "Serve LSP over stdio (default; launched by editor clients as a subprocess).",
        },
        Example {
            cmd: "clean lsp --stdio",
            what: "Explicit stdio transport — matches editor launch scripts that pass `--stdio`.",
        },
        Example {
            cmd: "clean lsp --tcp 127.0.0.1:9999",
            what: "Bind a TCP listener on the given address (integration-testing transport).",
        },
    ],
    see_also: &["server"],
    references: &[
        UNIFIED_CLI_REF,
        ORPHAN_INVENTORY_REF,
        ISSUE_3436,
        ISSUE_3450,
        CRATE_REF,
    ],
};

/// Static feature descriptor array registered by the top-level `clean` CLI.
///
/// The drift tests in `crates/clean-cli/tests/feature_coverage.rs` fail the
/// build if a clap path is missing from this list (or vice versa).
pub const FEATURES: &[FeatureDescriptor] = &[LSP_DESC];
