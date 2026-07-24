// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI surface for `clean server` (JSON-RPC server entrypoint).
//!
//! Part of Epic #3436 Phase 2. `clean server` is a single command — its args
//! live in [`ServerArgs`] and the top-level dispatcher invokes the server with
//! those fields. The [`FEATURES`] array registers one descriptor for the
//! unified feature index.
//!
//! Design: `designs/2026-04-18-unified-cli-feature-index.md`.

use std::path::PathBuf;

use clap::Args;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

/// Arguments for `clean server`.
#[derive(Args, Debug)]
pub struct ServerArgs {
    /// Port to listen on
    #[arg(short, long, default_value = "8080")]
    pub port: u16,
    /// Disable GPU acceleration
    #[arg(long)]
    pub no_gpu: bool,
    /// Use WebSocket transport instead of TCP
    #[arg(long)]
    pub websocket: bool,
    /// Pre-load Lean 4 Init library (.olean) at startup
    #[arg(long)]
    pub init: bool,
    /// Pre-load Lean 4 Std library (.olean) at startup (includes Init)
    #[arg(long)]
    pub stdlib: bool,
    /// Load a precomputed math theorem-index JSON file for proof-state theorem search
    #[arg(long, value_name = "PATH")]
    pub theorem_index: Option<PathBuf>,
}

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-server",
    target: "clean-server",
};

/// Descriptors for the `clean server` command.
pub const FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["server"],
    summary: "Start the clean JSON-RPC server",
    description: "Serves the clean verification API over JSON-RPC. The \
default TCP transport listens on `127.0.0.1:<port>`; pass `--websocket` for \
the WebSocket transport. `--init` / `--stdlib` pre-load Lean 4 Init or Std \
`.olean` files so the first request does not pay load cost. `--theorem-index` \
loads a precomputed math-project theorem index for proof-state theorem search.",
    category: Category::Meta,
    stability: Stability::V1,
    examples: &[Example {
        cmd: "clean server --port 8080 --init --theorem-index reports/math/theorem-index.json",
        what: "start the RPC server with Init and a math-project theorem index pre-loaded",
    }],
    see_also: &["repl"],
    references: &[DESIGN_REF, CRATE_REF],
    domain_root: Some("server"),
    alternative_forms: &[],
    feature_gate: None,
}];
