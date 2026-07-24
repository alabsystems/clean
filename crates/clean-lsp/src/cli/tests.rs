// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for `clean lsp` clap parsing and [`FEATURES`] descriptor shape.

use clap::Parser;
use clean_features::{ensure_has_example, ensure_unique_paths, FeatureDescriptor};

use super::{LspArgs, FEATURES};

/// Tiny parser embedding [`LspArgs`] so we can exercise clap integration
/// without pulling in the full top-level `clean_cli::cli_args::Cli` tree.
#[derive(Debug, Parser)]
struct Harness {
    #[command(subcommand)]
    command: Top,
}

#[derive(Debug, clap::Subcommand)]
enum Top {
    Lsp(LspArgs),
}

#[test]
fn test_lsp_defaults_parse() {
    let h = Harness::try_parse_from(["clean", "lsp"]).expect("parse");
    match h.command {
        Top::Lsp(args) => {
            assert!(!args.stdio, "stdio defaults to false when flag omitted");
            assert!(args.tcp.is_none(), "tcp defaults to None");
        }
    }
}

#[test]
fn test_lsp_stdio_flag_parse() {
    let h = Harness::try_parse_from(["clean", "lsp", "--stdio"]).expect("parse");
    match h.command {
        Top::Lsp(args) => {
            assert!(args.stdio, "--stdio must flip the flag");
            assert!(args.tcp.is_none(), "--stdio must not populate tcp");
        }
    }
}

#[test]
fn test_lsp_tcp_flag_parse() {
    let h = Harness::try_parse_from(["clean", "lsp", "--tcp", "127.0.0.1:9999"]).expect("parse");
    match h.command {
        Top::Lsp(args) => {
            assert!(!args.stdio);
            assert_eq!(args.tcp.as_deref(), Some("127.0.0.1:9999"));
        }
    }
}

#[test]
fn test_lsp_stdio_and_tcp_conflict() {
    // `conflicts_with = "tcp"` on `stdio` must reject the combined form so
    // callers get a clear error instead of a silent-priority decision.
    let err = Harness::try_parse_from(["clean", "lsp", "--stdio", "--tcp", "127.0.0.1:9999"])
        .expect_err("--stdio and --tcp must conflict");
    assert!(
        err.to_string()
            .to_lowercase()
            .contains("cannot be used with"),
        "expected clap conflict error, got: {err}"
    );
}

#[test]
fn test_features_paths_are_unique() {
    let descriptors: Vec<&FeatureDescriptor> = FEATURES.iter().collect();
    ensure_unique_paths(&descriptors).expect("lsp descriptor paths must be unique");
}

#[test]
fn test_every_feature_has_an_example() {
    for d in FEATURES {
        ensure_has_example(d).unwrap_or_else(|e| {
            panic!(
                "descriptor `{}` must have at least one example: {e}",
                d.path_display()
            )
        });
    }
}

#[test]
fn test_feature_path_under_lsp_root() {
    for d in FEATURES {
        assert_eq!(
            d.path[0],
            "lsp",
            "descriptor `{}` must live under `lsp`",
            d.path_display()
        );
    }
}

#[test]
fn test_features_register_single_descriptor() {
    // Guard against accidental descriptor duplication or removal when sibling
    // PRs edit the array. `clean lsp` has exactly one verb (unlike the
    // `olean` / `kernel` roots which aggregate multiple absorbed binaries).
    assert_eq!(
        FEATURES.len(),
        1,
        "clean lsp is a single-verb root; grew to {} descriptors — \
         update this test if a new sub-verb lands, or consolidate",
        FEATURES.len()
    );
}
