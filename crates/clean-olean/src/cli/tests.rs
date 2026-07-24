// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for `clean olean` clap parsing, resolve_args validation, and
//! [`FEATURES`] descriptor shape.

use std::path::PathBuf;

use clap::Parser;
use clean_features::{ensure_has_example, ensure_unique_paths, FeatureDescriptor};

use super::runner::resolve_args;
use super::{run, OleanArgs, OleanCliError, OleanCommands, VerifyBatchArgs, FEATURES};

/// Tiny parser embedding [`OleanArgs`] so we can exercise clap integration.
#[derive(Debug, Parser)]
struct Harness {
    #[command(subcommand)]
    command: Top,
}

#[derive(Debug, clap::Subcommand)]
enum Top {
    Olean(OleanArgs),
}

#[test]
fn test_verify_batch_defaults_parse() {
    let h =
        Harness::try_parse_from(["clean", "olean", "verify-batch", "/tmp/oleans"]).expect("parse");
    match h.command {
        Top::Olean(args) => match args.command {
            OleanCommands::VerifyBatch(a) => {
                assert_eq!(a.olean_dir, PathBuf::from("/tmp/oleans"));
                assert!(a.init_paths.is_empty());
                assert!(!a.json);
                assert_eq!(a.parallel, 1);
                assert!(!a.isolated);
                assert!(!a.load_only);
                assert!(!a.full_validation);
            }
            other => panic!("expected VerifyBatch, got {other:?}"),
        },
    }
}

#[test]
fn test_verify_batch_full_flag_set_parse() {
    let h = Harness::try_parse_from([
        "clean",
        "olean",
        "verify-batch",
        "/tmp/oleans",
        "--init-path",
        "/opt/lean/lib",
        "--init-path",
        "/usr/local/lib/lean",
        "--json",
        "--json-report",
        "report.json",
        "--limit",
        "10",
        "--isolated",
        "--load-only",
        "--parallel",
        "4",
        "--cache-file",
        "verify.cache",
        "--full-validation",
    ])
    .expect("parse");
    match h.command {
        Top::Olean(args) => match args.command {
            OleanCommands::VerifyBatch(a) => {
                assert_eq!(a.olean_dir, PathBuf::from("/tmp/oleans"));
                assert_eq!(a.init_paths.len(), 2);
                assert!(a.json);
                assert_eq!(a.json_report, Some(PathBuf::from("report.json")));
                assert_eq!(a.limit, Some(10));
                assert!(a.isolated);
                assert!(a.load_only);
                assert_eq!(a.parallel, 4);
                assert_eq!(a.cache_file, Some(PathBuf::from("verify.cache")));
                assert!(a.full_validation);
            }
            other => panic!("expected VerifyBatch, got {other:?}"),
        },
    }
}

#[test]
fn test_resolve_args_rejects_zero_parallel() {
    let args = VerifyBatchArgs {
        olean_dir: PathBuf::from("."),
        init_paths: Vec::new(),
        json: false,
        json_report: None,
        limit: None,
        isolated: false,
        load_only: false,
        parallel: 0,
        cache_file: None,
        full_validation: false,
        max_heartbeats: None,
        stream_elide_proof_values: super::StreamElidePolicy::None,
        cache_dir: None,
    };
    let err = resolve_args(args).expect_err("should reject --parallel 0");
    assert!(matches!(err, OleanCliError::InvalidParallel));
}

#[test]
fn test_resolve_args_rejects_non_directory() {
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    let args = VerifyBatchArgs {
        olean_dir: tmp.path().to_path_buf(),
        init_paths: Vec::new(),
        json: false,
        json_report: None,
        limit: None,
        isolated: false,
        load_only: false,
        parallel: 1,
        cache_file: None,
        full_validation: false,
        max_heartbeats: None,
        stream_elide_proof_values: super::StreamElidePolicy::None,
        cache_dir: None,
    };
    let err = resolve_args(args).expect_err("should reject file path");
    assert!(matches!(err, OleanCliError::NotADirectory(_)));
}

#[test]
fn test_features_paths_are_unique() {
    let descriptors: Vec<&FeatureDescriptor> = FEATURES.iter().collect();
    ensure_unique_paths(&descriptors).expect("olean descriptor paths must be unique");
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
fn test_feature_path_under_olean_root() {
    for d in FEATURES {
        assert_eq!(
            d.path[0],
            "olean",
            "descriptor `{}` must live under `olean`",
            d.path_display()
        );
    }
}

#[test]
fn test_generate_overlay_parses_required_flags() {
    let h = Harness::try_parse_from([
        "clean",
        "olean",
        "generate-overlay",
        "--output-dir",
        "/tmp/overlay",
        "--namespace",
        "Topology.Manifold",
        "--seed-topology-env",
    ])
    .expect("parse");
    match h.command {
        Top::Olean(args) => match args.command {
            OleanCommands::GenerateOverlay(g) => {
                assert_eq!(g.output_dir, PathBuf::from("/tmp/overlay"));
                assert_eq!(g.namespaces, vec!["Topology.Manifold".to_owned()]);
                assert!(g.seed_topology_env);
                assert!(g.modules.is_empty());
            }
            other => panic!("expected GenerateOverlay, got {other:?}"),
        },
    }
}

#[test]
fn test_generate_overlay_requires_source() {
    // Parsing succeeds; the dispatcher enforces the module-or-seed requirement.
    let h = Harness::try_parse_from([
        "clean",
        "olean",
        "generate-overlay",
        "--output-dir",
        "out",
        "--namespace",
        "Foo",
    ])
    .expect("parse");
    match h.command {
        Top::Olean(args) => {
            let err = run(args).expect_err("missing module/seed must error");
            assert!(matches!(err, OleanCliError::NoOverlaySource));
        }
    }
}
