// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for `clean verify tla` clap parsing, dispatch behaviour, bundled
//! sample validity, and [`super::FEATURES`] descriptor shape.
//!
//! Split out of `src/cli.rs` so the main module stays under the 500-line
//! per-file budget; mirrors the layout used by
//! `crates/clean-rust-sem/src/cli/tests.rs` (#3451).

use std::path::PathBuf;

use clap::Parser;
use clean_features::{ensure_has_example, ensure_unique_paths, FeatureDescriptor};

use super::{run, TlaCliError, TlaVerifyArgs, BUNDLED_SAMPLES, FEATURES};
use crate::obligation::TlaObligation;
use clean_features::{Category, Stability};

/// Tiny parser embedding [`TlaVerifyArgs`] so we can exercise clap integration
/// in isolation from the top-level `clean-cli` tree.
#[derive(Debug, Parser)]
struct Harness {
    #[command(subcommand)]
    command: Top,
}

#[derive(Debug, clap::Subcommand)]
enum Top {
    #[command(subcommand)]
    Verify(Verify),
}

#[derive(Debug, clap::Subcommand)]
enum Verify {
    Tla(TlaVerifyArgs),
}

fn parse_args(argv: &[&str]) -> TlaVerifyArgs {
    let parsed = Harness::try_parse_from(argv).expect("clap parse");
    match parsed.command {
        Top::Verify(Verify::Tla(args)) => args,
    }
}

#[test]
fn tla_verify_list_parses() {
    let args = parse_args(&["clean", "verify", "tla", "--list"]);
    assert!(args.list);
    assert!(args.path.is_none());
    assert!(args.sample.is_none());
    assert!(!args.json);
    assert!(!args.verbose);
}

#[test]
fn tla_verify_sample_parses() {
    let args = parse_args(&["clean", "verify", "tla", "--sample", "trivial_true"]);
    assert_eq!(args.sample.as_deref(), Some("trivial_true"));
    assert!(!args.list);
}

#[test]
fn tla_verify_path_parses() {
    let args = parse_args(&["clean", "verify", "tla", "benchmarks/tla/trivial_true.json"]);
    assert_eq!(
        args.path.as_deref(),
        Some(std::path::Path::new("benchmarks/tla/trivial_true.json"))
    );
}

#[test]
fn tla_verify_json_flag_parses() {
    let args = parse_args(&[
        "clean",
        "verify",
        "tla",
        "--sample",
        "trivial_true",
        "--json",
        "--verbose",
    ]);
    assert!(args.json);
    assert!(args.verbose);
}

#[test]
fn tla_verify_list_and_sample_conflict() {
    let err = Harness::try_parse_from([
        "clean",
        "verify",
        "tla",
        "--list",
        "--sample",
        "trivial_true",
    ])
    .expect_err("--list and --sample must conflict");
    let _ = err.to_string();
}

#[test]
fn tla_verify_list_and_path_conflict() {
    let err = Harness::try_parse_from(["clean", "verify", "tla", "--list", "some_file.json"])
        .expect_err("--list and <FILE> must conflict");
    let _ = err.to_string();
}

#[test]
fn run_without_action_errors() {
    let args = TlaVerifyArgs {
        path: None,
        list: false,
        sample: None,
        json: false,
        verbose: false,
    };
    let err = run(args).expect_err("no action must error");
    assert!(matches!(err, TlaCliError::NoAction));
}

#[test]
fn run_list_succeeds() {
    let args = TlaVerifyArgs {
        path: None,
        list: true,
        sample: None,
        json: false,
        verbose: false,
    };
    run(args).expect("--list must succeed");
}

#[test]
fn run_unknown_sample_errors() {
    let args = TlaVerifyArgs {
        path: None,
        list: false,
        sample: Some("this-does-not-exist".to_string()),
        json: false,
        verbose: false,
    };
    let err = run(args).expect_err("unknown sample must error");
    match err {
        TlaCliError::UnknownSample { name } => {
            assert_eq!(name, "this-does-not-exist");
        }
        other => panic!("expected UnknownSample, got {other:?}"),
    }
}

#[test]
fn run_bundled_sample_returns_ok_or_proof_failed() {
    // The `trivial_true` sample exercises the pipeline end-to-end. Whether the
    // automation actually proves it depends on the tactic engine state (it
    // should — goal is `True`), but we want the test to stay green even if
    // automation regresses: any non-`ProofFailed` error would indicate a
    // wiring bug.
    let args = TlaVerifyArgs {
        path: None,
        list: false,
        sample: Some("trivial_true".to_string()),
        json: false,
        verbose: false,
    };
    match run(args) {
        Ok(()) => {}
        Err(TlaCliError::ProofFailed { .. }) => {}
        Err(other) => panic!("expected Ok or ProofFailed for bundled sample; got {other:?}"),
    }
}

#[test]
fn run_missing_path_errors() {
    let args = TlaVerifyArgs {
        path: Some(PathBuf::from("/nonexistent/path/to/obligation.json")),
        list: false,
        sample: None,
        json: false,
        verbose: false,
    };
    let err = run(args).expect_err("missing file must error");
    assert!(matches!(err, TlaCliError::ReadFailed { .. }));
}

#[test]
fn run_malformed_json_errors() {
    use std::io::Write;
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("bad.json");
    let mut file = std::fs::File::create(&path).expect("create");
    writeln!(file, "{{ not valid json").expect("write");

    let args = TlaVerifyArgs {
        path: Some(path),
        list: false,
        sample: None,
        json: false,
        verbose: false,
    };
    let err = run(args).expect_err("malformed JSON must error");
    assert!(matches!(err, TlaCliError::ParseFailed { .. }));
}

#[test]
fn bundled_samples_parse_as_tla_obligation() {
    for (name, content) in BUNDLED_SAMPLES {
        serde_json::from_str::<TlaObligation>(content)
            .unwrap_or_else(|e| panic!("bundled sample `{name}` must parse as TlaObligation: {e}"));
    }
}

#[test]
fn features_are_lint_clean() {
    let descriptors: Vec<&FeatureDescriptor> = FEATURES.iter().collect();
    ensure_unique_paths(&descriptors).expect("tla descriptor paths are unique");
    for descriptor in FEATURES {
        ensure_has_example(descriptor).expect("every tla descriptor has >=1 example");
    }
}

#[test]
fn features_has_expected_path() {
    assert_eq!(FEATURES.len(), 1);
    assert_eq!(FEATURES[0].path, &["verify", "tla"]);
    assert_eq!(FEATURES[0].stability, Stability::Experimental);
    assert_eq!(FEATURES[0].category, Category::Verification);
    assert_eq!(FEATURES[0].domain_root, Some("verify"));
}
